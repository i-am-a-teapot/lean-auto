import Lean
import Auto.Lib.ExprExtra
import Auto.Lib.MetaExtra
open Lean Meta

private instance : ToString TransparencyMode where
  toString : TransparencyMode → String
  | .all       => "all"
  | .default   => "default"
  | .reducible => "reducible"
  | .instances => "instances"
  | .none      => "none"

private instance : Lean.KVMap.Value TransparencyMode where
  toDataValue t := toString t
  ofDataValue?
  | "all"       => some .all
  | "default"   => some .default
  | "reducible" => some .reducible
  | "instances" => some .instances
  | "none"      => some .none
  | _           => none

register_option auto.redMode : TransparencyMode := {
  defValue := .reducible
  descr := "TransparencyMode used when reducing collected facts"
}

register_option auto.mono.tyRed.mode : Meta.TransparencyMode := {
  defValue := .reducible
  descr := "Transparency level used when reducing types. The default mode `reducible` does nothing."
}

register_option auto.mono.tyDefEq.mode : Meta.TransparencyMode := {
  defValue := .default
  descr := "Transparency level used when testing definitional equality of types"
}

namespace Auto

def unfoldProj (e : Expr) : MetaM Expr :=
  match e with
  | .proj name idx struct => do
    let some (.inductInfo indi) := (← getEnv).find? name
      | throwError s!"{decl_name%} :: {name} is not a inductive type"
    let some structInfo := getStructureInfo? (← getEnv) name
      | throwError s!"{decl_name%} :: {name} is not a structure"
    let some projection := structInfo.getProjFn? idx
      | throwError s!"{decl_name%} :: Projection index out of bound"
    -- A primitive projection already fixes every structure parameter,
    -- including the exact class instances used by dependent fields. Asking
    -- instance search to reconstruct those parameters can fail or choose a
    -- different instance. Recover them from the structure value's type.
    let type ← Meta.whnf (← Meta.inferType struct)
    let parameters := type.getAppArgs
    unless type.getAppFn.isConstOf name && parameters.size == indi.numParams do
      throwError s!"{decl_name%} :: Unexpected structure type {type}"
    Meta.mkAppOptM projection ((parameters.map some).push (some struct))
  | _ => return e

def prepReduceExprWithMode (term : Expr) (mode : TransparencyMode) : MetaM Expr := do
  let red (e : Expr) : MetaM TransformStep := do
    let e := e.consumeMData
    let e ← Meta.whnf e
    return .continue e
  -- Reduce
  let term ← Meta.withTransparency mode <| Meta.transform term (pre := red) (usedLetOnly := false)
  -- Unfold projection
  let term ← Meta.transform term (pre := fun e => do return .continue (← unfoldProj e))
  return term

/-- This function is expensive -/
def prepReduceExpr (term : Expr) : MetaM Expr := do
  let mode := auto.redMode.get (← getOptions)
  prepReduceExprWithMode term mode

/--
  We assume that all defeq facts have the form
    `∀ (x₁ : ⋯) ⋯ (xₙ : ⋯), c ... = ...`
  where `c` is a constant. To avoid `whnf` from reducing
  `c ⋯` (which can happen when e.g. `c` is a recursor), we
  call `forallTelescope`, then call `prepReduceExpr` on
  · All the arguments of `c`, and
  · The right-hand side of the equation
-/
def prepReduceDefeq (type : Expr) : MetaM (Option Expr) := do
  let type := Expr.eraseMData type
  Meta.forallTelescope type fun xs b => do
    let .app (.app (.app (.const ``Eq lvls) ty) lhs) rhs := b
      | return .none
    let ty ← prepReduceExpr ty
    let lhFn := lhs.getAppFn
    let lhArgs ← lhs.getAppArgs.mapM prepReduceExpr
    let lhs := mkAppN lhFn lhArgs
    let rhs ← prepReduceExpr rhs
    let eq' := Lean.mkApp3 (.const ``Eq lvls) ty lhs rhs
    return .some (← mkForallFVars xs eq')

/-- Expose function-type aliases without unfolding propositions used as domains.
For example `Set α` is an arrow type, whereas `¬p` must remain a proposition:
expanding it here introduces logical constants after instance collection. -/
private partial def normalizeFunctionTypeAliases (e : Expr) : MetaM Expr := do
  if ← Meta.isProp e then return e
  let e' ← Meta.withDefault <| Meta.whnfNondependentForall e
  match e' with
  | .forallE name domain body bi =>
    if body.hasLooseBVar 0 then return e
    return .forallE name (← normalizeFunctionTypeAliases domain)
      (← normalizeFunctionTypeAliases body) bi
  | _ => return e

def prepReduceTypeForall (e : Expr) : MetaM Expr := do
  let e ← prepReduceExpr e
  let e ← normalizeFunctionTypeAliases e
  let mode := auto.mono.tyRed.mode.get (← getOptions)
  Meta.withTransparency mode <| Meta.normalizeNondependentForall e

end Auto
