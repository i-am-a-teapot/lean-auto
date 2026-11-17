import Auto.Tactic

open Lean Meta Elab Command

-- A caller-generated fact must reach reification exactly once. Returning the
-- same fact twice, and on every round, must terminate after one added round.
run_cmd liftTermElabM do
  let fact : Auto.Lemma := ⟨⟨mkConst ``True.intro, mkConst ``True, .leaf "extension test"⟩, #[]⟩
  let calls ← IO.mkRef 0
  let extend (_ : Array Auto.Lemma) := do
    calls.modify (· + 1)
    pure #[fact, fact]
  let count ← Auto.Monomorphization.monomorphize #[] #[]
    (fun state => pure state.facts.size) extend
  unless count == 1 do throwError "extension facts were lost or duplicated: {count}"
  unless (← calls.get) == 2 do throwError "extension failed to stop on repeated fact types"

-- Disabling extension rounds preserves the unextended problem and never calls
-- the hook. The optional callback also keeps old callers source-compatible.
run_cmd liftTermElabM do
  let calls ← IO.mkRef 0
  let count ← withOptions (fun opts => auto.mono.extensionRounds.set opts 0) <|
    Auto.Monomorphization.monomorphize #[] #[] (fun state => pure state.facts.size)
      (fun _ => do calls.modify (· + 1); pure #[])
  unless count == 0 && (← calls.get) == 0 do throwError "disabled extension ran"
  let original ← Auto.Monomorphization.monomorphize #[] #[] (fun state => pure state.facts.size)
  unless original == 0 do throwError "default callback changed the problem"

-- A productive callback that keeps discovering distinct facts must still obey
-- the configured round limit, rather than extending indefinitely.
run_cmd liftTermElabM do
  let calls ← IO.mkRef 0
  let count ← withOptions (fun opts => auto.mono.extensionRounds.set opts 2) <|
    Auto.Monomorphization.monomorphize #[] #[] (fun state => pure state.facts.size)
      (fun _ => do
        let n ← calls.get
        calls.modify (· + 1)
        let proof ← mkEqRefl (mkNatLit n)
        let fact : Auto.Lemma := ⟨⟨proof, ← inferType proof, .leaf "bounded extension"⟩, #[]⟩
        pure #[fact])
  unless count == 2 && (← calls.get) == 2 do throwError "extension round limit was ignored"
