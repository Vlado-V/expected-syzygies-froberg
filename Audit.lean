module

public import ESCtoFroberg
public import Solution
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Axiom audit of the loaded proof development. Only the three standard Lean
axioms are permitted. The independent Challenge is deliberately not imported. -/

open Lean Elab Command in
elab "#audit_esc_to_froberg" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let roots : List Name := [`Froberg, `ESCtoFroberg, `Solution]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let some origin := moduleNames[idx.toNat]?
        | throwError "Missing origin-module metadata for {name}"
      if roots.any (fun root => root.isPrefixOf origin) then
        match info with
        | .axiomInfo _ | .thmInfo _ =>
          let axioms ← Lean.collectAxioms name
          for axiomName in axioms do
            unless allowed.contains axiomName do
              throwError "Unexpected axiom {axiomName} in {name} (origin {origin})"
          checked := checked + 1
        | _ => pure ()
  logInfo m!"PASS: {checked} loaded local theorem/axiom interfaces. Only propext, Classical.choice, and Quot.sound allowed."

#audit_esc_to_froberg

#print axioms ESCtoFrobergPaper.main_result
#print axioms ESCtoFroberg.main_result
#print axioms ESCtoFroberg.independent_main_result
