import Lean

/-!
Audit declarations by their defining module, not their namespace: our theorems
live in Mathlib namespaces such as PointedCone. Uses Lean.collectAxioms.
The import-environment pattern follows Tau Ceti scripts/Axioms.lean and
importGraph (Kim Morrison, Paul Lezeau), Apache-2.0. This audit checks axiom
usage; the separate leanchecker replay checks proof terms.
-/
open Lean

def audit : CoreM (Nat × Array String) := do
  let env ← getEnv
  let mut count := 0
  let mut failures := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some mod := env.allImportedModuleNames[idx.toNat]? then
        if mod == `LeanFactory || (`LeanFactory).isPrefixOf mod then
          count := count + 1
          let axioms ← collectAxioms name
          let bad := axioms.filter fun a =>
            !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a
          if !bad.isEmpty then
            failures := failures.push s!"{name}: {bad.toList}"
  return (count, failures)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (count, failures) ← unsafe Lean.withImportModules #[{ module := `LeanFactory }] {}
    (trustLevel := 1024) fun env =>
      Prod.fst <$> Core.CoreM.toIO audit
        (ctx := { fileName := "axiom-audit", fileMap := default }) (s := { env := env })
  IO.println s!"Audited {count} declarations by defining module"
  for failure in failures do IO.eprintln failure
  return if count == 0 || !failures.isEmpty then 1 else 0
