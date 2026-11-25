import F3
import Lean.Util.CollectAxioms

/-!
Audit-only diagnostics. This file adds no mathematical assumptions or theorems.
It enumerates the public theorems actually present in the imported environment,
prints their types and transitive axiom dependencies, and rejects any axiom
outside the three ordinary logical axioms listed below.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option pp.universes false

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let entries := env.constants.toList.filter fun (name, info) =>
    (`F3).isPrefixOf name && (match info with | .thmInfo _ => true | _ => false)
  let entries := entries.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for (name, info) in entries do
    logInfo m!"AUDIT_TYPE {name} : {info.type}"
    let axioms ← collectAxioms name
    let axioms := axioms.qsort Name.lt
    logInfo m!"AUDIT_AXIOMS {name} := {axioms.toList}"
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in theorem {name}"
  logInfo m!"AUDIT_PUBLIC_THEOREM_COUNT {entries.size}"

#print F3.RowBound
#print F3.Feasible
#print F3.FeasibleValue
#print F3.OptimalValue
#print F3.frameValue
#print F3.frameSide
#print F3.GeometricSide
#print F3.geometricValue
#print F3.SharpValues
#print F3.formula
#print F3.CenteredTetrahedronEdge
#print F3.tetrahedronValue
#print F3.Dominance.FeasibleK
#print F3.General.FeasibleValue
#print F3.General.value
#print F3.General.GeometricSide
#print F3.General.geometricValue
#print F3.General.CoordinateAt
#print F3.General.SignedCoordinate
#print F3.General.BoundedOptimalCores
#print F3.General.ResidueStabilization
