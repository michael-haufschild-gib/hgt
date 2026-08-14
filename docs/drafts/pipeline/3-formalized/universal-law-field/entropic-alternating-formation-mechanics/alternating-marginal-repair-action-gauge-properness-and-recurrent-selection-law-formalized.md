# Alternating marginal repair, action conservation, gauge properness, and recurrent selection — formalized

- **ID:** `ulf-eafm-1-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper source:** `docs/drafts/pipeline/3-formalized/universal-law-field/entropic-alternating-formation-mechanics/alternating-marginal-repair-action-gauge-properness-and-recurrent-selection-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-AUDITED] [UMBRELLA-WIRED]`
  `[BRIDGE] [SINKHORN/IPFP CALIBRATION] [NOT FIELD CORE] [NOT RH]`

## Certified mechanism

| Paper law | Lean declaration |
|---|---|
| common-conditional marginal formation | `marginalRepair` |
| exact KL Pythagoras | `klDiv_marginalRepair_pythagorean` |
| arbitrary finite repair-action conservation | `repairHistory_conservation` |
| recurrent finite history forces every step stationary | `repairHistory_cycle_stationary` |
| global real-action conservation | `realActionRepairHistory_conservation` |
| cofinal approximate recurrence forces all generated action to vanish | `recurrentRealActionRepairHistory_stationary` |
| two-step conservation and stationary recurrence | `twoStepRepair_conservation`, `twoStepRepair_cycle_stationary` |
| exact row and column marginal repair | `bipartiteRowMass_rowRepair`, `bipartiteColumnMass_columnRepair` |
| uniqueness inside the multiplicative row/column repair classes | `bipartiteRowRepair_unique`, `bipartiteColumnRepair_unique` |
| functional reflection exchanges repairs | `bipartiteRowRepair_transpose`, `bipartiteColumnRepair_transpose` |
| literal finite-array KL, Gibbs nonnegativity, and equality criterion | `bipartiteRelativeEntropy`, `bipartiteRelativeEntropy_nonneg`, `bipartiteRelativeEntropy_eq_zero_iff` |
| literal row/column information projections | `bipartiteRelativeEntropy_rowRepair_pythagorean`, `bipartiteRelativeEntropy_columnRepair_pythagorean` |
| finite-array KL reflection invariance | `bipartiteRelativeEntropy_transpose` |
| positive feasible product packet and exact marginals | `bipartiteProductWitness_pos`, `bipartiteProductWitness_rowMass`, `bipartiteProductWitness_columnMass` |
| literal alternating repair history and positivity | `bipartiteAlternatingRepairHistory`, `bipartiteAlternatingRepairHistory_pos` |
| literal global action conservation, monotonicity, and initial-divergence bound | `bipartiteProductWitness_alternatingRepairHistory_conservation`, `monotone_bipartiteAlternatingRepairAction`, `bipartiteAlternatingRepairAction_le_initial` |
| literal recurrent history forces both target marginals and stationarity | `bipartiteProductWitness_alternatingRepairHistory_cycle_balanced` |
| potential formation has the global gauge | `bipartitePotentialForm_gauge`, `bipartitePotentialForm_eq_self_iff_gauge` |
| positive formation energy has exactly that radical | `bipartiteFormationEnergy_eq_zero_iff_gauge` |
| reflection preserves formation energy | `bipartiteFormationEnergy_transpose` |
| actual quotient kernel is exactly the global gauge line | `bipartiteEdgeSumLinearMap_ker`, `bipartiteQuotientEdgeSum_injective` |
| descended quotient energy is positive definite | `bipartiteQuotientFormationEnergy_eq_zero_iff` |
| every quotient-energy sublevel is compact | `isCompact_bipartiteQuotientFormationEnergy_sublevel` |

## Interpretation

Lean certifies an exact finite entropic-repair calibration: failure-driven marginal repairs pay exact
nonnegative KL action; accumulated action telescopes; a recurrent finite history with finite target
divergence cannot move. In the positive bipartite chart, functional reflection exchanges the two
repair laws while the formation stabilizer and positive-energy radical coincide in one global
gauge direction. Whole-corpus audit shows this is not the first field mechanism: the targets and
schedule remain supplied, while the earlier abelian-relaxation theorem already generates legality,
repair, completion, recurrence, lineage, and work from one source. The theorem does not supply an
RH specialization or arithmetic source packet.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveEntropicAlternatingFormation.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint
```

Direct elaboration and targeted leaf build (3,492 jobs) passed in foreground. A missing cached
`ConstitutiveEssentialFormationMechanics.olean` was directly checked and rebuilt as its named
module only; domain umbrella then directly elaborated cleanly. Scratch `#print axioms` for literal
product-history conservation and cycle balance, entropy transpose invariance, recurrent real-action
selection, quotient positive-definiteness, and compact quotient sublevels reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden-token scan and `git diff --check` are clean. No
`sorry`, `admit`, added axiom, `opaque`, `unsafe`, computation certificate, or enlarged heartbeat is
used here. Project-wide `scripts/formal_tools.py lint` source checks completed, but its umbrella
reachability gate exits nonzero on unrelated concurrent `RHTower.FieldOne*`, `RHTower.Hedenmalm*`,
`RHTower.Sieve.Maynard*`, `RHTower.Suzuki*`, `RHTower.Xi*`, and
`HTGeometry.CauchyTransformOpenUniqueness` modules; this card's module remains directly reachable
from `GaloisForLFunctions.HTGeometry.UniversalLawField`.
