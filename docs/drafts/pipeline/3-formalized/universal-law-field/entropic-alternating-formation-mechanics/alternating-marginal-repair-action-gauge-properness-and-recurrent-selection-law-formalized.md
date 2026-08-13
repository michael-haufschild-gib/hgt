# Alternating marginal repair, action conservation, gauge properness, and recurrent selection — formalized

- **ID:** `ulf-eafm-1-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/entropic-alternating-formation-mechanics/alternating-marginal-repair-action-gauge-properness-and-recurrent-selection-law.md`
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
| potential formation has the global gauge | `bipartitePotentialForm_gauge`, `bipartitePotentialForm_eq_self_iff_gauge` |
| positive formation energy has exactly that radical | `bipartiteFormationEnergy_eq_zero_iff_gauge` |
| reflection preserves formation energy | `bipartiteFormationEnergy_transpose` |

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

Direct elaboration, leaf build (3,492 jobs), axiom audit, and universal-law-field umbrella build
(11,862 jobs) passed in the foreground. Scratch `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound` for audited capstones. The new module's forbidden-token scan
and `git diff --check` are clean. Project-wide `formal_tools.py lint` is currently blocked by
unrelated, concurrently added `RHTower.FieldOne*`, `RHTower.Sieve.Maynard*`, and
`RHTower.Suzuki*` modules not yet reachable from the `RHTower` umbrella; none belongs to this
task's allowed folder or module. No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, computation
certificate, or enlarged heartbeat is used here.
