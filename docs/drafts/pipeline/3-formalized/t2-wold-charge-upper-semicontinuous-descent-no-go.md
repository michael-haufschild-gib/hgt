# T2 Wold-charge upper-semicontinuous descent no-go

- **ID:** T2-USC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** T2
- **Statement:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` A compact-open sequentially upper-semicontinuous scalar majorant of every canonical multiplicity-matched Wold orbit charge exists exactly under RH.

## RH proof chain

`upper-semicontinuous exact charge descent → no strict-right Xi divisor → RH`.
This kills every one-sided-regular scalar repair of T2's canonical singular current. A survivor must retain source marking or exhibit a downward compact-open singularity of at least one Wold quantum.

## Frontier

- `[CORPUS]` `xiSourceMatchedBubble_tendstoLocallyUniformly`: every off-line Xi copy has canonical source-matched bubbles converging compact-open to `xi`.
- `[CORPUS]` `two_le_xiReflectedWoldOrbitChargeEnergy_of_re_ne_half`: every off-line bubble retains charge energy at least `2`; wall charge is zero.
- `[CORPUS]` `xiWoldOrbitChargeEnergyCompactOpenDescent_iff_riemannHypothesis`: exact sequentially continuous descent is RH-equivalent; upper semicontinuity and lower-majorant faithfulness are untreated.
- `[LITERATURE]` Hurwitz/Poincaré--Lelong theory controls divisors locally under compact-open convergence. Noncompact zero-current convergence requires additional tightness/boundedness; no exact Xi/Wold charge-majorant classification was found: https://arxiv.org/abs/1106.5244, https://doi.org/10.1007/s12220-024-01847-8.

## Paper proof

Define sequential upper semicontinuity by eventual inequalities `Q(F_n) ≤ Q(f)+ε` under locally uniform convergence. Under `¬RH`, choose an off-line divisor. Faithfulness gives `2 ≤ charge ≤ Q(bubble_n)` for every `n`, while the anchor gives `Q(xi)≤0`; upper semicontinuity with `ε=1` forces eventually `Q(bubble_n)≤1`, contradiction. Under RH, the zero reporter works because every Wold charge vanishes. Moreover every faithful anchored reporter under `¬RH` has a canonical bubble with `Q(xi)+2 ≤ Q(bubble_n)` for every `n`; this is the sharp positive jump survivor.

## Hostile attack

- Exact equality is not assumed: only charge domination is required.
- Continuity is not assumed: only the upper half of sequential continuity is used.
- No compactness of the full divisor or bounded reporter is assumed.
- **Verdict:** `SURVIVES HOSTILE AUDIT`.

## Gates

- [x] 0 → 1 in-progress: corpus frontier, external parent-theory audit, exact falsifiable claim, RH chain
- [x] 1 → 2 fully-proven: dependency-closed epsilon-one contradiction and quantified jump survivor
- [x] 2 → 3 formalized: `XiHeatCassiniWoldOrbitChargeUpperSemicontinuousNoGo.lean`; source check and targeted build pass; axiom audit is `[propext, Classical.choice, Quot.sound]`
