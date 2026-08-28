# KMSS source transposition classification and no-go (2026-08-28)

Current frontier map remained read-only.

Formal module:
- `formal/GaloisForLFunctions/RHTower/XiKoszulSourceTranspositionClassification.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- research card retired at `docs/drafts/pipeline/5-failed/kmss-source-transposition-isotypic-classification.md`

Results:
1. For every prime `p` and scalar `c : ℂ`, explicit all-prime Calderón--Witt legs give traced cups `c` and `-c`.
2. General transposition-character classification:
   `Nonempty (DeningerCalderonWittKoszulCharacterLift χ c) ↔ (χ + 1) * c = 0`.
3. Sign lifts are universal; trivial/order-blind lifts exist exactly for `c = 0`.
4. Strong no-go:
   `¬ Nonempty (DeningerCalderonWittOrderBlindCoefficientFaithfulCompletion p)`.
   No linear scalar completion can be both swap-invariant and coefficient-faithful even at one prime.
5. Tensoring with a second `-1` sign makes reverse-order compensation universal for every scalar, so Koszul/theta sign cancellation is RH-blind.
6. Canonical Xi signed cup vanishes iff the zero is on the critical line; universal vanishing at any fixed prime iff RH.

Interpretation:
- KMSS LAND already exists canonically in the sign representation.
- KMSS ORIENT, when formulated as coefficient-faithful order-blind scalar completion, is impossible.
- Adding a theta sign cancels obstruction tautologically and loses RH selectivity.
- Surviving direction would need an ordered/orientation-valued target or a genuinely non-equivariant fixed-orientation source law, not sign cancellation.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/XiKoszulSourceTranspositionClassification.lean` green.
- `lake build GaloisForLFunctions.RHTower.XiKoszulSourceTranspositionClassification` green.
- five capstones added to `scripts/check_axioms.sh`; audit passes with only `[propext, Classical.choice, Quot.sound]`.
- global lint forbidden-declaration scan clean; unrelated concurrently unwired modules make global reachability check fail.
- no stale Lean/lake processes.
- external search through 2026-08-28 found no exact paper match; generic sign obstruction is classical, so novelty claim is limited to exact corpus-defined source realization/no-go and remains search-negative, not expert-certified.
