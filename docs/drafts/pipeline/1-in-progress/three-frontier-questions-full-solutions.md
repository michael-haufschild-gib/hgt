# Joint edge payment, source orientation, and the heat count

- **ID:** three-frontier-questions
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.3
- **Statement:** Resolve Q1–Q3 and every listed subquestion by unconditional Lean theorems.

## Required conclusions

| Question | Required mathematical conclusion | Status |
|---|---|---|
| Q1 | All-vector logarithmic defect reserve for the complete Weil form; defect-relative conductor decomposition | Reserve formalized for each fixed overlap; prescribed growing-overlap horizon and conductor/shell decomposition open |
| Q1/A1 | Top-band joint cancellation, then top-band perturbations of Ramanujan modes | Pole-vector case formalized in `TheShellsAndThePoleCancelOnTheTopBand`; conductor perturbations open |
| Q1/A2 | Growing Euler heads and joint head–pole–tail cancellation | Growing-head theorem exists in `TheIndexOfAGrowingEulerHeadIsUnbounded`; joint cancellation open |
| Q1/O1 | Ramanujan–Plancherel decomposition of the shell block | Open |
| Q2 | Equality of the two actual Ξ source polarizations | Open; corpus theorem identifies this with RH |
| Q2/defect | Theta–prime expression for `(σ − 1/2)S(s) − Re(ξ′/ξ)(s)`, at some `σ > 1` | Full-divisor and prime identities formalized; two-limit theta reading at `s=4` in progress |
| Q2/charge | Theta-prefix reading of window collision charge with explicit error | Open |
| Q2/calibration | Integer analogue of the calibrated explicit-formula Rosati pairing | Formalized: `tsum_explicit_eq_xiWeilPolarization` and `norm_sq_sub_explicit_eq_half_reflectionDefect`; source and transitive standard-axiom audits passed |
| Q3 | Actual growth law for the de Bruijn–Newman nonreal count at zero | Open |
| Q3/flux | Consequence of summing the actual localized outer flux over heights | Open |
| Q3/tower | Arithmetic ceiling for a nonblind prime tower | Open |
| Q3/functional | Global monotone functional for the actual zero dynamics | Open |

## Proof discipline

Existing criteria, bounds and obstructions are inputs, not substitutes for these conclusions.
Every claimed solution requires the exact theorem, dependency audit and successful
`lake --old env lean` check. No unproved sign or analytic input may enter a premise.

## Mathematical inputs

- `riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`: exact orientation receiver.
- `exists_card_deep_le_mul_nonrealZeroCount`: transfers a heat-count law to deep-zero counts.
- `exists_abs_jointWitnessCoefficient_le_uniform_overlap`: the pole and shells cancel on the
  top-band witness with bound `Kφ G(c + 1 + log N)`, uniformly for `1 ≤ c ≤ N/4`.
  Arbitrary coefficient vectors remain outside this theorem.
- `completedShellEnergy_div_conductor_le` and `log_conductor_sub_log_overlap_le_completedEnergy`
  prove `E_m(c) ≥ E_1(c/m) ≥ log(m/c) + min(0, completeWeilSelfFinitePart φ 1)`.
  Both are uniform scalar laws with direct Lean and standard-axiom audits; finite-horizon
  operator transfer remains separate.

## Formalized fixed-overlap reserve

Let `R_N = (log N)I − P_N`, with conductor eigenvalues
`λ_m = γ + log m + tameDifferent(m)`. The row bounds compare `R_N` with `D_N`
up to an absolute multiple of the mass. Starting from the proved reserve
`W_N ≥ β(c)D_N − B(c)I`, `β(c) ≍ c⁻⁷`, set `δ(c)=β(c)/2`.
Then `W_N − δ(c)R_N` still has a positive defect reserve. Its conductor
quasimode energies are `E_m(c) − δ(c)λ_m`.

Proved scalar input: `E_m(c) ≥ δ(c)(λ_m − C log(2c))`, uniformly in `m,c≥1`.
For polynomially bounded `m`, use `E_m(c)≥0` and `tameDifferent(m)≤log m`.
For larger `m`, bound the finite shell correction using the divisor formula
for Ramanujan sums and a polynomial lower bound for the totient.
Finite Ramanujan approximation plus norm quasimodes transfers this floor to
the shifted matrices. `exists_completeWeil_logarithmic_defect_reserve` proves
`∃a,C>0, ∀c≥1, eventually N, ∀x`; direct Lean check and standard-axiom audit
passed. Proof: `../3-formalized/logarithmic-reserve-by-shifting-the-prime-energy.md`.

The constants are independent of `c`. The horizon is ineffective and depends
on `c`; no prescribed growing-overlap claim follows without a separate rate.

## Full-divisor resolvent identity

At `Re s>1`, positivity of `Re(s−ρ)⁻¹` gives absolute convergence of
`S(s)=Σ|s−ρ|⁻²`. The signed depth sum is
`(Re s−1/2)S(s)−Re ξ′/ξ(s)`. Reindexing by `ρ↦1−conj ρ` and using
`pair_depth_resolvent` identifies it with
`Σ 2(Re s−1/2)(Re ρ−1/2)²/(|s−ρ|²|s−ρ*|²)`.
Formalized in `HilbertianExplicitFormulas/TheXiResolventDepthIdentity.lean` as
`sub_mul_xiSamePointResolvent_sub_logDeriv`. Its prime expansion is
`xiResolventDepth_eq_samePoint_sub_arch_add_prime`. Direct Lean check passed;
both transitive axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`.
Theta-source identification remains separate.

## Gates

- [x] Full requested conclusions fixed.
- [ ] Dependency-closed paper proofs of every conclusion.
- [ ] Exact Lean formalizations, umbrella imports and axiom audits.
