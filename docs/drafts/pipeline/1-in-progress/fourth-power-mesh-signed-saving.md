# Fourth-power mesh signed saving

- **ID:** fourth-power-mesh-signed-saving
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3010/opus.md, Question 2
- **Statement:** For every ε > 0 there is C ≥ 0 such that, for every integer J ≥ 2,
  `mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C * (J : ℝ) ^ (3 + ε)`.

## Goal

Prove or refute this exact statement unconditionally and formalize the answer.
Criteria, weaker estimates, and obstructions do not resolve the question.

## Gates

- [x] Exact quantifiers checked in `QuasiRHPowerMeshMeanSquareAbscissa.lean`.
- [ ] Dependency-closed proof or refutation.
- [ ] Lean theorem; foreground `lake --old env lean` audit; standard axioms only;
  owning umbrella import.

## Mathematical state

`RHTower.xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower` identifies
the target with `∀ ρ : ℂ, xi ρ = 0 → 1/4 ≤ ρ.re ∧ ρ.re ≤ 3/4`.
The covariance differs from the literal tail square energy by a diagonal in
`[0, (9/25)J]`. The head costs at most `(9/25)J³` on this mesh.
Consequently the unpaid term is signed high-dilation cancellation, not either
of these already bounded contributions.

## Checked inputs and remaining gaps

- `mobiusHighDilationClippedAbelKernel_eq_full_add_terminal`: even `q = 1`
  retains a weighted Möbius prefix of length `M / 2` and a terminal sum.
  The quotient restriction `q < j` does not shorten that Möbius prefix.
- `mobiusDivisorFiniteClockEnergy_source_cancellation`: prime insertion pays
  a negative copied square but retains a signed mixed term. Its sign and
  cumulative size over growing prime cores remain unpaid.
- `mobiusDivisorFiniteClockEnergy_insert_cost_le`: the available absolute
  insertion cost contains `4^(P.card-1)`, hence gives no uniform growing-core
  estimate at the required exponent.
- `eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos`: for each
  fixed nonempty core `P`, the large-prime release coefficient has sign
  `(-1)^(P.card+1)`. Unqualified insertion monotonicity therefore fails.
  `mobiusDivisorPreparedPrimeCube_unconditional` arranges all signs on a
  prescribed finite prime cube, but bounds neither total helper energy cost
  nor the cutoff threshold uniformly over growing cores.
- `twoScaleSquareCutoffMultiplier_lt_one`: the quarter-threshold contraction
  controls a common-head cutoff error. The full receiver-energy recurrence
  is an additional, unproved statement.
- `MobiusProductFibre.pair_sign`: grouping a nonzero Möbius pair by its product
  gives the single Liouville sign of that product. Cancellation between
  distinct product fibres remains necessary.
- `ArithmeticIndexDescent.exists_fullPolarNonfirst_gamma_approximation`
  retains the complete Gamma energy and both pole moments after removing a
  fixed detail head. Its source omits the coarse prime form and first-prime
  mixed block; the estimate does not bound the complete Weil form.

These facts are existing results, not a proof, refutation, or retirement of
the target. No new arithmetic saving has been established.

## Verification

`lake --old env lean GaloisForLFunctions/RHTower/QuasiRHPowerMeshMeanSquareAbscissa.lean`
passes. A separate importing scratch file checked `#print axioms` for the
three-quarters equivalence, covariance comparison, and diagonal bound; all
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The requested upper bound and its negation remain unproved.

## Exact arithmetic content of the covariance

Write `M = j⁴`, `D = j³`, `F = primeFreeDivisorDefect`, `K(q) = mobiusHighDilationClippedAbelKernel M D q`.
Then `mobiusDivisorDilationTail M D = Σ_{q<j} F(q) K(q)`
(`mobiusDivisorDilationTail_pow_eq_Icc_pred_smallQuotient`), and by
`mobiusHighDilationClippedAbelKernel_eq_full_add_terminal` each `K(q)` is
`(√(q+1) − √q)·(Σ_{D<d≤M/(q+1)} μ(d)√d)` plus a terminal clipped Möbius sum over `(M/(q+1), M/q)`.
So the tail is a `j`-term combination of weighted Möbius sums over the hyperbola cells
`(M/(q+1), M/q]`, with divisor-side coefficients `F(q)`. The `q = 1` cell alone is
`F(1)·Σ_{j³<d<j⁴} μ(d)(√min(M, 2d) − √d)` with `F(1) = 2γ − 1 ≠ 0`: a smoothed Mertens
sum over `(M^{3/4}, M)` of trivial size `M^{3/2}`, target `M^{5/4+ε}`.
The full covariance target is equivalent to the `3/4` strip. An upper bound for
the full signed sum does not separately bound its `q = 1` summand.
`powerMeshEnergy_exponent_eq_sInf` identifies the Abel-energy exponent as
`8Θ − 3`; it does not state an exact covariance exponent. The comparison with
covariance has an additional `O(J³)` head cost. Thus a covariance bound with
exponent below `5` would give a fixed strip, but the comparison alone does not
identify the covariance exponent below `3`.

## Conjecture ledger

| # | Mechanism | Verdict | Lesson |
|---|---|---|---|
| L1 | Bound the `q = 1` cell by a Mertens estimate | circular | needs `M(x) ≪ x^{3/4+ε}`; by `zetaZeroAbscissa_le_of_moebius_power_bound` that is the conclusion |
| L2 | Mesh averaging: treat `M(j⁴)`, `j ≤ J`, as decorrelated samples | unproved cancellation | `exists_powerGap_pow_samples` transfers sampling gaps; it is not a Mertens mean-square estimate. The proved Abel-energy exponent is `8Θ − 3` in the mesh index. |
| L3 | Plancherel: mean square of the tail via `∫|1/ζ(σ+it)|²/|s|²` | circular | needs `1/ζ` square-integrable on `Re s = 3/4 + ε`, which is the strip |
| L4 | Pair the divisor fluctuation `ΔF(q) = log q + 2γ − τ(q)` with `M(M/q)` and exploit independence | circular | the full hyperbola sum is `ψ(M) − M` (`psiDefect_eq_mobius_primeFreeDivisorDefect`), exponent exactly `Θ`; the corner cannot be smaller in general |
| L5 | Voronoi expansion of `Δ(q)` and stationary phase in `q` | circular | reorganises to `Σ_d μ(d) d^{1/4}·(phase)`, again a Möbius sum at scale `M` |
| L6 | Refute: show the covariance exceeds `J^{3+ε}` | not available | would exhibit a zero with `Re ρ > 3/4`; no such input exists in the corpus |
| L7 | Zero density (`exists_zeroHeightBox_ncard_le_gm_unconditional`, 30/13) with VK region | no strip | density counts zeros; one zero at `σ > 3/4` is not excluded (`DensityEnvelopeNoGo`) |
| L8 | Dirichlet-polynomial mean values and large values (`dirichlet_meanValue_theorem`, `largeValues_dirPoly`) | no strip | they produce density estimates, which is L7 |
| L9 | Vaughan Type I/II decomposition of `μ` on `(j³, j⁴)` | circular | `zetaZeroAbscissa_lt_one_iff_uniform_pmUndampedVaughan_power`: a Vaughan power saving is exactly a fixed strip |
| L10 | Short-window Möbius saving as input | circular | `zetaZeroAbscissa_lt_one_of_moebiusPowerWindowSaving` |
| L11 | Positive normalisation or Cauchy–Schwarz on the channels | sign-blind | `not_mobiusDivisorDilationPositiveMeshEnergy_le_pow`: envelope `≍ J^5`, never `≤ CJ^4` |
| L12 | Complete Weil positivity at a growing overlap `c_N → ∞` as a strip producer | open elsewhere | a slowly growing schedule is compatible with every zero (visibility needs `log N ≲ c^{1+2δ}/A(c)`); an explicit rate is review Question 1 |
| L13 | Prime grouping / successor pairing of channels | insufficient | first pairing contracts the diagonal only (`MobiusDivisorPrimePairEnergy.sum_mobiusDivisorPrimePair`); the ordered covariance is untouched |
| L14 | Any argument using only `μ ∗ 1 = δ`, `|F(q)| ≤ 24√q`, partial summation, Perron | cannot decide | `regular_integers_do_not_constrain_zeros`, `overRegular_integers_do_not_constrain_zeros`: these inputs hold for Beurling systems with `N(x) = ρx + O(x^θ)` for every fixed `θ > 0`, or with `N(x) − ρx → const`, that have a zero at any `β ∈ (1/2, 1)`; the equivalence proof transfers, so the covariance bound fails there |

The equivalent Möbius and `ψ` estimates remain valid research targets; assuming
them would leave the required arithmetic input unproved. The inspected absolute
bounds and identities do not establish `Θ ≤ 3/4`. No proof or refutation of the
requested covariance bound has been obtained.
