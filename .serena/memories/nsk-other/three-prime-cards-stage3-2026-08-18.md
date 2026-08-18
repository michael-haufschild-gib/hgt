# Three "other" prime cards → stage 3 (session 2026-08-18)

Goal: promote to stage 3
1. `prime-wold-accelerated-type-modular-drift-law` — **DONE, promoted 2026-08-18**
2. `prime-valuation-dyadic-fermion-normal-cone-law` — in progress
3. `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — not started

## 1. Wold accelerated type — CLOSED

Two new modules, both axiom-clean and umbrella-wired:

- `RHTower/GenusOneOccupationCompactBound.lean` — `(14a)`.
  `norm_finitePrimeGenusOnePolarizedPhase_two_sided`: for `‖t‖ ≤ R` and `δ ≤ ‖t ∓ n‖` for every
  `n ≥ 1`, `e^{-C(R,δ)} ≤ ‖Φ^(1)_S(t)‖ ≤ e^{C(R,δ)}` **uniformly in the finite prime set `S`**.
  Mechanism: `reflectedPrimaryLogDefect z = log‖1-z‖ - log‖1+z‖ + 2 Re z` is `O(‖z‖³)` for
  `‖z‖ ≤ 1/4` (linear term cancels against the tangent counterterm, quadratic by reflection);
  occupation monomials = reciprocals of distinct `S`-smooth integers (`occupationSmoothIndex`,
  injective) so the majorant is `A/n³`, summable against `∑ n^{-3}`.  Also
  `log_blockComparisonGauge_le` `(14c)` and
  `tendsto_mertensProduct_mul_ell2_blockComparisonGauge` (§5.1 compact-uniform type zero).
- `RHTower/SoninDepthApertureRigidity.lean` — `(18e)`.  `(18c)` was ALREADY OWNED as
  `norm_burnolExtendedSoninEvaluationVector_geometric_lower/_upper` in
  `RHTower/BurnolSoninCrossApertureRiesz.lean`; feed into `norm_le_of_soninDepth_rigidity`.

## 2. Dyadic fermion normal cone — infrastructure built, `(11)`–`(13b)` CLOSED

New modules (axiom-clean, wired):

- `HTGeometry/GeometricHellingerExpansion.lean` —
  `abs_log_geometricHellingerAffinity_add_le`: `|log H^geo(a,b) + ½(√a-√b)²| ≤ 4(a²+b²)` on
  `0 ≤ a,b ≤ 3/4`.  Same shape/constant as the corpus's parity-digit version
  `abs_log_bitHellingerAffinity_zero_add_le`.
- `RHTower/PrimeProfileWindowLimit.lean` — reusable:
  `divProfile F t = F t / t` (0 at 0); `tendsto_sum_divProfile` (∑_{p≤N} F(t_p)/p → ∫₀¹ F/t, from
  `tendsto_mertensPrimeWindow_div_log`); `tendsto_finsetSum_Icc_zero` (Tannery on the growing
  prime window, eventual bound); `tendsto_prod_Icc_of_tendsto_sum_log`.
- `RHTower/SquarefreeCriticalNormalCone.lean` —
  `radialNome c n = n^{-(1-2c)}`, `sq_sqrt_radialNome_sub` (the displacement is
  `(e^{c log n} - e^{d log n})²/n`), `radialNome_le` (≤ 3/4 on |c| ≤ 1/8),
  `sq_radialNome_le` (≤ n^{-3/2}); `coherentKernel u v = exp(-½∫₀¹(e^{ut}-e^{vt})² dt/t)`;
  `tendsto_criticalParityAffinity` = `(11)`+`(13b)`, `tendsto_criticalGeometricAffinity` = `(13)`,
  `tendsto_higherDigitTail_one` = `(12)`.

### Still to do for card 2
`(13c)`–`(13i)` Fock/coherent realization; `(13j)`–`(13o)` half-normal end (needs
`∫₀¹(1-e^{-at})dt/t = γ + log a + E₁(a)` for `(13o)`); `(13p)`–`(13z)` prime-profile theorem
(same machinery, nome `p^{-1}e^{2f(t_p)}`, needs eventual uniform `≤ 3/4`); `(13aa)`–`(13ac)`
defect measure + reflection rigidity; `(17)` Wold scale; `(18)`–`(22)` dyadic Fisher
decomposition; `(23)`–`(27)` Euler/first-trace/right-half.

## 3. Weyl idealizer card
Theorem A is fully Lean.  Open: Selberg positive proportion `N_0(T) ≫ T log T`
(`SuperlinearSamples xiRealDivisor`) and Bochner–Schwartz for positive-definite tempered
distributions.  Both are genuine large formalization sub-projects.
