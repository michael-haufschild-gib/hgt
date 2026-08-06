# Card: prime-sieve-wold-gamma-bv-relative-character — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
(its "Formalization status" section carries the full declaration tables).

## DONE (unconditional; axioms = propext/Classical.choice/Quot.sound), all wired
into `GaloisForLFunctions/HTGeometry.lean`

### `HTGeometry/PrimeSieveDensityTelescope.lean` — Section 3, (13),(14)
`sieveDensity`, `sieveDensity_insert`, `sieveDensity_sub_insert`, `sievePrefix`,
`sum_sieveDensity_div_prime`, `tendsto_sieveDensity_sievePrefix`,
`hasSum_sieveDensity_div_prime`, `tsum_sieveDensity_div_prime` (boxed (14)).

### `HTGeometry/PrimeSieveEulerTrace.lean` — arithmetic of (3), trace input to (6)
`sievePrimorial`, `coprime_sievePrimorial`, `coprime_sievePrimorial_insert_iff`,
`sievedSum`, `sievedSum_insert` (the splitting of (3)), `sievedSum_eq_mul_prod`,
`sievedSum_rpow_inv`.

### `HTGeometry/PrimeSieveHarmonicInclusionExclusion.lean` — Section 3, (11),(12)
`sum_Icc_one_div_eq_harmonic`, `sievePrimorial_ne_zero`, `divisors_gcd_eq_filter`,
`sum_divisors_moebius_real`, `multiples_Icc`, `sievedHarmonic`,
`sievedHarmonic_eq_sum_divisors` (=(12)), `moebiusDiv`,
`isMultiplicative_moebiusDiv`, `isMultiplicative_moebiusDivSum`,
`sum_divisors_moebiusDiv_prime`, `sum_divisors_moebiusDiv_sievePrimorial`
(= `∑_{d|M_P} μ(d)/d = a_P`), `tendsto_natDiv_atTop`, `tendsto_natDiv_div_self`,
`tendsto_log_natDiv_sub_log`, `tendsto_harmonic_natDiv_sub_log`,
`sieveHarmonicConstant`, `tendsto_sievedHarmonic_sub` (=(11)).

### `HTGeometry/PrimeSieveRegularDeterminant.lean` — Section 2, (5)–(9)
`sieveTrace`, `sieveTrace_eq_mul_prod`, `sieveTrace_insert`, `sieveTrace_nonneg`,
`sieveTraceBound` (=ζ(3)), `natPow_inv_le`, `sieveTrace_le_bound`,
`sieveLogPhi` (=(6)), `norm_sieveLogPhi_term_le`, `summable_sieveLogPhi_bound`,
`summable_sieveLogPhi_term`, `sieveLogPhi_insert` (boxed (5)),
`abs_sieveLogPhi_le`, `abs_sieveLogPhi_insert_sub_le` (=(7)),
`vacuumLogPhi`, `exp_vacuumLogPhi` (=(9) closed form),
`hasSum_vacuumSeries`, `tendsto_sieveTrace_sievePrefix` (Tannery, replaces the
Euler-product argument and is (8) at the level of power traces),
`tendsto_sieveLogPhi_sievePrefix` (=(9)).

## mathlib assets used (verified on this toolchain)
`Real.tendsto_harmonic_sub_log`, `Real.eulerMascheroniConstant`, `harmonic`,
`Real.hasSum_log_sub_log_of_abs_lt_one`, `hasSum_nat_add_iff`,
`tendsto_tsum_of_dominated_convergence` (Tannery, `Analysis/Normed/Group/Tannery`),
`ArithmeticFunction.moebius_mul_coe_zeta`, `coe_mul_zeta_apply`,
`IsMultiplicative.natCast`, `IsMultiplicative.mul`, `Nat.Prime.divisors`,
`Real.summable_one_div_nat_pow`, `summable_geometric_of_lt_one`, `inv_anti₀`,
`pow_le_pow_right₀`, `tsum_geometric_of_lt_one`, `tsum_of_norm_bounded`.

Traps hit: `open scoped ArithmeticFunction.Moebius` is needed for `μ`;
`rw [Finset.mem_image]` fails on `Finset Nat.Primes` (SetLike instance clash) —
use `Finset.mem_image_of_mem`; `hasSum_nat_add_iff` needs `(f := ...)` explicit
(higher-order unification); `field_simp` often closes the goal so a trailing
`ring` errors with "No goals".

## REMAINING
1. Section 1 (1)–(3) as operators on `ℓ²(ℕ_{>0})`: `Q e_n = n⁻¹e_n`,
   `S_p e_n = e_{pn}`, `E_p = I − S_pS_p*`, `E_P` the coordinate projection.
   The arithmetic content of (3) is `sievedSum_insert`; what is left is the
   operator packaging, plus `(4)` = the identification of `sieveLogPhi` with
   `log det₂(I−tQ_P) − log det₂(I+tQ_P)` using the corpus germ
   `operatorFredholmDet2Germ` (`HTGeometry/OperatorFredholmGerm.lean`, over
   `HilbertSchmidtTrace.lean`: `opTrace`, `IsHilbertSchmidt`, `hsBasis`), and
   `(8)` HS convergence.
2. Section 4 (15)–(18): BV scale-decimation and `J(E_P p_a) = a_P J(p_a)`.
   `J` is the pole-cancelled BV/co-Poisson principal-normal class; the two
   homogeneity laws (16) come from the parent card
   `not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`.
   Locate/construct the corpus `J` before formalizing; (17)–(18) are then a
   purely algebraic induction over commuting `E_q = I − S_q D_q`.
3. Sections 5–6: assemble (19)–(21) and the naive no-go.
Conjecture (24) has no paper proof — NOT a formalization target.
