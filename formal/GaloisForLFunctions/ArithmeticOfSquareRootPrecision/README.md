# ArithmeticOfSquareRootPrecision (ASRP)

Namespace `GaloisForLFunctions.ArithmeticOfSquareRootPrecision`; umbrella `ArithmeticOfSquareRootPrecision.lean`; 24 modules. Every theorem is unconditional; RH appears only inside equivalences. 7 modules end with `#print axioms` lines.

## 1. Motivation

The corpus reduces RH to one count, `ψ(x) − x = O(√x log²x)`. ASRP asks which statements about a prime-side weight can carry information at square-root precision, how much integrality over `ℤ` extracts, and where classical methods lose precision. The basic invariant is the precision class of a statement, meaning the set of perturbations of the weight it survives. The basic integer is the horizon period `lcm(1, …, N)`, whose logarithm is `ψ(N)`. Over `𝔽_q` the sign is a point count and the count is an integer. Over `ℤ` the integers are log-orders, and the question is whether integrality reaches beyond linear precision.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weight, partial sum | `partialSum a x` | `A(x) = Σ_{1≤n≤x} a(n)` |
| Square-root scale | `sqrtScale` | `√x log²x` |
| Precision class | `PrecisionClass φ`, `sqrtClass` | perturbations with partial sums `O(φ)`; `𝒬` for `√x log²x` |
| Count and halves | `Count`, `UpperCount`, `LowerCount` | `A(x) − x = O(√x log²x)`, one-sided versions |
| Precision exponent | `precisionExponent a` | `inf{θ : A(x) − x = O(x^θ)}` |
| Battery weights | `vonMangoldtWeight`, `liouvilleWeight`, `liouvilleMixture t`, `powerWeight η`, `towerWeight p` | `Λ`, `λΛ`, `(1−t)Λ + tλΛ`, `n^{−η}`, `Λ·1_{p^ℕ}` |
| Deciding-input tests | `liouvilleTwist`, `liouvilleTail` | `λ·a`; `a` on `[0, X]`, `λΛ` beyond |
| Laws of a weight | `PrimeNumberLaw`, `ShortIntervalLaw α`, `ErrorLaw E` | `A(x)/x → 1`; `(A(x+x^α) − A(x))/x^α → 1`; `A(x) − x = O(E)` |
| Nair functional | `nairIntegral P`, `horizonPoly` | `∫₀¹P` for `P ∈ ℤ[X]` |
| Integrality halves | `SiegelHalf φ`, `LiouvilleHalf φ`, `IdealSiegelHalf Q φ`, `IdealLiouvilleHalf Q φ` | small positive Nair integrals exist; every positive one is large; restricted to the ideal `(Q)` |
| Admissible scale | `AdmissibleScale φ` | monotone, nonnegative, eventually `≥ 1` |
| Integer Dirichlet polynomial | `intDirichlet a σ` | `Σ_{i<N} a_i (i+1)^{−σ}` |
| Twin torsion | `twinTorsion n`, `evenVonMangoldt` | `lcm(1..n)/lcm(1..⌊√n⌋)²`; `Λ` on even `Ω` |
| Chebyshev transform | `chebyshevTransform a n`, `inversionOp E x`, `weightFun` | `Σ_{d≤n} a(d)⌊n/d⌋`; `Σ_{k≤x} μ(k)E(x/k)` |
| Mertens, Möbius moments | `mertens`, `moebiusMoment`, `logMoebiusMoment` | `M(N)`; `Σ μ(k)/k`; `Σ μ(k) log k/k` |
| Stirling pieces | `stirlingMain`, `stirlingMonotone`, `stirlingSawtooth`, `stirlingStep` | `t log t − t`; monotone part; sawtooth |
| Curve precision | `CountAtPrecision D θ`, `LowerCountAtPrecision`, `UpperCountAtPrecision` | `|N_k − q^k − 1| ≤ Cq^{kθ}` and halves |
| Gauges | `signGauge F`, `flippedMass F`, `torusGauge t`, `gaugeDistance t` | sign flips on a prime set; `θ_F`; cosine rotation; `Σ(1 − cos 2πt_p) log p` |
| Complex gauges | `ComplexCount`, `complexTorusGauge`, `gaugeCurrent`, `balancedGauge`, `conjugatedGauge`, `meanGaugeCurrent` | complex counts, sine currents, Euler-factor conjugation |
| Tower positivity | `TowerIndexZero p λ` | every tower kernel along `p` has index zero |
| Aperture positivity | `AperturePositive A λ` | Weil positivity for tests supported in `[−A, A]` |
| Successor | `successorWeight` | the weight `1` |

External: `zeroReSup` (`Θ = sup Re ρ`), `exists_abs_chebyshevPsi_sub_le_rpow`, `frequently_rpow_lt_chebyshevPsi_sub`, `mertens_omega_pm_sqrt`, `Matveev.effectiveBakerBound_holds`, `weilFullFunctional`, `WeilPositiveFull` (RHTower); `CurveDatum`, `goldenDatum` (ArithmeticCastelnuovoSeveri); `log_inv_integral_le_psi`, `exists_int_eq_lcmUpto_mul_integral`, `hyperellipticDatum` (ArithmeticEffectivityTheory); `towerKernel`, `forall_negIndex_towerKernel_eq_zero_iff` (HeckeKreinToeplitz); `re_weilFullFunctional_ge_of_aperture_le_threeTenths` (SquareRootThreshold).

## 3. Language

- Visible move: a perturbation after which the weight never satisfies the count. Invisible move: one that leaves the count unchanged (count ⇔ RH).
- Deciding input: a property of weights that implies the count.
- Stabilizer: the perturbations a statement survives at a weight.
- Producer: a construction that yields a count without assuming it.
- Siegel half: existence of small auxiliaries. Liouville half: every nonzero value is large.
- Successor model: a weight within `𝒬` of the integer count (an over-regular Beurling count).

## 4. Mechanisms

**A. Precision classes**
1. Stabilizer law: if `a` satisfies the count, `a + δ` does iff `δ ∈ 𝒬`.
2. Power threshold: `Σ_{n≤x} n^{−η} ≥ x^{1−η}/2`, and `≤ 2√x` for `η ≥ ½`. So `εn^{−η} ∈ 𝒬 ⇔ η ≥ ½`.
3. Landau: both signs of `ψ(x) − x` reach `x^b` for every `b < Θ`, so each half of the count is RH. The step function `A(x)` stays `1/4` away from `x`, so precision exponents are `≥ 0`.
4. Littlewood's oscillation of `ψ(x) − x` excludes every one-signed `x^{1−η}` drift, unconditionally.
5. Monotonicity: the lower count is monotone and the upper count antitone in the weight. Minorants with lower counts and majorants with upper counts give RH.
6. For one-signed perturbations, the precision class is read off the abscissa of absolute convergence relative to `½`.

**B. Integrality**
7. Reciprocal Bézout: integer combinations of `1/b_i` reach exactly `1/lcm(b_i)`. So the Nair lattice in degree `≤ n` is `lcm(1..n+1)⁻¹ℤ` and the floor is attained.
8. The floor attained makes the Siegel half the lower count and the Liouville half the upper count, at every admissible scale.
9. Moment residues: clearing lower denominators of `∫₀¹ x^j Q` leaves a fixed residue, so a fixed ideal `(Q)` costs only a bounded factor `C₀`.
10. Integer Dirichlet polynomials: `lcm^m·D(m) ∈ ℤ` at `s = m ≥ 1` (sharp), `D(−k) ∈ ℤ`, Rolle bounds the real zeros, and Siegel's lemma gives vanishing on the trivial lattice.
11. Sup-norm ceilings: `b^nP(a/b) ∈ ℤ`, so a sup norm below `b^{−n}` forces `P(a/b) = 0`.
12. Twin as torsion: `Σ λΛ = 2ψ(√n) − ψ(n)` and `exp(Σ λΛ) = 1/|ℤ/r_n|`.

**C. Where precision is lost**
13. The Chebyshev identity `T_Λ(n) = log n!` is exact (precision class `{0}`). The count is its Möbius inversion, which is unbounded at every precision: an error of size `y^θ` can invert to `≥ π(x)`.
14. Abel summation: a monotone error bounded by `B` inverts to `≤ 3BK`, where `K` bounds the Mertens function. Constant errors invert to `M(x) = Ω±(√x)`.
15. Stirling split `log⌊y⌋! = F + G + h`: `G` is monotone (Mertens precision), and `h` is a sawtooth of amplitude `log y`. `I(F) = x((log x − 1)m − ℓ)`.

**D. Gauges and towers**
16. Gauge defect: `Λ − signGauge F` has partial sums between `2θ_F` and `2θ_F + 2(ψ − θ)`. Torus gauges measure the cosine deficit.
17. Complex lift: greedily conjugating whole Euler factors against the running sine current keeps it `≤ log x`. Random fair conjugation has current `O(√x log²x)` a.s.
18. Two-prime alias elimination: `2π(k₁ log q − k₂ log p) = e_q log p − e_p log q`, with Baker giving polynomial separation.
19. Aperture window: tests in `[−A, A]` read `λ` only on `n ≤ e^{2A}`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Stabilizer law | `count_add_iff_mem_sqrtClass` | proved |
| Power threshold; precision rigidity, sharp | `smul_powerWeight_mem_sqrtClass_iff`, `not_count_and_count_add_smul_powerWeight`, `count_add_smul_powerWeight` | proved |
| Count, upper half, lower half each ⇔ RH | `count_vonMangoldt_iff`, `upperCount_vonMangoldt_iff`, `lowerCount_vonMangoldt_iff` | proved |
| Precision exponent of `Λ` is `Θ`; RH ⇔ exponent `½` | `precisionExponent_vonMangoldt`, `riemannHypothesis_iff_precisionExponent` | proved |
| Battery classification | `battery_classification`, `not_count_liouvilleMixture`, `not_count_vonMangoldt_add_smul_powerWeight`, `count_vonMangoldt_add_smul_towerWeight_iff` | proved |
| Deciding-input theorem | `deciding_input_necessary_properties`, `not_of_twist_stable`, `not_of_finite_window`, `not_of_stable_visible` | proved |
| PNT, Guth–Maynard and error laws above `√x` cannot decide | `producers_are_precision_blind`, `errorLaw_cannot_decide` | proved |
| Nair lattice; floor attained; `ψ(n+1)` = best integrality bound | `nairLattice_eq`, `isLeast_positive_nairIntegral`, `isGreatest_log_inv_nairIntegral` | proved |
| Siegel/Liouville halves = lower/upper count; RH at `√x log²x` | `siegelHalf_iff_lower`, `liouvilleHalf_iff_upper`, `riemannHypothesis_iff_siegelHalf_sqrtScale`, `riemannHypothesis_iff_liouvilleHalf_sqrtScale` | proved |
| Integrality exponent = `Θ`; strip ⇔ integrality at some `θ < 1` | `siegelExponent_eq_zeroReSup`, `liouvilleExponent_eq_zeroReSup`, `zeroReSup_lt_one_iff_siegelHalf` | proved |
| Fixed polynomial ideals keep integrality precision | `exists_uniform_nairIntegral_multiple`, `exists_isLeast_nairIntegral_multiple`, `ideal_integrality_exponents_eq_zeroReSup`, `riemannHypothesis_iff_idealSiegelHalf` | proved |
| Integer Dirichlet polynomials: Liouville inequality sharp, zero estimates, Siegel's lemma | `one_div_lcmUpto_pow_le_abs_intDirichlet`, `exists_intDirichlet_eq_one_div_lcmUpto_pow`, `card_lt_of_intDirichlet_eq_zero`, `exists_intDirichlet_vanishing_on_trivial_lattice` | proved |
| `Σ λΛ = 2ψ(√n) − ψ(n)`; twin value is a reciprocal group order | `partialSum_liouvilleWeight_eq`, `exp_partialSum_liouvilleWeight` | proved |
| Chebyshev identity exact; inversion unbounded at every precision | `chebyshevTransform_vonMangoldt`, `eq_of_chebyshevTransform_eq`, `psi_eq_sum_moebius_log_factorial`, `not_inversion_bounded` | proved |
| Curve precision exponent `½ + max log|β|/log q`; lower half suffices; golden calibration | `precisionExponent_eq`, `lowerCountAtPrecision_iff`, `golden_countAtPrecision_iff`, `golden_upperCount_and_not_lowerCount`, `hyperelliptic_countAtPrecision_half` | proved |
| Weights below `Λ`; sign and torus gauge stabilizers | `count_iff_of_le_vonMangoldt`, `count_signGauge_iff`, `count_signGauge_of_finite`, `count_torusGauge_iff` | proved |
| Complex count lifts of real gauges | `complexCount_torusGauge_iff`, `complexCount_balancedGauge_iff`, `exists_complexCount_lift_iff`, `ae_fair_complexCount_iff` | proved |
| RH in eight precision currencies; `Θ` three readings | `riemannHypothesis_precision_tfae`, `zero_width_three_readings`, `zeroReSup_lt_one_tfae` | proved |
| Sup-norm certificates vanish at `0, ½, 1` | `eventually_vanish_of_supCeiling` | proved |
| Majorants/minorants; abscissa visibility | `riemannHypothesis_of_majorant`, `riemannHypothesis_of_minorant`, `count_iff_of_vonMangoldt_le`, `not_count_add_of_half_lt_abscissaOfAbsConv` | proved |
| Two-prime non-aliasing at polynomial precision | `two_prime_alias_bound_in_Δ`, `liouville_separation`, `exists_baker_separation` | proved |
| Monotone inversion law; RH ⇔ monotone inversion at `x^{½+δ}` | `abs_inversionOp_le_of_monotoneOn`, `not_monotone_inversion_lt_half`, `riemannHypothesis_iff_monotone_inversion` | proved |
| Tower positivity is precision-exact; `Λ + 1/n` separates it from the count | `towerIndexZero_add_iff`, `count_and_not_towerIndexZero_add_inv` | proved |
| Stirling split; arithmetic Chebyshev ledger | `abs_psi_sub_smooth_sub_sawtooth_le`, `abs_psi_sub_moments_sub_sawtooth_le` | proved |
| No finite aperture decides; aperture `3/10` is weight-blind | `not_riemannHypothesis_of_aperturePositive_imp_count`, `aperturePositive_threeTenths` | proved |
| Count = comparison with the successor | `count_iff_sub_one_mem_sqrtClass`, `riemannHypothesis_iff_vonMangoldt_sub_one_mem_sqrtClass` | proved |

## 6. Tools

**Developed**
- Precision-class calculus (`PrecisionClass.add_mem`, `mono`, `not_mem_precisionClass_of_lower_bound`, `mem_sqrtClass_of_eventually_zero`).
- Integer-to-real horizon transfer (`lower_real_of_nat`, `upper_real_of_nat`).
- Reciprocal Bézout (`exists_int_sum_div_eq_inv_lcm`) and moment residues (`exists_int_cofactor_mul_nairRationalMoment`).
- Abel summation against `μ` (`sum_moebius_mul_eq`, `abs_sum_moebius_mul_le_of_antitone`).
- Stirling bounds (`log_factorial_sub_bounds`, `sawtooth_bounds`).
- Greedy and random Euler-factor conjugation (`balancedGauge`, `ae_gaugeCurrent_sub_mean_isBigO`).
- Abscissa–partial sum dictionary (`abscissaOfAbsConv_le_of_partialSum_isBigO`, `partialSum_isBigO_of_abscissaOfAbsConv_lt`).

**To build**
- A ceiling (certificate) for a small positive Nair integral at square-root precision, beyond sup-norm and the integer Chebyshev problem.
- Cancellation in the sawtooth inversion `I_n(h)` and in the Möbius moments, from arithmetic input.
- A deciding input that is parity-breaking, precision-faithful and of unbounded aperture, other than tower positivity itself.
- The precision classes of Hecke defects, covariant regulators and torsion orbits from other programmes.

## 7. Open questions

1. Can integrality certify a small positive integral at precision `x^{½+ε}` (the Siegel half at square-root scale)?
2. What arithmetic structure bounds the sawtooth inversion `I_n(h)` below its trivial size `n`?
3. Is there an intermediate statement with precision class strictly between `{0}` (tower positivity) and `𝒬` (the count) that is provable?
4. Which auxiliaries vanish at rational points to growing order, as Stepanov's do at `𝔽_q`-points?
5. Does a selective statement exist whose stabilizer in the gauge torus is exactly the square-root gauge ball?

## 8. Traps

| Trap | Fact |
|---|---|
| The prime number theorem or short-interval laws carry square-root information | `Λ + εn^{−η}` satisfies PNT and Guth–Maynard and never the count |
| One half of the count is weaker than RH | Each half is RH over `ℤ` (no real zero in `(½, 1)`); only over `𝔽_q` is the upper half blind |
| Deleting or flipping one Euler factor changes the count | A prime tower carries `≤ log x`; finite flips are invisible |
| Integrality over `ℤ` is lossy | The Nair lattice is exact and the floor attained; precision is lost in the analytic ceiling |
| Restricting auxiliaries to an ideal sharpens integrality | Fixed ideals cost a bounded factor and keep every exponent |
| Better size bounds on the Stirling error give `ψ` | Möbius inversion is unbounded on every size class; only monotone errors invert, at Mertens precision |
| The count is gauge-invariant | Sign gauges pass iff the flipped prime mass is `O(√x log²x)`; the Liouville twin fails |
| RH-equivalent statements have the same precision | The count sees `𝒬`; tower positivity sees every coefficient (`Λ + 1/n` separates them) |
| Small-aperture Weil positivity carries information | Aperture `3/10` holds for every weight; any finite aperture is window-determined |
| Exact counting of the integers helps | The count uses the integers only modulo `𝒬`; over-regular Beurling systems share that class |
| Relative-error point counts see the sign over `𝔽_q` | The golden datum has `N_k/5^k → 1` and fails the square-root count |

## 9. Context

**Uses**

| Programme | Imports | What |
|---|---|---|
| RHTower | 8 | von Koch, Landau/Littlewood, Guth–Maynard, Mertens criteria, Baker bound, Liouville point |
| HTGeometry | 3 | exponential-polynomial zeros, positive square integrals, random signs |
| ArithmeticEffectivityTheory | 2 | Nair integrality, hyperelliptic calibration |
| ArithmeticCastelnuovoSeveri | 2 | curve data, one-sided power-sum bounds |
| SquareRootThreshold, HeckeKreinToeplitz | 1 each | aperture window certificates; tower index zero selects `Λ` |

**Used by**: ArithmeticKreinLangerTheory (`ChebyshevsProducerPassesTheIntegerChebyshevCap`), EffectiveArithmeticHodgeTheory (`TheTwistTowerCollapsesOverTheIntegers`), RHTower (`InfiniteSymmetry/ConfinementIsTheSquareRootCount`), umbrella.

| Neighbour | Relation |
|---|---|
| ArithmeticEffectivityTheory | Nair floor; ASRP proves it attained and computes its exact precision |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | global law = one-sided count; ASRP supplies the precision calculus and the tower-positivity contrast |
| SelectiveMultiscaleArithmeticPositivity | precision rigidity of tower positivity; ASRP gives the count-level analogue with sharp threshold |
| SquareRootThreshold | zero width `Θ`; ASRP identifies it with precision and integrality exponents |
| ArithmeticCastelnuovoSeveri | curve calibration and the golden datum |

## 10. Big picture

ASRP shows that the information RH needs is never missing from the arithmetic of `ℤ`. The Chebyshev identity is exact. The integrality lattice of the horizon is exact, and its floor is attained. Tower positivity sees every coefficient of `Λ`. The count itself, by contrast, sees only a square-root class: it cannot distinguish `Λ` from any finite modification, a flipped Euler factor, or an `n^{−1/2}` perturbation. All the classical estimates (PNT, short intervals, any error law weaker than square root) are shared by weights that fail the count, so none of them can decide.

Precision is lost at identifiable places: Möbius inversion of the Chebyshev identity, the analytic ceiling that certifies a small integral, and the sawtooth part of Stirling's error. A proof of RH along this axis must keep the identities of `Λ` alive through one of these steps, and that cannot be a size estimate. It needs an arithmetic certificate of square-root size: a Stepanov-type auxiliary over `ℤ`, cancellation in `μ` against the sawtooth, or a positivity statement that, like tower positivity, carries the identities of `Λ` and not just its size.
