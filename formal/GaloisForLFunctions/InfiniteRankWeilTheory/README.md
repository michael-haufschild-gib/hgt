# Infinite-Rank Weil Theory over Spec ℤ (IRW)

Namespace `GaloisForLFunctions.InfiniteRankWeilTheory`; umbrella `InfiniteRankWeilTheory.lean`;
11 modules. Specification: §2.8b of
[the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

## 1. Motivation

Weil's theorem for a curve of genus `g` over `𝔽_q`, in the form the corpus proves for every
hyperelliptic curve, has three steps:

1. **Crude count.** At every level `n` of the base-change tower, `|N_n − qⁿ − 1| ≤ C q^{n/2}` with `C`
   independent of `n` (Stepanov's auxiliary polynomial).
2. **Self-improvement.** Power sums of `2g` numbers that are `O(1)` at every level put every number in
   the closed unit disc. The constant `C` does not matter.
3. **Reflection.** The functional equation `β ↦ 1/β` turns `|β| ≤ 1` into `|β| = 1`.

Read as a **count**, the channel numbers extend to an `ℕ`-valued count whose Tate limit is the
intersection form.

Over `Spec ℤ` the modes are the zeros of `ξ`: infinitely many, about `T log T` up to height `T`, with
ordinates of infinite Kronecker rank. Every step changes character at infinite rank, and IRW is the
theory of that change. It treats curves and `ζ` as two instances of one object, a **Weil tower** (modes
closed under conjugation and `z ↦ 1/z`), and asks for each step what its infinite-rank form is, when it
holds, what it costs, and which arithmetic input it needs that the finite-rank form gets for free.

| Step | Finite rank (curve) | Infinite rank (`ℤ`), as proved here |
|---|---|---|
| crude count | `O(1)` traces at every level | a bound on the level sums along a **thick** set of levels of one tower (with ZAL it is RH); in primes, `\|(X − ψ(X)) + X(Σ_{n≤X}Λ(n)/n − log X + γ)\| ≤ C X^{½}` along `X = e^{νℓ}`, `ν` in a thick set |
| self-improvement | finite elimination; any constant | works for towers whose outer part is **well-founded** (ZAL); the window length is the **exceptional rank** (number of distinct visible top points), and the infinite remainder enters only through its **trace norm** |
| AAL | automatic (finite rank, periodic heads) | AAL fails exactly at an **isolated top**: a finite-rank datum riding on an infinite-rank remainder |
| reflection | `β ↦ 1/β` | acts on level sums only by `S(−ν) = conj S(ν)`; consistent with every finite off-line layer |
| count | Tate limit of a count | a count positive by damping survives the critical weight; a count positive by renormalization does not |

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weil tower | `WeilTower`, `reflPerm` | modes `z_i`, `i ∈ ι` (with multiplicity), closed under `z ↦ z̄` and `z ↦ 1/z` |
| Level sum | `levelSum z b ν` | `S(ν) = Σ_i b_i z_iᵛ`, `ν ∈ ℤ`: the infinite-rank power sum |
| Trace norm | `∑' i, ‖b i‖` | the currency in which an infinite remainder is paid |
| Curve tower | `CurveDatum.toWeilTower` | normalized Frobenius eigenvalues, finite rank `2g` |
| Tower of a configuration | `frobTower ℓ ρ` | `z_i = e^{ℓ(ρ_i − ½)}`: the prime tower at `ℓ = log p`, any base `ℓ > 0` |
| Tower of `ζ` | `zetaTower ℓ`, `zetaConfig`, `lagWeight` | zeros of `ξ` with multiplicity; weights `1/(ρ(1−ρ))` |
| Configuration | `ρ : ι → ℂ` | modes in the strip; `ZerosApproachLine`, `AsymptoticAbscissaLaw`, `RightRH`, `EventualToGlobal` |
| Isolated top | `HasIsolatedTop` | finite nonempty layer on `Re = Θ > ½`, all other modes left of `Θ₂ < Θ` |
| Well-founded outer part | `WellFoundedAbove z ρ` | finitely many modes above every radius `> ρ` |
| Thick set of levels | `Thick G` | contains arbitrarily long runs arbitrarily far out |
| Merged weight | `∑ j ∈ F with z j = z i, b j` | total weight at one point; a point is **visible** if it is nonzero |
| Roots-of-unity tower | `rootsOfUnityTower R k` | outer `R·μ_k`, inner `R⁻¹·μ_k`: the barrier model |
| Cosh model | `coshModel Q`, `quartet` | `cosh(s − ½) Π_{q∈Q}(s−q)(s−q̄)(s−1+q)(s−1+q̄)` |
| Return | `IsReturn P δ t`, `phase` | `\|p^{−it} − 1\| ≤ δ` for all `p ∈ P` |
| Smooth Dirichlet polynomial | `dpoly S c`, `logMoment`, `momentMap` | `Σ_{n∈S} c_n n^{−s}` on `P`-smooth `S`; its logarithmic moments = derivatives |
| Fejér mean value | `fejerMean`, `fejerKernel`, `collisionCount` | `∫_0^T (1 − t/T)\|Σ a_n n^{−it}\|² dt`; kernel `(1 − cos λT)/(Tλ²)` |
| Toeplitz kernel, damping | `toeplitz`, `ToeplitzPositive`, `dampWeight` | `[k(i − j)]`; `ρ^{\|ν\|}`, `ρ = e^{−δ}` |
| Prime deviation | `primeDeviation X` | `(X − ψ(X)) + X(Σ_{n≤X}Λ(n)/n − log X + γ) − log 2π + O(X⁻²)` |

## 3. Language

- **Level**: an exponent `ν` of a tower; for `ζ` at base `ℓ`, the scale `X = e^{νℓ}`.
- **Crude bound on `G`**: `|S(ν)| ≤ Cρᵛ` for `ν ∈ G`, any constant `C`.
- **Self-improves on `G`**: a crude bound on `G` at rate `ρ` forces every visible mode into `|z| ≤ ρ`.
- **Exceptional rank**: the number of distinct visible top points; for `ζ` without AAL, the number of
  top zeros. **Total rank** is the number of all modes; at infinite rank it is `∞`.
- **Rank barrier**: whatever depends on the total rank is void at infinite rank; only the exceptional
  rank and the trace norm may enter.
- **Exceptional coordinate**: the number of modes beyond each depth. ZAL is its crude statement, AAL its
  self-improvement, B13 (finitely many off-line zeros ⇒ none) its base case at `σ = ½`.
- **Forced vanishing**: approximate vanishing at every return, produced by moment conditions.
- **Collision**: a pair `m ≠ n` with `|log(n/m)| ≲ 1/T`.
- **Damped count / renormalized count**: positive at weight `δ` because of a Schur product with
  `ρ^{|ν|}`, or because a self-energy `c(δ) → ∞` was added.

## 4. Mechanisms

1. **Inverse Vandermonde.** Distinct points on a circle with coefficients not all zero give an
   exponential polynomial of size `≥ ε` at some level of every window of `k` levels, with `ε` independent
   of the window. A remainder of modulus `≤ r < R` of any rank costs only `(Σ|b|) rᵛ`.
2. **Polynomial window constants against geometric decay.** Under an isolated top, every rate `ρ < R` is
   exceeded at some level of every window of `k` levels beyond some point; so a thick set of levels
   self-improves.
3. **Roots of unity.** A top layer `R·μ_k` has vanishing level sums off `kℤ`; no bound on a set of
   density `< 1`, and no window shorter than the exceptional rank, self-improves.
4. **Vandermonde hiding and its price.** `N` unimodular modes cancel any values on a window of `N`
   levels; cancelling a visible top of modulus `R ≥ 1` at position `M` costs trace norm `≥ εR^{M+1}`.
5. **Well-founded elimination.** If the outer part is finite above every radius, the largest visible
   outer point is an isolated top and mechanism 2 removes it. With reflection-compatible weights the
   inner part goes with it.
6. **Isolated tops are the failures of AAL.** A finite nonempty exceptional set has a top layer with a
   gap below it; conversely an isolated top is a finite nonempty exceptional set.
7. **Cosh models.** `cosh(s − ½)` has all zeros on the critical line; multiplying by quartet polynomials
   places any finite off-line layer while keeping the functional equation, reality and order one.
8. **Freezing at returns.** `|n^{−it} − 1| ≤ Ω(n)δ` for `P`-smooth `n` at a `δ`-return; logarithmic
   moments are derivatives; the `J`-th exponential tail bounds a polynomial with a zero of order `J`.
9. **Linear independence of `log p`.** Two primes have no common exact return besides `t = 0`.
10. **Fejér identity.** `∫_0^T (1 − t/T) cos(λt) dt = (1 − cos λT)/(Tλ²)`, a nonnegative kernel
    `≥ 2T/π²` on `|λ| ≤ π/T` and `≤ min(T/2, 2/(Tλ²))`; distinct integers in `[1, N]` are `|n − m|/N`
    apart in logarithm, which sums the off-diagonal to `O(N²)`.
11. **Kac–Murdock–Szegő and Schur.** `ρ^{|i−j|} = Σ_{k≤min(i,j)} c_k ρ^{i−k}ρ^{j−k}` with `c_0 = 1`,
    `c_k = 1 − ρ²`; Hadamard products of positive matrices are positive.

## 5. Questions and their answers

| # | Question (§2.8b) | Answer | Lean |
|---|---|---|---|
| Q1 | What replaces "finitely many power sums" when the modes are infinite and grow like `T log T`? | Level sums on **windows of length the exceptional rank**, with the infinite remainder paid in **trace norm**; a crude bound on a **thick** set of levels self-improves past every isolated visible top. Sharp: windows shorter than the exceptional rank and sets of density `1 − 1/k` fail, also with an infinite critical remainder; hiding is possible on every finite window and costs trace norm `≥ εR^{M+1}`. | `exists_pos_forall_window_le_norm_levelSum`, `eventually_forall_window_exists_lt_norm_levelSum`, `not_forall_mem_thick_norm_levelSum_le`, `levelSum_rootsOfUnityTower_eq_zero`, `norm_levelSum_rootsOfUnity_add_le`, `exists_unimodular_cancelling_layer`, `le_tsum_norm_of_hides_top` |
| Q2 | Which exceptional-set bound self-improves under the FE? | For every configuration RH = ZAL + AAL, and AAL fails exactly at an isolated top. **None** self-improves from the FE with order one and reality (cosh models carry every finite layer); **none** from an Euler product with integer norms and linear counting (one-off); **every** one under vertical periodicity (function fields); AAL is invariant under symmetric shifts. For `ζ`, AAL follows from lag growth exponent `0` along a thick set of levels of one tower, in primes from a thick-set crude count at every exponent `½ + a`. Density-zero exceptional sets fare no better under the FE alone (canonical products over any sparse reflection-closed layer [C]); heavy-return bounds (B97) are statements at large height, blind to every finite layer, so they belong to the crude step, not to the self-improvement. | `rightRH_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `not_asymptoticAbscissaLaw_iff_hasIsolatedTop`, `not_asymptoticAbscissaLaw_coshModelZeros`, `integerNormOneOff_zal_not_aal`, `asymptoticAbscissaLaw_of_vertical_period`, `asymptoticAbscissaLaw_shift_iff`, `asymptoticAbscissaLaw_of_thick_lag_bound`, `asymptoticAbscissaLaw_of_thick_primeDeviation_bound` |
| Q3 | What is the infinite-rank analogue of `\|α\| ≤ √q` from `Σαⁿ = O(q^{n/2})`? | **Well-founded elimination**: in a tower whose outer part is finite above every radius `> ρ`, a bound `Cρᵛ` on a thick set of levels leaves no visible mode outside radius `ρ`, whatever `C`; with reflection only the unit circle stays visible. For curves this is RH from traces bounded on a thick set; for `ζ` it is `RH ⇔ ZAL ∧` one thick bounded lag, equivalently one thick crude count in primes at exponent `½`. Without well-foundedness the argument has no top to remove, and Wolff configurations (`ArithmeticCastelnuovoSeveri`) show that accumulating outer parts can be invisible to a tower. | `mergedWeight_eq_zero_of_thick_bound`, `WeilTower.mergedWeight_eq_zero_of_norm_ne_one`, `CurveDatum.unitary_of_thick_trace_bound`, `CurveDatum.unitary_of_thick_pointCount_bound`, `riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded`, `riemannHypothesis_iff_zerosApproachLine_and_thick_primeDeviation` |
| Q4 | Is a finite top layer compatible with the FE once the bottom layer is reflected into the power sums? | **Yes.** On level sums the FE is the symmetry `S(−ν) = conj S(ν)` and the outer and inner parts have equal rank; the reflected bottom layer lies below the critical layer and enters every window only through the remainder. Every finite reflection-closed layer is the off-line zero set of an entire function of order one with FE and reality, all other zeros critical (ZAL holds, AAL fails). The Dirichlet series must enter. | `WeilTower.levelSum_neg`, `WeilTower.encard_outer_eq_encard_inner`, `coshModel_one_sub`, `coshModel_conj`, `norm_coshModel_le`, `coshModel_eq_zero_iff`, `zerosApproachLine_coshModelZeros`, `not_asymptoticAbscissaLaw_coshModelZeros` |
| Q5 | Which auxiliary function has forced vanishing at the returns of the prime orbit with controlled size? | **Moment-annihilated smooth Dirichlet polynomials.** They exist on any `J + 1` integers; at every `δ`-return they are `≤ δ·(logarithmic mass) + (J-th exponential tail)` on the whole disc about `s₀ + it`: `J` linear conditions force approximate vanishing to order `J` at all returns at once. But the prime orbit has no exact return besides `t = 0`, so the vanishing is approximate only; a Rouché copy of a zero of order `J` at a return needs the freezing error `δ·(mass)` below `min_{\|w\|=r}\|A(s₀+w)\|`, which is at most the `J`-th tail. That precision cost is the missing Frobenius. | `norm_phase_sub_one_le_of_smooth`, `norm_dpoly_shift_sub_le`, `exists_ne_zero_moments_eq_zero`, `norm_dpoly_le_expTail`, `norm_dpoly_near_return_le`, `eq_zero_of_exact_return` |
| Q6 | What survives of a positive count at `δ>0` as `δ→0`? | **Everything, if the positivity comes from damping; nothing, if it comes from renormalization.** Damping `ρ^{\|ν\|}` is Toeplitz positive and preserves Toeplitz positivity, and positivity of all damped kernels gives positivity at `δ = 0`. A critical layer with nonnegative weights is positive at every weight. But every real symmetric form, indefinite ones included, is the renormalized limit of raw forms made positive by a divergent diagonal counterterm. The renormalized torsion forms are of this second kind, so a critical-weight count must be a damping of something positive. | `toeplitz_dampWeight_posSemidef`, `toeplitzPositive_damp`, `toeplitzPositive_of_damped`, `toeplitzPositive_criticalLayer`, `eventually_posSemidef_add_counterterm`, `not_posSemidef_swap` |

## 6. Tools

| # | Tool (§2.8b) | Built | Module |
|---|---|---|---|
| T1 | infinite-rank Turán theorem with tail controlled by the reflected bottom layer | windows of length the exceptional rank; remainder of any rank, inner layer included, paid in trace norm; syndetic excursions; thick-set self-improvement; hiding cost | `TheExceptionalRankDecidesTheWindow`, `TheRankBarrier` |
| T2 | Frobenius substitute for auxiliary functions at the archimedean place | freezing of smooth polynomials at returns; moment-annihilated auxiliary polynomials; forced near-vanishing on discs about every return; flatness bound; uniqueness of exact returns | `ReturnsFreezeSmoothPolynomials` |
| T3 | mean values for Dirichlet polynomials longer than the height, with main terms | exact Fejér collision identity at every length; collision lower bounds; for `Σ_{n≤N} n^{−it}` the mean value lies between `TN(N+1)/(π²(T+1))` and `TN/2 + 6N²`, so beyond the height its main term has exact order `N²` against the diagonal `TN/2`; prime collisions = prime pairs at `\|log(p'/p)\| ≤ π/T` | `LongMeanValuesAreCollisionCounts` |
| T4 | count on correspondences at the critical weight | Toeplitz positivity of damped counts at every weight, losslessly to `δ = 0`; positivity of critical layers; no-go for renormalized counts | `TheCriticalWeight` |

T4 delivers the critical-weight count for damped objects. A count over `ℤ` whose Tate limit is the
Weil form exists iff RH (`CountingHolography`), so the arithmetic count itself is the open core, not a tool.

## 7. Pillar theorems

| Theorem | Lean |
|---|---|
| Reflection on level sums; equal outer and inner rank | `WeilTower.levelSum_neg`, `WeilTower.encard_outer_eq_encard_inner` |
| Vandermonde window bound | `exists_pos_forall_window_le_norm_expSum`, `exists_pos_forall_window_le_norm_pointSum` |
| Isolated-top window bound at infinite rank | `exists_pos_forall_window_le_norm_levelSum` |
| Syndetic excursions; thick sets self-improve | `eventually_forall_window_exists_lt_norm_levelSum`, `not_forall_mem_thick_norm_levelSum_le` |
| Price of hiding a top | `exists_pos_forall_window_vanish_le_tsum_norm`, `le_tsum_norm_of_hides_top` |
| Rank barrier | `levelSum_rootsOfUnityTower_eq_zero`, `card_Ioc_filter_not_dvd`, `norm_levelSum_rootsOfUnity_add_le`, `exists_unimodular_cancelling_layer` |
| Infinite-rank Hasse–Weil | `mergedWeight_eq_zero_of_thick_bound`, `WeilTower.mergedWeight_eq_zero_of_norm_ne_one` |
| Curves on thick sets of levels | `CurveDatum.unitary_of_thick_trace_bound`, `CurveDatum.unitary_of_thick_pointCount_bound` |
| RH = ZAL + AAL for every configuration; AAL fails at isolated tops | `rightRH_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `not_asymptoticAbscissaLaw_iff_hasIsolatedTop` |
| AAL = eventual-to-global; ZAL = well-founded tower | `asymptoticAbscissaLaw_iff_eventualToGlobal`, `wellFoundedAbove_frobTower_iff` |
| Periodic heads; symmetric shifts | `asymptoticAbscissaLaw_of_vertical_period`, `asymptoticAbscissaLaw_shift_iff` |
| FE admits every finite layer | `coshModel_one_sub`, `coshModel_conj`, `differentiable_coshModel`, `norm_coshModel_le`, `not_asymptoticAbscissaLaw_coshModelZeros` |
| Towers of `ζ`: lag = level sum; every point visible | `zetaTower`, `weilLagFunction_mul_eq_levelSum`, `mergedLagWeight_ne_zero` |
| Without AAL the lag is large once in every `k` levels, at every base | `exists_syndetic_lag_excursions_of_not_asymptoticAbscissaLaw` |
| A single top pair `Θ ± iγ` is seen at every level of the tower at base `π/γ` | `eventually_lag_large_of_single_top_pair` |
| AAL from a thick lag bound; RH = ZAL + one thick bounded lag | `asymptoticAbscissaLaw_of_thick_lag_bound`, `riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded` |
| The crude count in primes | `weilLagFunction_eq_primeDeviation`, `asymptoticAbscissaLaw_of_thick_primeDeviation_bound`, `riemannHypothesis_iff_zerosApproachLine_and_thick_primeDeviation` |
| Returns freeze smooth polynomials; forced vanishing; one exact return | `norm_dpoly_shift_sub_le`, `norm_dpoly_near_return_le`, `eq_zero_of_exact_return` |
| Long mean values are collision forms; order `N²` beyond the height | `fejerMean_eq`, `collisionCount_le_fejerMean`, `fejerMean_one_ge`, `fejerMean_one_le`, `primeCollisions_le_fejerMean` |
| Damping is lossless; renormalization carries no sign | `toeplitzPositive_damp`, `toeplitzPositive_of_damped`, `eventually_posSemidef_add_counterterm` |
| Calibration | `goldenDatum_not_thick_trace_bounded`, `not_forall_thick_trace_le_of_outer`, `integerNormOneOff_zal_not_aal` |

All are unconditional; the `ζ` statements depend only on `propext`, `Classical.choice`, `Quot.sound`.

## 8. Traps

| Trap | Truth |
|---|---|
| A constant-factor crude bound over `ℤ` is Stepanov's step | `\|ψ(x) − x\| ≤ C√x` is false; the crude statement lives on thick sets of levels of a smoothed tower, and the exceptional coordinate (ZAL) is what it needs |
| Turán's theorem works at infinite rank | its constants decay in the total rank; only the exceptional rank may enter |
| A bound on most levels self-improves | roots-of-unity tops vanish on density `1 − 1/k`, also over an infinite critical remainder |
| Finite rank of the critical part is needed to cancel a top | it is not: `N` modes hide any top on `N` levels; the obstruction is trace norm |
| Elimination holds for every summable tower | the proof needs a well-founded outer part (ZAL); accumulating outer parts can be invisible to a tower (Wolff walls) |
| The FE excludes a top layer through the power sums | the FE is the symmetry `S(−ν) = conj S(ν)`; cosh models carry every finite layer |
| Euler products with positive coefficients force AAL | the integer-norm one-off has ZAL and one top pair |
| AAL uses the position of the line | symmetric shifts preserve AAL |
| A thick-set bound is as strong as a bound at all levels | for self-improvement it is; producing it on a thick set is the crude step, and is open |
| Returns make every polynomial vanish | only moment-annihilated smooth ones, approximately, and the precision must beat the `J`-th tail |
| Forced vanishing at returns gives a Stepanov count | there are no exact returns besides `t = 0`; approximate vanishing forces no zeros without Rouché precision |
| A long mean value is its diagonal | beyond the height the collision form dominates; for primes it is a prime-pair count |
| A count positive at every `δ > 0` is positive at `δ = 0` | true for damping, false for renormalization |

## 9. Open research topics

1. **The crude step.** A bound on the lag (or on `primeDeviation`) along a thick set of levels of one
   tower, at every exponent `½ + a`: it gives AAL. The same at exponent `½`, with ZAL, is RH. No
   unconditional estimate gives a power saving for the prime deviation on any thick set of scales; the
   strongest pointwise saving is Vinogradov–Korobov.
2. **The finite stratum.** B13 in tower form: a finite visible outer part that survives a bounded lag on
   one thick set. The window length there is at most the off-line count `κ`; for one quartet it is `1`
   at the resonant base `π/γ` (`eventually_lag_large_of_single_top_pair`), so the first rung asks to
   exclude a lag that exceeds every `e^{aνπ/γ}`, `a < β − ½`, at every large level.
3. **Precision of forced vanishing.** A lower bound for `min_{|w|=r}|A(s₀ + w)|` for moment-annihilated
   polynomials that beats the single-prime return count at constant precision (B97).
4. **Main terms of prime collisions.** An asymptotic for the prime collision count at lengths
   `T^{1+θ}`: a binary problem of Hardy–Littlewood type.
5. **A damped arithmetic count.** A count on correspondences of `Spec ℤ` that is positive because it is
   a damping, not a renormalization (B87, B88).
6. **Non-well-founded towers.** Classify the towers with accumulating outer parts whose level sums are
   bounded on thick sets (Wolff walls); decide whether `ζ`'s towers can have one without ZAL.

## 10. Calibration

| Model | Present | Absent | IRW reading |
|---|---|---|---|
| Curves of every genus | all three steps | — | finite rank; thick-set crude count ⇒ RH |
| Golden fake, graph black holes | FE, integrality, rational zeta | damping | crude count fails on every thick set |
| Function fields | periodic heads | — | AAL automatic |
| Cosh models | FE, order one, reality, infinitely many critical zeros | Dirichlet series | ZAL, not AAL |
| Integer-norm one-off | Euler product, integer norms, linear counting | FE | ZAL, not AAL |
| Roots-of-unity tower | reflection, conjugation, visible top | — | bounded on density `1 − 1/k` |
| Symmetric shifts `ξ(s+a)ξ(s−a)` | FE, Euler product | the line | AAL ⇔ AAL(`ξ`) |

## 11. Context

| Neighbour | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | `CurveDatum`, `goldenDatum`, `frobEig`, prime towers, Wolff walls |
| ArithmeticOrientationGeometry | orbit correlations, eventual Hasse–Weil, rate = depth (the continuous-level form of Q3) |
| CountingHolography | crude count ⇔ count law on curves; the Tate door over `ℤ` |
| RHTower | AAL, ZAL, `weilLagFunction` and its prime side, `XiZeroCopy` and its involutions |
| ZeroConfigurationGeometry | eventual-to-global law and shift invariance for `ξ`; finite oscillation of `ψ` |
| HTGeometry | Turán's second main theorem (quantitative windows over the zeros of `ξ`) |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | finite stratum, Krein–Langer structure, tower decides |
| ArithmeticPositiveDuality | Beurling one-offs, positive annihilators |
| TailArithmeticOfThePrimeOrbit, PrimeTorusTheory | returns, precision law, Kronecker scale |
| HeightHomotopyArithmeticCounts | renormalized torsion forms on `ℓ²(n^δ)`: the renormalized side of Q6 |

## 12. Success criteria and contributions

IRW succeeds when each step of the curve proof has a theorem-level infinite-rank form, each question
Q1–Q6 has a theorem-level answer (positive, or a sharp no-go with its positive survivor), each tool
exists in its strongest unconditional form, every statement reduces to the curve proof at finite rank,
and the open core is one precise statement per step. That state is reached; what remains open is the
crude step — ZAL (at least quasi-RH) and the thick-set crude count of topic 1 — and the arithmetic
count of topic 5, which is RH.

A **contribution** must be unconditional; state its rank dependence (total, exceptional, none); say on
which calibration models it holds and fails; be invariant under symmetric shifts or say why not; and not
be an exact restatement of an RH-equivalent already in the corpus. A new producer must say on which set
of levels it bounds which tower, at which exponent, and why that set is thick.

## 13. Big picture

At finite rank Weil's three steps are a crude count, algebra, and a symmetry. At infinite rank the
algebra survives in a precise form: the self-improvement is the Vandermonde window theorem, its window
is the exceptional rank, its remainder is paid in trace norm, and it applies to well-founded towers on
thick sets of levels. The thick-set condition is sharp (roots-of-unity tops); well-foundedness is the
tower form of ZAL. The symmetry survives as a symmetry and does nothing more: it is consistent with
every finite top layer. What changes is the first step. On a curve the crude count is cheap because
the Frobenius fixes the points; over `ℤ` the prime orbit has one exact return, forced vanishing is
approximate, and the admissible precision shrinks with the order like the exponential tail. So the
infinite-rank Weil proof needs its new input in the crude step: a crude count along a thick set of
geometric scales of one tower, which at every exponent above `½` gives AAL, and at `½` together with
ZAL gives RH. Every other step is now a theorem.
