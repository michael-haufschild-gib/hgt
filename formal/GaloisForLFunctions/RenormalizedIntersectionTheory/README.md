# Renormalized Intersection Theory of the Scaling Surface (RIT)

Namespace `GaloisForLFunctions.RenormalizedIntersectionTheory`; umbrella
`RenormalizedIntersectionTheory.lean`. Everything is unconditional. Theorems named
`riemannHypothesis_iff_*` are equivalences and `riemannHypothesis_of_*` are implications into RH;
neither is a proof of RH.

## 1. Motivation

Weil's proof for a curve `C/𝔽_q` uses one object on `C × C`, the graph of Frobenius. Its
intersection with the diagonal counts points, the Hodge index on the plane it spans with the fibres
gives the sign (Castelnuovo–Severi), and the graph is canonical, so no twin of `ζ_C` carries it.

Over `ℤ` the corpus has these ingredients separately: the scaling correspondences and their
intersection numbers (the Weil correlation, AOG, HKT), the local hyperbolic planes at every place
(pole–successor states, AKG), the divergent diagonal and its running counterterm (AIT, RBG, AKLT),
and the localized sign problem of the complete Weil matrix (CACT, CAF, RAPT). RIT puts them on one
object, the **renormalized intersection pairing of scaling correspondences**, and answers with
theorems what this geometry delivers: how local poles glue to the global one, where the Hodge index
lives, what Castelnuovo–Severi says, what a Künneth square adds, and what separates `ℤ` from
`𝔽_q[T]`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Scaling correspondences, intersection matrix | `AdelicKreinGeometry.ratCorr`, `HeckeKreinToeplitz.zetaKernel` | `Γ_u · Γ_v = K_ζ(u⁻¹v)`, `K_ζ(u) = W(B, B(· − log u))` |
| Pole class | `AdelicKreinGeometry.boostMassU` | `ℓ(w) = Σ w_i u_i^{−1/2}`; on integer slopes the pole conductor `v_1` |
| Glued global state | `AdelicKreinGeometry.archGlue`, `weilArchState` | `K(|a|) − c|a|^{−1/2}|b|`: pole class + archimedean successor |
| Hyperplane index | `AdelicKreinGeometry.boostPolarIndex` | negative squares on `ℓ = 0` |
| Renormalized Hodge index | `RenormalizedHodgeIndex` | `boostPolarIndex K = 0` |
| Local boosts | `localBoost`, `archBoost`, `primeUnit` | `χ_p(u) = |u|_p^{1/2}`, `χ_∞(u) = |u|^{1/2}` |
| Weights | `weightChar S t` | `χ^t = ∏_{p∈t} χ_p · ∏_{p∈S∖t} χ_p⁻¹` |
| Separated sum / tensor product of local poles | `sumPole`, `tensorPole` | `Σ_p (χ_p + χ_p⁻¹)`, `∏_p (χ_p + χ_p⁻¹)` |
| `S`-units, separating unit | `sUnit`, `sepUnit` | `∏_{q∈S} q^{n_q}`, `∏_{q∈S} q²` |
| Positive index | `posIndex` | `κ₊(k) = κ(−k)` |
| Tensor (Künneth) kernel | `tensorKernel`, `kunnethZeta` | `(k ⊠ l)(g, h) = k(g) l(h)`; `K_ζ ⊠ K_ζ` |
| Spline series, spline weights | `splineSeries`, `splineWeight` | `F(t) = Σ_ρ e^{t(ρ−1/2)} w_ρ`, `K_ζ(u) = F(−log u)` |
| Integer slopes | `integerSlopes`, `finHorizon` | the atoms `1, …, N` of the complete Weil matrix |
| Glued test index | `gluedTestIndex` | supremum over tests of the index of `K_{λ,g}` glued to the archimedean successor |
| `S`-unit group; renormalized infinite product | `sUnitHom`, `sUnits`, `halfPole`, `infTensorPole` | `∏_p ½(χ_p + χ_p⁻¹)` |
| Hadamard powers | `fun u => zetaKernel u ^ (n + 1)` | restriction of the tensor powers to the diagonal |
| Sign gauge at atomic resolution | `gaugeAtom` | `D·1 − P_N(ω·)` on the horizon `{1, …, N}` |
| Atomic Hodge defect | `HeckeKreinToeplitz.poleNegIndex` | index of `gaugeAtom` on the pole hyperplane `Σ x_n/√n = 0` |
| Margin | `SelectiveMultiscaleArithmeticPositivity.HasHyperplaneGap` | `g` with `P_N(ωx) ≤ (log N − γ − g + ε)|x|²` on the pole hyperplane |
| Separation | `HodgeSeparates` | just above `ζ`'s ceiling the Hodge index holds for `ζ` and fails for `ω`, infinitely often |
| Separation from a base gauge | `HodgeSeparatesFrom` | the same, measured against a gauge `ω₀` of margin `g`; the `2`-adic probe uses the `2`-flip |
| Polar moment, prime mean, logarithmic prime mass | `polarMoment`, `primeMean`, `primeSetLogMass` | `M(N) = Σ_{n≤N} (ω(n)/n) log(N/n)`, `Σ_{p≤n} ω(p) log p/p`, `Σ_{p∈P, p≤n} log p/p` |
| Residue-class primes | `residueClassPrimes` | the primes `≡ r mod q` |
| Conductor weights and energies of a prime set | `ArithmeticCountingPositivity.primeSetSpectralWeight`, `ramanujanAdjunctionEnergy`, `flipPrimeWeight`, `flipPrimeEnergy` | `w_P(m) = (μ * ω_P)(m)²/φ(m)`, `E_m = γ + log m + Σ_{p∣m} log p/(p − 1)`; on `∏_{p∈T} p`: `∏ 4/(p − 1)` and `Σ p log p/(p − 1)` |
| Critical zeros seen by the spline; on-line configuration | `criticalSeen`, `zetaOnLine` | zeros `1/2 + iγ` with `B̂(γ) ≠ 0`; the on-line part of `K_ζ` as a Bohr series |
| Band poles of the loop-Eisenstein factor | `reflectionPoles` | zeros of `Λ(s + 1)` with `−1/2 < Re s < 0` |
| Heat dilation kernel | `AdelicKreinGeometry.heatDilationKernel` | the correlation of `H_t`, glued as `heatArchState` |

## 3. Language

- **Renormalized pairing**: the pairing of scaling correspondences on families of slopes, with the
  pole class split off by the archimedean glue.
- **Pole-orthogonal hyperplane**: `ℓ = 0`; on the integer slopes `v_1^⊥`.
- **Renormalized Hodge index**: no negative square on the pole-orthogonal hyperplane; equivalently
  the glued global state has exactly one negative square, the successor's.
- **Separated sum, tensor product, extremal component**: the three ways to combine local poles.
- **Weight**: a sign pattern `t ⊆ S`; **extremal** weights are `t = ∅` and `t = S`.
- **Archimedean weight**: one that agrees on the primes of `S` with `u ↦ u^s`.
- **Exponents**: `log |u|` on the `S`-units, the dilation factors of the extremal weight.
- **All-or-nothing**: an index that only takes the values `0` and `∞`.
- **Hodge defect**: the hyperplane index `boostPolarIndex K`; the Hodge index is defect `0`.
- **Margin** of a sign gauge: its largest hyperplane gap; `ζ` has the maximal margin `2 log 2`,
  set by the conductor-`2` excitation.
- **Relative logarithmic density** `κ` of a prime set `P`: `Σ_{p∈P, p≤n} log p/p = κ log n + O(1)`;
  its flip has prime mean `β = 1 − 2κ`.

## 4. Mechanisms

**Gluing.**
1. The archimedean place glues by a hyperplane: `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`. For
   Weil's correlation the hyperplane carries the whole index, `κ^{(½)}(K_ζ) = κ(K_ζ)`. The pole pair
   vanishes on the hyperplane, so the glued index is blind to the pole weight.
2. Local poles expand in weights: `∏_{p∈S}(χ_p + χ_p⁻¹) = Σ_{t⊆S} χ^t`; weights pair as `t ↔ S∖t`; at
   the separating unit `∏ q²` the values `∏_{S∖t} q / ∏_t q` are distinct by unique factorization, so
   every weight pair costs exactly one square.
3. The product formula identifies the archimedean boost with the extremal weight on the `S`-units;
   comparing moduli prime by prime shows that the extremal weights are the only archimedean ones.
4. Dividing every local pole by `2` makes the product over all primes finite at each point; on the
   `S`-units it is `2^{−|S|}` times the product over `S`, so it carries every weight pair of every `S`
   and gives the extremal one weight `2^{−|S|}`.
5. Gluing never loses a square, so a test-uniform index ceiling transfers to the glued state; flip
   twins have no ceiling, `ζ` has the ceiling `κ(K_ζ)` attained by the cubic spline.

**Density.**
6. `log p / log q` is irrational, so with two primes the exponents of the extremal weight are dense;
   with one prime (and over `𝔽_q[T]`) they form a lattice.

**Künneth.**
7. On product families the Gram matrix of `k ⊠ l` is a Kronecker product, on arbitrary families its
   diagonal principal submatrix; Kronecker inertia gives both bounds of the index law.
8. The zero side of `K_ζ` is absolutely summable on the strip, so `F` is continuous and the tensor
   square is the exponential sum over pairs of zeros.
9. A bound on `K_ζ` over `ℚ_{>0}` transfers to all real scales by density of `log ℚ_{>0}` and
   continuity of `F`; a bounded spline orbit has zero width `0`.

**Complete Weil matrix.**
10. On integer slopes the boost functional is `√(log N)⟨·, v_1⟩`.
11. A single eigenvalue below `T` and a floor `L` give `⟨Ax, x⟩ ≥ T‖x‖² − (T − L)⟨x, e⟩²`, and
   orthogonality to `v_1` bounds `⟨x, e⟩` by the projection error of `v_1`.
12. Codimension one: two negative eigenvectors span a plane that meets every hyperplane, so
   positivity on one hyperplane leaves at most one negative eigenvalue.
13. One hyperplane, three readings: on atomic tests the continuous pole moment `∫ f e^{−u/2}` is
   `(∫ g e^{−u/2}) Σ x_n/√n`, a positive multiple of `⟨x, v_1⟩`; so the Markov hyperplane of
   SpacingScaleHarmonicAnalysis, the harmonic hyperplane and `v_1^⊥` coincide, and on it Weil's form
   is the Markov form.

**Powers.**
14. Schur: the Hadamard product is the tensor kernel restricted to the diagonal, so positive times
   positive is positive; a positive-definite power bounds `‖K_ζ‖`, which is RH.
15. Neutral pairs: on the finite stratum `−K_ζ` is the negated on-line part (negative semidefinite)
   plus the hyperbolic pairs of the right zeros with negated weights; removing the semidefinite part
   can only lower the index, and the arithmetic index formula counts one square per pair. So
   `κ₊ ≥ κ`, and the Kronecker inertia of positive against negative families gives `κ(K ⊠ K) ≥ κ²`.

**Positive squares.**
16. On the critical line the zero summand is `m_ρ|B̂(γ)|²` with `B̂(x) = (sin x/x)⁴`, so the on-line
   kernel is a Bohr series with nonnegative coefficients, and its positive index counts the critical
   zeros off the lattice `πℤ`; a window `(T, 2T]` has `≥ c₀ T log T` distinct critical ordinates and
   `≤ T/π + 1` lattice points. The off-line pairs of the finite stratum are a finite-rank
   perturbation, which cannot remove infinitely many squares.

**Selection.**
17. The `2`-adic probe: multiplying a twin by the `2`-flip adds `2` to its flip set; on finite flip
   sets the greatest gap drops strictly when a prime is added unless it is already maximal, and the
   `2`-flip is submaximal, so the probed twin falls strictly below the `2`-flip's margin.
18. Margin and Hodge defect are the same datum read two ways: a gap bounds the form on the
   hyperplane, hence kills the defect above `log N − γ − g`; a vector violating the gap is a negative
   direction of `D·1 − P_N(ω·)` on the hyperplane. Real forms extend to complex vectors through real
   and imaginary parts, because the pole functional has real coefficients.

**Heat.**
19. The heat kernel `K_t` is a finite sum of Jordan pair kernels at the nonreal right zeros of `H_t`;
   the archimedean glue adds one square, so the Hodge defect of `K_t` is the zero count, which only
   drops, by one per conjugate pair colliding on the real line.

**Wirsing.**
20. The Chebyshev identity turns the logarithmic moment of a completely multiplicative `ω` into
   `Σ_d Λ(d)ω(d)/d · L(N/d)`; Abel summation of the prime mean `β log t + O(1)` against `L(N/k)`
   costs the total variation of `L`, at most `H_N`, and the divisor swap returns the polar moment.
   So `L(N) log N = (1 + β)M(N) + O(log N)` with `M(N + 1) − M(N) = L(N) Δlog N`.
21. Bernoulli twice: to first order `A(log N)^b` is a supersolution of the recursion for
   `b > |1 + β|`; to second order the drift of `M/(log N)^{1+β}` is bounded by a telescoping
   difference of `(log N)^{−β}`, so `M/(log N)^{1+β} ± G(log N)^{−β}` are monotone envelopes that
   pinch a limit: `L(N) = C(log N)^β + O(1)`.

**Conductor series.**
22. A gap above `s` bounds every finite conductor packet `Σ_{m∈S} w_P(m)/(E_m − γ − s)` by `1/s` at any
   Euler density (ArithmeticCountingPositivity); so a packet above `1/s` separates, and at positive
   density, where the packets exhaust the secular series, nothing else does.
23. On squarefree conductors the weights are multiplicative and the energies additive. The bound
   `1/e ≥ Σ_j 2^{−j−1} e^{−2^{−j} e}` turns a packet into Euler products
   `∏_{p∈P, p≤X}(1 + (4/(p − 1)) e^{−σ p log p/(p − 1)})`; Abel summation of a lower logarithmic density
   `1/4` makes them `≫ σ^{−1}`, and the dyadic sum over `σ = 2^{−j}` diverges.

## 5. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Hodge index = index one of the glued state; hyperplane positivity | `renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one`, `renormalizedHodgeIndex_iff` | unconditional |
| The pole class carries no zero: `κ^{(½)}(K_ζ) = κ(K_ζ)` | `boostPolarIndex_ratCorr` | unconditional |
| RH = renormalized Hodge index = positivity on the pole-orthogonal hyperplane | `riemannHypothesis_iff_renormalizedHodgeIndex`, `riemannHypothesis_iff_hyperplane_nonneg` | equivalences |
| Pole blindness; quantum bound; collision mass reads the hyperplane index | `renormalizedHodgeIndex_add_polePair_iff`, `boostPolarIndex_ratCorr_le_iSup_collisionCharge`, `eventually_two_mul_boostPolarIndex_le_collisionMassAfter`, `tendsto_collisionMassAfter_of_boostPolarIndex_eq_top` | unconditional |
| The glued test index selects ζ: `κ(K_ζ) + 1` for `Λ`, `∞` for every finite flip twin; RH = glued test index one | `gluedTestIndex_vonMangoldt`, `gluedTestIndex_finiteFlip_eq_top`, `riemannHypothesis_iff_gluedTestIndex_eq_one` | unconditional; equivalence |
| Separated sum of `|S|` local poles has `|S|` squares | `negIndex_sumPole` | unconditional |
| Tensor product of `|S|` local poles has `2^{|S|−1}` squares; weight count | `negIndex_tensorPole`, `negIndex_weightPairs`, `tensorPole_eq_sum_pairKernel` | unconditional |
| The extremal pair has one square and is the archimedean pole on the `S`-units | `negIndex_extremalPair`, `archBoost_sUnit_eq_weightChar_empty`, `archPole_sUnit_eq_extremalPair` | unconditional |
| The archimedean weights are exactly the extremal ones | `exists_cpow_weightChar_iff` | unconditional |
| The renormalized infinite product of the local poles has infinite index and gives the global pole weight `2^{−|S|}` on the `S`-units | `infTensorPole_sUnit`, `negIndex_infTensorPole_comp_sUnits`, `negIndex_infTensorPole_eq_top`, `infTensorPole_sUnit_eq_arch_add` | unconditional |
| Exponents: dense for two primes; quantized for one prime and for commensurable place sizes (`𝔽_q[T]`) | `irrational_log_div_log`, `dense_exponents_pair`, `not_dense_exponents_single`, `not_dense_exponents_of_quantized`, `log_norm_archBoost_sUnit` | unconditional |
| Künneth inertia law | `hermIndex_kronecker_le_negIndex_tensor`, `negIndex_tensorKernel_le`, `negIndex_tensorKernel_eq_zero`, `negIndex_tensorKernel_self_eq_zero_or_top`, `negIndex_mul_le_negIndex_tensorKernel` | unconditional |
| A bounded Weil kernel is RH; Castelnuovo–Severi for rational scaling correspondences is RH | `riemannHypothesis_of_norm_zetaKernel_le`, `riemannHypothesis_iff_castelnuovoSeveri` | implication; equivalence |
| `K_ζ` has a positive square unless RH; the Künneth square of `K_ζ` is RH | `riemannHypothesis_of_posIndex_zetaKernel_eq_zero`, `riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero` | implication; equivalence |
| Künneth spectral identity: the diagonal square has the sums `ρ + ρ'` as frequencies | `kunnethZeta_eq_tsum`, `zetaKernel_sq_eq_tsum` | unconditional |
| The spline sees infinitely many critical zeros; the critical zeros carry infinitely many positive squares, `κ₊(K_on) = ∞`; on the finite stratum `κ₊(K_ζ) = ∞`; the Künneth square is all-or-nothing: RH or `κ(K_ζ ⊠ K_ζ) = ∞` | `criticalSeen_infinite`, `orbitKernel_onLine_eq_bohrSum`, `posIndex_orbitKernel_onLine_eq_top`, `posIndex_zetaKernel_eq_top_of_finite`, `riemannHypothesis_or_negIndex_kunnethZeta_eq_top` | unconditional; dichotomy |
| Pole class on integer slopes = complete-Weil ground conductor | `boostMassU_integerSlopes_eq_inner`, `boostMassU_integerSlopes_eq_zero_iff` | unconditional |
| Hodge index with gap at every fixed overlap | `eventually_completeWeil_floor_on_poleHyperplane` | unconditional |
| Hodge index at iterated-logarithmic overlap; the Hodge index on `v_1^⊥` is RH at overlap `2(log N)^α` for every `α > 0` (smooth profiles) and every `α > 1/2` (tilted spline); it leaves at most one negative eigenvalue | `eventually_completeWeil_hodgeIndex_iteratedLog`, `eventually_completeWeil_hodgeIndex_packet_root`, `exists_growing_packet_hodgeIndex_root`, `riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`, `riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log`, `riemannHypothesis_iff_completeWeil_hodgeIndex_log`, `poleHyperplane_markov_nonneg_iff_hodgeIndex`, `eigenvalues_nonneg_or_of_nonneg_on_orthogonal` | unconditional; equivalences |
| Schur product; every Hadamard power of `K_ζ` is RH | `isPosDefKernel_mul`, `isPosDefKernel_pow`, `riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow`, `riemannHypothesis_iff_negIndex_zetaKernel_pow_eq_zero` | unconditional; equivalences |
| Off-line zeros are neutral pairs: `κ(K_ζ) ≤ κ₊(K_ζ)` on the finite stratum; the Künneth square at least squares the index, `κ(K_ζ)² ≤ κ(K_ζ ⊠ K_ζ)`; a finite Künneth index is Lindelöf and a zero-free half-plane | `negIndex_zetaKernel_le_posIndex`, `sq_negIndex_zetaKernel_le_negIndex_kunnethZeta`, `negIndex_zetaKernel_le_negIndex_kunnethZeta`, `lindelof_of_negIndex_kunnethZeta_lt_top`, `quasiRH_of_negIndex_kunnethZeta_lt_top` | unconditional; implications |
| The atomic Hodge index separates `ζ` from a sign gauge iff the gauge's margin is below `2 log 2`: separated are Liouville, every gauge with `S_N² = o(log N)`, every cofinite flip, the prime flips `p < 11`, and exactly those flips of an arbitrary prime set (finite or infinite) whose greatest gap is below `2 log 2`; not separated are the prime flips `p ≥ 11` and every gauge with `S_N/H_N → 1`. With the `2`-adic probe (the index measured against the `2`-flip of `ζ`) every nontrivial prime-set twin of positive harmonic density is separated; every twin flipping all primes outside a set of positive harmonic density has bounded harmonic sums and is separated | `hodgeSeparates_liouville_mul_primeSetFlip`, `abs_harmonicSum_liouville_mul_primeSetFlip_le`, `hodgeSeparates_iff_not_hasHyperplaneGap`, `hodgeSeparates_primeSetFlip_iff`, `hodgeSeparates_cofiniteFlip`, `hodgeSeparatesFrom_iff`, `hodgeSeparates_or_probe_primeSetFlip`, `eventually_poleNegIndex_gauge_eq_zero_of_hasHyperplaneGap`, `frequently_one_le_poleNegIndex_gauge_of_not_hasHyperplaneGap`, `hodgeSeparates_liouville`, `hodgeSeparates_of_harmonicSum_small`, `hodgeSeparates_primeFlip_iff`, `not_hodgeSeparates_of_correlation` | unconditional |
| The renormalized Hodge index is the Hodge index of the scaling surface, and a sign-free Serre-dual `h⁰` with quadratic Riemann–Roch growth exists iff it holds | `renormalizedHodgeIndex_ratCorr_iff_scalingSurface_hodgeIndex`, `renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0` | equivalences |
| The loop-Eisenstein intertwining factor `Λ(s)/Λ(s+1)` has exactly `κ^{(½)}(K_ζ)` denominator zeros in the band `−1/2 < Re s < 0`; the Hodge index is their absence | `boostPolarIndex_ratCorr_eq_encard_reflectionPoles`, `renormalizedHodgeIndex_iff_reflectionPoles_eq_empty`, `riemannHypothesis_iff_reflectionPoles_eq_empty` | unconditional; equivalences |
| Wirsing for twins: `L(N) log N = (1 + β)M(N) + O(log N)`; `|L(N)| ≪ (log N)^{b−1}` for `b > |1 + β|`; `L(N) = C(log N)^β + O(1)` for `0 < β ≤ 1`; a flip of relative logarithmic density `κ` has `L(N) = C(log N)^{1−2κ} + O(1)` for `κ < 1/2`, bounded `L` for `κ > 1/2`, and is separated for `κ > 1/4`; residue-class twins with `φ(q) < 4`, among them the flips of the primes `≡ 1` and `≡ 3 mod 4`, are separated | `exists_abs_wirsing_equation_le`, `exists_abs_gaugeHarmonicSum_le_rpow`, `exists_abs_gaugeHarmonicSum_sub_rpow_le`, `exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le`, `exists_abs_gaugeHarmonicSum_primeSetFlip_le_const`, `hodgeSeparates_primeSetFlip_of_primeSetLogMass`, `exists_abs_primeSetLogMass_residueClassPrimes_sub_le`, `exists_abs_gaugeHarmonicSum_residueClassFlip_sub_rpow_le`, `hodgeSeparates_residueClassFlip`, `hodgeSeparates_primeSetFlip_one_mod_four`, `hodgeSeparates_primeSetFlip_three_mod_four` | unconditional |
| Conductor series: a finite packet above `1/s` separates a prime-set twin at any density, and at positive density separation is exactly a positive secular value; a lower logarithmic density `≥ 1/4` makes the packets unbounded and separates, residue-class twins with `φ(q) ≤ 4` included (the primes `≡ 1 mod 5`); flipping `2` separates; with the `2`-adic probe every nontrivial prime-set twin is separated | `hodgeSeparates_primeSetFlip_of_packet`, `hodgeSeparates_primeSetFlip_iff_secular_pos`, `exists_packet_gt_of_lowerLogDensity`, `hodgeSeparates_primeSetFlip_of_lowerLogDensity`, `hodgeSeparates_residueClassFlip_of_totient_le_four`, `hodgeSeparates_primeSetFlip_one_mod_five`, `hodgeSeparates_primeSetFlip_of_two_mem`, `hodgeSeparates_or_probe_every_primeSetFlip` | unconditional |
| Heat flow: Hodge defect of `K_t` = nonreal right zeros of `H_t` = pairs colliding after `t`; nonincreasing, jumps at collisions, zero for `t ≥ 1/8`; RH = Hodge index along the flow | `boostPolarIndex_heatDilationKernel`, `boostPolarIndex_heat_eq_sum_collisionPairs`, `antitoneOn_boostPolarIndex_heat`, `exists_left_boostPolarIndex_heat_eq_add_collisionPairs`, `renormalizedHodgeIndex_heat_of_eighth_le`, `riemannHypothesis_iff_forall_renormalizedHodgeIndex_heat`, `boostPolarIndex_ratCorr_lt_top_iff_bdd_heat` | unconditional; equivalence |

## 6. Tools

The tools named in the founding question, and where they live:

| Tool | Where | Use in RIT |
|---|---|---|
| Renormalized Pontryagin spaces with running counterterms and product-formula gluing | AdelicKreinGeometry (archimedean glue, gluing formula at every place); RIT (product-formula classification) | the glued state, the hyperplane index, the extremal weight |
| Adelic shell decompositions, archimedean shell calculus | AdelicKreinGeometry (`TheShellDecompositionOfAPoleSuccessorForm`), RenormalizedArithmeticPotentialTheory (completed shell energies) | the complete Weil matrix at fixed overlap |
| Ramanujan conductor frames beyond the square-root horizon | CompletedArithmeticForms (`RamanujanConductorFrames`), CriticalArithmeticCorrelationTheory | the pole class `v_1`, the conductor-2 excitation, confinement |
| Index theorems for renormalized Toeplitz/Fredholm forms | HeckeKreinToeplitz (index = right zeros, Bohr series, hyperbolic pairs), HTGeometry (Wiener–Hopf index) | Hodge defects, positive squares, Künneth law |
| Theta log-volumes as `h⁰` | ArithmeticOrientationGeometry (`TheThetaH0OfSpecZ`), SelectivePositivityAndThresholdLaws | the quadratic Riemann–Roch equivalence |
| Loop-group Eisenstein series as global carriers | HTGeometry/LoopEisenstein (affine `A_1` Weyl sums with `ξ`-ratio coefficients) | the band poles of the intertwining factor `Λ(s)/Λ(s+1)` count the Hodge defect |
| The heat flow as a homotopy of Pontryagin spaces | AdelicKreinGeometry (`TheHeatDeformedArchimedeanState`); RIT (Hodge defects along the flow) | the collision quantum as an index |

**Developed in RIT.**
- Finset form of the Krein–Langer index formula (`negIndex_sum_pairKernel_eq_card`) and its use on
  subgroups (`reflectChar_comp`, `sUnits`).
- Separation of weight pairs at `∏_{q∈S} q²` (`weightPairs_separation`).
- Weight calculus: expansion, reflection `t ↔ S∖t`, separating unit, unique-factorization separation
  (`weightValue_injOn`, `weightValue_ne_one`).
- Positive index and Kronecker inertia for tensor kernels on product groups; diagonal restriction.
- Continuity of zero-side exponential sums on the strip and density transfer from `ℚ_{>0}` to `ℝ`.
- Single-window Rayleigh bound and orthogonal-overlap bound for spectral windows.
- Pole-class identity between the archimedean glue and the complete Weil matrix.
- Codimension-one bound: hyperplane positivity leaves at most one negative eigenvalue.
- Schur product for kernels on groups through the Künneth law.
- Dictionary between hyperplane gaps (SMAP, ArithmeticCountingPositivity) and atomic Hodge defects
  (HKT): real bounds on the pole hyperplane ⇔ vanishing pole index.
- Hodge defects of the heat kernels, read off the glued heat states.
- The pole moment of a recentred atomic test as a positive multiple of `⟨x, v_1⟩`, turning
  continuous pole-hyperplane statements into Hodge statements for the complete Weil matrix.
- The on-line part of `K_ζ` as a Bohr series, and the lattice count that leaves infinitely many
  critical zeros seen by the spline.
- Separation from a base gauge and the `2`-adic probe for prime-set twins.
- The Wirsing bound and asymptotic for logarithmic sums of completely multiplicative `|ω| ≤ 1` with
  a prime mean: the Levin–Fainleib equation and the Bernoulli envelopes.
- The Laplace–Euler bound for squarefree conductor packets: dyadic exponentials, multiplicative
  weights, additive energies and Abel summation of a lower logarithmic density.

**To build.**
- Resolvent control of the twisted horizon vector at scale `c_N²` at zero Euler density: the
  maximal-margin side of the conductor-series criterion.
- A function-field version of the extremal-weight gluing theorem (the quantization of its exponents
  is proved).

## 7. Questions and answers

| Question | Answer |
|---|---|
| Is the global pole a product-formula coupling of local poles with one square? | Not as a sum (`|S|` squares), nor as a tensor product (`2^{|S|−1}`), nor as the renormalized product over all primes (infinite index, global pole of weight `2^{−|S|} → 0`); exactly as the extremal weight of the tensor product, which the product formula makes the archimedean pole and which is the only archimedean-continuous weight. The one square must be supplied by the archimedean place. |
| Is the renormalized pairing definite on the pole-orthogonal hyperplane? | This is RH, at infinite resolution (`riemannHypothesis_iff_hyperplane_nonneg`) and at every power of the logarithm (`riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`). At every fixed overlap the complete Weil form is positive there with a gap above the pole energy, at iterated-logarithmic overlap it is positive, and below the nineteenth root of the logarithm it is positive on fixed and slowly growing conductor packets. |
| What is `Γ_u · Γ_u`, and does Castelnuovo–Severi hold? | At infinite resolution `Γ_u · Γ_u = K_ζ(1)` for every `u`; at atomic resolution the diagonal diverges and is renormalized by the running counterterm `log N − γ`. Castelnuovo–Severi is `‖K_ζ(u)‖ ≤ K_ζ(1)` at every rational scale; it is RH, and any uniform bound on `K_ζ` already is. |
| Is there a Künneth formula whose `H²` carries `ρ + ρ'`? | The diagonal of `K_ζ ⊠ K_ζ` is the exponential sum over pairs of zeros with frequencies `ρ + ρ'`; its arithmetic side is the square of the prime side, so no new Euler product appears, and products of the spectrum are depth-homogeneous (ArithmeticKunnethTheory). |
| Does the Künneth square soften the sign? | No: it is positive iff RH, and so is every Hadamard power; its diagonal carries the sums `ρ + ρ'`; its index is at least `κ(K_ζ)²`, and it is all-or-nothing: RH, or infinitely many negative squares — the critical zeros supply infinitely many positive squares, and each off-line zero is multiplied by all of them. |
| What is the canonical counterterm and finite part? | The running counterterm `log N − γ` (Mertens); over `𝔽_q[T]` the ceiling is exact (`ArithmeticKreinLangerTheory.TheFunctionFieldCeilingIsExact`); no fixed counterterm works (`AdelicKreinGeometry.NoFixedCountertermMakesThePrimeKernelPontryagin`). |
| Is the collision quantum an index? | Yes: along the heat flow the Hodge defect of `K_t` is the number of conjugate pairs colliding after time `t`, and it drops by one per colliding pair. At `t = 0` the hyperplane index is bounded by the largest horizontal collision charge and, on the finite stratum, the collision mass is twice the index plus the multiplicity excess (HKT). |
| What separates `ℤ` from `𝔽_q[T]`? | Density of the extremal weight: dense exponents for two primes, a lattice over one prime and over `𝔽_q[T]`. |
| Why are negative directions confined to low conductors? | At fixed overlap: the low spectrum lives on the low conductors (`RenormalizedArithmeticPotentialTheory.TheLowCompleteWeilSpectrumLivesOnTheLowConductors`), the pole class carries the bottom and the hyperplane sits a gap above it. At iterated-logarithmic overlap the Hodge index holds. At `(log N)^α`, `α < 1/19`, it holds on fixed and slowly growing conductor packets, and on all of `v_1^⊥` it is RH for every `α > 0` with a smooth profile: confinement uniform over packets at any power of the logarithm is exactly the missing sign. |
| Does the pairing select `ζ` among its twins? | Yes. The glued test index is `κ(K_ζ) + 1` for `ζ` and `∞` for every finite flip twin. At atomic resolution the Hodge index separates `ζ` from a sign gauge exactly when the gauge's margin is below `2 log 2`: the Liouville twin, every cofinite flip, every gauge with `S_N² = o(log N)`, the prime flips `p < 11`, and every prime-set twin of submaximal greatest gap. Measured against the `2`-flip (the `2`-adic probe) it separates every nontrivial prime-set twin of positive harmonic density, the flips of primes `≥ 11` included, and it separates every twin flipping all primes outside a set of positive harmonic density. Among the flips of sets `P` for which both `Σ_{p∈P} 1/p` and `Σ_{p∉P} 1/p` diverge, every one that flips `2`, whose flipped primes have lower logarithmic density at least `1/4` (residue classes with `φ(q) ≤ 4`), or that carries a conductor packet above `1/s` is separated, and the `2`-adic probe separates every nontrivial prime-set twin. Open: zero-density twins without `2` whose packets all stay below `1/s` (numerically one unit class mod `7` without `2`), for which the convergent secular series predicts the maximal margin. |
| Is there a global carrier of the sign? | The loop Eisenstein series: the intertwining factor `Λ(s)/Λ(s+1)` of its constant term has exactly as many denominator zeros in the band `−1/2 < Re s < 0` as the pairing has negative squares on the pole-orthogonal hyperplane. |
| Is the heat flow a homotopy of glued states? | Yes: the Hodge defect of `K_t` is the number of nonreal right zeros of `H_t`; it is nonincreasing, drops by one per colliding pair, vanishes for `t ≥ 1/8`; RH is the Hodge index along the whole flow, and finite defect at `t = 0` is bounded defect along the flow. |
| What is `h⁰` on the scaling surface, and its Serre dual? | On the base, the theta log-volume `h⁰` of `Spec ℤ` with exact linear Riemann–Roch (`ArithmeticOrientationGeometry.TheThetaH0OfSpecZ`). On the surface, a sign-free `h⁰` with Serre dual `h¹ = h⁰(K − ·)`, quadratic Riemann–Roch growth and subquadratic degree-zero growth exists iff the renormalized Hodge index holds (`renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0`): it is the same datum as the sign, so it cannot be built before the sign is proved. |

## 8. Open research topics

1. Uniformity of the Hodge index at a power of the logarithm: at `(log N)^α`, `α < 1/19`, it holds on
   every fixed conductor packet and on slowly growing initial packets, and on all of `v_1^⊥` at
   `(log log N)^{<1/16}`; on all of `v_1^⊥` at `(log N)^α` it is RH. Every gain in the size of the
   packets or in the schedule for all vectors is a new unconditional positivity statement.
2. The positive index of `K_ζ` on the infinite stratum (it is infinite on the finite stratum and
   for the on-line part); with it the Künneth square would be all-or-nothing by the same mechanism on
   both strata (the dichotomy itself is already proved).
3. The maximal-margin side at zero Euler density. A prime-set twin is separated when one conductor
   packet exceeds `1/s`, at any density, and at positive density only then. At zero density with
   `2 ∉ P` and every packet below `1/s` (numerically one unit class mod `7` without `2`, density `1/6`)
   the secular series converges and predicts the maximal margin `2 log 2`. Proving it needs the actual
   resolvent of the twisted horizon vector at scale `c_N² ≍ (log N)^{−4κ}`: beyond finitely many
   conductor eigenlines its spectral mass must sit at energies `≫ c_N^{−2}`. With
   `L − γ − P_N = D − M_err`, `D` the Dirichlet form of the multiplicative graph, this is an upper bound
   on `⟨ω_⊥, (D − M_err − s)^{−1} ω_⊥⟩`, i.e. Thomson flows of small energy for the twisted charge.

## 9. Traps

| Trap | Fact |
|---|---|
| Summing local poles gives the global pole | Separated places keep one square each (`negIndex_sumPole`) |
| The tensor product of local poles is the global pole | It has `2^{|S|−1}` squares; only its extremal weight is global |
| The product over all primes, suitably renormalized, recovers the global pole | It has infinite index and weights the global pole by `2^{−|S|} → 0` |
| An index cannot select because it is twin-blind | Twin-blindness is for unitary twists; the glued test index separates every finite flip twin |
| The pole selects ζ on the hyperplane | The glued index is blind to the pole weight |
| A tensor square softens the sign | `K_ζ ⊠ K_ζ` is positive iff RH |
| Castelnuovo–Severi is weaker than RH | At rational scales it is RH; so is any uniform bound on `K_ζ` |
| The archimedean place is one more place | Its exponents are dense once two primes are present |
| A fixed counterterm renormalizes the diagonal | Only the running counterterm `log N − γ` does |
| Positivity at fixed overlap is a step toward RH | It holds unconditionally, with a gap on the hyperplane; RH needs growing overlap |
| The pole class might carry the negative square at finite resolution, so the hyperplane is weaker than RH | At every power of the logarithm positivity on `v_1^⊥` alone is RH |
| A finite but nonzero Künneth index is possible | The Künneth square is all-or-nothing: RH or infinitely many negative squares |
| A Hadamard power or tensor square is an easier sign problem | Every Hadamard power is RH; a finite Künneth index already carries the finite stratum |
| The Liouville twin escapes selection because it flips every prime | Its margin is `0`, so the atomic Hodge index separates it |
| The atomic Hodge index separates every twin | It separates exactly the margins below `2 log 2`; flips of primes `≥ 11` keep `ζ`'s margin and need the `2`-adic probe |
| The heat flow could create Hodge defect | The defect only drops, one per colliding pair |
| Twins whose flipped and unflipped primes both have divergent reciprocal sums escape the atomic Hodge index | Flipping `2`, a lower logarithmic density `≥ 1/4`, or one conductor packet above `1/s` separates them (the primes `≡ 1 mod 4`, `≡ 1 mod 5`); the `2`-adic probe separates all |

## 10. Context

| Neighbour | Interface |
|---|---|
| AdelicKreinGeometry | archimedean gluing formula, boost-polar index, pole pair, local signatures |
| HeckeKreinToeplitz | index formula for hyperbolic pairs, `K_ζ`, index = right zeros, collision charges |
| ArithmeticOrientationGeometry | spline orbit, rate theorem, configuration orbit correlations |
| CriticalArithmeticCorrelationTheory, RenormalizedArithmeticPotentialTheory | complete Weil matrix, ground state, Ramanujan vectors |
| HTGeometry | Hermitian inertia, Kronecker inertia, spectral windows |
| ArithmeticKreinLangerTheory, ArithmeticIntersectionTheory, RenormalizedBiarithmeticGeometry | counterterms, circle intersections, survival cones |
| SquareRootThreshold | zero width, tempered configurations |
| ArithmeticCastelnuovoSeveri, ArithmeticKunnethTheory | finite-field calibration (Frobenius span), golden datum failing the Hodge index, depth-homogeneity of spectral products |
| SelectiveMultiscaleArithmeticPositivity, ArithmeticCountingPositivity | hyperplane gaps (margins) of sign gauges and their classification for prime flips |
| RHTower (Mertens, Chebyshev identity), RenormalizedArithmeticPotentialTheory (Mertens in residue classes) | Mertens with bounded error, `log = 1 * Λ` for completely multiplicative twists, class Mertens sums |

In the RH research map RIT sits on the seam of the three wall families: the sign (Σ) is the
hyperplane positivity, the count (Π) enters through the zero width and the running counterterm, and
selection (Γ) is the open input on the pole-blind hyperplane.

## 11. Success criteria

The criteria the field must meet, and where they stand:

| Criterion | Status |
|---|---|
| Calibration over `𝔽_q`; the golden datum fails where the Hodge index fails | Quantized exponents over `𝔽_q[T]` (`not_dense_exponents_of_quantized`); calibration and the golden datum in ArithmeticCastelnuovoSeveri (`goldenDatum_not_hodgeIndex_at_01`) |
| Positivity by identity on `v_1^⊥` | Open; at fixed and iterated-logarithmic overlap positivity holds by estimate, at every power of the logarithm it is RH |
| Confinement with polynomial dependence | Fixed overlap and iterated-logarithmic overlap for all vectors; fixed and slowly growing packets below the nineteenth root of the logarithm; uniformity over packets at a power of the logarithm is RH |
| Product-formula gluing to one square | Settled as a classification: only the extremal weight, i.e. the archimedean pole, has one square |
| Quadratic Riemann–Roch | Equivalent to the renormalized Hodge index (`renormalizedHodgeIndex_ratCorr_iff_exists_serreDual_h0`); linear Riemann–Roch for the base in ArithmeticOrientationGeometry |
| One topology for both readings | Dense exponents with two primes; continuity against height decay in AdelicKreinGeometry |
| Integrality | Indices are integers: Hodge defects in `ℕ∞`, so any bound below `1` is the Hodge index |
| Zero-independence and twin sensitivity | Glued test index and atomic Hodge index separate `ζ` from its twins, including the twins of relative logarithmic density `κ > 1/4` (residue-class twins mod `3`, `4`, `6`) |

The field is developed when each question of §7 has a Lean theorem that answers it — an equivalence,
a classification or a no-go — and each tool of §6 is used by a pillar. It succeeds when one of its sign
statements on the pole-orthogonal hyperplane is proved at a resolution beyond fixed overlap without
passing through an estimate that its own no-gos exclude.

## 12. What counts as a contribution

- A Lean theorem, unconditional, in this folder, wired into the umbrella.
- It states a property of the renormalized pairing (gluing, hyperplane, weights, Künneth, density,
  counterterm) or builds a tool that another pillar uses.
- Equivalences with RH are labelled as such; every positive theorem says which wall it does not cross.
- New objects are built from integers, adeles and Weil's data, never from zero copies.

## 13. Big picture

The geometry Weil used survives over `ℤ` in renormalized form, and RIT pins down where the missing
sign sits. The global pole is the extremal weight of the product of the local poles — the unique
archimedean-continuous one — and the product formula makes its exponents dense as soon as two primes
are present; that density is what distinguishes `ℤ` from `𝔽_q[T]`. No assembly of local poles —
sum, product, or renormalized product over all primes — has one square: the global pole must be
supplied by the archimedean place, and it is. The archimedean place glues by one
hyperplane, orthogonal to the pole class, which on integer slopes is the ground conductor of the
complete Weil matrix. On that hyperplane positivity holds at every fixed overlap with a gap, and
positivity at every resolution is RH. Castelnuovo–Severi for the rational scaling correspondences, a
uniform bound on `K_ζ`, positivity of the Künneth square and glued test index one are each RH: the
intersection-theoretic reformulations do not soften the problem; they concentrate it on one
hyperplane and one function; so does every Hadamard power, and the Künneth square is all-or-nothing
because the critical zeros carry infinitely many positive squares. The quadratic Riemann–Roch of the
surface and the band poles of the loop-Eisenstein intertwining factor are the same datum as the
sign. Selection exists inside the pairing: the glued test index separates `ζ` from every finite flip
twin, the atomic Hodge index from exactly the twins of submaximal margin, and its `2`-adic probe from
every nontrivial prime-set twin of positive density. The heat flow deforms the glued state through
finite-index states, paying one unit of Hodge defect per collision, to the Hodge-index state at
`t = 1/8`. What is missing is the sign at growing resolution uniformly in the conductor: the Hodge
index holds at iterated-logarithmic overlap and on conductor packets below the nineteenth root of the
logarithm, and on the whole hyperplane at every power of the logarithm it is RH.
