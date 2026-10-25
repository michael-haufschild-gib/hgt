# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-25, corpus snapshot `0fa51c933`. Scope: the 31 live routes, 17 standalone candidates, PW-B, and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). The supporting note [what forces blindness](what-forces-blindness.md) is assessed against its Lean sources in §1.5.

## Evidence and classification

**Sources.** The inventory comes from the [frontier map](../rh-current-frontier-map.md), the [killed-routes catalogue](../rh-killed-routes.md) and the supporting note. Every status below was checked against the Lean corpus in three ways:

- about 90 queries with `scripts/formal_tools.py research`, covering every route receiver, every candidate and the supporting programmes;
- reading the module docstrings and statements of all Lean modules changed on 2026-10-25 (about 70 files), plus the key theorems of the 2410 frontier;
- checking whether a package umbrella reaches each module that the status documents cite with [S].

The working record is `logs/review-2510-update/`. No compilation and no axiom audit was run.

**Labels.** [L] = source reachable from a package umbrella at the snapshot. [S] = source that no umbrella reaches; it is not certified closure. A conditional theorem keeps its premises. A receiver (an RH-equivalent reformulation) is not a producer of its input.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: integration, finite certificates, regularity checks, transport of proved estimates, corollary assembly. IDs `W1`–`W9`, defined in the [summary](hard-obstacles-summary.md#1-just-work).
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements. Each is equivalent to RH, or stronger.
  - `B2.*`: classical open problems weaker than RH, such as quasi-RH, zero simplicity and density hypotheses.
  - `B3.*`: open problems isolated by this research. No solution is known and none is proved equivalent to RH.

Notation: `Δ = sup_ρ |Re ρ − 1/2|` (zero width), `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ`, which is quasi-RH. RH is rate zero.

## 1. Facts that fix the present frontier

### 1.1 Source status

| Item | Present status | Consequence |
|---|---|---|
| Summation-scope "defects" | **None exists.** Mathlib parses `∑ x ∈ s, f x - c` as `(∑ x ∈ s, f x) - c`. This was checked for every statement previously reported as defective, including `sum_Ioc_sq_mul_eq_abel` and `abs_sum_Ioc_sub_tsum_le_of_blocks` (centred-prime band) and `abs_sum_re_pow_sub_le` (upper Lefschetz bounds). Under the alleged parse each statement fails at an explicit point (`a₁ = a₁ − c` at `N = 1`; `2 ≤ windowConst 1 = 0` at `u = 1, N = 2`), and the proofs use the correct reading. | The centred-prime band and the balanced statistic are [L] quasi-RH equivalences (`centredPrimeBandPowerSaving_iff`, `balancedStatisticPowerSaving_iff`). The one-sided Lefschetz and genus-one graph-degree modules are [L] and prove exactly what they state (§2, HF and ACS). |
| Integration | 20 committed modules are [S]: 14 ACS Meyer and reading modules (`BoundedMeyerSourceSurface`, `BoundedMeyerFaithfulReserve`, `PositiveMeyerDegreesSeeReducedCriticalJets`, `MeyerAlgebraicCharacters`, `MeyerHermitianDegreePart`, `FiniteMeyerProjectorsSplitPositiveEnergy`, `MeyerFiniteJetAlgebra`, `MeyerFiniteProjectorAlgebra`, the four origin-mass modules, `SmoothFiniteReadingKernels`, `ArithmeticMajorantConeGeometry`); four BVI Vaughan leaves (`TheTopologyOfSubcriticalVaughanGramLimits`, `UniformLogarithmicCancellationInMobiusFloorSums`, `UniformStretchedExponentialCancellationInTheVaughanConvolution`, `VaughanGramsAtTheirActualHarmonicAmplitude`); `FiniteMobiusHarmonicSumsHaveExplicitLowerBounds`; APT `CriticalPrimeChannelBeyondLinearWindows`. | Everything else cited below is [L]. This includes the maximal blind Meyer ideal, harmonic coupling, sparse-spectrum annihilators, the FE/count-fluctuation theorem, the general-frequency Hamburger step, the Vaughan subcritical limit set with its amplitude and rank leaves, AOT active cosets, THIM integer local exponents, the SSA half-damping endpoints, the ground-rate equality, the prime-shell ladder, the Meyer source surface and the global majorants. `W1` integrates the rest. |
| Proof integrity | No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` in code positions of the project packages. `native_decide` occurs at `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean:749` (PA order-24 quadrature) and at `HTGeometry/MilnorKTwoSteinbergSurjective.lean:138` (not route-related). The first is imported only by three modules: `PrimeArchMomentTwentyThreeClosure`, `ThetaFirstAtomTailMajorantOrder` and `PrimeArchPositivePairedDiagonalExteriorOverlap`. | No route receiver depends on it. `W2` replaces both certificates. |

### 1.2 The first rung of every cancellation receiver is quasi-RH

Every graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is equivalent to a fixed zero-free strip [L]:

- WL lag or deficit at a fixed rate `σ < 1/2`;
- PBM regularized-series convergence on `Re s > α` (`xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`);
- the JAS positive level-one budget (`exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive`);
- BVI balanced-band and centred-prime-band power saving;
- short-window Möbius and prime saving (`moebius_and_prime_powerWindowSaving_iff_quasiRH`, `primePowerWindowSaving_iff_all_receiver_forms`);
- the Vaughan empty leg (`TheEmptyVaughanLegDetectsAFixedStrip`);
- RW and ACS floors at any rate `< 1/2`.

Unconditional arithmetic stops at the Vinogradov–Korobov region, which the corpus proves (`riemannZeta_ne_zero_vinogradovKorobov`), together with the de la Vallée Poussin and Littlewood regions. **No cancellation route has an intermediate target between Vinogradov–Korobov and a zero-free strip.** The multiplicative forcing law of §1.5 meets the same rung.

### 1.3 Positivity: the pointwise and averaged frontiers

- **Exact form [L].** For every real compact `C²` test, with no parity or moment restriction: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, and the endpoint is attained.
- **Pointwise positivity windows [L].**
  - Full form `≥ ‖f‖²/5000` through radius `3/10` (`fullZeroForm_ge_of_support_le_threeTenths`).
  - Odd form `≥ ‖f‖²/1000` through `181/500`.
  - Primitive smooth Hodge index through `(log 2 + 1/50)/2`.

  The archimedean part alone is positive on nonnegative one-sided windows up to `10/21`; that is not full-form positivity. The graded floor `−Ce^{r−κr^α}`, `α < 3/5`, still has leading rate `1/2`.
- **Averaged positivity [L].** For `A ≤ κ₀ log Γ` and `F₀ ∈ C²_c([−A, A])`:
  `Γ⁻¹∫_Γ^{2Γ} Q(F₀ cos γ·) dγ ≥ c₀ log Γ ‖F₀‖² − C₀ Γ^{−4/3} N(F₀)²` (`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`).

  The set of frequencies where the form is positive has positive measure, and the bad-frequency volume is bounded. Subpower averaged coercivity holds up to `A ≤ α log Γ` with `α < 2/3`, that is, prime support up to `Γ^{4/3}`. No theorem shortens the window `[Γ, 2Γ]`.
- **Aperture flow [L].** `μ(A)` is strictly decreasing, and RH holds iff `μ(A) > 0` at every finite `A`. On the prime-threshold ladder (`a₀ = 3/10`, `a_{j+1} = ½ log(j+2)`) every birth jump is zero. RH holds iff the cumulative frozen relaxation never exceeds `μ(3/10)` (`riemannHypothesis_iff_sum_frozen_relaxation_le`). Permanently frozen finite prime families are eventually `≤ −αe^c`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor.
- **Rates [L].** `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2` (`groundEnergyRate_eq_polarGroundEnergyRate`), `CompensatedWidthFloor (1/2)` and `RH ⇔ groundRate = 0`. Compensated floors at every `σ > Δ` are equivalent to `polarRate = Δ`. Bounded local off-line depth mass suffices for that equality; a failure needs collapsed clusters at doubly exponential height.
- **Finite-level existence [L].** RH holds iff every aperture `A` admits real weights, of any sign and growth and with no relation to the primes, that make the full Weil functional nonnegative on tests supported in `[−A, A]` (`riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`). A failure of RH is visible at one finite aperture for every weight system.

### 1.4 Realization: the maximal blind carrier

**Orientation [L].** On an FE-symmetric tempered configuration, the following are equivalent: orbit Hodge positivity, the orbit Hasse–Weil bound, and blindness to off-line pairs. A generic orbit's growth rate equals the depth of the deepest zero it sees. A scale-stable family is positive iff it is jointly blind. The global index `D` (distinct right zeros) is finite iff all sufficiently high zeros are critical, and RH ⇔ `D < 2`. The spline orbit decides RH by index `0` and by index `≤ 1` (`riemannHypothesis_iff_splineOrbit_negIndex_le_one`).

**Maximality theorem [L]** (`MaximalBlindIdealOfTheMeyerSource`).

- *Definition and characterization.* Mixed-trace boundedness along the centered scaling flow defines a carrier without reference to Ξ zeros. It holds exactly for sources whose Mellin transform vanishes at every off-line zero (`meyerTraceOrbitBounded_iff_offLine_values_zero`).
- *Structure.* The carrier `meyerTraceBoundedIdeal` is a two-sided, sharp-stable, flow-invariant convolution ideal. It contains every Poisson boundary and every critical jet of every order.
- *Exhaustion.* It equals the whole source iff RH holds, with no simplicity condition (`meyerTraceBoundedIdeal_eq_top_iff`).
- *Geometry.* Its restricted surface has Hodge index, RR, Bézout, ampleness and additive closure unconditionally.
- *Maximality.* Every sharp-stable right convolution ideal with nonnegative diagonal trace lies inside it (`le_meyerTraceBoundedIdeal_of_sharpPositiveIdeal`, `isGreatest_meyerSharpPositiveIdeal`). The proof turns an off-line value into a negative-trace packet `w = u − u♯` inside the ideal.
- *Real tests.* Every scale-shift-invariant Weil-nonnegative subspace of real tests consists of tests blind to off-line zeros (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`).

**Faithful variants.** These modules are [L] unless marked:

- Ordinary trace on the Meyer surface gives graded RR. Bézout, ampleness and additive closure are each equivalent to RH. Numerical equivalence equals principal equivalence iff every zero is simple.
- A faithful positive linear degree exists iff RH holds and every zero is simple.
- Hilbert–Schmidt reserve: `reserve − defect = ½‖A_g − A_{g♯}*‖²_HS`. The reserve gives Bézout and ampleness; RR holds for it iff RH holds and every zero is simple.
- [S] The bounded-orbit (operator-norm) carrier has RR, Bézout and ampleness; it is the whole source iff RH holds and every zero is simple.
- [S] Every positive Hermitian degree annihilates off-line blocks and higher critical jets. On finite packets it is a nonnegative weighting of critical values.
- [S] The origin-L² completion supports no continuous faithful cohomological reading; Poisson boundaries and every finite-jet graph are dense in it.

**The common pattern, now a theorem for one class.** Every unconditional positivity theorem in the corpus is positivity on a carrier blind to off-line zeros:

- low-grid-blind tests;
- bounded Meyer orbits;
- positive Hermitian degrees;
- jointly blind families;
- large-height heated heads;
- frequency averages.

For sharp-stable convolution ideals and scale-shift-invariant test spaces this is proved: single-channel positivity cannot leave the blind carrier. Simplicity enters only through operator-norm and faithful-degree carriers; the trace-bounded carrier reaches RH alone. What is missing is a **forcing law** with input from outside single-channel positivity.

### 1.5 Multiplicative forcing at the boundary line

`HarmonicCouplingForcesSourceBlindness` [L] couples dilated channels `s_k = σ + ikt` through `n^{−ikt} = (n^{−it})^k`.

- **Fejér barrier.** Every nonnegative cosine polynomial of degree 1 has `a₁ ≤ a₀`. Folded Fejér autocorrelation reaches `(6, 8, 2)` at degree 2. Every nonzero nonnegative cosine polynomial of any degree has `a₁ < 2a₀`.
- **Quantized forcing law.** Assume harmonic positivity on `σ > 1`, `a₀ < a₁`, origin pole of order at most 1, no poles at the harmonics `kt`, and integer zero orders. Then the zero order at `1 + it` is zero (`harmonic_quantized_zero_vanishing`). For ζ the hypotheses come from `Λ ≥ 0`, the residue at 1 and `ζ(2) ≠ 0`, with no circular input. The output is `riemannZeta_boundary_ne_zero_from_harmonic_forcing`, Mertens' `(3, 4, 1)` argument in divisor-order form.
- **Sharpness models.** Each model is [L] and satisfies all-degree harmonic positivity.
  - A double-pole Beurling system with nonnegative prime density keeps the zeros `1 ± it₀` at every degree.
  - A periodic-pole Euler ratio with a simple origin pole keeps a zero shielded by a second-harmonic pole.
  - Pole simplicity and harmonic pole isolation are therefore both necessary.
- **Coupled Weil ceiling.** For `f ≥ 0` and nonnegative coupling coefficients, the coupled off-line zero sum is at most the pole-plus-Gamma functional at every aperture. Off-line summands carry no sign, so this ceiling forces nothing by itself.
- **Interior.** The module's collar exclusion uses the classical region `riemannZeta_ne_zero_of_re_gt_one_sub` (`c/(log|t|)^9`), imported, not derived from the forcing law. The interior regions of de la Vallée Poussin, Littlewood and Vinogradov–Korobov are proved elsewhere in the corpus by the same positivity combined with growth bounds [L].

**Assessment of the supporting note.** The note's first claim, that single-channel correspondence-stable positivity is exhausted by off-line blindness, is the maximality theorem of §1.4. Its second claim is the Re s = 1 forcing law with its sharpness models. Two statements in the note go beyond the sources:

- The interior collar exclusion is imported, not forced.
- "Cannot reach `Re s = 1/2` without a higher-rank mechanism" is an interpretation, not a theorem.

Multiplicative forcing plus growth input reaches the Vinogradov–Korobov region, and its next rung is the fixed strip of §1.2.

### 1.6 Heat and divisor geometry

- **Local divisor geometry [L].** Complete at model level: the local repair cones, the sharp Hermite root barrier, the optimal first heat `a/(2h_{m+2}²)`, and the universal-reflector theorem (only positive monomials reflect the coefficient cone).
- **Large heights [L].** The radius-`R` head is coefficient-positive after heat `s` whenever `32R² ≤ s·N(t, R)`. Hence every positive heat repairs every sufficiently high head (`exists_radiusHead_heat_coeffNonneg`).
- **Positive time [L].** Zeros are real and simple beyond `2π exp((27/40+ε)/t)`. The Newman constant satisfies `Λ < 1/8` strictly.
- **What remains.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`: the de Bruijn–Newman core.

### 1.7 Cofactor escape (PM, CTF, BVI)

On every common limit of the actual cofactor Grams [L]:

- **Structure.** The limit carries a cyclic critical-Wiener module.
- **Admission.** Admission makes the module faithful and infinite-dimensional, with the full Bohr hull.
- **Escape.** On escape, the full paid ideal annihilates the module, and the module hull lies in the obstruction hull.
- **Zero-cofactor dichotomy.** `K_pp = 0` forces every vector `q ≥ p` to vanish and `dim ≤ p − 1`. An infinite module has `K_pp > 0` for every `p`.
- **Rank one.** A rank-one actual limit is the augmentation character or has `|χ(p)| = p^{−s}` with `s ≥ 1/2`.
- **Horizon order.** Every limit obeys the horizon-ratio law, which excludes odd-only white noise.
- **Reconstruction.** (Row, residual, trace) reconstruction is exact and injective, but only algebraically.

Abstract models satisfy every proved constraint except possibly the full paid ideal and the moving boundary:

- full white noise `K_{jk} = δ_{jk}/j` (PSD, sharp dilation, antipodality, horizon order);
- augmentation `K_{jk} = 1_{j=k=1}` (PSD, critical radius, packet contraction, horizon order). Its Wiener character is no half-plane point.

Neither model is shown to be compatible or incompatible with full paid-ideal annihilation and the moving forcing boundary.

### 1.8 Vaughan calibration and the half-damping endpoint

- **Vaughan [L].** At fixed cutoffs the leading Gram is rank one. Uniform product horizons give centered Grams `o(T^{1−2ε})`, and the absolute remainder budget has the trivial exponent `T^{1−2ε}`. A power gain for the empty leg is equivalent to `Θ < 1`.
- **Subcritical limit classification** (`TheSubcriticalVaughanGramLimitSet`, `TheOnlyAccumulationOfVaughanAmplitudesIsZero`, `TheRanksOfSubcriticalVaughanLimits` [L]; topology leaf [S]). Every moving-cutoff normalized limit at `0 < ε < 1/2` is the rank-≤ 1 smooth matrix at an amplitude `H_U² H_V²`. The amplitudes form a compact countable set whose only accumulation point is 0. Convergence occurs iff the cutoff product escapes or the amplitude is eventually constant. The leading order is classified completely; the residual below `T^{1−2ε}` is untouched.
- **Half damping [L].**
  - The signed prime-divisor hypercube form `Q_{1/2}(P)` is uniformly bounded over all squarefree `P`. This completes its phase diagram for `ε ≥ −1/2`.
  - Below half damping, a paid completely multiplicative pattern has an integer local exponent at every height, and exponent 0 off the real axis (`exists_int_localExponent_of_receiverBounded_damped`).
  - Dini and completely monotone defects are unpaid at every `0 < ε < 1/2`, and monotone defects obey the Dini law at `ε = 1/2`.

### 1.9 Functional equation and count regularity

A generalized-integer system with count error `O(x^{−p})`, `p > −σ`, cannot satisfy Riemann's functional equation on `−1/2 < σ < 0` (`false_of_functionalEquation_of_decaying_count` [L]). The over-regular Beurling systems with genuine zeros in `1/2 < Re s < 2/3` therefore violate it (`overRegularZeta_not_functionalEquation`). Under the functional equation the count must fluctuate at least as much as the sawtooth of `⌊x⌋`. Hamburger's theorem is formalized for ordinary Dirichlet series. Its Laplace step holds for arbitrary frequencies, where the imaginary-axis residues read the Bohr spectrum [L], and the Γ_R^d functional equation (d ≥ 3) has infinitely many solutions without Euler positivity [L]. **The corpus contains no system satisfying Riemann's functional equation, a Beurling Euler product with nonnegative prime measure and a simple pole, other than ζ.** It therefore has no countermodel with all of these invariants and an off-line zero.

## 2. The 31 routes

Each entry gives the present status, the (a) and (b) obstacles, and the walls involved (see the [walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime-cross-work receivers read `Δ` exactly; the endpoint is attained. RH ⇔ `E` bounded ⇔ coprime cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)` (`riemannHypothesis_iff_linear_criticalDeficitEnergy`). Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit has `Γ^{−1/2}` averaged decay up to `α < 2/3` [L]. Two primes on mixed lags suffice. The RH mean law keeps its RH premise.
**(a)** W4–W6: probe specialization and transport of supplied savings. W8(v): combine the high-zero tail with the filtered law into an averaged bounded-energy statement.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed `σ < 1/2`). B1.4 (from frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.7, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for every `A`. The flow never stalls. Shell decomposition: frozen relaxation (nonnegative) plus an arithmetic jump bracketed by collar correlations. On the prime-threshold ladder, RH ⇔ cumulative relaxation `≤ μ(3/10)`. Full and odd `H¹` rate sets are `[Δ, ∞)`; ground rate = polar rate [L]. Averaged log-aperture positivity (§1.3) and finite-level existence apply.
**(a)** W4/W7: certified low-sector matrices and further pointwise windows. W8(i): merge the RW, SRT and ACS rate dictionaries.
**(b)** B1.3 (sign at every aperture). B3.6 (signed collar/shell estimate along the moving ladder). B3.1 (`polarRate = Δ`). Fixed positive and exponential floors are excluded.
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent: `A(M)/M` bounded above, and bounded below. Actual terminal primes realize graph sources with vanishing diagonal cost. The isolated critical prime channel is negative on narrow windows. On dyadic and wider windows it has a positive limit `≥ log 2/(8π⁴)` [S]. Exact clock kernels and the two-block cross decomposition are present.
**(a)** W1 (integrate the beyond-linear-window module). W4–W6: schedules, clock kernels, finite cross-block identities.
**(b)** B1.1: the complete history (seed, inter-cutoff drift, covariance and endpoints together). Small diagonal cost does not give compactness.
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the literal matched-quantile history is RH-equivalent. The normalized history falls below `−δ(K+2)` cofinally, so no sublinear correction restores passivity. Hyperbola, centroid and square-debt identities and low-LCM payment are present.
**(a)** W4–W6: finite-history bookkeeping.
**(b)** B1.1: the full-history floor with high-LCM pairs, moving core and singular transport. Strong convergence does not give trace-norm control.
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** The current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond `primeArchHausdorffShiftThreshold k`, and RH ⇔ nonnegativity at every order and every shift below its threshold [L]. The order-24 closure rests on a `native_decide` certificate (§1.1) that no receiver imports.
**(a)** W2: a kernel-checkable replacement of the quadrature. W4/W7: further finite orders.
**(b)** B1.5: the remaining low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** Mertens at square root with slack is the closing estimate. Because `M(x) = Ω±(√x)` [L], `M = o(√x)` is impossible, and either one-sided `O(√x)` bound forces RH with simple zeros. The alternative receiver is the gap `θ(ε,t) < 1`. High-height Vinogradov–Korobov collars and bounded-height small-damping collars are proved. Other [L] results:

- prime-root and composite-order minor-arc laws;
- the all-modulus cross-scale saving `Q^{−δ/32}`;
- the diagonal Abel/PNT reduction;
- balanced-statistic and centred-prime band ⇔ `Θ < 1`;
- the complete Vaughan leading-order classification (§1.8).

**(a)** W5/W6: apply independent row estimates in their ranges.
**(b)** B2.1: the band power saving is exactly quasi-RH. B1.1: global cancellation, or interior anti-alignment between the collars. B2.6: power-saving sign correlations. Planted Euler factors keep the collars.
**Walls:** 1.0, 1.1, 1.12, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2` for `0 < t < 1/2`, and RH is equivalent to that bound at every such `t`. The one-sided bound `D_t(N) ≤ C` is also RH-equivalent. Full odd Weil positivity is an alternative receiver.
**(a)** W4, W6: chamber identities with the diagonal term kept.
**(b)** B1.3: signed nonlocal covariance at every `t`.
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** Critical-time Laguerre, Jensen and finite-head coefficient receivers are present. At any fixed `R² ≥ 1/2`, RH ⇔ all-height head coefficient positivity. Every positive heat repairs every sufficiently high head (§1.6). KKL positive-time reality holds beyond `2π exp((27/40+ε)/t)`. The local divisor geometry is complete.
**(a)** W8(iii): combine the radius-head and KKL results into an explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. W4/W7: finite Jensen and finite-head certificates at bounded height.
**(b)** B1.5: the zero-heat sign on the residual region (the de Bruijn–Newman core). B2.9: smaller upper bounds for the de Bruijn–Newman constant. B3.9: source-selective cofactor repair.
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace equals winding. An integral nonnegative residual below one vanishes, but neither its sign nor the sub-unit bound is derived. Literal Gaussian integer weights have nonpositive coprime covariance.
**(a)** W4, W6: trace and index bookkeeping.
**(b)** B1.6: a matrix-complete residual sign and an all-disc sub-unit estimate. The quantization step works; the source of the inequality is missing.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form / prime-window ceiling
**Status.** Exact forcing-sign dictionaries are present. The ceiling `c(L) ≤ e^{L/2} + B(1+L)` gives the AIP allocation. Prime-blind receivers are RH-equivalent. Finite `D` is even, and RH ⇔ `D < 2`. The archimedean place orients orbit segments, and full-cone source selection identifies `Λ` [L]. On curve data [L], the lower Lefschetz bound forces unitarity. The upper bound forces it unless a positive real outer eigenvalue exists; the golden datum has one, `φ`. In genus one, the Hodge index of the window equals degree positivity of `ℤ[F]` (`genusOne_hasse_tfae`). The Hecke graphs of `ℤ` satisfy no theorem of the square (`heckeCorrespondence_no_square_relation`).
**(a)** W4, W6: collar partitions, finite Gram data, ceiling-to-allocation transfer.
**(b)** B1.3: the complete pairing sign or the `O(L)` ceiling. B2.2: finite index. B3.10: compatible oriented families.
**Walls:** 1.3, 1.4, 3.13, 14.4.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy is nonnegative iff no odd bound state lies above `1/2`. One-signed odd bound states vanish; sign-changing ones are not excluded. The nodal criterion compares `sourceEnergy(absGraph)` with `4·sourcePair(pos, neg)`. Fixed-aperture completion, sharp cuts, generator-domain preservation (bounded skew-adjoint commutator) and window nodal convergence are [L].
**(a)** W5/W6: move concrete vectors through the completed domains.
**(b)** B1.3: the nodal or reflected-prime inequality.
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity holds on the coefficient orthant at small time. Fixed-rank coercivity holds. A Weil margin gives heat-Hankel positivity in a coupled rank–time window. Rank-`N` tests are blind above height `O(N√log N)`.
**(a)** W4/W7: finite-rank certificates and explicit window constants.
**(b)** B1.5: all-rank signed positivity at one common time. B3.12: decoupling rank from time.
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact Hilbert–Schmidt cone-positive renewal operator realizes the denominator through `det₂` with the exact divisor. Cone positivity does not confine resonances.
**(a)** W4, W6: determinant normalizations.
**(b)** B1.6: boundary-current orientation, i.e. mixed prime + Gamma ≥ pole with every cusp and seam term.
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH. Euler–Stieltjes saturation at one admissible `τ` is RH-equivalent. Collision masses are even and match the index bridge. Finite-head heat transfer, the Mehler bracket, Riemann–von Mangoldt cumulants, multi-pair witnesses, the sharp root barrier and optimal heat are [L]. Large-height repair as in §1.6.
**(a)** W8(iii): the explicit residual compact region. W4: finite polynomial heat transforms.
**(b)** B1.6: cap vanishing or source-side saturation. B1.5: heated-head positivity on the residual region.
**Walls:** 1.2, 1.14, 3.8.

### LI — Li even-cross clock
**Status.** The reciprocal-depth rate law holds: RH ⇔ subexponential lower floors at every positive rate. Each off-line rate is `≤ 1/431`, the maximal rate is `β < 1/300`, `β = 0` iff RH, and a positive `β` is attained on a finite packet. This currency is not `Δ`.
**(a)** W4/W7: finite Li/Jensen data with tails.
**(b)** B1.7: the subexponential floor.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** All [L]:

- The compact-`L²` first variation equals the extended Weil energy.
- Joint compact-window, moving-aperture and collared noncompact limits exist.
- On RH-complete factorial-tent families, RH ⇔ nonnegative first variation.
- Quantitative tent transfer.

**(a)** W5/W6: verify the cutoff and decay premises of specified families.
**(b)** B1.3, the same sign as RW. A common threshold across unbounded scale families stays open inside B1.3.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The cofactor-escape structure (§1.7) and the Vaughan classification (§1.8) are present. The size-truncated receiver equals the full natural form. Its exterior is paid, and `ε = 1/2` is paid for every squarefree support. Below half damping, paid multiplicative patterns have integer local exponents. The forcing splits into a power plus a bounded remainder, diffuse escape keeps the antipodal density, and the dilation commutator is bounded.
**(a)** W1: the ADR/BVI leaves. W5/W6: Vaughan calibration bookkeeping.
**(b)** B1.2: signed small-damping energy. B3.2: escape-state classification with the moving boundary. B3.3: quantitative coercivity. B3.11: the forward interior below half damping.
**Walls:** 1.8–1.10, 3.7, 3.12.

### JAS — Joint ancestry budget
**Status.** A positive level-one budget is equivalent to a half-plane bound `< 1/2`, i.e. quasi-RH [L]. The weighted budget variant obeys the same law. The half-power endpoint is RH. The Gamma–theta source is admitted at all finite supports.
**(a)** W4–W6: finite budgets.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Cofactor test family / Báez–Duarte
**Status.** Residual = `(1 − readout)² + centeredEnergy` and RH ⇔ both small together (`riemannHypothesis_iff_readout_and_centered_energy`). The floor `κ/log N` and the readout–energy uncertainty principle are exact. The Rayleigh quotient, variance criterion and cusp laws are present. Literal `−μ_N` aligns the readout.
**(a)** W4/W7: finite coefficient optimization.
**(b)** B1.2: rows with readout → 1 and centered energy → 0 at closing damping. B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat / critical feature variance
**Status.** All-degree positivity of the two literal source grids (spacings log 2 and log 3) on their polar hyperplanes is RH-equivalent; one grid alone aliases [L].
**(a)** W4/W7: finite Gram factorizations.
**(b)** B1.5: both grids at every degree.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton disc
**Status.** Line-centered Newton self-map discs covering every zero ⇔ RH. The interior margin has Laplacian `4(r² − |z−c|²)|Ξ''|² ≥ 0`. It is subharmonic, so the minimum principle is unavailable and boundary control does not give interior margin. Global scalar damping has only the trivial repair.
**(a)** W4: finite-disc identities.
**(b)** B1.5: the all-disc interior margin.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Bohr almost-periodic strong recurrence
**Status.** Each of the following is RH-equivalent: strong recurrence on every compact right-strip set, local recurrence at every point, and cutoff-uniform positive Haar mass of target twists. Recurrence holds exactly at points that are not zeros, and the self-return threshold reads the vanishing order.
**(a)** W5/W6: check specific compacts.
**(b)** B1.7: returns near possible zeros, without assuming zero-freeness.
**Walls:** 1.2, 3.2.

### EWU — Even Weil universality / pole-weight uniqueness
**Status.** Blind minima are attained and antitone, and they are nonnegative at every aperture ⇔ RH. Literal positivity holds on high dyadic, polynomial and lacunary windows. Full-cone source selection is [L]: pair tests recover every node, and single-node perturbations fail. Finite-level existence of positive weights at every aperture is RH-equivalent (§1.3).
**(a)** W4–W7.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Gaussian tail / Hedenmalm–Schur decay
**Status.** Uniform quartic Schur decay is RH-equivalent. An off-line zero forces a positive charge floor at late stages. Finite truncations converge strongly.
**(a)** W4.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil universality
**Status.** Odd positivity is RH-equivalent. The continuum light-cone variation is positive, and the compensated reflected-prime source is positive for every nonzero odd test. The fixed-support subunit collar is paid. Lattice Schur payment reduces to a finite head.
**(a)** W4–W7.
**(b)** B1.3: full reflected-prime and polar payment on unrestricted odd tests.
**Walls:** 1.3, 3.4.

### PBM — Prime-bias Mellin / regularized logarithm
**Status.** Graded receiver [L]: a half-plane bound at `α` ⇔ convergence of `Σ(Λ(n)−1)n^{−s}/log n` on `Re s > 1/2 + α`. RH is `α = 0`.
**(a)** W6.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1.

### RB — Robin bound
**Status.** The eventual Robin inequality holds iff it holds on colossally abundant numbers. Counterexamples need a growing lcm core and a small moving valuation defect. Failure exponents are tied to `Θ`.
**(a)** W4: finite checks.
**(b)** B1.7: the eventual extremal tail.
**Walls:** 1.1, 1.6.

### SRT — Square-root threshold and smooth detection
**Status.** One fixed-width late-lag family decides RH at every admissible width. The smooth detector has quadratic aperture `Cδ^{−2}(4+|γ|)²`. The single-height phase-selective law holds with explicit premises. Eventual all-height saving is refuted [L].
**(a)** W5/W6: instantiate witnesses.
**(b)** B1.4 and B1.1: horizon containment and the late-lag sign.
**Walls:** 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single shift
**Status.** Any one fixed shift `a > 0` against all even compact profiles decides RH. The antisymmetric light-cone kernel is positive. The subunit collar is paid for `log d ≤ a − R`.
**(a)** W5/W6.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Odd allocation for a test ⇔ nonnegativity of its zero form; allocation for all tests ⇔ RH. With universal constants, allocation holds up to a deficit `K e^r e^{−c√r}` (Sobolev norm), which is rate `1/2` [L]. Horizon-uniform Schur payment leaves a finite-head debt [L]. Active-coset payment and top-octave dominance are [L]. Shared-budget descent is exact: the excess is `kB`.
**(a)** W4/W7: finite ledgers.
**(b)** B1.3: one shared signed budget. B3.8: a nonlocal frustration calculus.
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi
**Status.** The exact source identity holds and RR is exact at every aperture.

- Reserve boundary rigidity: RR and Bézout on the same cone hold iff reserve = defect. Positive majorants give Bézout and ampleness, never RR. Finite readings (with mass) never give Bézout.
- The maximal blind Meyer ideal (§1.4) has the full restricted geometry, and its exhaustion is RH.
- The harmonic forcing law (§1.5) settles the boundary line.
- Sparse-spectrum annihilators exist [L]: if `Σ|a_k|^{−s} < ∞` for some `s < 1`, a compact `C²` test vanishes exactly on `{a_k}` off the real axis. ζ zeros are not such a set.
- Averaged log-aperture positivity [L].
- Zero census: simple-or-critical fraction `≥ 0.8876`; distinct critical ordinates `≥ 2H/(1+H) ≈ 0.8042`.
- TTPC: `N₀* ≥ (29/36 − β − ε)N`, and `β ≤ 1/18` would give `3/4`.

**(a)** W1: integrate the Meyer chain. W8(iv): restate effectivity as exhaustion of the maximal blind ideal.
**(b)**
- B1.6: an independent effectivity or forcing source that is not single-channel.
- B1.8: the faithful variants need simplicity.
- B3.4: a topology in which exhaustion can be proved by limits.
- B3.5: the surface section law.
- B3.14/B3.15: interior multiplicative forcing.
- B2.5: the coalescent surplus.
**Walls:** 1.3, 3.8, 14.4, 14.8, 14.10, 14.11.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Every one of them faces the forcing problem B1.6: construct the object before its sign, and prove the sign independently. The maximality theorem (§1.4) adds a constraint: a candidate whose positivity is single-channel and sharp-stable can only certify blindness.

| Candidate | Present construction / exact boundary | (a) Just work | (b) Open |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; the Fredholm trace receiver is exact. | W4, W5 | Annihilation law for the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support. | W4 | A pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W4 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; dyadic descent universality. | W4, W5 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W4–W6 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus; budgeted norm compression. | W4 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = off-line zero sum. | W4 | Cofinal contrast equality (B1.7). |
| **HJ** pre-divisor reflection | Prime/Gamma reservoir; residual = SEC charge = two-grid HCF sign. | W4 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W4 | Source lift with integral count (B1.6). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W4, W5 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained. | W4 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks are real-rooted, and their Ξ-limit ⇔ RH. Prime-log lossless stacks cannot converge to Ξ. | W4 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Energy probabilities erase grade. | W4 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W4, W5 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W4 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centered real compact-uniform convergence suffices. | W4, W6 | Arithmetic couplings with a centered limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W4 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W4 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C all read `Re ρ = 1/2` with exact depth laws. They detect blindness; they do not force it.

## 4. Supporting programmes

| Programme | Established | (a) Just work | (b) Open |
|---|---|---|---|
| **BVI** row cancellation | Prime and composite minor arcs. All-modulus `Q^{−δ/32}` saving. Diagonal reduction. Balanced and centred-prime band ⇔ `Θ<1` [L]. Kloosterman Parseval; prime Gram of rank three. | W6 | B2.1; B1.2 |
| **BVI** Vaughan | Leading Gram paid; product horizon `o(T^{1−2ε})`; absolute budget trivial; empty leg ⇔ strip; subcritical limit set classified (§1.8). | W1 (four leaves) | Signed interior energy (B1.2) |
| **ADR** cofactor module | §1.7. | W4 | B3.2, B3.3; ideal/hull equality |
| **ACCE** aperture flow, rates | §1.3; ground = polar rate [L]. | W8(i) | B3.6, B3.1 |
| **ACS / Meyer** | §1.4, §1.5. | W1, W8(iv) | B3.4, B3.5, B3.14, B3.15; B1.6, B1.8 |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; spline-orbit index laws; base theta `h⁰` with RR and Mellin. | W6 | B3.10, B3.5; B2.2 |
| **AOT** readings, hulls, width functor | Width functor; Wiener hull calculus; Bohr characters; active cosets [L]. | W6 | B3.4 |
| **ALDG** local divisor heat | §1.6. | W8(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height; finite-level existence. | W1 for the beyond-linear-window module | B1.4 |
| **BiScale** lag, packet, filtering | Endpoints; high-zero tail; filtered deficit. | W8(v) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping bounded but not Hilbert–Schmidt; boxes. | W4 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift floor `1/3` and lag-2 floor `1/4` exact; complex floor in `[−1/2, −1/3]`; half-damping hypercube endpoint for all squarefree `P` [L]. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; monotone-defect Dini law; integer local exponents below half damping [L]. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration and closure; cofactor-graph closedness ⇔ uniform estimate; finite pronic step embedding [L]. | — | Successor-sensitive carrier (B3.4) |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`; `β ≤ 1/18` would give 3/4. | — | B2.5, B2.7 |
| **Analytic inputs** | Guth–Maynard large values; 30/13 density; Heath–Brown all-length; sharp `S₂`; KKL horizon; dlVP, Littlewood and VK regions; FE/count fluctuation; Hamburger (ordinary frequencies) and the general-frequency Laplace step [L]. | — | B2.4, B2.8 |

## 5. Not open tasks

The following are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Exclusions with no source counterpart.** No summation-scope defects exist (BVI, APT, ACS). Filtered averaged coercivity is complete. The polar and full rates are equal [L].
- **Completed constructions.**
  - CHMD generator-domain and sharp-window passages.
  - Suzuki compact-`L²` and moving-window limits.
  - Heath–Brown all-length and sharp `S₂`.
  - The smooth detector.
  - Critical-deficit and Sobolev endpoint attainment.
  - Base theta `h⁰`.
  - Hermite optimal heat; large-height head repair at positive heat.
  - The maximal blind Meyer ideal and its restricted geometry.
  - Boundary-line nonvanishing as a forcing law.
  - The half-damping hypercube endpoint.
  - The Vaughan subcritical limit set.
  - The functional-equation/count-fluctuation theorem.
  - Sparse-spectrum annihilators.
  - Finite-level existence ⇔ RH.
- **Excluded mechanisms.**
  - positive exponential aperture floors;
  - eventual all-height phase saving;
  - non-monomial universal reflectors;
  - finite readings, with or without mass, as Bézout sources;
  - origin-L² faithful cohomology;
  - PSD, dilation and antipodality as escape exclusion;
  - permanently frozen finite prime families;
  - finite-dimensional affine-unitary successor carriers;
  - single-channel sharp-stable positive ideals as forcing carriers;
  - harmonic positivity without pole simplicity or with harmonic poles;
  - decaying count error under the functional equation.
- **Substitutions that do not hold.**
  - orthant positivity for signed positivity;
  - cone positivity for self-adjoint confinement;
  - finite rank for all ranks;
  - local payments for one budget;
  - finite aperture index for global index;
  - averages for selected heights;
  - an algebraic inverse for a bounded inverse;
  - a zero-indexed object for a pre-divisor construction;
  - an imported zero-free region for a forced one.
