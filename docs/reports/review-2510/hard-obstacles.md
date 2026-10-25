# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-25. Scope: the 31 live routes, 17 standalone candidates, PW-B, and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** The inventory comes from the four 2410 reviews, the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Every status below was checked against the Lean corpus with `scripts/formal_tools.py research` (48 saved queries) and by reading statements and module docstrings of all 340 Lean files that are new or changed since the 2410 review. The working record is `logs/review-2510/`. No compilation and no axiom audit was run.

**Labels.** [L] = committed source reachable from a package umbrella. [S] = working-tree source, or committed source that no umbrella imports; it is not certified closure. A conditional theorem keeps its premises. A receiver (an RH-equivalent reformulation) is not a producer of its input.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: integration, finite certificates, regularity checks, transport of proved estimates, corollary assembly. IDs `W1`–`W9`, defined in the [summary](hard-obstacles-summary.md#1-just-work).
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements. Each is equivalent to RH, or stronger.
  - `B2.*`: classical open problems weaker than RH, such as quasi-RH, zero simplicity and density hypotheses. They are first rungs or partial targets of the routes.
  - `B3.*`: open problems isolated by this research. No solution is known and none is proved equivalent to RH; some may be tractable.

Notation: `Δ = sup_ρ |Re ρ − 1/2|` (zero width), `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ`, which is quasi-RH. RH is rate zero.

## 1. Facts that fix the present frontier

### 1.1 Source status the frontier map does not yet reflect

| Item | Present status | Consequence |
|---|---|---|
| Summation-scope "defects" in BVI (`sum_range_moebiusWindowRow`, `sum_Ioc_sq_mul_eq_abel`, `sum_Ioc_two_pow_mul_eq`, `abs_sum_moebius_mul_kernelTerm_sub_le`, `hasMeanValue_of_rate`, μ² parity mean, `criticalPrimeEnergy_biUnion_range`) | **No defect exists.** Mathlib's `∑ x ∈ s, f x` parses its body at precedence 67, so `∑ x ∈ s, f x - c` means `(∑ x ∈ s, f x) - c`. Under the alleged parse, each statement is false at an explicit point, for example `0 = 2` at `Q=3, x=0` and `a₁ = a₁ − c` at `N=1`, so it could not have been proved. All affected BVI modules are sorry-free and imported by the BVI umbrella. | The balanced Möbius statistic and the centred-prime band are **[L] quasi-RH equivalences** (`balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`). The diagonal μ corollary, the every-modulus chain and the exact μ² coefficient hold as stated. |
| Zero-density filtered Weil coercivity | **Complete [L]**. The module has 3 700 lines, no sorry and is in the ACS umbrella. Its headline theorems are present, including averaged strict positivity at logarithmic aperture and a positive-measure set of positive frequencies. | Averaging is no longer an obstacle. What remains is selection: passing from the average to individual heights. |
| Ground-energy rates | **[S]**, actively edited working source: `groundEnergyRate = polarGroundEnergyRate` unconditionally; `CompensatedWidthFloor (1/2)`; `RH ⇔ groundEnergyRate = 0`. | The compensated/uncompensated rate distinction disappears. The only rate gap left is `polarGroundEnergyRate` versus `Δ`. |
| Integration state | Eighteen committed modules are reachable from no umbrella, so they are [S] by the corpus's own convention: thirteen ACS modules (the Meyer chain, majorant cone geometry, smooth reading kernels), AOT active cosets, the THIM Dini law and threshold, APT `CriticalPrimeChannelBeyondLinearWindows`, and `ZetaSmoothedLandauFormula`, whose full zero-sum estimate `exists_smoothedLandau_le` is assembled in uncommitted working source. Three more committed modules are reachable only through umbrella imports that are not yet committed: the prime-shell ladder, `MeyerSourceIntersectionSurface` and `GlobalArithmeticMajorantsSupplyBezout`. Eleven working-tree modules exist, including the bounded Meyer surface. | `W1` integration. The Meyer statements are listed in §1.4. |
| Proof-integrity scan | No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` in project files. There is one route-adjacent `native_decide`: `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean:749`, a rational quadrature for the PA order-24 moment closure. A dependency-closure check shows that the PA, JAS, HCF, ACS, WL and ACCE receivers used below do not import it. | `W2` replaces the certificate. No receiver claim is affected. |

### 1.2 The first rung of every cancellation receiver is quasi-RH

Every graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is equivalent to a fixed zero-free strip:

- WL lag/deficit at a fixed rate `σ < 1/2`.
- PBM regularized-series convergence on `Re s > α` (`xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`).
- JAS positive budget (`exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive`).
- BVI balanced-band and centred-prime-band power saving.
- Short-window Möbius saving.
- The Vaughan empty leg (`TheEmptyVaughanLegDetectsAFixedStrip`).
- RW/ACS floors at any rate `< 1/2`.

Unconditional arithmetic stops at Vinogradov–Korobov savings `exp(−κT^a)`, `a < 3/5`. **No cancellation route has an intermediate target between Vinogradov–Korobov and a zero-free strip.** Partial progress in this family therefore requires solving quasi-RH (`B2.1`) or working with averages.

### 1.3 Positivity: the pointwise and averaged frontiers

- **Exact form.** For every real compact `C²` test, with no parity or moment restriction: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, and the endpoint is attained. [L] [AllParity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AllParityCriticalDeficitAndEndpointSobolevLaws.lean)
- **Pointwise positivity windows.** Full form `≥ ‖f‖²/5000` through radius `3/10`. Odd form `≥ ‖f‖²/1000` through `181/500`. Smooth primitive form through `(log 2 + 1/50)/2`. The graded floor `−Ce^{r−κr^α}`, `α < 3/5`, still has leading rate `1/2`.
- **Averaged positivity [L].** For `A ≤ κ₀ log Γ` and `F₀ ∈ C²_c([−A, A])`:
  `Γ⁻¹∫_Γ^{2Γ} Q(F₀ cos γ·) dγ ≥ c₀ log Γ ‖F₀‖² − C₀ Γ^{−4/3} N(F₀)²`.
  The set of frequencies where the form is positive has positive measure. Subpower averaged coercivity holds up to `A ≤ α log Γ`, `α < 2/3`, that is, prime support `X ≤ Γ^{4/3}`, beyond the square-root (Nyquist) aperture `½ log Γ`. [Filtered Weil](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean)
- **Aperture flow [L; ladder module reachable only through an uncommitted umbrella import].** `μ(A)` is strictly decreasing, and RH holds iff `μ(A) > 0` at every finite `A`. On the prime-threshold ladder `a₀ = 3/10`, `a_{j+1} = ½ log(j+2)`, every birth jump is zero. RH holds iff the cumulative frozen relaxation never exceeds `μ(3/10)`. Families that keep a fixed finite set of primes frozen are eventually `≤ −αe^c`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor. [Shell flux](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean)
- **Rates.** By the [S] module, `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2`. Compensated floors at every `σ > Δ` are equivalent to `polarRate = Δ`. Bounded local off-line depth mass suffices for this equality; failure needs collapsed clusters at doubly exponential height. [Rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean)

### 1.4 Realization: blindness and faithfulness

**Orientation [L].** On an FE-symmetric tempered configuration, orbit Hodge positivity, the orbit Hasse–Weil bound and blindness to off-line pairs are equivalent. A generic orbit's growth rate equals the depth of the deepest zero it sees. A scale-stable family is positive iff it is jointly blind. The global index `D` (distinct right zeros) is finite iff all sufficiently high zeros are critical; RH iff `D < 2`. [Cycle orientation](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationOfACycle.lean), [index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean)

**Meyer surface** (genuine Poisson cohomology of the all-weight Meyer source). Unless marked otherwise these modules are [S] because no umbrella imports them.

- [L, umbrella import uncommitted] Ordinary trace gives graded Riemann–Roch (RR). Bézout, ampleness and additive closure are each equivalent to RH. Numerical equivalence equals principal equivalence iff every zero is simple. [Meyer surface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerSourceIntersectionSurface.lean)
- A faithful positive linear degree exists iff RH holds and every zero is simple.
- Every positive Hermitian degree annihilates off-line blocks and higher critical jets. What remains is a nonnegative weighting of critical values.
- Bounded centered orbits are exactly the critical highest jets.
- On the bounded-orbit carrier, RR, Bézout and ampleness all hold unconditionally. The carrier is the whole source iff RH holds and every zero is simple. [Bounded surface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BoundedMeyerSourceSurface.lean)
- Hilbert–Schmidt reserve: `reserve − defect = ½‖A_g − A_{g♯}*‖²_HS`. This reserve gives Bézout and ampleness; RR holds for it iff RH holds and every zero is simple.
- The origin-L² completion supports no continuous faithful cohomological reading. Poisson boundaries and every finite-jet graph are dense in it.

**The common pattern.** Every unconditional positivity theorem in the corpus is positivity on a carrier that is blind to off-line zeros:

- low-grid-blind tests;
- bounded Meyer orbits;
- positive Hermitian degrees;
- jointly blind families;
- large-height heated heads.

RH is the statement that the actual arithmetic source is itself blind. What is missing everywhere is a **forcing (exhaustion) law** that places the actual source in the closure of its blind carrier. Faithful versions of that law cost simplicity in addition to RH.

### 1.5 Heat and divisor geometry

- **Local divisor geometry [L].** The local divisor-repair cones, the sharp Hermite root barrier, the optimal first heat `a/(2h_{m+2}²)` and the universal-reflector theorem (only positive monomials reflect the coefficient cone) are complete at model level. [Optimal heat](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteOptimalHeat.lean)
- **Large heights [L].** The radius-`R` head of the horizontal Ξ slice is coefficient-positive after heat `s` whenever `32R² ≤ s·N(t, R)`. Since `N(t, R) → ∞`, every positive heat repairs every sufficiently high head. The proof uses zero counting only. [Radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean)
- **Positive time [L].** Zeros are real and simple beyond height `exp((27/40+ε)/t)`. [KKL horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean)
- **What remains.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`. This region is the de Bruijn–Newman core.

### 1.6 Cofactor escape (PM, CTF, BVI)

On every common limit of the actual cofactor Grams [L]:

- The limit carries a cyclic critical-Wiener module.
- Admission makes this module faithful, infinite-dimensional and with the full Bohr hull. A finite-dimensional module forces escape.
- On escape, the full paid ideal annihilates the module, and the module hull lies in the obstruction hull.
- (Row, residual, trace) reconstruction is exact and injective, but only algebraically.

Further results are [S] working source:

- Finite quotient index equals the joint spectral multiplicity.
- The Möbius and Liouville modules are unit-equivalent.
- Real Wiener convolution transports Grams.

White noise `K_{jk} = δ_{jk}/j` satisfies PSD packets, sharp dilation and antipodality. Those three constraints are therefore not enough to exclude escape. [Paid ideal](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/PaidWienerKernelsAnnihilateTheCofactorLimit.lean), [white noise](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/WhiteNoiseAndAntipodalEscapeData.lean)

**Vaughan calibration [L]:**

- Leading Gram: rank one at fixed cutoffs.
- Uniform product horizons: centered Grams are `o(T^{1−2ε})`.
- The absolute remainder budget has the trivial exponent `T^{1−2ε}`.
- Power gain for the empty leg is equivalent to `Θ < 1`.

What remains is the signed interior energy.

## 2. The 31 routes

Each entry gives the present status, the (a) and (b) obstacles, and the walls involved (see the [walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime-cross-work receivers read `Δ` exactly; the endpoint is attained. RH ⇔ `E` bounded ⇔ coprime cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)`. Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit has `Γ^{−1/2}` averaged decay up to `α < 2/3` [L]. Two primes on mixed lags suffice. The RH mean law keeps its RH premise. [Endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean)
**(a)** W4–W6: probe specialization and transport of supplied savings. W8: combine the high-zero tail with the filtered law into an averaged bounded-energy statement at its proved strength.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed `σ < 1/2`). B1.4 (from frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.7, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for every `A`. The flow never stalls. Shell decomposition: frozen relaxation (nonnegative) plus an arithmetic jump bracketed by collar correlations. On the prime-threshold ladder, RH ⇔ cumulative relaxation `≤ μ(3/10)`. Full and odd `H¹` rate sets are `[Δ, ∞)`. The averaged log-aperture positivity of §1.3 applies [L]. The ground rate equals the polar rate [S].
**(a)** W4/W7: certified low-sector matrices and further pointwise windows. W8: merge the rate dictionaries using the [S] equality once integrated.
**(b)** B1.3 (sign at every aperture). B3.6 (signed collar/shell estimate along the moving ladder). B3.1 (`polarRate = Δ`). Fixed positive and exponential floors are excluded.
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** An upper bound for the completed Möbius–divisor Abel moment is RH-equivalent. Actual terminal primes realize graph sources with vanishing diagonal cost. The isolated critical prime channel is negative on narrow windows. On dyadic and wider windows it has a positive limit `≥ log 2/(8π⁴)` ([S]: module not in an umbrella). Exact clock kernels and the two-block cross decomposition are present. [Abel receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean)
**(a)** W1 (integrate the beyond-linear-window module). W4–W6: schedules, clock kernels, finite cross-block identities.
**(b)** B1.1: complete history, meaning seed, inter-cutoff drift, covariance and endpoints together. Small diagonal cost does not give compactness.
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the literal matched-quantile history is RH-equivalent. Hyperbola, centroid and square-debt identities and low-LCM payment are present. [Floor criterion](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean)
**(a)** W4–W6: finite-history bookkeeping.
**(b)** B1.1: full-history floor with high-LCM pairs, moving core and singular transport. Strong convergence does not give trace-norm control.
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** The current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond `primeArchHausdorffShiftThreshold k`, and RH ⇔ nonnegativity at every order and every shift below its threshold [L]. The order-24 closure uses a `native_decide` certificate (§1.1) that the receivers do not import. [Fixed-order positivity](../../../formal/GaloisForLFunctions/RHTower/PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean)
**(a)** W2: kernel-checkable replacement of the quadrature. W4/W7: further finite orders.
**(b)** B1.5: the remaining low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** Mertens at square root with slack is the closing estimate. The alternative receiver is the gap `θ(ε,t) < 1`. High-height Vinogradov–Korobov collars and bounded-height small-damping collars are proved. [L] results:

- Prime-root and composite-order minor-arc laws.
- All-modulus cross-scale saving `Q^{−δ/32}`.
- Diagonal Abel/PNT reduction.
- Balanced Möbius statistic ⇔ `Θ < 1` (§1.1).

[Gap and collars](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean)
**(a)** W3: drop the defect qualifications. W5/W6: apply independent row estimates in their ranges.
**(b)** B2.1: the band power saving is exactly quasi-RH. B1.1: global cancellation or interior anti-alignment between the collars. B2.6: power-saving sign correlations. Planted Euler factors keep the collars.
**Walls:** 1.0, 1.1, 1.12, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2` for `0 < t < 1/2`; RH is equivalent to this bound at every such `t`. Full odd Weil positivity is an alternative receiver. [Directed covariance](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean)
**(a)** W4, W6: chamber identities with the diagonal term kept.
**(b)** B1.3: signed nonlocal covariance at every `t`.
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** Critical-time Laguerre, Jensen and finite-head coefficient receivers are present. At any fixed `R² ≥ 1/2`, RH ⇔ all-height head coefficient positivity. Every positive heat repairs every sufficiently high head (§1.5). KKL positive-time reality holds beyond `exp((27/40+ε)/t)`. The local divisor geometry is complete.
**(a)** W8: combine the radius-head and KKL results into an explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. W4/W7: finite Jensen and finite-head certificates at bounded height.
**(b)** B1.5: zero-heat sign on the residual region, the de Bruijn–Newman core. B2.9: smaller upper bounds for the de Bruijn–Newman constant. B3.9: source-selective cofactor repair.
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace equals winding. An integral nonnegative residual below one vanishes, but its sign and the sub-unit bound are not derived. Literal Gaussian integer weights have nonpositive coprime covariance. [Cubic specialization](../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicSpecialization.lean)
**(a)** W4, W6: trace and index bookkeeping.
**(b)** B1.6: matrix-complete residual sign and an all-disc sub-unit estimate. The quantization step works; the source of the inequality is missing.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form / prime-window ceiling
**Status.** Exact forcing-sign dictionaries are present. The ceiling `c(L) ≤ e^{L/2} + B(1+L)` gives the AIP allocation. Prime-blind receivers are RH-equivalent. Finite `D` is even and RH ⇔ `D < 2`. Orbit segments are oriented by the archimedean place. Full-cone source selection identifies `Λ` [L].
**(a)** W4, W6: collar partitions, finite Gram data, ceiling-to-allocation transfer.
**(b)** B1.3: complete pairing sign or the `O(L)` ceiling. B2.2: finite index. B3.10: compatible oriented families.
**Walls:** 1.3, 1.4, 3.13, 14.4.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy is nonnegative iff no odd bound state lies above `1/2`. The nodal criterion compares `sourceEnergy(absGraph)` with `4·sourcePair(pos, neg)`. Fixed-aperture completion, sharp cuts, generator-domain preservation (bounded skew-adjoint commutator) and window nodal convergence are [L]. [Generator domain](../../../formal/GaloisForLFunctions/RHTower/CHMDSharpGeneratorDomain.lean)
**(a)** W5/W6: move concrete vectors through the completed domains.
**(b)** B1.3: the nodal or reflected-prime inequality. Aperture-uniform coercivity is optional.
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity holds on the coefficient orthant at small time. Fixed-rank coercivity holds. A Weil margin gives heat-Hankel positivity in a coupled rank–time window. Rank-`N` tests are blind above height `O(N√log N)`.
**(a)** W4/W7: finite-rank certificates and explicit window constants.
**(b)** B1.5: all-rank signed positivity at one common time. B3.12: decoupling rank from time.
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact Hilbert–Schmidt cone-positive renewal operator realizes the denominator through `det₂` with the exact divisor. Cone positivity does not confine resonances. [Positive Fredholm](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalPositiveFredholm.lean)
**(a)** W4, W6: determinant normalizations.
**(b)** B1.6: boundary-current orientation, i.e. mixed prime + Gamma ≥ pole with every cusp and seam term.
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH. Euler–Stieltjes saturation at one admissible `τ` is RH-equivalent. Collision masses are even, and the counts match the index bridge. Results available: finite-head heat transfer, the Mehler bracket, Riemann–von Mangoldt cumulants, multi-pair witnesses, the sharp root barrier and optimal heat [L]. Large-height repair as in §1.5. [Global cap](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean)
**(a)** W8: the explicit residual compact region. W4: finite polynomial heat transforms.
**(b)** B1.6: cap vanishing or source-side saturation. B1.5: heated-head positivity on the residual region.
**Walls:** 1.2, 1.14, 3.8.

### LI — Li even-cross clock
**Status.** The reciprocal-depth rate law holds: RH ⇔ subexponential lower floors at every positive rate. The maximal reciprocal frequency satisfies `β < 1/300`, with each off-line rate `≤ 1/431`; `β = 0` iff RH, and a positive `β` is attained on a finite packet. This currency is not `Δ`. [Max growth](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockMaxGrowthRate.lean)
**(a)** W4/W7: finite Li/Jensen data with tails.
**(b)** B1.7: the subexponential floor.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** All [L]:

- Compact-`L²` first variation equals the extended Weil energy.
- Joint compact-window, moving-aperture and collared noncompact limits.
- On RH-complete factorial-tent families, RH ⇔ nonnegative first variation.
- Quantitative tent transfer.

[RH-complete transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean)
**(a)** W5/W6: verify the cutoff and decay premises of specified families.
**(b)** B1.3, the same sign as RW. A common threshold across unbounded scale families stays open inside B1.3.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The Vaughan and cofactor-escape structure of §1.6 is present. The size-truncated receiver equals the full natural form; its exterior is paid and `ε = 1/2` is paid. The forcing splits into a power plus a bounded remainder. Diffuse escape keeps the antipodal density. The dilation commutator is bounded. [Corrector](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ConstructingAnArithmeticCorrector.lean)
**(a)** W1: ADR working modules. W5/W6: Vaughan calibration bookkeeping.
**(b)** B1.2: signed small-damping energy. B3.2: escape-state classification and moving boundary. B3.3: quantitative coercivity. B3.11: the forward interior below half damping.
**Walls:** 1.8–1.10, 3.7, 3.12.

### JAS — Joint ancestry budget
**Status.** A positive level-one budget is equivalent to a half-plane bound `< 1/2`, i.e. quasi-RH [L]. The half-power endpoint is RH. The Gamma–theta source is admitted at all finite supports. [Budget law](../../../formal/GaloisForLFunctions/RHTower/JointAncestryBudgetZeroFreeLaw.lean)
**(a)** W4–W6: finite budgets.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Cofactor test family / Báez–Duarte
**Status.** Residual = `(1 − readout)² + centeredEnergy`. The Rayleigh quotient, variance criterion and cusp laws are present. Literal `−μ_N` aligns the readout. [Dual problem](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheDualProblemRayleighQuotientAndCofactorCuspLaws.lean)
**(a)** W4/W7: finite coefficient optimization.
**(b)** B1.2: rows with readout → 1 and centered energy → 0 at closing damping. B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat / critical feature variance
**Status.** All-degree positivity of the two literal source grids (spacings log 2 and log 3) on their polar hyperplanes is RH-equivalent; one grid aliases [L].
**(a)** W4/W7: finite Gram factorizations.
**(b)** B1.5: both grids at every degree.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton disc
**Status.** Line-centered Newton self-map discs covering every zero ⇔ RH. The interior margin has a nonnegative Laplacian; boundary control does not give it. [Disc margin](../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean)
**(a)** W4: finite-disc identities.
**(b)** B1.5: all-disc interior margin.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Bohr almost-periodic strong recurrence
**Status.** Strong recurrence on every compact right-strip set, local recurrence at every point, or cutoff-uniform positive Haar mass of target twists: each is RH-equivalent. Recurrence holds exactly at points that are not zeros. [Compact recurrence](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceOnCompactSets.lean)
**(a)** W5/W6: check specific compacts.
**(b)** B1.7: returns near possible zeros, without assuming zero-freeness.
**Walls:** 1.2, 3.2.

### EWU — Even Weil universality / pole-weight uniqueness
**Status.** Blind minima are attained and antitone; nonnegative at every aperture ⇔ RH. Literal positivity holds on high dyadic, polynomial and lacunary windows. Full-cone source selection is [L]: pair tests recover every node, and single-node perturbations fail.
**(a)** W4–W7.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Gaussian tail / Hedenmalm–Schur decay
**Status.** Uniform quartic Schur decay is RH-equivalent. Finite truncations converge strongly.
**(a)** W4.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil universality
**Status.** Odd positivity is RH-equivalent. Continuum light-cone variation is positive. The fixed-support subunit collar is paid. Lattice Schur payment reduces to a finite head.
**(a)** W4–W7.
**(b)** B1.3: full reflected-prime and polar payment on unrestricted odd tests.
**Walls:** 1.3, 3.4.

### PBM — Prime-bias Mellin / regularized logarithm
**Status.** Graded receiver [L]: a half-plane bound at `α` ⇔ convergence of `Σ(Λ(n)−1)n^{−s}/log n` on `Re s > α`. RH is `α = 1/2`.
**(a)** W6.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1.

### RB — Robin bound
**Status.** The eventual Robin inequality holds iff it holds on colossally abundant numbers. Counterexamples need a growing lcm core and a small moving valuation defect.
**(a)** W4: finite checks.
**(b)** B1.7: the eventual extremal tail.
**Walls:** 1.1, 1.6.

### SRT — Square-root threshold and smooth detection
**Status.** One fixed-width late-lag family decides RH. The smooth detector has quadratic aperture `Cδ^{−2}(4+|γ|)²`. The single-height phase-selective law holds with explicit premises. Eventual all-height saving is refuted [L].
**(a)** W5/W6: instantiate witnesses.
**(b)** B1.4 and B1.1: horizon containment and the late-lag sign.
**Walls:** 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single shift
**Status.** Any one fixed shift `a > 0` against all even compact profiles decides RH. The antisymmetric light-cone kernel is positive. The subunit collar is paid for `log d ≤ a − R`.
**(a)** W5/W6.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Odd allocation for a test ⇔ nonnegativity of its zero form; allocation for all tests ⇔ RH. Horizon-uniform Schur payment leaves a finite-head debt [L]. Active-coset payment [S]. Shared-budget descent is exact: the excess is `kB`.
**(a)** W1: integrate active cosets. W4/W7: finite ledgers.
**(b)** B1.3: one shared signed budget. B3.8: a nonlocal frustration calculus.
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi
**Status.** The exact source identity holds and RR is exact at every aperture. Reserve boundary rigidity: RR and Bézout on the same cone hold iff reserve = defect. Positive majorants give Bézout and ampleness, never RR. Finite readings (with mass) never give Bézout. The Meyer surface and bounded carrier are as in §1.4. Averaged log-aperture positivity [L]. Zero census: `offLineMoment ≤ 0.066V`; simple-or-critical fraction `≥ 0.8876`. [Exact effectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean)
**(a)** W1: integrate the Meyer chain. W8: restate effectivity as an exhaustion criterion.
**(b)** B1.6: Bézout on the exact cone, i.e. an independent effectivity source. B1.8: faithful variants need simplicity. B3.4: a jet-retaining completion with tail control. B3.5: the surface section law.
**Walls:** 1.3, 3.8, 14.4, 14.8, 14.9.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Every one of them faces the forcing problem B1.6: construct the object before its sign and prove the sign independently.

| Candidate | Present construction / exact boundary | (a) Just work | (b) Open |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set. | W4, W5 | Annihilation law for the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support. | W4 | A pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W4 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy. | W4, W5 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W4–W6 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W4 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = off-line zero sum. | W4 | Cofinal contrast equality (B1.7). |
| **HJ** pre-divisor reflection | Prime/Gamma reservoir; residual = SEC charge. | W4 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line. | W4 | Source lift with integral count (B1.6). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W4, W5 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained. | W4 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks are real-rooted; their Ξ-limit ⇔ RH. | W4 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Energy probabilities erase grade. | W4 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W4, W5 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ RH. | W4 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centered real compact-uniform convergence suffices. | W4, W6 | Arithmetic couplings with a centered limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W4 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W4 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C all read `Re ρ = 1/2` with exact depth laws. They detect blindness; they do not force it.

## 4. Supporting programmes

| Programme | Established | (a) Just work | (b) Open |
|---|---|---|---|
| **BVI** row cancellation | Prime and composite minor arcs. All-modulus `Q^{−δ/32}` saving. Diagonal reduction. Balanced and centred-prime band ⇔ `Θ<1` [L]. Kloosterman Parseval; prime Gram of rank three. | W3 | B2.1; B1.2 |
| **BVI** Vaughan | Leading Gram paid; product horizon `o(T^{1−2ε})`; absolute budget trivial; empty leg ⇔ strip. | W6 | Signed interior energy (B1.2) |
| **ADR** cofactor module | §1.6. | W1 | B3.2, B3.3; ideal/hull equality |
| **ACCE** aperture flow, rates | §1.3; ground = polar rate [S]. | W1, W8 | B3.6, B3.1 |
| **ACS / Meyer** | §1.4. | W1, W8 | B3.4, B3.5; B1.6, B1.8 |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; base theta `h⁰` with RR and Mellin. | W6 | B3.10, B3.5; B2.2 |
| **AOT** readings, hulls, width functor | Width functor; Wiener hull calculus; Bohr characters [S]. | W1 | B3.4 |
| **ALDG** local divisor heat | §1.5. | W8 | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height. | W1 for the beyond-linear-window module | B1.4 |
| **BiScale** lag, packet, filtering | Endpoints; high-zero tail; filtered deficit. | W8 | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping bounded but not Hilbert–Schmidt; boxes. | W4 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift floor `1/3` and lag-2 floor `1/4` exact; complex floor in `[−1/2, −1/3]`; size-cutoff receiver. | — | B3.13, B2.6 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; pronic dilations [S]; the critical partial-sum core [S]. | W1 | Successor-sensitive carrier (B3.4) |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`; `β ≤ 1/18` would give 3/4. | — | B2.5, B2.7 |
| **Analytic inputs** | Guth–Maynard large values; 30/13 density; Heath–Brown all-length; sharp `S₂`; KKL horizon. | W1 for the Landau formula | B2.4, B2.8 |

## 5. Not open tasks

The following are complete results or excluded shortcuts. They must not reappear as open obstacles:

- **Exclusions with no source counterpart.** The BVI summation-scope "defects" do not exist. Filtered averaged coercivity is complete. The polar/full rate distinction is closed in working source.
- **Completed constructions.** CHMD generator-domain and sharp-window passages; Suzuki compact-`L²` and moving-window limits; Heath–Brown all-length and sharp `S₂`; the smooth detector; critical-deficit and Sobolev endpoint attainment; base theta `h⁰`; Hermite optimal heat; large-height head repair at positive heat.
- **Excluded mechanisms.**
  - positive exponential aperture floors;
  - eventual all-height phase saving;
  - non-monomial universal reflectors;
  - finite readings, with or without mass, as Bézout sources;
  - origin-L² faithful cohomology;
  - PSD, dilation and antipodality as escape exclusion;
  - permanently frozen finite prime families;
  - finite-dimensional affine-unitary successor carriers.
- **Substitutions that do not hold.**
  - orthant positivity for signed positivity;
  - cone positivity for self-adjoint confinement;
  - finite rank for all ranks;
  - local payments for one budget;
  - finite aperture index for global index;
  - averages for selected heights;
  - an algebraic inverse for a bounded inverse;
  - a zero-indexed object for a pre-divisor construction.
