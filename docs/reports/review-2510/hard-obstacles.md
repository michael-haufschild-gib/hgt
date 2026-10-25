# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-25, corpus `eb175d946` plus the working tree of that day. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** The route inventory is that of the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Every status below was checked against Lean source: corpus searches with `scripts/formal_tools.py research` across all route receivers and open obstacles, full reading of the statements of every module changed since the previous review, and statement reading of older modules that the searches surfaced. The working record is `logs/review-2510-refresh/`. Nothing was compiled. Integration labels follow the frontier map; `[S]` marks a result the frontier map lists as not yet integrated.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, premise checks, transport of proved estimates, corollary assembly, technical strengthening of a proved theorem. IDs `W1`–`W9`, defined in the [summary](hard-obstacles-summary.md#1-just-work).
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger.
  - `B2.*`: classical open problems weaker than RH.
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

Notation: `Δ = sup_ρ |Re ρ − 1/2|`, `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero.

## 1. Facts that fix the present frontier

### 1.1 Proof integrity

No `sorry`, `admit`, `axiom`, `opaque` or `unsafe` occurs in code positions of the project packages. `native_decide` occurs in exactly two files: `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean` (PA order-24 quadrature; imported by no route receiver) and `HTGeometry/MilnorKTwoSteinbergSurjective.lean` (not route-related). `W2` replaces both.

### 1.2 The first rung of every cancellation receiver is quasi-RH

Each graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is equivalent to a fixed zero-free strip `Θ < 1`:

- WL lag or deficit at a fixed rate `σ < 1/2`;
- PBM regularized-series convergence on `Re s > α`;
- the JAS level-one budget;
- the balanced Möbius statistic and the centred-prime band (`balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`);
- short-window Möbius and prime saving;
- the Vaughan empty leg, and now every power improvement in the Vaughan picture: uniform convolution power cancellation (gain transfer `η/(2+η)`), uniform residual Gram power rates, a common-threshold factorial-order-one envelope, and reciprocal-tail power gains at any positive damping [S];
- RW and ACS floors at any rate `< 1/2`.

Unconditional arithmetic stops at the Vinogradov–Korobov region (`riemannZeta_ne_zero_vinogradovKorobov`), with the de la Vallée Poussin and Littlewood regions. No cancellation receiver has a target between Vinogradov–Korobov and a fixed strip. Multiplicative forcing meets the same rung (§1.6).

### 1.3 Positivity: pointwise and averaged frontiers

- **Exact form.** For every real compact `C²` test: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, endpoint attained.
- **Pointwise windows.** Full form `≥ ‖f‖²/5000` through radius `3/10`; odd form `≥ ‖f‖²/1000` through `181/500`; primitive smooth Hodge index through `(log 2 + 1/50)/2`. The graded floor `−Ce^{r−κr^α}`, `α < 3/5`, still has leading rate `1/2`.
- **Averaged positivity.** For `A ≤ κ₀ log Γ` and `F₀ ∈ C²_c([−A, A])`: `Γ⁻¹∫_Γ^{2Γ} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−4/3} N(F₀)²` (`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`). The main term is the local critical-zero weight; off-line contributions are controlled by zero-density shell bounds. Subpower averaged coercivity holds for `A ≤ α log Γ`, `α < 2/3`. No theorem shortens the window `[Γ, 2Γ]`.
- **Aperture flow.** `μ(A)` is strictly decreasing; RH iff `μ(A) > 0` at every finite `A`. On the prime-threshold ladder every birth jump vanishes, and RH holds iff cumulative frozen relaxation never exceeds `μ(3/10)`. Permanently frozen finite prime families are eventually `≤ −αe^c`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor.
- **Rates.** `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2` and `RH ⇔ groundRate = 0`. The CCM form-norm and Birman–Schwinger rates equal `Δ` unconditionally; the physical-`L²` equality `polarRate = Δ` holds under locally bounded off-line depth and is otherwise open.
- **Finite level.** RH holds iff every aperture admits some real weight system making the full Weil functional nonnegative on tests supported there.

### 1.4 Realization: the maximal blind carrier

- **Maximality.** `meyerTraceBoundedIdeal` (mixed-trace boundedness along the centered flow) consists exactly of the sources whose Mellin transform vanishes at every off-line zero. It is a two-sided, sharp-stable, flow-invariant convolution ideal containing every critical jet; its restricted surface has Hodge index, RR, Bézout, ampleness and additive closure; it is the whole source iff RH, with no simplicity condition. Every sharp-stable right convolution ideal with nonnegative trace lies inside it (`isGreatest_meyerSharpPositiveIdeal`), and every scale-shift-invariant Weil-nonnegative test space is off-line blind.
- **Faithful variants.** Faithful positive degrees, the Hilbert–Schmidt reserve and the bounded-orbit carrier each reach RH only together with simple zeros. The origin-`L²` completion supports no continuous faithful reading.
- **Common pattern.** Every unconditional positivity theorem in the corpus is positivity on a carrier blind to off-line zeros (low-grid-blind tests, bounded orbits, positive degrees, jointly blind families, large-height heated heads, frequency averages). For single-channel sharp-stable carriers this is a theorem.
- **Forcing transfer.** `ArithmeticForcesBlindness` proves that a Meyer source or scaling cycle whose off-line transform vanishes outside a zero-free region lies in the blind carrier (`arithmetic_forces_blindness_unconditional`). Blindness means vanishing at off-line zeros and a zero-free region contains none, so this is a tautological transfer, not a forcing law for the actual source. Its region is the boundary lines plus the imported classical collar `c/(log|t|)^9`.

### 1.5 Invariants: degree-one rigidity and its sharp relaxations

**Rigidity (APD).** Let `ν ≥ 0` be a Borel measure on `[1, ∞)` with `∫u⁻² dν < ∞` whose theta transform satisfies Riemann's degree-one law `θ_ν(x) = x^{−1/2}θ_ν(1/x) + α + βx^{−1/2}`. Then `ν = (−2 Re α)·Σ_{n≥1} δ_n` (`measure_eq_of_measureTheta_relation`). Mechanism: pairing the half-plane Laplace identity with the Fejér tent `2(1−|τ|)` annihilates the Poisson side and the polar residues and leaves `∫(sin πu/πu)² dν = 0`, which confines `ν` to the integers; imaginary-axis periodicity then equalizes the weights.

- A Beurling prime measure `P` on `(1, ∞)` whose integer measure `Σ P^{*m}/m!` obeys the law is `Σ (Λ(n)/log n) δ_n` (`eq_riemannPrimeMeasure_of_beurling_theta_relation`; iff form in `ArithmeticForcesBlindness`).
- The completed-FE version (`measure_eq_of_completed_functional_equation`) assumes the inverse-3/2 moment, the `Γ_ℝ` identities on `Re s = −1/2, 3/2` and a common holomorphic remainder with `|E(s)| ≤ C/(1+Im(s)²)` on the strip.
- Countable discrete Beurling systems with the law have ζ's Dirichlet series, unique factorization and a norm-preserving bijection of prime labels with the rational primes [S].
- Without nonnegativity only the linear constraint `Σ a_n (sin πλ_n/πλ_n)² = 0` survives; self-dual combinations of even characters break uniqueness.
- Hamburger rigidity for ordinary Dirichlet series survives an Abel-sublinear `L¹` defect of the FE on the critical line (`coeff_eq_of_critical_line_even_sublinear_defect`).

**Sharp relaxations.** Each relaxation of the invariant set breaks the conclusion. Dropping the simple pole, strip holomorphy or the functional equation gives Lean models with zeros off the critical line; dropping coefficient positivity breaks uniqueness. Positivity of the generalized von Mangoldt measure (`Λ ≥ 0`) implies positivity of the integer measure, so the first three models satisfy (N).

| Invariant dropped | Model | Off-line zeros |
|---|---|---|
| Simple pole (pole order 2, completion entire) | `F = ζ·((s−1/2)²−w²)/(s(s−1))` (`lambdaPositive_poleOrderTwo_not_criticalLine`) | real pair `1/2 ± w` |
| Simple pole (pole order 3, completion entire) | `F = ζ·quartet/(s(s−1))²` (`lambdaPositive_entire_functionalEquation_not_criticalLine`) | complex quartet `1/2 ± a₀ ± iγ` |
| Holomorphy of the completion in the strip | `F = ζ·quartet/((s−1/2)²−c²)⁴` (`lambdaPositive_functionalEquation_not_criticalLine`) | complex quartet, poles at `1/2 ± c` |
| Riemann's FE | over-regular positive Beurling systems (`overRegularZeta_not_functionalEquation`) | zeros in `1/2 < Re s < 2/3` |
| Coefficient positivity | self-dual character combinations | uniqueness fails |

- **Pole-order budget.** For finite reflection-antisymmetric corrections of ζ's log measure, local finiteness of the prime measure at `x = 1` forces a trace condition, so `ord₁F − 1` equals the inserted zero multiplicity counted by frequency pairs `{w, −w}`. A real or critical insertion costs one unit; a genuinely complex off-line quadruple occupies two pairs and forces `ord₁F ≥ 3` (`poleOrderBudget`, `poleOrderBudget_ge_two`).
- **Pole-order rigidity.** For degree `d`, conductor one and entire completion `(s(s−1))^κ Γ_ℝ^d T`: if every zero is critical, then `κ = d`, RH holds and `T = ζ^d` (`pole_order_rigidity`).
- **Consequence.** The degree-one invariant set (N: coefficient positivity on `[1,∞)`; FE: Riemann's `Γ_ℝ` equation; S: a simple pole and no other poles of the completion; G: the growth premises) determines ζ, and each relaxation breaks that conclusion. Countermodels cannot refute a mechanism that uses all four invariants. Conversely, a proof must use all four, and in degree one no family larger than `{ζ}` carries them.

### 1.6 Multiplicative forcing: boundary complete, interior capped

**Boundary (MPG).** The boundary divisor `D(u)` (pole order minus zero order at `1 + iu`) of any Euler product with nonnegative log-coefficients is an even positive-definite function on the discrete group `ℝ`.

- **Classification.** An integer-valued such `D` with `D(0) = 1` takes values in `{−1, 0, 1}`; a boundary zero at `u` forces a pole at `2u`; locally finite `D` is `δ₀`, a lattice indicator or an alternating lattice character.
- **Forcing law.** Nonnegative weights, integer divisor, simple pole and pole isolation force `D = δ₀` (`boundary_forcing_law`). Each invariant is necessary, with a realized datum. For ζ the inputs are `Λ ≥ 0` and the residue at 1 (`riemannZeta_boundary_ne_zero_of_posDef`).
- **Profiles.** On a progression, boundary profiles of positive families are exactly the coefficient sequences of nonnegative cosine polynomials, all realized by ζ twists.
- **The interior is invisible.** Bounded-mass data contribute zero divisor. `ζ(s)Φ(s+κ)` with an alternating one-prime factor satisfies all four boundary invariants yet vanishes inside the strip, paying with interior poles (`interior_zero_invisible`).

**Interior.** Every interior use of multiplicative positivity reduces to a scalar comparison of pole, zero and growth terms, and its capacity is now computed exactly.

- **Fejér barrier.** Degree `K` gives `a₁ ≤ 2cos(π/(K+2))·a₀`, attained (`cosinePolynomial_first_le_fejer`, `fejer_barrier_sharp`).
- **Growth-to-forcing law.** For `A, G, η > 0` and `B ≥ 0`: some `δ > 0` has `A/δ + G < B/(δ+η)` iff `√A + √(Gη) < √B`. The certified width is exactly `(√B − √A)²/G` (`exclusion_iff`).
- **Caps.** With growth payment `L·S`, degree one excludes nothing and degree `K` excludes only `η < (1 − ρ_K^{−1/2})²/L`. Any finite set of frequencies, incommensurable or not, satisfies `a(γ) ≤ 2a(0)`, so every finite positive certificate is capped by `(3 − 2√2)/(2L)` (`multiFrequency_purchase_le_two`, `multiFrequency_width_cap`). The normalized simple-zero saddle gain has supremum `3 − 2√2`, unattained at finite degree (`isLUB_fejerSaddleGainSet`).
- **Fibre decomposition.** The part of a nonnegative certificate on the multiples of `ω` is again nonnegative, so the purchase at `ω` obeys the Fejér barrier of that fibre's degree (`multiFrequency_purchase_le_fibre_fejer`). `ℚ`-independent channels do not raise each other's barrier, and two channels attain the product of their barriers. Two zeros at equal depth and incommensurable heights are excluded jointly iff `√A + √(Gη) < √(B₁ + B₂)`, with joint purchase below 4 and width below `1/(4L)` (`twoZero_exclusion_iff`). A multi-channel certificate is the direct sum of one-channel problems, one per rational fibre.
- **Calibration.** The dlVP region `β ≤ 1 − (2−√3)²/G_γ` is an instance of the law and is optimal for its input (`xiZero_re_le_dlvp`, `dlvp_input_consistent`).

Within this scalar comparison, interior gains come only from growth input. The next rung of growth input is a fixed strip.

### 1.7 Heat and divisor geometry

- **Local geometry.** Complete at model level: repair cones, the sharp Hermite root barrier, optimal first heat `a/(2h_{m+2}²)`, universal reflectors (positive monomials only).
- **Large heights.** Every positive heat repairs every sufficiently high radius head (`exists_radiusHead_heat_coeffNonneg`).
- **Positive time.** Zeros are real and simple beyond `2π exp((27/40+ε)/t)`; `Λ < 1/8` (`newmanConstant_lt_eighth`).
- **Residual.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`: the de Bruijn–Newman core.

### 1.8 Cofactor escape (PM, CTF, BVI, MC)

On every common limit of the actual cofactor Grams at `0 < ε < 1/2`:

- **Structure.** A cyclic critical-Wiener module; admission gives a unique full-sequence limit, faithful and infinite-dimensional with full Bohr hull; escape gives paid ideal ⊆ annihilator and module hull ⊆ obstruction hull.
- **Record minima.** Some actual limit has `K_pp ≥ p^{2ε−2} > 0` for every `p` and all rows nonzero (`exists_actualCofactorLimit_kernel_diag_ge_rpow`). The construction uses only the upper bound `E_ε(N) ≤ D(1 + N^{1−2ε})` and record minima of `E_ε(N)/N^{1−2ε+1/(m+1)}`.
- **Families.** The set of actual kernels is a singleton or has cardinality continuum. No zero-diagonal kernel, augmentation included, can be the unique one; if a zero-diagonal limit occurs, the family is continuum and the receiver escapes.
- **Contraction calculus.** For `K_pp > 0`, `M(j,k) = K(pj,pk)/K_pp` is again an actual limit; its module is the closed range of `D_p`, embedded isometrically. The annihilator is the principal quotient `I_L : (δ_p)`, contractions compose multiplicatively, and finite index drops by the dilation nullity.
- **Rank one.** A nonaugmentation rank-one actual character is `η(p)p^{−s}` with `s ≥ 1/2` and `η` a multiplicative `±1` character.
- **Horizon order and moving origins.** `p ↦ pK_pp` is antitone; odd-only white noise is excluded. Reset-origin limits `(K + cKmax)/(1+c)` are faithful for every `c > 0`, with infinite Hilbert dimension and continuum annihilator-quotient rank. Raw moving origins add constant Gram mass and violate the zero-origin contraction of fixed-origin kernels, so they are not fixed-origin limits; moving successor limits are origin traces.
- **Surviving model.** Full white noise `K_jk = δ_jk/j` satisfies PSD, sharp dilation, antipodality, horizon order and the record floor (`1/p ≥ p^{2ε−2}`). Its module is faithful. On escape the paid ideal lies in the annihilator, so white noise is incompatible with escape exactly when the paid ideal is nonzero. No corpus theorem decides whether the paid ideal of `μ_ε` is nonzero when the receiver escapes.

### 1.9 Vaughan calibration and the half-damping transition

- **Above half damping.** A common critical-Wiener majorant pays every centered piece; the actual infinite Gram of the limiting rows `(A, A, −A, 0, pole)` is PSD of rank exactly two, and moving limits converge to it [S].
- **At half damping.** The actual receiver has bounded pronic norm. Finite moving Gram limits are exactly `G_{1/2} + ℓ·ssᵀ`, every `ℓ ≥ 0` realized (rank two at `ℓ = 0`, three otherwise); the product horizon selects `ℓ = 0` [S].
- **Below half damping.** Every subcritical moving-cutoff normalized limit is the rank-≤ 1 smooth matrix at an amplitude from a compact countable set with zero as its only accumulation point. The residual below `T^{1−2ε}` is open; every power improvement of it is a fixed strip (§1.2).
- **Endpoint invariants.** The centred pole has positive finite energy independent of cutoffs. The tail-rate suprema are `1 − Θ` (tail) and `4(1 − Θ)` (square-cutoff energy) at every damping. Attaining the endpoint rate forces simple boundary zeros, and Mertens' `Ω±(√x)` forces endpoint oscillation [S].
- **Half-damping hypercube endpoint.** `Q_{1/2}(P)` is bounded over every squarefree `P`; sub-half paid multiplicative patterns have integer local exponents; Dini and completely monotone defects are unpaid at every `0 < ε < 1/2`.

### 1.10 Payment domains (golden one-prime model)

On the normalized one-prime coefficient space the payment domain `{g : partial sums ∈ ℓ²}` is not closed. Its closure is the kernel of total evaluation, and the reduced cokernel is isometrically `ℂ`. The continuous dual of the unreduced quotient is one-dimensional. The closure gap has Hamel dimension continuum, with power-tail kernels in the closure that are paid exactly above the half-exponent threshold. In this model no continuous functional except total evaluation sees payment; payment must be controlled through the graph norm, not by closure.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls involved ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime cross-work receivers read `Δ` exactly, endpoint attained. RH ⇔ `E` bounded ⇔ cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)`. Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit has `Γ^{−1/2}` averaged decay for `α < 2/3`. Two primes on mixed lags suffice. The RH mean law keeps its RH premise.
**(a)** W4–W6. W8(i): an averaged bounded-energy statement from the high-zero tail and the filtered law.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed `σ < 1/2`). B1.4 (frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.7, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; shell decomposition into nonnegative frozen relaxation plus an arithmetic jump bracketed by collar correlations; on the prime-threshold ladder, RH ⇔ cumulative relaxation `≤ μ(3/10)`. `H¹` rate sets `[Δ, ∞)`; ground = polar rate. Averaged log-aperture positivity and finite-level existence apply.
**(a)** W4/W7: certified low-sector matrices and further windows. W8(ii): merge the RW, SRT and ACS rate dictionaries.
**(b)** B1.3 (sign at every aperture). B3.6 (signed collar estimate on the moving ladder). B3.1 (`polarRate = Δ`). B3.7 (short-window averaged positivity, the graded path to selection).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent. Actual terminal primes realize graph sources with vanishing diagonal cost. The isolated critical prime channel is negative on narrow windows and has a positive limit `≥ log 2/(8π⁴)` on dyadic and wider windows [S]. Bounded graph norm with vanishing diagonal does not give compactness.
**(a)** W4–W6: schedules, clock kernels, cross-block identities.
**(b)** B1.1: the complete history (seed, drift, covariance, endpoints jointly).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the matched-quantile history is RH-equivalent; the normalized history falls below `−δ(K+2)` cofinally. Hyperbola, centroid, square-debt identities and low-LCM payment are present.
**(a)** W4–W6.
**(b)** B1.1: the full-history floor with high-LCM pairs, moving core and singular transport.
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond its shift threshold; RH ⇔ nonnegativity at every order below its threshold. The order-24 closure rests on a `native_decide` quadrature that no receiver imports.
**(a)** W2; W4/W7: further orders.
**(b)** B1.5: low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`, so `M = o(√x)` is impossible and either one-sided `O(√x)` bound forces RH with simple zeros. The gap receiver `θ(ε,t) < 1` has proved high-height and small-damping collars. Proved: prime-root and composite-order minor arcs, all-modulus `Q^{−δ/32}` saving, the diagonal reduction, balanced and centred-prime bands ⇔ `Θ < 1`, and the full Vaughan picture of §1.9.
**(a)** W5/W6: apply row estimates in their ranges.
**(b)** B2.1 (band saving is exactly quasi-RH). B1.1 (global cancellation or interior anti-alignment). B2.6 (power-saving sign correlations). Planted Euler factors keep the collars.
**Walls:** 1.0, 1.1, 1.12, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2` for `0 < t < 1/2`; RH ⇔ the bound at every such `t`; the one-sided bound `D_t(N) ≤ C` is RH-equivalent. Odd Weil positivity is an alternative receiver.
**(a)** W4, W6.
**(b)** B1.3: signed nonlocal covariance at every `t`.
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** Laguerre, Jensen and finite-head receivers; at fixed `R² ≥ 1/2`, RH ⇔ all-height head coefficient positivity. Every positive heat repairs every sufficiently high head; KKL positive-time reality; complete local divisor geometry.
**(a)** W8(iii): the explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. W4/W7: bounded-height certificates.
**(b)** B1.5 (zero-heat sign on the residual region). B2.9 (smaller de Bruijn–Newman bounds). B3.9 (source-selective cofactor repair).
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace equals winding; an integral nonnegative residual below one vanishes, but neither its sign nor the sub-unit bound is derived. Literal Gaussian integer weights have nonpositive coprime covariance.
**(a)** W4, W6.
**(b)** B1.6: a matrix-complete residual sign and an all-disc sub-unit estimate.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form / prime-window ceiling
**Status.** Exact forcing-sign dictionaries; the ceiling `c(L) ≤ e^{L/2} + B(1+L)` gives AIP allocation; prime-blind receivers are RH-equivalent; finite `D` is even and RH ⇔ `D < 2`. Full-cone source selection identifies `Λ`, and positive-measure rigidity (§1.5) identifies the source among all positive measures with the theta law. Curve calibration: lower Lefschetz forces unitarity; upper forces it unless a positive real outer eigenvalue exists (golden `φ`); genus-one Hodge index = degree positivity of `ℤ[F]`; the Hecke graphs of `ℤ` satisfy no theorem of the square.
**(a)** W4, W6.
**(b)** B1.3 (the pairing sign or the `O(L)` ceiling). B2.2 (finite index). B3.10 (compatible oriented families).
**Walls:** 1.3, 1.4, 3.13, 14.4, 14.12.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state lies above `1/2`; one-signed bound states vanish, sign-changing ones are not excluded. Fixed-aperture completion, sharp cuts, generator-domain preservation and window nodal convergence are proved.
**(a)** W5/W6.
**(b)** B1.3: the nodal or reflected-prime inequality.
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the coefficient orthant at small time; fixed-rank coercivity; a Weil margin gives heat-Hankel positivity in a coupled rank–time window; rank-`N` tests are blind above height `O(N√log N)`.
**(a)** W4/W7.
**(b)** B1.5 (all-rank signed positivity at one time). B3.12 (decoupling rank from time).
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact Hilbert–Schmidt cone-positive renewal operator realizes the denominator through `det₂` with the exact divisor; cone positivity does not confine resonances.
**(a)** W4, W6.
**(b)** B1.6: boundary-current orientation (mixed prime + Gamma ≥ pole with every cusp and seam term).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH; Euler–Stieltjes saturation at one admissible `τ` is RH-equivalent; collision masses are even and match the index bridge `2(D+E)`; Mehler bracket, cumulants, multi-pair witnesses, root barrier and optimal heat are proved; large-height repair as in §1.7.
**(a)** W8(iii); W4.
**(b)** B1.6 (cap vanishing or saturation). B1.5 (heated-head positivity on the residual region).
**Walls:** 1.2, 1.14, 3.8.

### LI — Li even-cross clock
**Status.** RH ⇔ subexponential lower floors at every positive rate. Off-line rates `≤ 1/431`, maximal rate `β < 1/300`, `β = 0` iff RH, positive `β` attained on a finite packet. The currency is reciprocal depth, not `Δ`.
**(a)** W4/W7.
**(b)** B1.7: the subexponential floor.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint compact-window, moving-aperture and collared noncompact limits; on RH-complete factorial-tent families, RH ⇔ nonnegative first variation; quantitative tent transfer. Common shift thresholds exist for each fixed high-scale family, not across unbounded families.
**(a)** W5/W6.
**(b)** B1.3, the same sign as RW.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The size-truncated receiver equals the full natural form; its exterior is paid; `ε = 1/2` is paid for every squarefree support. The cofactor structure of §1.8 (record-minimum floor, singleton/continuum families, contraction calculus, rank-one sign law) and the Vaughan transition of §1.9 are proved. The forcing splits into a power plus a bounded remainder; diffuse escape keeps the antipodal density; the dilation commutator is bounded; (residual, trace) reconstruction is injective but only algebraic.
**(a)** W5/W6: Vaughan bookkeeping; W9 for the [S] Vaughan leaves.
**(b)** B1.2 (signed small-damping energy). B3.2 (escape classification; decisive sub-question B3.16: is the paid ideal nonzero on escape?). B3.3 (quantitative coercivity). B3.11 (sub-half forward interior).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry budget
**Status.** A positive level-one budget ⇔ a half-plane bound `< 1/2`; the half-power endpoint is RH; the Gamma–theta source is admitted at all finite supports.
**(a)** W4–W6.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Cofactor test family / Báez–Duarte
**Status.** Residual = `(1 − readout)² + centeredEnergy`; RH ⇔ both small together; the floor `κ/log N` and the readout–energy uncertainty principle are exact; literal `−μ_N` aligns the readout.
**(a)** W4/W7.
**(b)** B1.2 (readout → 1 and centered energy → 0 together). B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat / critical feature variance
**Status.** All-degree positivity of the two literal source grids (spacings `log 2`, `log 3`) on their polar hyperplanes is RH-equivalent; one grid aliases.
**(a)** W4/W7.
**(b)** B1.5: both grids at every degree.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton disc
**Status.** Line-centered Newton discs covering every zero ⇔ RH; the interior margin is subharmonic (`Δ = 4(r² − |z−c|²)|Ξ''|² ≥ 0`), so boundary control gives no interior margin; global scalar damping has only the trivial repair.
**(a)** W4.
**(b)** B1.5: the all-disc interior margin.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Bohr almost-periodic strong recurrence
**Status.** Strong recurrence on every compact right-strip set, local recurrence at every point, and cutoff-uniform positive Haar mass of target twists are each RH-equivalent; recurrence holds exactly at non-zeros; the self-return threshold reads the vanishing order.
**(a)** W5/W6.
**(b)** B1.7: returns near possible zeros.
**Walls:** 1.2, 3.2.

### EWU — Even Weil universality / pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; literal positivity on high dyadic, polynomial and lacunary windows; full-cone source selection (single-node perturbations fail); finite-level existence ⇔ RH.
**(a)** W4–W7.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Gaussian tail / Hedenmalm–Schur decay
**Status.** Uniform quartic Schur decay is RH-equivalent; an off-line zero forces a late positive charge floor; truncations converge strongly.
**(a)** W4.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil universality
**Status.** Odd positivity is RH-equivalent; continuum light-cone variation positive; compensated reflected-prime source positive on nonzero odd tests; fixed-support subunit collar paid; lattice Schur payment reduces to a finite head.
**(a)** W4–W7.
**(b)** B1.3: full reflected-prime and polar payment.
**Walls:** 1.3, 3.4.

### PBM — Prime-bias Mellin / regularized logarithm
**Status.** A half-plane bound at `α` ⇔ convergence of `Σ(Λ(n)−1)n^{−s}/log n` on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** W6.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1.

### RB — Robin bound
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need a growing lcm core and a small moving valuation defect.
**(a)** W4.
**(b)** B1.7: the eventual extremal tail.
**Walls:** 1.1, 1.6.

### SRT — Square-root threshold and smooth detection
**Status.** One fixed-width late-lag family decides RH at every admissible width; smooth detector at aperture `Cδ^{−2}(4+|γ|)²`; the single-height phase-selective law holds with explicit premises; eventual all-height saving is refuted; phases recur syndetically.
**(a)** W5/W6.
**(b)** B1.4 and B1.1: horizon containment and the late-lag sign.
**Walls:** 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single shift
**Status.** One fixed shift `a > 0` against all even compact profiles decides RH; antisymmetric light-cone kernel positive; subunit collar paid for `log d ≤ a − R`.
**(a)** W5/W6.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation up to `Ke^r e^{−c√r}` (rate `1/2`); horizon-uniform Schur payment to a finite head; active cosets and top-octave dominance; exact shared-budget descent (excess `kB`).
**(a)** W4/W7.
**(b)** B1.3 (one shared signed budget). B3.8 (nonlocal frustration calculus).
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi
**Status.**
- Exact source identity; RR exact at every aperture; reserve boundary rigidity (RR + Bézout on one cone ⇔ reserve = defect); positive majorants give Bézout and ampleness, never RR; finite readings with mass never give Bézout.
- Maximal blind ideal with the full restricted geometry; exhaustion is RH (§1.4).
- Multiplicative forcing: the boundary theory is complete and the interior is capped by growth input (§1.6).
- Degree-one rigidity: ζ is the only positive measure on `[1, ∞)` with the theta law, and each relaxation has off-line countermodels (§1.5).
- Sparse-spectrum annihilators for `Σ|a_k|^{−s} < ∞`, `s < 1` (not applicable to ζ zeros); averaged log-aperture positivity.
- Zero census: simple-or-critical fraction `≥ 0.8876`; distinct critical ordinates `≥ 0.8042`. TTPC: `N₀* ≥ (29/36 − β − ε)N`, and `β ≤ 1/18` would give `3/4`.
**(a)** W8(iv): restate effectivity as exhaustion of the maximal blind ideal. W8(v): the bare-FE form of the rigidity theorem.
**(b)**
- B1.6: an independent effectivity or forcing input outside the single-channel class.
- B1.8: the faithful variants need simplicity.
- B1.9: the absolute pole-order budget (RH at pole order one).
- B3.4: a limit topology for exhaustion.
- B3.5: the surface section law.
- B3.17: coupled positivity outside the maximality class.
- B2.5: the coalescent surplus.
**Walls:** 1.3, 3.8, 14.4, 14.8, 14.10–14.13.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6: construct the object before its sign and prove the sign independently. Three theorems constrain every candidate. Single-channel sharp-stable positivity can certify only blindness (§1.4). Finite multiplicative certificates are capped by growth input (§1.6). A candidate mechanism must also distinguish ζ from the pole-order-2, pole-order-3 and strip-pole models of §1.5, because those models keep `Λ ≥ 0` and the exact functional equation.

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; Fredholm trace receiver exact. | W4, W5 | Annihilation of the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support. | W4 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W4 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; dyadic descent universality. | W4, W5 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W4–W6 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W4 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = sum over off-line zeros of `log|ρ/(1−ρ)|`, zero on critical zeros. | W4 | Cofinal contrast equality (B1.7). |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W4 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W4 | Source lift with integral count (B1.6). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W4, W5 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained. | W4 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; Ξ-limit ⇔ RH; prime-log stacks cannot converge to Ξ. | W4 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Energy probabilities erase grade. | W4 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W4, W5 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W4 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centered real compact-uniform convergence suffices. | W4, W6 | Arithmetic couplings with a centered limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W4 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W4 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read `Re ρ = 1/2` with exact depth laws. They detect blindness; they do not force it. FEL is the zero-side analogue of the Hamburger squeeze: a nonnegative functional that vanishes exactly on critical zeros. What it lacks is the arithmetic upper bound that would force the functional to zero.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows | Minor arcs; all-modulus `Q^{−δ/32}`; diagonal reduction; balanced and centred-prime bands ⇔ `Θ < 1`; Kloosterman Parseval; prime Gram of rank three. | W6 | B2.1; B1.2 |
| **BVI** Vaughan | Half-damping transition (§1.9); every power improvement ⇔ fixed strip. | W9 | B1.2 |
| **ADR** cofactor modules | §1.8. | W4 | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates | §1.3. | W8(ii) | B3.6, B3.1 |
| **ACS / Meyer** | §1.4. | W8(iv) | B3.4, B3.5, B3.17; B1.6, B1.8 |
| **APD** positive duality | Positive-measure and Beurling rigidity (§1.5); discrete realization [S]. | W8(v), W9 | B1.9 |
| **MPG** multiplicative positivity | Boundary theory complete; interior capped (§1.6). | — | — (programme closed below RH strength; B1.9 is its interior continuation) |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; spline orbit; base theta `h⁰` with RR and Mellin. | W6 | B3.10, B3.5; B2.2 |
| **AOT** readings, hulls, width functor | Width functor; Wiener hulls; Bohr characters; active cosets. | W6 | B3.4 |
| **ALDG** local divisor heat | §1.7. | W8(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height; finite-level existence. | W9 | B1.4 |
| **BiScale** lag, packet, filtering | Endpoints; high-zero tail; filtered deficit. | W8(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt; boxes. | W4 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3` and lag-2 `1/4` floors exact; complex floor in `[−1/2, −1/3]`; half-damping hypercube endpoint. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half damping. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure and one-dimensional dual (§1.10); chirp phase group. | — | B3.3, B3.4 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`. | — | B2.5, B2.7 |
| **Analytic inputs** | Guth–Maynard; 30/13 and Ingham–Huxley density; short-interval zero weights; Heath–Brown all-length; sharp `S₂`; KKL; dlVP, Littlewood, VK; FE/count fluctuation; Hamburger rigidity and stability. | — | B2.4, B2.8 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - Invariant completeness in degree one: rigidity plus sharp relaxation models (§1.5).
  - Interior multiplicative forcing by finite positive certificates beyond growth input: excluded (§1.6).
  - Summation-scope "defects": none ever existed (Mathlib parses the `∑` body at precedence 67).
  - Polar versus full ground-energy rate: equal.
- **Completed constructions.** Filtered averaged coercivity; CHMD generator domain and sharp windows; Suzuki compact-`L²` and moving-window limits; Heath–Brown all-length and sharp `S₂`; the smooth detector; endpoint attainment; base theta `h⁰`; Hermite optimal heat; large-height head repair; the maximal blind ideal; the boundary forcing law and its completeness; the exact Fejér barrier and growth-to-forcing law; positive-measure Hamburger rigidity; the half-damping hypercube endpoint; the Vaughan half-damping transition; record-minimum cofactor limits and the contraction calculus; sparse-spectrum annihilators; finite-level existence ⇔ RH.
- **Excluded mechanisms.**
  - positive exponential aperture floors;
  - eventual all-height phase saving;
  - non-monomial universal reflectors;
  - finite readings, with or without mass, as Bézout sources;
  - origin-`L²` faithful cohomology;
  - PSD, dilation and antipodality as escape exclusion;
  - augmentation as the unique escape state;
  - permanently frozen finite prime families;
  - finite-dimensional affine-unitary successor carriers;
  - single-channel sharp-stable positive ideals as forcing carriers;
  - harmonic positivity without pole simplicity or with harmonic poles;
  - more finite frequencies against a fixed growth payment;
  - decaying count error under the functional equation;
  - `Λ ≥ 0` plus the exact functional equation without the simple pole or without strip holomorphy;
  - Wiener closure as a substitute for payment.
- **Substitutions that do not hold.** Orthant for signed positivity; cone positivity for self-adjoint confinement; finite for all ranks; local payments for one budget; finite-aperture for global index; averages for selected heights; algebraic for bounded inverses; zero-indexed objects for pre-divisor constructions; imported for forced regions; a zero-free-region transfer for a forcing law.
