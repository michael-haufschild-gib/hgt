# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-25, corpus `e4965f55a` with the working tree of that day. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** The route inventory is that of the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading Lean statements; the record is `logs/review-2510-update/working-log.md`. Nothing was compiled. Labels follow the frontier map: `[S]` working source not yet integrated, `[P]` paper proof, `[R]` assessment or model calculation of the review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, premise checks, transport of proved estimates, corollary assembly, technical strengthening of a proved theorem. IDs `W1`–`W9`, defined in the [summary](hard-obstacles-summary.md#1-just-work).
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger.
  - `B2.*`: classical open problems weaker than RH.
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

Notation: `Δ = sup_ρ |Re ρ − 1/2|`, `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree.

## 1. Facts that fix the present frontier

### 1.1 The first rung of every cancellation receiver is quasi-RH

Each graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is equivalent to a fixed zero-free strip `Θ < 1`:

- WL lag or deficit at a fixed rate `σ < 1/2`;
- PBM regularized-series convergence on `Re s > 1/2 + α`;
- the JAS level-one budget;
- the balanced Möbius statistic and the centred-prime band (`balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`);
- short-window Möbius and prime saving;
- every power improvement in the Vaughan picture: the empty leg, uniform convolution power cancellation (gain transfer `η/(2+η)`), uniform residual Gram power rates, a common-threshold factorial-order-one envelope, reciprocal-tail gains at every positive damping [S];
- RW and ACS floors at any rate `< 1/2`;
- admission of the cofactor receiver at a fixed damping `ε`, which fails exactly when uncancelled zeros lie right of `1/2 + ε` (visible-pole index, §1.7).

Unconditional arithmetic stops at the Vinogradov–Korobov region (`riemannZeta_ne_zero_vinogradovKorobov`), with the de la Vallée Poussin and Littlewood regions. No cancellation receiver has a target between Vinogradov–Korobov and a fixed strip. Multiplicative forcing, including its completed-system form (§1.5), meets the same rung.

### 1.2 Positivity: pointwise and averaged frontiers

- **Exact form.** For every real compact `C²` test: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, endpoint attained.
- **Pointwise windows.** Full form `≥ ‖f‖²/5000` through radius `3/10`; odd form `≥ ‖f‖²/1000` through `181/500`; primitive smooth Hodge index through `(log 2 + 1/50)/2`. The graded floor `−Ce^{r−κr^α}`, `α < 3/5`, still has leading rate `1/2`.
- **Averaged positivity.** For `A ≤ κ₀ log Γ` and `F₀ ∈ C²_c([−A, A])`: `Γ⁻¹∫_Γ^{2Γ} [Q(F₀ cos γ·) + Q(F₀ sin γ·)] dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−4/3} N(F₀)²` (`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`). The main term is the local critical-zero weight; off-line contributions are controlled by zero-density shell bounds. Subpower averaged coercivity holds for `A ≤ α log Γ`, `α < 2/3`. No theorem shortens the window `[Γ, 2Γ]`.
- **Single heights.** At a height `ξ` where the prime polynomial obeys `Re Π_f(⌊e^{2a}⌋, ξ) ≤ c e^a ‖f‖²`, the `(4+ε)e^a` horizon is replaced by `c e^a`; finite-prime phases recur syndetically, and no uniformly eventual power saving exists.
- **Aperture flow.** `μ(A)` is strictly decreasing; RH iff `μ(A) > 0` at every finite `A`. On the prime-threshold ladder every birth jump vanishes, and RH holds iff cumulative frozen relaxation never exceeds `μ(3/10)`. Permanently frozen finite prime families are eventually `≤ −αe^c`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor.
- **Rates.** `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2` and `RH ⇔ groundRate = 0`. The CCM form-norm and Birman–Schwinger rates equal `Δ` unconditionally; the physical-`L²` equality `polarRate = Δ` holds under locally bounded off-line depth and is otherwise open.
- **Finite level.** RH holds iff every aperture admits some real weight system making the full Weil functional nonnegative on tests supported there.

### 1.3 Realization: the maximal blind carrier

- **Maximality.** `meyerTraceBoundedIdeal` consists exactly of the sources whose Mellin transform vanishes at every off-line zero. It is a two-sided, sharp-stable, flow-invariant convolution ideal containing every critical jet; its restricted surface has Hodge index, RR, Bézout, ampleness and additive closure; it is the whole source iff RH, with no simplicity condition. Every sharp-stable right convolution ideal with nonnegative trace lies inside it (`isGreatest_meyerSharpPositiveIdeal`), and every scale-shift-invariant Weil-nonnegative test space is off-line blind.
- **Topology.** The ideal is closed in the natural Fréchet topology, unconditionally. It is dense in the critical-jet topology and closed there, or in any coarser topology, iff RH (`isClosed_criticalJet_iff`). Closedness of the blind ideal is information about the off-line divisor; no topology built from critical data decides exhaustion.
- **Faithful variants.** Faithful positive degrees, the Hilbert–Schmidt reserve and the bounded-orbit carrier each reach RH only together with simple zeros. The origin-`L²` completion supports no continuous faithful reading.
- **Common pattern.** Every unconditional positivity theorem in the corpus is positivity on a carrier blind to off-line zeros (low-grid-blind tests, bounded orbits, positive degrees, jointly blind families, large-height heated heads, frequency averages). For single-channel sharp-stable carriers this is a theorem.
- **Forcing transfer.** `ArithmeticForcesBlindness` places in the blind carrier a Meyer source or scaling cycle whose off-line transform vanishes outside a zero-free region. A zero-free region contains no off-line zeros, so this is a tautological transfer, not a forcing law for the actual source.

### 1.4 Positive Poisson pairs

The explicit formula is a Poisson pair between the prime measure and the zero measure (APD).

- **Both sides.** For `x > 0` the damped symmetric prime measure `½Σ Λ(n) n^{−1−x}(δ_{log n} + δ_{−log n})` is a finite positive measure with characteristic function `Re(−ζ'/ζ)(1+x+iu)` (`charFun_primeMeasure`). Positive spectral measures for the scale functions of every `C²` test exist iff RH (`riemannHypothesis_iff_forall_spectralMeasure`). On tests vanishing for `|x| ≥ log 2` the prime side is empty (`weilFullFunctional_of_prime_free`): positivity and the prime-free gap sit on the same side of the Weil pair.
- **Gap rigidity.** A locally finite positive measure with gap `(−1,1)∖{0}` is tent self-dual iff it is `μ{0}Σ_n δ_n`; a wider gap forces zero; every narrower gap admits the non-comb `comb_{aℤ} + a⁻¹ comb_{a⁻¹ℤ}`. With the gap only on the dual side, the conclusion is a uniform local mass bound. On the Weil pair this leaves only density statements.
- **Integer positive-definite functions.** On every abelian group, integer-valued even positive-definite `φ` with `φ(0) = 1` is a sign character of a subgroup extended by zero; isolation forces `δ₀` iff the group has no 2-torsion. The classification is independent of rank.
- **Lattice Bochner and the two-prime receiver.** Positive definiteness on `ℤ^r` is the coefficient sequence of a positive torus measure. RH iff the cubic-spline correlation on `ℤ log p + ℤ log q` is positive definite on `ℤ²`. At `s = k log p + l log q` this correlation reads only primes in `[p^k q^l e^{−8}, p^k q^l e^8]`.
- **Affine induction.** A positive-definite function on a subgroup extends to the group iff it is positive definite; positivity on the affine group of `ℚ` is induced from the dilations, and the successor coordinates are free. A forcing law there must prescribe the successor part from the source.
- **Curve calibration.** For a curve datum, purity ⇔ positive definiteness of the trace sequence on `ℤ` ⇔ Hasse–Weil ⇔ span Hodge index; the golden datum `1 − 5X + 5X²` fails on every group.

### 1.5 Invariants, pole order and multiplicative forcing

**Degree-one rigidity (APD).** A Borel measure `ν ≥ 0` on `[1, ∞)` with `∫u⁻² dν < ∞` whose theta transform satisfies Riemann's degree-one law is `(−2 Re α)·Σ_{n≥1} δ_n` (`measure_eq_of_measureTheta_relation`). A Beurling prime measure whose integer measure obeys the law is `Σ (Λ(n)/log n) δ_n`. The completed-FE version assumes the inverse-3/2 moment, the `Γ_ℝ` identities on `Re s = −1/2, 3/2` and a strip remainder `|E(s)| ≤ C/(1+Im(s)²)`. Countable discrete Beurling systems with the law are ζ's, with a norm-preserving bijection of prime labels onto the rational primes [S]. Without positivity only `Σ a_n (sin πλ_n/πλ_n)² = 0` survives.

**Relaxation models.** Each relaxation of the invariant set breaks the conclusion.

| Invariant relaxed | Model | Off-line zeros |
|---|---|---|
| Simple pole, no refund (pole order 2) | `F = ζ·((s−1/2)²−w²)/(s(s−1))` (`lambdaPositive_poleOrderTwo_not_criticalLine`) | real pair `1/2 ± w` |
| Simple pole, one critical refund (pole order 2) | remove a critical pair `1/2 ± iγ`, insert the quartet of `1/2 + a + iγ`, `0 < a ≤ 1/4` (`lambdaPositive_refunded_complex_stray`) | complex quartet |
| Simple pole, no refund (pole order 3) | `F = ζ·quartet/(s(s−1))²` (`lambdaPositive_entire_functionalEquation_not_criticalLine`) | complex quartet |
| Holomorphy of the completion in the strip | `F = ζ·quartet/((s−1/2)²−c²)⁴` (`lambdaPositive_functionalEquation_not_criticalLine`) | complex quartet, poles at `1/2 ± c` |
| Riemann's FE | over-regular positive Beurling systems (`overRegularZeta_not_functionalEquation`) | zeros in `1/2 < Re s < 2/3` |
| Coefficient positivity | self-dual character combinations | uniqueness fails |

**Pole order and zeros.**

- **Index–pole conservation.** For a finite reflection-antisymmetric deformation of ζ, counted by frequency pairs (inserted `I_off, I_crit`, removed `R_off, R_crit`): `(Weil-index increment) = (pole-order increment) + R_crit − I_crit`. This is an identity. The absolute inequality `ind₋(W_F) ≤ ord₁F − 1` is false: the refunded quartet raises the pole order by one and the index by two (`absolute_inequality_fails`). Applied to ζ, every member of the family gives only lower bounds `ind₋(W_ζ) ≥ R_off − I_off`.
- **Simple-pole rigidity [S].** A nonzero entire `E` with `E(1−s) = εE(s)`, nonvanishing on a right ray, and `−E'/E + ξ'/ξ = Laplace(ν)` there with `ν ≥ 0`, forces `ν|_{(0,∞)} = 0`, `ε = 1` and `E = cξ`; no finite-order premise, arbitrary critical refunds allowed (`simple_pole_nonneg_laplace_refund_rigidity`).
- **Threshold.** Positive relative deformations of ξ are rigid at pole order one and admit every off-line type at pole order two. The simple pole is the exact rigidity threshold. Pole order pays for inserted zeros; it does not budget ζ's own zeros.
- **Gauge collapse [S].** An entire finite-order `E = (s(s−1))^κ G` with `E(1−s) = εE(s)`, `G` bounded on a right half-plane and `G(σ) → 1`, is a monic polynomial of degree `2κ` with `ε = 1`; its off-critical quartets obey `2Σm ≤ κ`. Without an archimedean factor a completed gauge is a polynomial.
- **Pole-order rigidity.** For degree `d`, conductor one and entire completion `(s(s−1))^κ Γ_ℝ^d T`: if every zero is critical, then `κ = d`, RH holds and `T = ζ^d`.

**Boundary (MPG).** The boundary divisor `D(u)` (pole order minus zero order at `1 + iu`) of an Euler product with nonnegative log-coefficients is an even positive-definite function on `ℝ`.

- **Forcing law.** Nonnegative weights, integer divisor, simple pole and pole isolation force `D = δ₀`, each invariant necessary with a realized datum (`boundary_forcing_law`). For ζ the inputs are `Λ ≥ 0` and the residue at 1.
- **Capacity [S].** Integer-valued positive-definite `D` with `D(0) = k` and `D ≤ 0` off zero is exactly `kδ₀ − Σ m_z(δ_z + δ_{−z})` with `2Σm_z ≤ k`; every placement is realized by nonnegative twisted-Λ weights, the log-derivative coefficients of `ζ^{k−2M}Π(ζ²/(ζ(s+iz)ζ(s−iz)))^{m_z}`. A pole of order `k` carries at most `⌊k/2⌋` boundary zeros. For any finite set of heights, `Σ −D(z) ≤ D(0)/2` without commensurability (`total_zero_mass_le`).
- **Realization.** A finite even profile at arbitrary real heights is positive definite iff its Bohr polynomial is nonnegative iff it is realized by nonnegative weights iff by integer-multiplicity weights.
- **Interior invisibility.** Bounded-mass data contribute zero divisor; `ζ(s)Φ(s+κ)` satisfies all four boundary invariants yet vanishes in the strip.

**Completed systems [S] (SBWF).** A completed positive system has `F` holomorphic and nonvanishing on `Re s > 1` with positive-definite vertical sections of `Re(−F'/F)`, and an order-one entire completion `Λ = (s(s−1))^κ Γ_ℝ^d F` with `Λ(1−s) = Λ(s)` and conjugation symmetry. Hadamard's zero-pair series gives `Σ m_ℓ(Re 1/(s−ρ_ℓ) + Re 1/(s−ρ̄_ℓ)) ≤ Re(Λ'/Λ)(s)` on `Re s > 1`.

- **Collective boundary capacity.** If `κ < 2Σ m_ℓ` for zeros with distinct positive ordinates, not all of them lie on `Re s = 1` (`collective_half_pole_interior_forcing`). The threshold is exact for odd `κ`: `ζ` twisted at `r` boundary heights is a completed positive system with `κ = 2r + 1` and `r` zeros on `Re s = 1`.
- **Collar sparsity.** For `Δ`-separated ordinates in `[Δ, T]` and `√r·κ < Σ m_ℓ`, one zero lies left of `1 − (√(Σm/√r) − √κ)²/G` with `G ≍ κ/Δ² + r(κ + d log T)`. At most `κ²` such zeros enter the collar of width `≍_{κ,Δ} 1/(d log T)` (`card_separated_collar_zeros_le_sq_poleOrder`): for ζ, at most one.
- **Scope.** This is the first theorem over the whole class graded by `(κ, d)`. Its content is boundary capacity and a dlVP-scale collar; it gives no interior rate.

**Interior capacity of finite certificates.** Every interior use of multiplicative positivity is a scalar comparison of pole, zero and growth terms.

- **Fejér barrier.** Degree `K` gives `a₁ ≤ 2cos(π/(K+2))·a₀`, attained.
- **Growth-to-forcing law.** Some `δ > 0` has `A/δ + G < B/(δ+η)` iff `√A + √(Gη) < √B`; the certified width is exactly `(√B − √A)²/G` (`exclusion_iff`).
- **Caps.** Every finite positive certificate, with any frequencies, satisfies `a(γ) ≤ 2a(0)` and is capped by `(3 − 2√2)/(2L)`. A multi-channel certificate is a direct sum of one-channel problems on its rational fibres; independent channels keep their own barriers; two zeros at equal depth are excluded jointly iff `√A + √(Gη) < √(B₁+B₂)`, width below `1/(4L)`.
- **Quantum budget.** Admissible zero orders are exactly `m ≤ b(η) = (√A + √(Gη))²/B`; forcing iff `b < 1` (`< 2` for even orders). At the boundary `b(0) = A/B ∈ (1/2, 1]`. At `η = 1/2` with growth `L·W`, `W ≥ B`, every Fejér certificate has `b ≥ 1` once `L ≥ 2(1 − 2^{−1/2})² ≈ 0.17` and `b ≥ 2` once `L ≥ 1` (`fejer_quantumBudget_half`). Multiplicative positivity contains no quantized inequality at the critical line.
- **Calibration.** The dlVP region `β ≤ 1 − (2−√3)²/G_γ` is an instance of the law and optimal for its input.

### 1.6 Heat and divisor geometry

- **Local geometry.** Complete at model level: repair cones, the sharp Hermite root barrier, optimal first heat `a/(2h_{m+2}²)`, universal reflectors (positive monomials only).
- **Large heights.** Every positive heat repairs every sufficiently high radius head (`exists_radiusHead_heat_coeffNonneg`).
- **Positive time.** Zeros are real and simple beyond `2π exp((27/40+ε)/t)`; `Λ < 1/8`.
- **Residual.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`: the de Bruijn–Newman core.

### 1.7 Cofactor escape (PM, CTF, BVI, MC)

On every common limit of the actual cofactor Grams at `0 < ε < 1/2`:

- **Structure.** A cyclic critical-Wiener module. Admission gives a unique full-sequence limit, faithful and infinite-dimensional with full Bohr hull; escape gives paid ideal ⊆ annihilator and module hull ⊆ obstruction hull.
- **Record minima.** Some actual limit has `K_pp ≥ p^{2ε−2} > 0` for every `p`. The set of actual kernels is a singleton or has cardinality continuum; no zero-diagonal kernel, augmentation included, can be the unique one.
- **Contraction calculus.** For `K_pp > 0`, `M(j,k) = K(pj,pk)/K_pp` is again an actual limit; its module is the closed range of `D_p`; annihilators are principal quotients `I_L : (δ_p)`; contractions compose; finite index drops by the dilation nullity.
- **Characters and hulls.** Every common eigencharacter has augmentation modulus or `|χ(p)| = p^{−s}`, `s ≥ 1/2`; a nonaugmentation rank-one character is `η(p)p^{−s}` with `η` a multiplicative `±1` character. Every hull character of a finite-dimensional actual module lies on an eigenvector and in the pointwise closure of half-plane evaluations.
- **Visible-pole index.** For paid `k` and `1/2 + ε < Re ρ < 1`, `ord k(ρ−ε) ≥ (ord ζ(ρ) − ord ζ(ρ−ε))₊`; strict order loss on `Re ρ = 1/2 + ε` forces `k(ρ−ε) = 0`. Visible interior multiplicities plus distinct boundary poles bound `dim(A/I_paid)` from below, also on every Wiener-unit orbit (Liouville). The Fermi Mellin divisor is `ord ζ(s) − ord ζ(s+ε)`.
- **Moving origins.** Reset-origin limits `(K + cKmax)/(1+c)` are faithful for every `c > 0`; raw moving origins add constant Gram mass and are not fixed-origin limits.
- **Surviving model.** Full white noise `K_jk = δ_jk/j` satisfies PSD, sharp dilation, antipodality, horizon order and the record floor. It is faithful, so a nonzero paid ideal on escape would exclude it.
- **Spectral reading [R].** The cofactor Gram is the truncated translation Gram of `b(u) = e^{−u/2}A_ε(⌊e^u⌋)` with `b̂(τ) = G(1/2+iτ)`, `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`. Admission corresponds to `G` in the Hardy space of `Re s > 1/2`; escape states are horizon Grams of the translated top zeros `ρ − ε`, kernels `Σ B_{ρρ'} j^{−(ρ−ε)} k^{−(ρ̄'−ε)}`, `B ⪰ 0`, and the paid ideal annihilates them automatically. On this reading a nonzero paid ideal excludes white noise but not the zero-driven states, and excluding escape at a fixed `ε` is a fixed strip.

### 1.8 Vaughan calibration and the half-damping transition

- **Above half damping.** A common critical-Wiener majorant pays every centered piece; the actual infinite Gram of the limiting rows `(A, A, −A, 0, pole)` is PSD of rank exactly two, and moving limits converge to it.
- **At half damping.** Finite moving Gram limits are exactly `G_{1/2} + ℓ·ssᵀ`, every `ℓ ≥ 0` realized; the product horizon selects `ℓ = 0`.
- **Below half damping.** Every subcritical moving-cutoff normalized limit is the rank-≤1 smooth matrix at an amplitude from a compact countable set with zero as its only accumulation point. The residual below `T^{1−2ε}` is open; every power improvement of it is a fixed strip [S].
- **Endpoint invariants.** The centred pole has positive finite energy independent of cutoffs. Tail-rate suprema are `1 − Θ` and `4(1 − Θ)` at every damping; attaining the endpoint rate forces simple boundary zeros, and the endpoint tail oscillates [S].
- **Half-damping hypercube endpoint.** `Q_{1/2}(P)` is bounded over every squarefree `P`; sub-half paid multiplicative patterns have integer local exponents; Dini and completely monotone defects are unpaid at every `0 < ε < 1/2`.

### 1.9 Payment domains (golden one-prime model)

On the normalized one-prime coefficient space the payment domain `{g : partial sums ∈ ℓ²}` is not closed. Its closure is the kernel of total evaluation, the reduced cokernel is isometrically `ℂ`, and the continuous dual of the unreduced quotient is one-dimensional. The closure gap has Hamel dimension continuum. Payment must be controlled through the graph norm, not by closure.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls involved ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime cross-work receivers read `Δ` exactly, endpoint attained. RH ⇔ `E` bounded ⇔ cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)`. Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit has `Γ^{−1/2}` averaged decay for `α < 2/3`. Two primes on mixed lags suffice. The RH mean law keeps its RH premise.
**(a)** W2–W4. W6(i): an averaged bounded-energy statement from the high-zero tail and the filtered law.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed `σ < 1/2`). B1.4 (frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.7, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; shell decomposition into nonnegative frozen relaxation plus an arithmetic jump bracketed by collar correlations; on the prime-threshold ladder, RH ⇔ cumulative relaxation `≤ μ(3/10)`. `H¹` rate sets `[Δ, ∞)`; ground = polar rate. Averaged log-aperture positivity and finite-level existence apply.
**(a)** W2/W5: certified low-sector matrices and further windows. W6(ii): merge the RW, SRT and ACS rate dictionaries.
**(b)** B1.3 (sign at every aperture). B3.6 (signed collar estimate on the moving ladder). B3.1 (`polarRate = Δ`). B3.7 (short-window averaged positivity).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent. Actual terminal primes realize graph sources with vanishing diagonal cost. The isolated critical prime channel is negative on narrow windows and has a positive limit `≥ log 2/(8π⁴)` on dyadic and wider windows [S]. Bounded graph norm with vanishing diagonal does not give compactness.
**(a)** W2–W4: schedules, clock kernels, cross-block identities.
**(b)** B1.1: the complete history (seed, drift, covariance, endpoints jointly).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the matched-quantile history is RH-equivalent; the normalized history falls below `−δ(K+2)` cofinally. Hyperbola, centroid, square-debt identities and low-LCM payment are present.
**(a)** W2–W4.
**(b)** B1.1: the full-history floor with high-LCM pairs, moving core and singular transport.
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond its shift threshold; RH ⇔ nonnegativity at every order below its threshold. The centered order-24 finite moment sign closes through rational polynomial enclosures with outward rounding.
**(a)** W2/W5: further orders.
**(b)** B1.5: low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`, so `M = o(√x)` is impossible and either one-sided `O(√x)` bound forces RH with simple zeros. The gap receiver `θ(ε,t) < 1` has proved high-height and small-damping collars. Proved: prime-root and composite-order minor arcs, all-modulus `Q^{−δ/32}` saving, the diagonal reduction, balanced and centred-prime bands ⇔ `Θ < 1`, the full Vaughan picture of §1.8 and the visible-pole index on the Liouville orbit.
**(a)** W3/W4: apply row estimates in their ranges.
**(b)** B2.1 (band saving is exactly quasi-RH). B1.1 (global cancellation or interior anti-alignment). B2.6 (power-saving sign correlations). Planted Euler factors keep the collars.
**Walls:** 1.0, 1.1, 1.12, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2` for `0 < t < 1/2`; RH ⇔ the bound at every such `t`; the one-sided bound `D_t(N) ≤ C` is RH-equivalent. Odd Weil positivity is an alternative receiver.
**(a)** W2, W4.
**(b)** B1.3: signed nonlocal covariance at every `t`.
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** Laguerre, Jensen and finite-head receivers; at fixed `R² ≥ 1/2`, RH ⇔ all-height head coefficient positivity. Every positive heat repairs every sufficiently high head; KKL positive-time reality; complete local divisor geometry.
**(a)** W6(iii): the explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. W2/W5: bounded-height certificates.
**(b)** B1.5 (zero-heat sign on the residual region). B2.9 (smaller de Bruijn–Newman bounds). B3.9 (source-selective cofactor repair).
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace equals winding; an integral nonnegative residual below one vanishes, but neither its sign nor the sub-unit bound is derived. Literal Gaussian integer weights have nonpositive coprime covariance.
**(a)** W2, W4.
**(b)** B1.6: a matrix-complete residual sign and an all-disc sub-unit estimate.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form / prime-window ceiling
**Status.** Exact forcing-sign dictionaries; the ceiling `c(L) ≤ e^{L/2} + B(1+L)` gives AIP allocation; prime-blind receivers are RH-equivalent; finite `D` is even and RH ⇔ `D < 2`. Full-cone source selection identifies `Λ`, and positive-measure rigidity identifies the source among positive measures with the theta law. The two-prime spline orbit is a Bochner problem on `T²`. Curve calibration: lower Lefschetz forces unitarity; upper forces it unless a positive real outer eigenvalue exists (golden `φ`); genus-one Hodge index = degree positivity of `ℤ[F]`; the Hecke graphs of `ℤ` satisfy no theorem of the square.
**(a)** W2, W4.
**(b)** B1.3 (the pairing sign or the `O(L)` ceiling). B1.7 (`D < 2`). B2.2 (finite index). B3.10 (compatible oriented families). B3.21 (prescribed successor coordinates).
**Walls:** 1.3, 1.4, 3.13, 14.4, 14.12.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state lies above `1/2`; one-signed bound states vanish, sign-changing ones are not excluded. Fixed-aperture completion, sharp cuts, generator-domain preservation and window nodal convergence are proved.
**(a)** W3/W4.
**(b)** B1.3: the nodal or reflected-prime inequality.
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the coefficient orthant at small time; fixed-rank coercivity; a Weil margin gives heat-Hankel positivity in a coupled rank–time window; rank-`N` tests are blind above height `O(N√log N)`.
**(a)** W2/W5.
**(b)** B1.5 (all-rank signed positivity at one time). B3.12 (decoupling rank from time).
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact Hilbert–Schmidt cone-positive renewal operator realizes the denominator through `det₂` with the exact divisor; cone positivity does not confine resonances.
**(a)** W2, W4.
**(b)** B1.6: boundary-current orientation (mixed prime + Gamma ≥ pole with every cusp and seam term).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH; Euler–Stieltjes saturation at one admissible `τ` is RH-equivalent; collision masses are even and match the index bridge `2(D+E)`; Mehler bracket, cumulants, multi-pair witnesses, root barrier and optimal heat are proved; large-height repair as in §1.6.
**(a)** W6(iii); W2.
**(b)** B1.6 (cap vanishing or saturation). B1.5 (heated-head positivity on the residual region).
**Walls:** 1.2, 1.14, 3.8.

### LI — Li even-cross clock
**Status.** RH ⇔ subexponential lower floors at every positive rate. Off-line rates `≤ 1/431`, maximal rate `β < 1/300`, `β = 0` iff RH, positive `β` attained on a finite packet. The currency is reciprocal depth, not `Δ`.
**(a)** W2/W5.
**(b)** B1.7: the subexponential floor.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint compact-window, moving-aperture and collared noncompact limits; on RH-complete factorial-tent families, RH ⇔ nonnegative first variation; quantitative tent transfer. Common shift thresholds exist for each fixed high-scale family, not across unbounded families.
**(a)** W3/W4.
**(b)** B1.3, the same sign as RW.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The size-truncated receiver equals the full natural form; its exterior is paid; `ε = 1/2` is paid for every squarefree support. The cofactor structure of §1.7 and the Vaughan transition of §1.8 are proved. The forcing splits into a power plus a bounded remainder; diffuse escape keeps the antipodal density; the dilation commutator is bounded; (residual, trace) reconstruction is injective but only algebraic.
**(a)** W3/W4: Vaughan bookkeeping. W7: the cofactor spectral identity and the translated-zero battery.
**(b)** B1.2 (signed small-damping energy). B3.2 (escape-state classification). B3.3 (quantitative coercivity). B3.11 (sub-half forward interior). B3.16 (paid ideal on escape; not decisive on the spectral reading).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry budget
**Status.** A positive level-one budget ⇔ a half-plane bound `< 1/2`; the half-power endpoint is RH; the Gamma–theta source is admitted at all finite supports.
**(a)** W2–W4.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Cofactor test family / Báez–Duarte
**Status.** Residual = `(1 − readout)² + centeredEnergy`; RH ⇔ both small together; the floor `κ/log N` and the readout–energy uncertainty principle are exact; literal `−μ_N` aligns the readout.
**(a)** W2/W5.
**(b)** B1.2 (readout → 1 and centered energy → 0 together). B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat / critical feature variance
**Status.** All-degree positivity of the two literal source grids (spacings `log 2`, `log 3`) on their polar hyperplanes is RH-equivalent; one grid aliases.
**(a)** W2/W5.
**(b)** B1.5: both grids at every degree.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton disc
**Status.** Line-centered Newton discs covering every zero ⇔ RH; the interior margin is subharmonic, so boundary control gives no interior margin; global scalar damping has only the trivial repair.
**(a)** W2.
**(b)** B1.5: the all-disc interior margin.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Bohr almost-periodic strong recurrence
**Status.** Strong recurrence on every compact right-strip set, local recurrence at every point, and cutoff-uniform positive Haar mass of target twists are each RH-equivalent; recurrence holds exactly at non-zeros; the self-return threshold reads the vanishing order.
**(a)** W3/W4.
**(b)** B1.7: returns near possible zeros.
**Walls:** 1.2, 3.2.

### EWU — Even Weil universality / pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; literal positivity on high dyadic, polynomial and lacunary windows; full-cone source selection (single-node perturbations fail); finite-level existence ⇔ RH.
**(a)** W2–W5.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Gaussian tail / Hedenmalm–Schur decay
**Status.** Uniform quartic Schur decay is RH-equivalent; an off-line zero forces a late positive charge floor; truncations converge strongly.
**(a)** W2.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil universality
**Status.** Odd positivity is RH-equivalent; continuum light-cone variation positive; compensated reflected-prime source positive on nonzero odd tests; fixed-support subunit collar paid; lattice Schur payment reduces to a finite head.
**(a)** W2–W5.
**(b)** B1.3: full reflected-prime and polar payment.
**Walls:** 1.3, 3.4.

### PBM — Prime-bias Mellin / regularized logarithm
**Status.** A half-plane bound at `α` ⇔ convergence of `Σ(Λ(n)−1)n^{−s}/log n` on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** W4.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1.

### RB — Robin bound
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need a growing lcm core and a small moving valuation defect.
**(a)** W2.
**(b)** B1.7: the eventual extremal tail.
**Walls:** 1.1, 1.6.

### SRT — Square-root threshold and smooth detection
**Status.** One fixed-width late-lag family decides RH at every admissible width; smooth detector at aperture `Cδ^{−2}(4+|γ|)²`; the single-height phase-selective law holds with explicit premises; eventual all-height saving is refuted; phases recur syndetically.
**(a)** W3/W4.
**(b)** B1.4 and B1.1: horizon containment and the late-lag sign. B3.20: signed near-coincidence cancellation at one height.
**Walls:** 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single shift
**Status.** One fixed shift `a > 0` against all even compact profiles decides RH; antisymmetric light-cone kernel positive; subunit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation up to `Ke^r e^{−c√r}` (rate `1/2`); horizon-uniform Schur payment to a finite head; active cosets and top-octave dominance; exact shared-budget descent (excess `kB`).
**(a)** W2/W5.
**(b)** B1.3 (one shared signed budget). B3.8 (nonlocal frustration calculus).
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi
**Status.**
- Exact source identity; RR exact at every aperture; reserve boundary rigidity (RR + Bézout on one cone ⇔ reserve = defect); positive majorants give Bézout and ampleness, never RR; finite readings with mass never give Bézout.
- Maximal blind ideal with the full restricted geometry and its exact topology; exhaustion is RH (§1.3).
- Positive Poisson pairs: prime side positive, spectral side RH-equivalent, gap rigidity gives only density statements on the Weil pair (§1.4).
- Invariants: degree-one rigidity; relaxation models; index–pole conservation; simple-pole rigidity [S]; the simple pole is the exact rigidity threshold (§1.5).
- Multiplicative forcing: boundary theory and capacity complete; completed-system capacity and collar sparsity [S]; interior capped by growth input; no quantized inequality at the critical line (§1.5).
- Sparse-spectrum annihilators for `Σ|a_k|^{−s} < ∞`, `s < 1` (not applicable to ζ zeros); averaged log-aperture positivity.
- Zero census: simple-or-critical fraction `≥ 0.8876`; distinct critical ordinates `≥ 0.8042`. TTPC: `N₀* ≥ (29/36 − β − ε)N`, and `β ≤ 1/18` would give `3/4`.

**(a)** W1 (battery). W6(iv): effectivity as exhaustion of the maximal blind ideal. W6(v): the bare-FE form of rigidity. W6(vii): the conservation identity for infinite corrections. W6(viii)–(ix): ζ calibration and unification of the capacity laws.
**(b)**
- B1.6: an independent effectivity or forcing input outside the exhausted classes.
- B1.8: the faithful variants need simplicity.
- B3.4: spectral synthesis in the blind ideal.
- B3.5: the surface section law.
- B3.17: scale-side coupled positivity outside the maximality class.
- B3.18: the equality case of collective boundary capacity at even `κ`.
- B3.19: a base for coefficient systems over `Spec ℤ`.
- B2.5: the coalescent surplus.

**Walls:** 1.3, 1.15, 3.8, 14.4, 14.8, 14.10–14.14.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6: construct the object before its sign and prove the sign independently. Four theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness (§1.3);
- finite multiplicative certificates are capped by growth input, and coupled height channels give only boundary capacity (§1.5);
- a mechanism must separate ζ from the relaxation models of §1.5, which keep `Λ ≥ 0` and the exact functional equation at pole order two;
- pole order pays only for inserted zeros, so a mechanism that sees ζ's own zeros must see more than pole order (§1.5).

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; Fredholm trace receiver exact. | W1–W3 | Annihilation of the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support. | W1, W2 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W1, W2 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; dyadic descent universality. | W2, W3 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W2–W4 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W1, W2 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = sum over off-line zeros of `log|ρ/(1−ρ)|`, zero on critical zeros. | W2 | Cofinal contrast equality (B1.7). |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W1, W2 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W1, W2 | Source lift with integral count (B1.6). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W2, W3 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained. | W2 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; Ξ-limit ⇔ RH; prime-log stacks cannot converge to Ξ. | W2 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Energy probabilities erase grade. | W2 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W2, W3 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W1, W2 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centered real compact-uniform convergence suffices. | W2, W4 | Arithmetic couplings with a centered limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W2 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read `Re ρ = 1/2` with exact depth laws. They detect blindness; they do not force it. FEL is the zero-side analogue of the Hamburger squeeze: a nonnegative functional that vanishes exactly on critical zeros. What it lacks is the arithmetic upper bound that would force the functional to zero.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows | Minor arcs; all-modulus `Q^{−δ/32}`; diagonal reduction; balanced and centred-prime bands ⇔ `Θ < 1`; Kloosterman Parseval; prime Gram of rank three. | W4 | B2.1; B1.2 |
| **BVI** Vaughan | Half-damping transition (§1.8); every power improvement ⇔ fixed strip; floor coefficients converge in critical Wiener norm above half damping. | W4 | B1.2 |
| **ADR / AOT** cofactor modules | §1.7: record minima, contraction calculus, eigencharacter moduli, finite hulls, visible-pole index. | W7 | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates | §1.2. | W6(ii) | B3.6, B3.1 |
| **ACS / Meyer** | §1.3. | W6(iv) | B3.4, B3.5, B3.17; B1.6, B1.8 |
| **APD** positive duality | §1.4 and the invariant half of §1.5: Poisson-pair rigidity, integer positive-definite classification, lattice Bochner, affine induction, quantum budget, blind-ideal topology, curve calibration. | W6(v) | B3.21; its "third forcing instance in the strip" is B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, total zero mass, realization; interior capped (§1.5). | W9 | — (complete below RH strength; integral realization of profiles by Beurling systems is open but blocks no route) |
| **SBWF** strip Bochner–Weil forcing | Coupled height-channel form; boundary and polar-surface shadows; completed-system capacity and `κ²` collar sparsity; gauge collapse; simple-pole rigidity (§1.5) [S]. | W6(vii)–(ix) | B3.18; B3.17 (scale side) |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; spline orbit; base theta `h⁰` with RR and Mellin. | W4 | B3.10, B3.5; B2.2 |
| **AOT** readings, hulls, width functor | Width functor; Wiener hulls; Bohr characters; active cosets; prescribed finite Wiener jets. | W4 | B3.4 |
| **ALDG** local divisor heat | §1.6. | W6(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering | Endpoints; high-zero tail; filtered deficit. | W6(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt; boxes. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3` and lag-2 `1/4` floors exact; complex floor in `[−1/2, −1/3]`; half-damping hypercube endpoint. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half damping. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure and one-dimensional dual (§1.9); chirp phase group. | — | B3.3 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`. | — | B2.5, B2.7 |
| **Analytic inputs** | Guth–Maynard; 30/13 and Ingham–Huxley density; short-interval zero weights; Heath–Brown all-length; sharp `S₂`; KKL; dlVP, Littlewood, VK; FE/count fluctuation; Hamburger rigidity and stability. | W9 | B2.4, B2.8 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - Invariant completeness in degree one: rigidity plus relaxation models (§1.5).
  - The absolute pole-order budget `ind₋(W_F) ≤ ord₁F − 1`: false; the exact law is the index–pole conservation identity, and it gives only lower bounds on `ind₋(W_ζ)` (§1.5).
  - The rigidity threshold of positive relative deformations: pole order one is rigid [S], pole order two admits every off-line type (§1.5).
  - Interior multiplicative forcing by finite positive certificates beyond growth input: excluded (§1.5).
  - Coupled height channels as interior forcing: they give boundary capacity and a `1/log T` collar only (§1.5).
  - Quantized inequalities from multiplicative positivity at the critical line: none (§1.5).
  - Closedness of the maximal blind ideal: closed naturally, closed for critical data iff RH (§1.3).
  - Summation-scope "defects": none ever existed (Mathlib parses the `∑` body at precedence 67).
  - Polar versus full ground-energy rate: equal.
- **Completed constructions.** Filtered averaged coercivity; CHMD generator domain and sharp windows; Suzuki compact-`L²` and moving-window limits; Heath–Brown all-length and sharp `S₂`; the smooth detector; endpoint attainment; base theta `h⁰`; Hermite optimal heat; large-height head repair; the maximal blind ideal and its topology; the boundary forcing law, capacity and realization; the exact Fejér barrier, growth-to-forcing law and quantum budget; positive-measure Hamburger rigidity; Poisson gap rigidity; lattice Bochner; affine induction; the half-damping hypercube endpoint; the Vaughan half-damping transition; record-minimum cofactor limits, the contraction calculus and the visible-pole index; sparse-spectrum annihilators; finite-level existence ⇔ RH; the PA order-24 finite moment sign.
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
  - free affine extension as an additional positivity constraint;
  - harmonic positivity without pole simplicity or with harmonic poles;
  - more finite frequencies, or more height channels, against a fixed growth payment;
  - decaying count error under the functional equation;
  - `Λ ≥ 0` plus the exact functional equation without the simple pole or without strip holomorphy;
  - pole order as payment for ζ's own off-line zeros;
  - Wiener closure as a substitute for payment.
- **Substitutions that do not hold.** Orthant for signed positivity; cone positivity for self-adjoint confinement; finite for all ranks; local payments for one budget; finite-aperture for global index; averages for selected heights; algebraic for bounded inverses; zero-indexed objects for pre-divisor constructions; imported for forced regions; a zero-free-region transfer for a forcing law; boundary capacity for interior depth.
