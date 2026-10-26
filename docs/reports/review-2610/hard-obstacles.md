# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-26, corpus `e889b7985` with the working tree of that day. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** The route inventory is that of the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module headers and theorem statements; the record is `logs/review-2610/working-log.md`. Nothing was compiled. Labels: `[S]` working source not yet integrated, `[P]` paper proof, `[R]` assessment or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, premise checks, transport of proved estimates, corollary assembly, classical ranges of known estimates, technical strengthening of a proved theorem. IDs `W1`–`W12`, defined in the [summary](hard-obstacles-summary.md#1-just-work).
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

Notation: `Δ = sup_ρ |Re ρ − 1/2|`, `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. `Q_γ(F) = Q(F cos γ·) + Q(F sin γ·)` is the complete Weil form of the two modulations of a real test `F`. `Φ(γ) = Σ_q (Re q − 1/2)²/(1 + (Im q − γ)²)²` is the off-line field; it vanishes identically under RH.

## 1. Facts that fix the present frontier

### 1.1 The first rung of every cancellation receiver is quasi-RH

Each graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is a fixed zero-free strip `Θ < 1`:

- WL lag or deficit at a fixed rate `σ < 1/2`; PBM convergence on `Re s > 1/2 + α`; the JAS level-one budget;
- the balanced Möbius statistic and the centred-prime band (`balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`); short-window Möbius and prime saving;
- every power improvement in the Vaughan picture: empty leg, uniform convolution power cancellation, uniform residual Gram power rates, factorial-order-one envelopes, reciprocal-tail gains at every positive damping;
- RW and ACS floors at any rate `< 1/2`; admission of the cofactor receiver at a fixed damping `ε`, obstructed exactly by uncancelled zeros right of `1/2 + ε` (visible-pole index);
- the one-prime Lefschetz sequence: for one test `g` and every prime `p`, `c_m^{(p)} = W(T_{p^m} g, g) = O(p^{θm})` iff `Δ ≤ θ` (`zeta_exists_universal_lefschetz_growth`); one-sided bounds at two distinct primes already give the strip (`zeta_width_le_iff_oneSided`).

Unconditional arithmetic stops at the Vinogradov–Korobov region (`riemannZeta_ne_zero_vinogradovKorobov`), with the de la Vallée Poussin and Littlewood regions. No cancellation receiver has a target between Vinogradov–Korobov and a fixed strip. Multiplicative forcing and its completed-system form reach the same rung: their collar has width `≍ 1/(d log T)`.

### 1.2 The gauge principle

The gauge torus `G = (ℝ/ℤ)^{primes}` acts on arithmetic sources by the unimodular completely multiplicative twists `χ_x(n) = Π_p e(x_p v_p(n))`. Statistics built from coincidences of products are gauge invariant; additive relations (`ab − cd = h ≠ 0`, affine maps with `b ≠ 0`, the successor) are gauge charged, with gauge mean zero. Multiplicative data determine a finite source exactly up to its gauge orbit (`MultiplicativeDataDetermineASourceUpToGauge`).

- **The actual source is one gauge point.** For every bounded source, Haar-almost every twist has `|Σ_{n≤N} a_n χ_x(n)| ≤ C_x √(N+1)(1 + log(N+1))²`. For `μ` the half-power law holds at almost every gauge point, fails at the Liouville twin (`λμ = μ²`), and at the point `0` it is RH (`moebius_gauge_trichotomy`) [S].
- **Pair and near-incidence statistics are gauge charge.** Successor correlations, the coalescent prime-pair surplus of TTPC and the near-incidence form beyond the square-root threshold all have gauge mean zero and diagonal variance; the surplus meets every budget for Haar-almost every twist of the primes.
- **The archimedean line has a threshold.** Windowed `2k`-th moments of a Dirichlet polynomial equal `‖η‖²` times its gauge moment plus the near-incidence form; below `2rX^k ≤ 1` the near-incidence form vanishes and the line sees the whole torus.
- **Amplification loses linearly.** A rate from an amplified observable needs a loss law `b_k = o(k)`. Gauge Jensen, `(∫|D|²)^k ≤ ∫|D|^{2k}`, makes every bound routed through gauge moments lose at least linearly (`MultiplicativeAmplificationLosesLinearly`). Relative powers move the gauge point (`χ_x^k = χ_{kx}`) and fix `ζ`; external products commute with twists. Product receivers of any order gain on depth exactly what a single receiver of the same total length gains (`ProductReceiversSeeDepthOnlyThroughTotalLength`). Over `𝔽_q` a fixed budget forces purity and the golden datum loses linearly (`TheGoldenDatumHasNoFixedBudget`).

Consequence: any argument that uses only multiplicative data proves its statement for the whole gauge orbit and decides nothing at the point `0`. A ζ-specific sign must use gauge-charged structure: the archimedean place (Gamma factor, functional equation, the line), additive structure, or the boundary of finite presentations. The Möbius boundary of affine maps separates `μ` from its Liouville twin by the prime number theorem (`moebius_boundary_separates_twin`).

### 1.3 Positivity: pointwise, averaged and at zero ordinates

- **Exact form.** For every real compact `C²` test: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, endpoint attained.
- **Pointwise windows.** Full form `≥ ‖f‖²/5000` through radius `3/10`; odd form `≥ ‖f‖²/1000` through `181/500`; primitive Hodge index through `(log 2 + 1/50)/2`.
- **Short-window averaged positivity.** For `Γ^{99/100} ≤ H ≤ Γ/8`, `0 ≤ A ≤ κ₀ log Γ` and real `F₀ ∈ C²_c([−A, A])`: `H⁻¹∫_Γ^{Γ+H} Q_γ(F₀) dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−1/2} N(F₀)²` (`exists_shortWindow_frequencyAverage_quadrature_pos`). Remote zeros are paid by Lorentzian mass, the core by Riemann–von Mangoldt on short windows, near-line zeros by Selberg's near-line density on windows of length `U^{99/100}` (`exists_shortWindowZeros_weighted_le`).
- **Pointwise reading of the negative part.** `Q_γ(F₀) ≥ −4(A + 1)² e^A N(F₀)² Φ(γ)` at every height, aperture and test (`neg_offLineField_le_fullZeroForm`). On every such window, `|{γ : Φ(γ) > η}| ≤ CH/(η log Γ)`, independent of the aperture and the test.
- **Zero ordinates.** Each window holds `≥ H log Γ/(16π)` zero copies, all but `CH/η` with `Φ(Im q) ≤ η`; at those ordinates every nonnegative `F₀` has `Q_γ(F₀) ≥ (∫F₀)² − 4η(A + 1)² e^A N(F₀)²` (`exists_shortWindow_almostEvery_zeroOrdinate_positive`). A set of heights of measure `≥ cH/(A+1) − CH/(η log Γ)` carries `Q_γ(F₀) ≥ (∫F₀)²/4 − 4η(A+1)²e^A N(F₀)²` for all nonnegative `F₀` of aperture `A`. Signed tests keep only the negative floor.
- **Witness persistence.** A zero's witness at aperture `A` stays negative on an interval of length `2(1 − r/Z(γ))/A`, independent of the depth (`TheWitnessOfAZeroPersistsForTheReciprocalAperture`). At `A ≍ log T` an exceptional-height bound excludes an individual zero only below the zero-spacing scale `≍ 1/log T`.
- **Aperture flow.** `μ(A)` is strictly decreasing; RH iff `μ(A) > 0` at every finite `A`. On the prime-threshold ladder every birth jump vanishes and RH iff cumulative frozen relaxation `≤ μ(3/10)`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor.
- **Rates.** `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; CCM form-norm and Birman–Schwinger rates equal `Δ`; physical-`L²` equality `polarRate = Δ` holds under locally bounded off-line depth and is otherwise open.
- **Finite level.** RH iff every aperture admits some real weight system making the full Weil functional nonnegative on tests supported there.

### 1.4 Realization: blind, half-blind and isotropic carriers

- **Maximality.** `meyerTraceBoundedIdeal`, the sources whose Mellin transform vanishes at every off-line zero, is the greatest sharp-stable convolution ideal with nonnegative trace; it keeps every critical jet, carries restricted Hodge index, RR, Bézout and ampleness, and is the whole source iff RH. Every scale-shift-invariant Weil-nonnegative test space is blind.
- **Coupled isotropy.** For channels coupled by divisor-multiplier operators on a carrier closed under diagonal point convolution, positivity forces the fibres at `ρ` and `ρ* = 1 − ρ̄` to be orthogonal for the coupling matrix `K_ρ(a,b) = m_ρ conj τ_{ab}(ρ*) + m_{ρ*} τ_{ba}(ρ)`; positivity on all tuples forces `K_ρ = 0` at every off-line zero (`coupled_isotropy`, `coupling_vanishes_of_nonneg_on_all`). A single positive convolution ideal without sharp stability is half-blind; sharp stability gives full blindness.
- **A positive ideal that is not blind.** The sources vanishing at the zeros left of the line form a convolution ideal with nonnegative trace, defined without zeros by bounded backward-flow mixed traces; it strictly contains the blind ideal unless RH, and equals the whole source iff RH (`leftBlindIdeal_eq_top_iff`).
- **Topology and synthesis.** The blind ideal is closed in the natural Fréchet topology, and closed in a critical-data topology iff RH. Every divisor-order ideal is the closure of its jet sources plus the Poisson boundary; critical jets plus boundary synthesize the full-jet blind ideal, which is the value-blind ideal iff every off-line zero is simple, and the whole source iff RH (`closure_orderJetSpan_sup_poissonBoundary`, with uniform Gaussian tails of canonical products from `TailCanonicalProducts`).
- **Faithful variants.** Faithful positive degrees, the Hilbert–Schmidt reserve and the bounded-orbit carrier reach RH only together with simple zeros. Origin-`L²` supports no continuous faithful reading.
- **Common pattern.** Every unconditional positivity theorem in the corpus is positivity on a blind, half-blind or isotropic carrier, or positivity on average over heights. `ArithmeticForcesBlindness` transfers sources supported outside a zero-free region into the blind carrier; that is a transfer, not forcing.

### 1.5 Positive Poisson pairs and the successor

- **Both sides of the explicit formula.** The damped prime measure is finite and positive with characteristic function `Re(−ζ'/ζ)(1+x+iu)`; positive spectral measures for every `C²` test exist iff RH. On tests vanishing for `|x| ≥ log 2` the prime side is empty, so the prime-free gap sits on the side of the known positivity.
- **Gap rigidity.** A positive tent-self-dual measure with gap `(−1,1)∖{0}` is a Dirac comb; a wider gap forces zero; narrower gaps admit dual-lattice non-combs. With the gap on one side only, the conclusion is a uniform local mass bound.
- **Integer positive-definite functions** on every abelian group are sign characters of subgroups; isolation forces `δ₀` iff the group has no 2-torsion.
- **Two-prime receiver.** RH iff the cubic-spline correlation on `ℤ log p + ℤ log q` is positive definite on `ℤ²`, equivalently the Fourier sequence of a positive measure on `T²`.
- **Affine group and successor.** Affine positivity on `Aff(ℚ)` is induced from the dilations with free successor coordinates. A prescribed integer successor forces the Hecke weight `(nd)^{−1/2}` and is incompatible with any dilation part continuous at `1`; Hecke states `(nd)^{−s}` are positive definite iff `s ≥ 1/2`; the Bost–Connes successor at `β > 1` forces `(nd)^{−β/2}`; equality states are twisted Haar states; a single successor period with dilation continuity makes the successor constant (Mautner).
- **Prime-torus split.** Positive-definite functions on `ℚ_{>0}` are Fourier transforms of positive measures on the prime torus; each splits uniquely as `f_arch + f_null` (`kronecker_decomposition`), the archimedean part carried by the Kronecker line, the null part giving it mass zero. Integer and Bost–Connes successors force the null part only; atomic archimedean dilation spectra, Weil's correlation under RH among them, carry no successor beyond the trivial extensions (`successor_blind_of_atomic_archimedean`; `weil_successor_blind` [S]). The Hecke dilation spectrum is a prime-Poisson law, Haar-equivalent iff `s > 1/2` and singular for `s ≤ 1/2` (`heckeState_kakutani_wall`) [S].
- **Curve calibration.** Purity of a curve datum ⇔ positive definiteness of its trace sequence on `ℤ` ⇔ Hasse–Weil ⇔ span Hodge index; the golden datum `1 − 5X + 5X²` fails on every group. Künneth–Adams counts and symmetric-power coefficients are all nonnegative iff the point counts are, and the golden datum passes this whole hierarchy (`kunneth_positivity_tfae`): Weil's positivity is positivity of correspondences, not of products of counts.

### 1.6 Invariants, pole order and multiplicative forcing

**Degree-one rigidity.** A Borel measure `ν ≥ 0` on `[1, ∞)` with `∫u⁻² dν < ∞` whose theta transform satisfies Riemann's degree-one law is `(−2 Re α) Σ_{n≥1} δ_n`; the completed version holds under absolute convergence, the completed FE and finite order, strip decay following by Phragmén–Lindelöf (`measure_eq_of_completed_functional_equation_of_finiteOrder`). A Beurling prime measure with the law is `Σ (Λ(n)/log n) δ_n`; countable Beurling systems with the completed FE are ζ's. **Stability:** an `L¹` critical-line defect `g` of the FE bounds the off-lattice mass by `(6/π)‖g‖₁` and every unit-tent mass within `(18/π + 4κ/π²)‖g‖₁` of `2 Re β`. Without positivity only `Σ a_n sinc²(πλ_n) = 0` survives.

**Relaxation models.**

| Invariant relaxed | Model | Off-line zeros |
|---|---|---|
| Simple pole (pole order 2) | `ζ·(s−β)(s−1+β)/(s(s−1))`, a `CompletedPositiveSystem 2 1` | real pair `β, 1−β` |
| Simple pole, one critical refund | remove Hardy's pair `1/2 ± iγ₀`, insert the quartet of `1/2 + a + iγ₀`, `0 < a ≤ 1/4`; a `CompletedPositiveSystem 2 1` | complex quartet |
| Simple pole (pole order 3) | `ζ·quartet/(s(s−1))²` | complex quartet |
| Holomorphy of the completion in the strip | `ζ·quartet/((s−1/2)²−c²)⁴` | quartet, strip poles |
| Riemann's FE | over-regular positive Beurling systems | zeros in `1/2 < Re s < 2/3` |
| Coefficient positivity | self-dual character combinations | uniqueness fails |
| Sign of `ζ` on `(0,1)` (boundary invariants kept) | `ζ(s)/ζ(s + 1 − β)`, log-coefficients `Λ(n)(1 − n^{β−1}) ≥ 0` | real zero at any `β < 1` |

**Pole order and zeros.**

- **Conservation.** For finite reflection-antisymmetric deformations of ζ, `(Weil-index increment) = (pole-order increment) + R_crit − I_crit`. The absolute inequality `ind₋ ≤ ord₁F − 1` is false; applied to ζ, every deformation gives only lower bounds on its index.
- **Pole order one is rigid.** A nonzero entire `E` with `E(1−s) = εE(s)` and `−E'/E + ξ'/ξ = Laplace(ν)`, `ν ≥ 0`, on a right ray is `cξ`.
- **Real-zero budget.** Every `CompletedPositiveSystem κ d` satisfies `4 ord_{1/2}Λ + 8Σ_{x∈X} ord_x Λ + 5d < 9κ` for every finite `X ⊂ (1/2, 1]` (`real_zero_archimedean_budget`). Hence `κ ≥ 1`, `κ = 1` forces `d = 1`, and a simple-pole system has no real zeros. No entire `κ = 0` Laplace-positive completion exists.
- **Gauge collapse.** An entire finite-order `E = (s(s−1))^κ G` with the FE, `G` bounded on a right half-plane and `G(σ) → 1`, is a monic polynomial of degree `2κ`; its off-critical quartets obey `2Σm ≤ κ`.
- **Threshold.** Positive relative deformations of ξ are rigid at pole order one and admit every off-line type at pole order two: the simple pole is the exact rigidity threshold. Pole order pays for inserted zeros, not for ζ's own.

**Boundary (MPG).** The boundary divisor `D` of nonnegative log-coefficients is an even positive-definite function. Nonnegative weights, integer divisor, simple pole and pole isolation force `D = δ₀`, each invariant necessary. A pole of order `k` carries at most `⌊k/2⌋` boundary zeros, every placement realized; `Σ_{z∈Z} −D(z) ≤ D(0)/2` at any finite set of heights. Every locally finite even positive-definite configuration is the boundary divisor of one Dirichlet series `Σ Λ(n) g(log n) n^{−s}` with fixed `g ≥ 0` (`arithmetic_bochner`), and of an integral Euler product over the rational primes (`integral_bochner`) [S]. Integer boundary divisors with a simple pole are `δ₀`, a lattice indicator, an alternating lattice character or the constant `1` (Baire regularity). Decay exponents obey `Σα_z ≤ k/2` without boundary limits; a simple pole admits no decay faster than `x^{1/2}`. For families over a finite abelian group the only unforced configuration is a two-torsion exception, realized at every depth (the Siegel family). Bounded-mass data contribute zero divisor: the boundary does not see the interior.

**Completed systems (SBWF).** For `CompletedPositiveSystem κ d F Λ` (positive-definite vertical sections of `Re(−F'/F)` on `Re s > 1`, order-one entire completion `(s(s−1))^κ Γ_ℝ^d F` with `Λ(1−s) = Λ(s)` and conjugation symmetry):

- **Sharp collar capacity.** Every finite set `Z` of zeros with `0 < Im z ≤ T` and `Re z > 1 − w(κ, d, T)`, `w ≍_κ 1/(d log(3 + T))` independent of `Z`, satisfies `2Σ_{z∈Z} ord_z Λ ≤ κ`; no separation or low-ordinate cutoff (`two_mul_sum_order_collar_zeros_le_poleOrder`). Sharp at odd `κ = 2r + 1` by ζ twisted at `r` boundary heights.
- **κ = 1.** `Λ(z) ≠ 0` on the whole slab `|Im z| ≤ T`, `Re z > 1 − w(1, d, T)`, real axis included (`ne_zero_of_mem_sharpCollar_one`).
- **Scope.** A class theorem graded by `(κ, d)` whose content is boundary capacity and a dlVP-scale collar. It gives no interior rate.

**Interior capacity of finite certificates.** Degree `K` gives `a₁ ≤ 2cos(π/(K+2)) a₀`; some `δ > 0` has `A/δ + G < B/(δ+η)` iff `√A + √(Gη) < √B`, certified width `(√B − √A)²/G`; every finite certificate obeys `a(γ) ≤ 2a(0)` and the cap `(3 − 2√2)/(2L)`; multi-channel certificates split into rational fibres. Admissible zero orders are `m ≤ b(η) = (√A + √(Gη))²/B`; at `η = 1/2` every Fejér certificate has `b ≥ 1` once `L ≥ 0.17` and `b ≥ 2` once `L ≥ 1`. The dlVP region is an instance of the law and optimal for its input.

### 1.7 Lefschetz theory at one prime

For a test `g` and a prime `p`, the Lefschetz sequence `c_m = W(T_{p^m} g, g) = Σ_τ X_τ conj X_{1−τ̄} β_τ^m`, `β_τ = p^{τ − 1/2}`, is the analogue of `N_m − q^m − 1`, and its two-element windows `{g, T_{p^m} g}` are Weil's spans.

- **Growth.** One test `g` serves every prime: `c_m^{(p)} = O(R^m)`, `R ≥ 1`, iff `R ≥ p^Δ`; RH iff `|c_m^{(p)}| ≤ c_0^{(p)}` for all `m` at any single prime (`zeta_riemannHypothesis_iff_universal_minors`).
- **Zeros as ratios.** For each right zero `ρ` some test has `c_{m+1}/c_m → p^{ρ−1/2}` at every prime; two primes determine `ρ`, since prime logarithms are independent.
- **One-sided bounds.** At two distinct primes, all-test one-sided bounds `±Re c_m = O(p^{θm})` characterize `Δ ≤ θ`; one-sided Weil inequalities at two primes characterize RH [S]. One prime leaves the zeros with `Im ρ log p ∈ πℤ`.
- **Tower laws.** At every prime one `p`-tower carries one negative square per distinct outer eigenvalue (ζ is deep-sparse by Ingham–Huxley); at all but finitely many primes it carries the whole Hodge defect. Fixed-test blindness requires the folded spectrum to separate (`not_accessibleOff_of_towerGram_psd`). For a curve, towers at arithmetic scales are base changes; ζ has no period, and its primes behave like the non-arithmetic scales of a curve.

Over `ℤ` the receiver side of Weil's argument is complete. Weil's input is missing: a fixed budget for `c_m`, which over `𝔽_q` comes from Riemann–Roch on `C × C` (genus `2g`) and the Hodge index of correspondences.

### 1.8 Heat and divisor geometry

- **Local geometry.** Complete at model level: repair cones, the sharp Hermite root barrier, optimal first heat `a/(2h_{m+2}²)`, universal reflectors (positive monomials only).
- **Large heights.** Every positive heat repairs every sufficiently high radius head.
- **Positive time.** Zeros are real and simple beyond `2π exp((27/40+ε)/t)`; `Λ < 1/8`.
- **Residual.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`: the de Bruijn–Newman core.

### 1.9 Cofactor modules and escape

On every common limit of the actual cofactor Grams at `0 < ε < 1/2`:

- **Structure.** A cyclic critical-Wiener module. Admission gives a unique full-sequence limit, faithful and infinite-dimensional with full Bohr hull; escape gives paid ideal ⊆ annihilator and module hull ⊆ obstruction hull.
- **Record minima.** Some actual limit has `K_pp ≥ p^{2ε−2} > 0` for every `p`; kernel families are singletons or continua.
- **Contraction calculus, characters, visible poles.** Contractions are actual limits; eigencharacters have augmentation modulus or `|χ(p)| = p^{−s}`, `s ≥ 1/2`; finite hulls lie in the half-plane closure; visible interior multiplicities and boundary poles bound `dim(A/I_paid)` from below.
- **Symbol and eigenstates.** On power rows the renormalized cofactor acts by `ζ(s + ε)`: `(I + D̃) n^s = ζ(s+ε) n^s` modulo admitted rows. The power-log eigenspace of `D̃` at exponent `s` has dimension `ord_{s+ε} ζ`; on any finite exponent window `F ⊂ {1/2 ≤ Re s < 1 − ε}` it is the direct sum of blocks at the translated zeros `ρ − ε ∈ F`, of total dimension `Σ ord_{s+ε} ζ` (`powerLogRows_global_renormalizedInversion_iff_order`). The kernel of the renormalized residual is `ℝ q_ε`, with `q_ε` the Möbius floor inverse of the pole power.
- **Euler laws.** The eta transform `(I − 2^{1−ε} D₂) S_ε` is pole-free with symbol `η(s + ε)`; its moving tail is a dilation-regularity question. Euler laws at `2` and `3` determine the pole trace uniquely; one law leaves a periodic ghost; twisted laws force tied exponents [S].
- **Surviving model.** White noise `K_jk = δ_jk/j` satisfies every proved constraint on the kernels.

On finite exponent windows the translated zeros are exactly the eigenstates. Whether every actual escape state is generated by them is the open completeness question.

### 1.10 Vaughan calibration and the half-damping transition

- **Above half damping.** A common critical-Wiener majorant pays every centred piece; the infinite Gram of the limiting rows is PSD of rank two.
- **At half damping.** Finite moving Gram limits are `G_{1/2} + ℓ·ssᵀ`, every `ℓ ≥ 0` realized; the product horizon selects `ℓ = 0`.
- **Below half damping.** Leading-order limits are classified; the residual below `T^{1−2ε}` is open, and every power improvement of it is a fixed strip.
- **Endpoint invariants.** Tail-rate suprema are `1 − Θ` and `4(1 − Θ)`; attaining the endpoint rate forces simple boundary zeros; the endpoint tail oscillates.
- **Hypercube.** `Q_{1/2}(P)` is bounded over every squarefree `P`; sub-half paid multiplicative patterns have integer local exponents; Dini and completely monotone defects are unpaid below half damping.

### 1.11 Payment domains

On the normalized one-prime coefficient space the payment domain `{g : partial sums ∈ ℓ²}` is not closed; its closure is the kernel of total evaluation, the continuous dual of the quotient is one-dimensional and the closure gap has Hamel dimension continuum. Payment is controlled by the graph norm, not by closure.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime cross-work receivers read `Δ` exactly, endpoint attained; RH ⇔ `E` bounded ⇔ cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)`. Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit decays like `Γ^{−1/2}` on frequency averages over `[Γ, 2Γ]` for `α < 2/3`. Two primes on mixed lags suffice.
**(a)** W2–W4. W7(i): an averaged bounded-energy statement from the high-zero tail and the filtered law. W6: the filtered deficit on short windows from Selberg's short-window density.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed rate `σ < 1/2`). B1.4 (from frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.15, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; shell flux decomposes into frozen relaxation plus an arithmetic jump bracketed by collar correlations; on the prime-threshold ladder, RH ⇔ cumulative relaxation `≤ μ(3/10)`. Ground rate = polar rate. Short-window averaged positivity and the off-line-field floor apply to the complete form.
**(a)** W2/W5: certified low-sector matrices and further windows. W7(ii): one rate dictionary. W4: state the short-window and zero-ordinate theorems in RW's ground-energy coordinates.
**(b)** B1.3 (sign at every aperture). B3.6 (signed collar estimate on the moving ladder). B3.1 (`polarRate = Δ`). B1.4 (selection).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent. Terminal primes realize graph sources with vanishing diagonal cost. The isolated critical prime channel is negative on narrow windows and has a positive limit `≥ log 2/(8π⁴)` on dyadic and wider windows [S]. Bounded graph norm with vanishing diagonal does not give compactness.
**(a)** W2–W4: schedules, clock kernels, cross-block identities.
**(b)** B1.1: the complete history (seed, drift, covariance, endpoints jointly).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the matched-quantile history is RH-equivalent; the normalized history falls below `−δ(K+2)` cofinally. Hyperbola, centroid, square-debt identities and low-LCM payment are proved.
**(a)** W2–W4.
**(b)** B1.1: the full-history floor with high-LCM pairs, moving core and singular transport.
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond its shift threshold; RH ⇔ nonnegativity at every order below its threshold. The centred order-24 finite moment sign closes through rational enclosures with outward rounding, now as kernel-checked integer cell certificates.
**(a)** W2/W5: further orders.
**(b)** B1.5: low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; either one-sided `O(√x)` bound forces RH with simple zeros. The gap receiver `θ(ε,t) < 1` has high-height and small-damping collars. Proved: prime-root and composite-order minor arcs, all-modulus `Q^{−δ/32}` saving, diagonal reduction, balanced and centred-prime bands ⇔ `Θ < 1`, the Vaughan picture of §1.10, the visible-pole index on the Liouville orbit. On the gauge orbit of `μ` the half-power law holds almost surely, fails at the Liouville twin and at the point `0` is RH [S].
**(a)** W3/W4: apply row estimates in their ranges.
**(b)** B2.1 (band saving is exactly quasi-RH). B1.1 (global cancellation, equivalently the gauge point `0` outside a Haar-null exceptional set containing the Liouville twin). B2.6 (power-saving sign correlations).
**Walls:** 1.0, 1.1, 1.12, 1.18, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2` for `0 < t < 1/2`; RH ⇔ the bound at every such `t`; the one-sided bound `D_t(N) ≤ C` is RH-equivalent. Odd Weil positivity is an alternative receiver.
**(a)** W2, W4.
**(b)** B1.3: signed nonlocal covariance at every `t`.
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** Laguerre, Jensen and finite-head receivers; at fixed `R² ≥ 1/2`, RH ⇔ all-height head coefficient positivity. Every positive heat repairs every sufficiently high head; positive-time reality beyond `2π exp((27/40+ε)/t)`; complete local divisor geometry.
**(a)** W7(iii): the explicit residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. W2/W5: bounded-height certificates.
**(b)** B1.5 (zero-heat sign on the residual region). B2.9 (smaller de Bruijn–Newman bounds). B3.9 (source-selective cofactor repair).
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace equals winding; an integral nonnegative residual below one vanishes, but neither its sign nor the sub-unit bound is derived. Literal Gaussian integer weights have nonpositive coprime covariance.
**(a)** W2, W4.
**(b)** B1.6: a matrix-complete residual sign and an all-disc sub-unit estimate.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** Exact forcing-sign dictionaries; the ceiling `c(L) ≤ e^{L/2} + B(1+L)` gives AIP allocation; prime-blind receivers are RH-equivalent; finite `D` is even and RH ⇔ `D < 2`. One prime tower carries the whole Hodge defect at all but finitely many primes; the Lefschetz receivers of §1.7 apply. Full-cone source selection identifies `Λ`; positive-measure rigidity identifies the source among positive measures with the theta law. The two-prime orbit is a Bochner problem on `T²`. Calibration: lower Lefschetz forces unitarity, upper forces it unless a positive real outer eigenvalue exists; genus-one Hodge index = degree positivity of `ℤ[F]`; the Hecke graphs of `ℤ` satisfy no theorem of the square; Künneth positivity is point-count positivity.
**(a)** W2, W4.
**(b)** B1.3 (the pairing sign or the `O(L)` ceiling). B1.7 (`D < 2`). B1.9 (a fixed budget for one prime's Lefschetz sequence). B2.2 (finite index). B3.10 (compatible oriented families). B3.22 (a correspondence ring with a theorem of the square).
**Walls:** 1.3, 1.4, 1.17, 3.13, 14.2, 14.4, 14.16.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state lies above `1/2`; one-signed bound states vanish, sign-changing ones are not excluded. Fixed-aperture completion, sharp cuts, generator-domain preservation and window nodal convergence are proved.
**(a)** W3/W4; W4 for the short-window averaged form.
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
**Status.** The nonnegative global cap vanishes iff RH; Euler–Stieltjes saturation at one admissible `τ` is RH-equivalent; collision masses are even and match the index bridge `2(D+E)`; Mehler bracket, cumulants, multi-pair witnesses, root barrier, optimal heat and large-height repair are proved.
**(a)** W7(iii); W2.
**(b)** B1.6 (cap vanishing or saturation). B1.5 (heated-head positivity on the residual region).
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate. Off-line rates `≤ 1/431`, maximal rate `β < 1/300`, `β = 0` iff RH. The currency is reciprocal depth, not `Δ`.
**(a)** W2/W5.
**(b)** B1.7: the subexponential floor.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint compact-window, moving-aperture and collared noncompact limits; on RH-complete factorial-tent families, RH ⇔ nonnegative first variation; quantitative tent transfer. Common shift thresholds exist for each fixed high-scale family, not across unbounded families.
**(a)** W3/W4.
**(b)** B1.3, the same sign as RW.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The size-truncated receiver equals the full natural form; its exterior is paid; `ε = 1/2` is paid for every squarefree support. The cofactor structure of §1.9, including the translated-zero eigenstate classification on finite windows, and the Vaughan transition of §1.10 are proved. Reconstruction from (residual, trace) is injective but only algebraic.
**(a)** W3/W4: Vaughan bookkeeping. W8: the cofactor Plancherel identity and the infinite-dimensional battery.
**(b)** B1.2 (signed small-damping energy). B3.2 (escape completeness). B3.3 (quantitative coercivity). B3.11 (sub-half forward interior). B3.16 (paid ideal on escape).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** A positive level-one budget ⇔ a half-plane bound `< 1/2`; the half-power endpoint is RH; the Gamma–theta source is admitted at all finite supports.
**(a)** W2–W4.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Chronological tail and Báez–Duarte approximation
**Status.** Residual = `(1 − readout)² + centeredEnergy`; RH ⇔ both small together; the floor `κ/log N` and the readout–energy uncertainty principle are exact; literal `−μ_N` aligns the readout.
**(a)** W2/W5.
**(b)** B1.2 (readout → 1 and centred energy → 0 together). B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat trace / critical feature variance
**Status.** All-degree positivity of the two literal source grids (spacings `log 2`, `log 3`) on their polar hyperplanes is RH-equivalent; one grid aliases.
**(a)** W2/W5.
**(b)** B1.5: both grids at every degree.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton invariant discs
**Status.** Line-centred Newton discs covering every zero ⇔ RH; the interior margin is subharmonic, so boundary control gives no interior margin; global scalar damping has only the trivial repair.
**(a)** W2.
**(b)** B1.5: the all-disc interior margin.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Deterministic zeta self-return
**Status.** Strong recurrence on every compact right-strip set, local recurrence at every point and cutoff-uniform positive Haar mass of target twists are each RH-equivalent; recurrence holds exactly at non-zeros.
**(a)** W3/W4.
**(b)** B1.7: returns near possible zeros.
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; literal positivity on high dyadic, polynomial and lacunary windows; full-cone source selection; finite-level existence ⇔ RH.
**(a)** W2–W5.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay is RH-equivalent; an off-line zero forces a late positive charge floor; truncations converge strongly.
**(a)** W2.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity is RH-equivalent; continuum light-cone variation positive; reflected-prime source positive on nonzero odd tests; fixed-support subunit collar paid; lattice Schur payment reduces to a finite head.
**(a)** W2–W5.
**(b)** B1.3: full reflected-prime and polar payment.
**Walls:** 1.3, 3.4.

### PBM — Regularized prime/log-ζ abscissa
**Status.** A half-plane bound at `α` ⇔ convergence of `Σ(Λ(n)−1)n^{−s}/log n` on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** W4.
**(b)** B2.1 at the first rung, B1.1 at the endpoint.
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas divisor-sum criterion
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need a growing lcm core and a small moving valuation defect.
**(a)** W2.
**(b)** B1.7: the eventual extremal tail.
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH at every admissible width; smooth detector at aperture `Cδ^{−2}(4+|γ|)²`; the single-height phase-selective law holds; eventual all-height saving is refuted; phases recur syndetically. One prime tower, one test: the Lefschetz receivers of §1.7. On short windows almost every height and almost every zero ordinate is nearly positive (§1.3).
**(a)** W3/W4; W6.
**(b)** B1.4 and B1.1 (horizon containment and the late-lag sign). B1.9 (the one-prime Lefschetz budget). B3.20 (signed near-coincidence cancellation at one height).
**Walls:** 1.17, 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift `a > 0` against all even compact profiles decides RH; antisymmetric light-cone kernel positive; subunit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation up to `Ke^r e^{−c√r}` (rate `1/2`); horizon-uniform Schur payment to a finite head; active cosets and top-octave dominance; exact shared-budget descent (excess `kB`).
**(a)** W2/W5.
**(b)** B1.3 (one shared signed budget). B3.8 (nonlocal frustration calculus).
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Exact source identity; RR exact at every aperture; reserve boundary rigidity; positive majorants give Bézout and ampleness, never RR; finite readings with mass never give Bézout.
- Maximal blind ideal with its restricted geometry, topology and spectral synthesis; coupled carriers are isotropic, not blind (§1.4).
- Averaged positivity on windows `Γ^{99/100}`, the off-line-field floor, positivity at almost every zero ordinate for nonnegative tests, positive-measure height sets (§1.3).
- Lefschetz receivers at one prime (§1.7).
- Invariants: degree-one rigidity and its stability; relaxation models; conservation identity; κ = 1 rigidity; real-zero budget `5d < 9κ`; sharp `⌊κ/2⌋` collar capacity in completed systems (§1.6).
- Zero census: simple-or-critical fraction `≥ 0.8876`; distinct critical ordinates `≥ 0.8042`; TTPC `N₀* ≥ (29/36 − β − ε)N`, where the surplus `β` is gauge charge.

**(a)** W1 (battery). W7(iv): effectivity as exhaustion. W7(v)–(vii): the harmonic collar from the MPG/SBWF calibration, conservation for infinite corrections, one capacity law. W11: the κ = 1 class collapse.
**(b)**
- B1.6: forcing or exhaustion by an input outside the exhausted classes (now including coupled point-stable carriers).
- B1.8: faithful variants need simplicity.
- B1.9: a sublinear loss law.
- B3.5: the surface section law.
- B3.17: positivity beyond isotropy on carriers not closed under point convolution.
- B3.18: the even-`κ` equality case of collar capacity.
- B3.19: a base for coefficient systems.
- B3.22: a correspondence ring with a theorem of the square.
- B2.5: the coalescent surplus at the gauge point `0`.

**Walls:** 1.3, 1.15, 1.17, 3.8, 3.14, 14.4, 14.8, 14.10–14.16.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6: construct the object before its sign and prove the sign independently. Five theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness, and coupled point-stable positivity only isotropy (§1.4);
- finite multiplicative certificates are capped by growth input, and completed systems carry only boundary capacity and a `1/log T` collar (§1.6);
- a mechanism must separate ζ from the relaxation models of §1.6, which keep `Λ ≥ 0` and the exact FE at pole order two;
- pole order pays only for inserted zeros, so a mechanism that sees ζ's own zeros must see more than pole order (§1.6);
- a mechanism built from multiplicative data alone proves its conclusion for the whole gauge orbit, including the Liouville twin (§1.2).

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
| **W1C** Ising law convergence | Centred real compact-uniform convergence suffices. | W2, W4 | Arithmetic couplings with a centred limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W2 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read `Re ρ = 1/2` with exact depth laws. They detect blindness; they do not force it. FEL is the zero-side analogue of the Hamburger squeeze: a nonnegative functional vanishing exactly on critical zeros, without the arithmetic upper bound that would force it to zero. RFHM, SC and the candidates fed by multiplicative weights (W1C couplings, MSC) must also state which gauge-charged datum they use.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; diagonal reduction; balanced and centred-prime bands ⇔ `Θ < 1`; Kloosterman Parseval; the half-damping transition (§1.10); every power improvement ⇔ a fixed strip. | W4 | B2.1; B1.2 |
| **ADR / AOT** cofactor modules | §1.9: record minima, contraction calculus, eigencharacter moduli, finite hulls, visible-pole index, ζ- and η-symbols, translated-zero eigenstates, two-factor pole trace. | W8 | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates | §1.3. | W7(ii) | B3.6, B3.1 |
| **ACS / Meyer** | §1.3, §1.4, §1.7. | W7(iv) | B3.5, B3.17, B3.22; B1.6, B1.8, B1.9 |
| **APD** positive duality | §1.5 and the invariant half of §1.6: Poisson rigidity, sign characters, lattice and `ℚ_{>0}` Bochner, affine induction, Hecke and Bost–Connes states, Kronecker split, quantum budget, blind-ideal topology and synthesis, coupled isotropy, theta-law stability, curve calibration. | W12 | B3.23; its third forcing instance is B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, regularity, decay law, families and the Siegel exception, arithmetic and integral Bochner; interior capped (§1.6). | W10 | — (complete below RH strength; integral realization of profiles by Beurling systems blocks no route) |
| **SBWF** strip Bochner–Weil forcing | Coupled height form and its shadows; completed-system capacity with sharp `⌊κ/2⌋` collars; κ = 1 exception-free collar; reflection identity and `5d < 9κ`; gauge collapse; κ = 1 rigidity; κ = 2 realizations (§1.6). | W7(vii), W11 | B3.18 |
| **ACG** correlation geometry | §1.2: gauge invariance, a.e. square-root cancellation, gauge charge of successor, pair and surplus statistics, archimedean-line threshold, linear loss law, Möbius boundary separation, witness persistence. | W9, W12 | B1.9, B3.20, B3.24 |
| **AKT** Künneth theory | Product receivers see depth only through total length; product moments are diagonal below the threshold; Künneth positivity = point-count positivity. | W9 | B3.22 |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; spline orbit; base theta `h⁰` with RR and Mellin. | W4 | B3.10, B3.5; B2.2 |
| **ALDG** local divisor heat | §1.8. | W7(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering | Endpoints; high-zero tail; filtered deficit; compact logarithmic producers converge in physical `L²` [S]. | W6, W7(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt; boxes. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3` and lag-2 `1/4` floors exact; complex floor in `[−1/2, −1/3]`; half-damping hypercube endpoint. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half damping. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure (§1.11); chirp phase group. | — | B3.3 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`; the surplus is gauge charge. | — | B2.5, B2.7, B3.24 |
| **Analytic inputs** | Guth–Maynard; 30/13 and Ingham–Huxley density; Selberg near-line density on windows `U^{99/100}`; Heath–Brown all-length; sharp `S₂`; KKL; dlVP, Littlewood, VK; FE/count fluctuation; Hamburger rigidity and stability. | W6, W10 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - Invariant completeness in degree one: rigidity, its finite-order and `L¹`-defect forms, and the relaxation models (§1.6).
  - The absolute pole-order budget: false; the conservation identity is exact and gives only lower bounds on `ind₋(W_ζ)`.
  - The rigidity threshold of positive relative deformations: pole order one rigid, pole order two admits every off-line type.
  - Interior multiplicative forcing by finite certificates beyond growth input: excluded; no quantized inequality at the critical line.
  - Coupled height channels: boundary capacity and the sharp `⌊κ/2⌋` collar, no interior rate.
  - Closedness and spectral synthesis of the blind ideal: closed naturally, closed for critical data iff RH; synthesized by jets plus the Poisson boundary.
  - Coupled positivity on point-stable carriers: isotropy, not blindness.
  - Successor coordinates as a coupling to Weil's correlation: none; the integer successor forces a Kronecker-null spectrum and Weil's atomic spectrum carries no successor.
  - Averaged positivity on windows `Γ^{99/100} ≤ H ≤ Γ/8`: proved.
  - Translated zeros as cofactor eigenstates on finite exponent windows: proved.
  - Depth homogeneity for gauge-moment amplification and for product receivers: proved.
  - Summation-scope "defects": none ever existed (Mathlib parses the `∑` body at precedence 67).
  - Polar versus full ground-energy rate: equal.
- **Completed constructions.** Filtered and short-window averaged coercivity; zero-ordinate and positive-measure height positivity for nonnegative tests; CHMD generator domain and sharp windows; Suzuki compact-`L²` and moving-window limits; Heath–Brown all-length and sharp `S₂`; the smooth detector; endpoint attainment; base theta `h⁰`; Hermite optimal heat; large-height head repair; the maximal blind ideal, its topology and synthesis; the left-blind ideal; the boundary forcing law, capacity, regularity and arithmetic Bochner realization; the exact Fejér barrier, growth-to-forcing law and quantum budget; positive-measure rigidity and stability; Poisson gap rigidity; lattice and `ℚ_{>0}` Bochner; affine induction; Hecke and Bost–Connes states; the Kronecker split; the sharp collar and κ = 1 collar; the real-zero budget; the half-damping hypercube endpoint; the Vaughan transition; record-minimum cofactor limits, contraction calculus, visible-pole index, ζ/η symbols and eigenstate classification; one-prime Lefschetz receivers; sparse-spectrum annihilators; finite-level existence ⇔ RH; the PA order-24 finite moment sign.
- **Excluded mechanisms.**
  - positive exponential aperture floors; eventual all-height phase saving;
  - non-monomial universal reflectors; finite readings, with or without mass, as Bézout sources; origin-`L²` faithful cohomology;
  - PSD, dilation and antipodality as escape exclusion; augmentation as the unique escape state;
  - permanently frozen finite prime families; finite-dimensional affine-unitary successor carriers;
  - single-channel sharp-stable positive ideals, and coupled point-stable carriers, as forcing carriers;
  - free affine extension, and prescribed integer successors, as constraints on Weil's correlation;
  - harmonic positivity without pole simplicity or with harmonic poles; more frequencies or height channels against a fixed growth payment;
  - decaying count error under the FE; `Λ ≥ 0` plus the exact FE without the simple pole or strip holomorphy;
  - pole order as payment for ζ's own off-line zeros; Wiener closure as a substitute for payment;
  - multiplicative (gauge-invariant) data, moments of any order and tensor products as sources of a sublinear loss; Künneth or symmetric-power count positivity as purity;
  - gauge-averaged or almost-sure cancellation as a bound at the gauge point `0`;
  - averaged or almost-every-height positivity as exclusion of an individual zero above the zero-spacing scale.
- **Substitutions that do not hold.** Orthant for signed positivity; cone positivity for self-adjoint confinement; finite for all ranks; local payments for one budget; finite-aperture for global index; averages for selected heights; nonnegative tests for the full cone; algebraic for bounded inverses; zero-indexed objects for pre-divisor constructions; imported for forced regions; a zero-free-region transfer for a forcing law; boundary capacity for interior depth; isotropy for blindness; the gauge orbit for the gauge point; product positivity for correspondence positivity.
