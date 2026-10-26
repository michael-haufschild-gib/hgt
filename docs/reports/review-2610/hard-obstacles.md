# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-26, corpus `8b9038260` with the working tree of that day. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** The route inventory is that of the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md), together with the programme statements of [APD](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/README.md), [ACP](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/README.md) and [SBWF](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/README.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements; the record is `logs/review-2610/working-log-v2.md`. Nothing was compiled. Labels: `[L]` integrated according to the frontier map, `[S]` working source not recorded as integrated, `[P]` paper proof, `[R]` assessment or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, classical ranges of known estimates. IDs `W1`–`W12`, defined in the [summary](hard-obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

Notation: `Δ = sup_ρ |Re ρ − 1/2|`, `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ`, `ρ* = 1 − ρ̄` is its reflection; `{ρ, ρ*}` is a reflection pair, off-line when `Re ρ ≠ 1/2`. `β_ρ = p^{ρ − 1/2}` is the Hecke symbol of `ρ` at the prime `p`. `c_m^{(p)}(g) = W(T_{p^m} g, g)` is the Lefschetz sequence of a test `g`. `Q_γ(F) = Q(F cos γ·) + Q(F sin γ·)` is the complete Weil form of the two modulations of a real test `F`; `Φ(γ) = Σ_q (Re q − 1/2)²/(1 + (Im q − γ)²)²` is the off-line field, identically zero under RH.

## 1. Facts that fix the present frontier

### 1.1 The local type of a reflection pair

The Rosati trace `τ_x(ξ) = δ(ξ·x, x)` of a cycle splits over the reflection pairs of its spectrum. At an off-line pair the local form is `2 Re(u v̄)` in the coordinates `(ĝ(ρ), ĝ(ρ*))`, of signature `(1, 1)`. A correspondence acts on this fibre in one of three ways (ACP P4, P5, P13):

| Type | Action on the fibre | Correspondences | What positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost `diag(β, β̄⁻¹)`, `|β| ≠ 1` | Hecke operators, the archimedean flow, every gauge twist — exactly at off-line pairs | `u v̄ = 0`: isotropy, half-blindness |
| Elliptic | rotation, or the reflection swap `(u, v) ↦ (v, u)` | Hecke operators on the line; the symmetric Hecke operator at a resonant prime; the functional equation | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on the polar part | the additive successor | nothing |

- **Multiplicative symmetry is hyperbolic exactly off the line.** `|β_ρ| = 1` iff `Re ρ = 1/2` (`norm_heckeSymbol_eq_one_iff`). On real even fibres the symmetric Hecke symbol `p^{ρ−1/2} + p^{1/2−ρ}` is real iff `γ log p ∈ πℤ`; a non-real point resonates at one prime at most, so positivity under two primes forces `ĝ(ρ) = 0` (`eq_zero_of_two_prime_symCyclic_nonneg`).
- **Separation is hyperbolic.** Diagonal isometries of the local form separate the two points of a pair iff they are boosts; antidiagonal isometries fix positive lines (`separating_isometry_is_boost`).
- **The successor is unipotent.** `Σ Λ(n)(n+1)^{−s} = −ζ'/ζ(s) − D_Λ(s)` with `D_Λ` holomorphic on `Re s > 0`: the shifted prime source has the poles of `−ζ'/ζ` in the strip with the same principal parts (`succShift_vonMangoldt_eq`).
- **A budget pays a hyperbolic pair only on a finite segment.** A bounded remainder plus `2 Re(w e^{(δ+iγ)t})`, `w ≠ 0`, `δ > 0`, `γ ≠ 0`, exceeds every budget `B` before `log((|K| + |B| + 1)/|w|)/δ + π/(2|γ|)` (`exists_gt_abs_of_hyperbolic`).
- **Resolution is length.** `|p^{iγ} − p^{iγ'}| ≤ log p · |γ − γ'|`; a polynomial correspondence separating two critical symbols by `1` has derivative bound `C` with `1 ≤ C log p |γ − γ'|`; modulation by `cos(γu)` translates the transform instead of acting on it (ACP P11).
- **Sparse annihilators need a lattice.** `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = 1/2` and `N Im ρ log p ∈ 2πℤ`; it never kills an off-line symbol (ACP P14).

Consequence [R]: every multiplicative mechanism is invariant under a symmetry that is hyperbolic exactly at the off-line zeros. This is the common origin of the blindness, half-blindness and isotropy of positive carriers (§1.7), of the growth `p^{Δm}` of Lefschetz sequences (§1.3), and of the failure of averaging to isolate a zero (it averages elliptic phases). A positivity specific to `ζ` must (i) localize at an off-line pair, (ii) have a non-hyperbolic local symmetry there, (iii) live on autocorrelations that change sign at prime-power logarithms.

### 1.2 Weil's argument over `ℤ`, layer by layer

Over `𝔽_q`, for the Frobenius `F` of a curve of genus `g`, Weil's proof has six layers. ACP establishes what each becomes over `ℤ`:

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, Rosati adjoint, `F F' = q` | exact (AOG) | no: they hold on the golden datum `1 − 5X + 5X²` |
| L2 Theorem of the square | graph map `End → NS` is quadratic | free: normalized graphs `N(y)` are quadratic, unique modulo fibres, `deg N(y) = δ(y, y)/2` (`normGraph_square`, `normGraph_degree`); the scale map `a ↦ T_a` satisfies no parallelogram law (`heckeCorrespondence_no_square_relation`) | no: the golden datum has it and a graph of degree `−1` |
| L3 Budget | `δ(Δ, Δ) = 2g`, constant on the Frobenius orbit | free: similitude law; the budget of a test is its Weil norm, constant along every normalized Hecke orbit (`normGraph_degree_act`) | no: golden budget `2`, complex fake budget `4` |
| L4 Kernel counts | `deg P(F) = #ker = Π P(α_i) ≥ 0`; exterior counts `det(c ∓ Λ^k F) ≥ 0` | determinant degree pairs conjugates, nonnegative on every datum without real eigenvalues; the complex fake (`q = 16`, roots `±8i, ±2i`) passes every point count and kernel count and violates Hasse–Weil (`counts_do_not_force_purity`); exterior counts for `1 ≤ k ≤ dim/2`, `c > (√q)^k`, force unitarity in every genus (`unitary_of_exteriorDetDeg_nonneg`); no arithmetic exterior carrier exists | `H¹` counts see real pairs only; the strip zeros of `ζ` are non-real (`zeta_strip_zero_im_ne_zero`) |
| L4′ Spectrum of `f f′` | eigenvalues `P(α_i)P(q/α_i) ≥ 0` | `(β − c)(β⁻¹ − c) ≥ 0` for all real `c` iff `|β| = 1`; at one prime iff `Re ρ = 1/2` (`riemannHypothesis_iff_symSquare_heckeSymbol_nonneg`) | zero-indexed reformulation |
| L5 Rosati positivity | `Tr(ξ ξ') ≥ 0` from a polarization | `⇔` orbit Hodge index `⇔` RH; RH `⇔` every normalized Hecke graph of the cubic spline has nonnegative degree `⇔` the budget is sufficient at every scale, i.e. both graphs of `1 ± T` are effective (`riemannHypothesis_iff_spline_graphs_one_add_sub_nonneg`) | missing |
| L6 Base | even tensor powers over a base, fixed loss (Deligne) | receiver level: `|c(t)|^k ≤ C_k e^{L_k t}` gives width `≤ L_k/k`; linear loss `kσ` iff width `≤ σ`; sublinear or fixed loss iff RH (`riemannHypothesis_iff_fixed_tensor_loss`); golden loss `k log φ` | missing |

The first three layers are identities and hold over `ℤ` intact. What `ℤ` lacks is not a space, a ring of correspondences, a theorem of the square or a budget: it is the sign of layer L5, which over `𝔽_q` comes from Riemann–Roch on `C × C` (counting sections) and an ample class.

### 1.3 Lefschetz theory at one prime: the local–global split

For a test `g` and a prime `p`, `c_m = W(T_{p^m} g, g) = Σ_τ X_τ conj X_{1−τ̄} β_τ^m` is the analogue of `N_m − q^m − 1`; its two-element windows `{g, T_{p^m} g}` are Weil's spans.

- **Growth.** One test serves every prime: `c_m^{(p)} = O(R^m)`, `R ≥ 1`, iff `R ≥ p^Δ` (`zeta_exists_universal_lefschetz_growth`); RH iff `|c_m^{(p)}| ≤ c_0^{(p)}` for all `m` at any single prime (`zeta_riemannHypothesis_iff_universal_minors`).
- **One-sided bounds at one prime.** The two-term test `g + c T_v g` rotates every Frobenius weight into the right half-plane. At one prime, width `≤ θ` iff every test has `ε Re c_m = O(p^{θm})` for a fixed sign `ε`; RH iff every test satisfies the upper one-sided Weil inequality `Re W(T_{p^m} g, g) ≤ W(g, g)`, and iff it satisfies the lower one (`zeta_width_le_iff_oneSided_onePrime`, `zeta_riemannHypothesis_iff_oneSided_onePrime`).
- **Short cycles.** The breaking tests can be taken in `[−η, η]` for every `η > 0` (`zeta_riemannHypothesis_iff_oneSided_short`). RH iff Weil's form is nonnegative on every difference `g − T_{p^m} g` with `g` supported in `[−η, η]` (`zeta_riemannHypothesis_iff_twoWindows`). Hecke translates are Weil isometries, so for `η ≤ 3/10` each window is Weil positive, `Re W(T_v g, T_v g) ≥ ∫|g|²/5000` (`zeta_twoWindows_local_global`).
- **One shift.** For any fixed `v > 0`, e.g. `v = log 2`, RH iff `Re W(T_v g, g) ≤ W(g, g)` for every compact `C²` test, with unrestricted support (`zeta_riemannHypothesis_iff_oneShift`).
- **Zeros as ratios; towers.** For each right zero some test has `c_{m+1}/c_m → p^{ρ−1/2}`; two primes determine `ρ`. For every tempered configuration and scale, some window of some test's tower has `n` negative squares iff there are `n` distinct outer eigenvalues (`tower_law`); a fixed test is blind only behind a wall of positive-area or walled-off folded spectrum (`WolffBlindnessNeedsAWall`); light Blaschke walls are permeable (`masses_eq_zero_of_cauchy_eq_outside`).

Hodge index for `ζ` therefore splits into a **local part**, positivity on short cycles, which holds, and a **Lefschetz part**, the one-sided bound for the correspondences `T_{p^m}` of one prime on those cycles, which is all of RH. Over `ℤ` the receiver side of Weil's argument is complete; the input, a fixed budget that suffices for every `m`, is the L5 sign of §1.2.

### 1.4 The first rung of every cancellation receiver is quasi-RH

Each graded arithmetic-cancellation receiver has a weakest nontrivial statement, and that statement is a fixed zero-free strip `Θ < 1`:

- WL lag or deficit at a fixed rate `σ < 1/2`; PBM convergence on `Re s > 1/2 + α`; the JAS level-one budget;
- the balanced Möbius statistic and the centred-prime band (`balancedStatisticPowerSaving_iff`, `centredPrimeBandPowerSaving_iff`); short-window Möbius and prime saving;
- every power improvement in the Vaughan picture: empty leg, uniform convolution power cancellation, uniform residual Gram power rates, factorial-order-one envelopes, reciprocal-tail gains at every positive damping;
- RW and ACS floors at any rate `< 1/2`; admission of the cofactor receiver at a fixed damping `ε`;
- **power growth of the damped receiver energy** [S]: if `E_ε(T) ≤ C(T+1)^κ`, the Mellin pairing `ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))` is holomorphic on `Re s > (1+κ)/2` and every zero `ρ` with `Re ρ > (1+κ)/2 + ε` translates to a zero `ρ − ε` (`riemannZeta_sub_eq_zero_of_energy_growth`); subpower energy at every damping `0 < ε < 1/2` is RH (`riemannHypothesis_of_subpower_energy`). The trivial exponent `1 − 2ε` gives nothing; a uniform power saving over an interval of dampings is a strip;
- one-sided Lefschetz bounds `ε Re c_m = O(p^{θm})` at one prime (§1.3).

Unconditional arithmetic stops at the Vinogradov–Korobov region (`riemannZeta_ne_zero_vinogradovKorobov`), with the de la Vallée Poussin and Littlewood regions. No cancellation receiver has a target between Vinogradov–Korobov and a fixed strip. Multiplicative forcing and its completed-system form reach the same rung: their collar has width `≍ 1/(d log T)`.

### 1.5 The gauge principle

The gauge torus `G = (ℝ/ℤ)^{primes}` acts on arithmetic sources by the unimodular completely multiplicative twists `χ_x(n) = Π_p e(x_p v_p(n))`. Statistics built from coincidences of products are gauge invariant; additive relations (`ab − cd = h ≠ 0`, affine maps with `b ≠ 0`, the successor) are gauge charged, with gauge mean zero. Multiplicative data determine a finite source exactly up to its gauge orbit (`MultiplicativeDataDetermineASourceUpToGauge`).

- **Möbius: the point `0` is RH.** For every bounded source, Haar-almost every twist has `|Σ_{n≤N} a_n χ_x(n)| ≤ C_x √(N+1)(1 + log(N+1))²`. For `μ` the half-power law holds almost everywhere, fails at the Liouville twin, and at the point `0` is RH (`moebius_gauge_trichotomy`). Its exceptional set is comeager and Haar-null; strong exceptions contain a dense `G_δ`; every finite phase prescription has a twin tail with nonzero linear Mertens limit (`TheMoebiusExceptionalSetIsComeagerAndNull`). Charged boundaries are critical at `σ = 1/4` (`ChargedBoundariesAreCriticalAtAQuarter`).
- **Primes: the point `0` is atypical by its pole.** Almost every twist has `|ψ_x(N)| ≤ C_x √(N+1)(1 + log(N+1))³` (`ae_norm_twistedPsi_le`); `ψ_0(N)/N → 1` (`tendsto_twistedPsi_zero_div`); RH is the statement that after subtracting the pole the point `0` cancels at the square-root scale (`riemannHypothesis_iff_twistedPsi_zero_sub`). For `μ`, RH asks whether `0` is typical; for `Λ`, `0` is provably atypical, and RH asks that the archimedean pole be its only atypicality.
- **Pair and near-incidence statistics are gauge charge.** Successor correlations, the coalescent prime-pair surplus and the near-incidence form beyond the square-root threshold have gauge mean zero and diagonal variance.
- **The archimedean line has a threshold.** Windowed `2k`-th moments of a Dirichlet polynomial equal `‖η‖²` times the gauge moment plus the near-incidence form; below `2rX^k ≤ 1` the near-incidence form vanishes.
- **Amplification loses linearly.** A rate from an amplified observable needs `b_k = o(k)`. Gauge Jensen makes moment amplification lose at least linearly (`MultiplicativeAmplificationLosesLinearly`); every finite family average (characters mod `q`, archimedean windows, any finite weighted family of twists) does too: by family Jensen `(Σ w z)^k ≤ Σ w z^k`, a bound `Σ w z^k ≤ B_k` forces `k log m ≤ log B_k` with `m = Σ w z`, a linear loss whenever the family mean exceeds `1`; equality at order two holds iff the observable is flat on the family, which on a curve datum is unitarity (`family_moment_le`, `mul_log_mean_le_log_bound`, `sq_mean_eq_mean_sq_iff`, `curveDatum_flat_iff_unitary`) [S]. Product receivers of any order see depth only through total length (`ProductReceiversSeeDepthOnlyThroughTotalLength`). Relative powers of `ζ` are `ζ`.
- **On nonnegative tests `ζ` is the worst twin.** The Weil functional is affine in the prime weights; for `f ≥ 0` and every `w ≤ Λ` (sign twins, the Liouville twin, truncations, the prime-free weight), `Re W_Λ(f ⋆ f̃) ≤ Re W_w(f ⋆ f̃)` (`re_weilFullFunctional_vonMangoldt_le_of_nonneg`): positivity on that cone transfers to every dominated twin. A negative atom at `n₀` makes the flipped twin strictly worse (`flipTwin_lt`).
- **The first window through a prime.** A kernel supported in `(−log 2, log 2)` has the same Weil functional for every weight, so the aperture-`3/10` certificate holds for every prime weight. Below `log 3` only the atom at `2` is read; two weights differ by `(w'(2) − w(2)) 2^{−1/2}(k(log 2) + k(−log 2))` (`re_weilFullFunctional_ge_of_odd_window_sub_atom_two`). The odd `[−181/500, 181/500]` certificate holds for every weight with `w(2) = log 2`; for the Liouville twist it holds on odd tests whose correlation at `log 2` is nonnegative and is **undecided** on the rest (`re_weilFullFunctional_liouvilleTwist_odd_window`).

Consequence: an argument that uses only multiplicative data proves its statement for the whole gauge orbit and decides nothing at the point `0`; a positivity argument on nonnegative tests proves it for every dominated twin. A `ζ`-specific sign must use gauge-charged structure: the archimedean place, additive structure, the boundary of finite presentations, or the signs of prime-power atoms. The Möbius boundary of affine maps separates `μ` from its Liouville twin at PNT strength (`moebius_boundary_separates_twin`).

### 1.6 Positivity: pointwise, averaged, at zero ordinates, without localization

- **Exact form.** For every real compact `C²` test: `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫ incoming·G²(C_F)`. The full and odd `H¹` floor-rate sets equal `[Δ, ∞)`, endpoint attained.
- **Pointwise windows.** Full form `≥ ‖f‖²/5000` through radius `3/10`; odd form `≥ ‖f‖²/1000` through `181/500`; primitive Hodge index through `(log 2 + 1/50)/2`.
- **Positivity beyond isotropy without localization.** For `0 < a ≤ 3/10` the carrier `realTestsAt a` is coercively Weil positive, sees both points of every pair (some test is nonzero at any two prescribed Mellin points), and is positive for every prime weight (`positivity_beyond_isotropy_at_finite_aperture`): full fibres, no localization, no source.
- **Short-window averaged positivity.** For `Γ^{99/100} ≤ H ≤ Γ/8`, `0 ≤ A ≤ κ₀ log Γ` and real `F₀ ∈ C²_c([−A, A])`: `H⁻¹∫_Γ^{Γ+H} Q_γ(F₀) dγ ≥ (1/16) log Γ ‖F₀‖² − C₀ Γ^{−1/2} N(F₀)²` (`exists_shortWindow_frequencyAverage_quadrature_pos`).
- **Pointwise reading of the negative part.** `Q_γ(F₀) ≥ −4(A + 1)² e^A N(F₀)² Φ(γ)` at every height, aperture and test; on every such window `|{γ : Φ(γ) > η}| ≤ CH/(η log Γ)`, independent of the aperture and the test.
- **Zero ordinates.** Each window holds `≥ H log Γ/(16π)` zero copies, all but `CH/η` with `Φ(Im q) ≤ η`; there every nonnegative `F₀` has `Q_γ(F₀) ≥ (∫F₀)² − 4η(A + 1)² e^A N(F₀)²`. A set of heights of measure `≥ cH/(A+1) − CH/(η log Γ)` carries `Q_γ(F₀) ≥ (∫F₀)²/4 − 4η(A+1)²e^A N(F₀)²` for all nonnegative `F₀` of aperture `A`. Signed tests keep only the negative floor; by §1.5 positivity on nonnegative tests is shared by every dominated twin.
- **Witness persistence.** A zero's witness at aperture `A` stays negative on an interval of length `2(1 − r/Z(γ))/A`; at `A ≍ log T` an exceptional-height bound excludes an individual zero only below the zero-spacing scale.
- **Aperture flow.** `μ(A)` is strictly decreasing; RH iff `μ(A) > 0` at every finite `A`; on the prime-threshold ladder every birth jump vanishes and RH iff cumulative frozen relaxation `≤ μ(3/10)`. The Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})` excludes every positive exponential floor.
- **Rates.** `0 ≤ Δ ≤ polarRate = groundRate ≤ 1/2`, `RH ⇔ groundRate = 0`; CCM form-norm and Birman–Schwinger rates equal `Δ`; physical-`L²` equality `polarRate = Δ` holds under locally bounded off-line depth and is otherwise open.
- **Finite level.** RH iff every aperture admits some real weight system making the full Weil functional nonnegative on tests supported there.

### 1.7 Realization: blind, half-blind and isotropic carriers

- **Maximality.** `meyerTraceBoundedIdeal`, the sources whose Mellin transform vanishes at every off-line zero, is the greatest sharp-stable convolution ideal with nonnegative trace; it keeps every critical jet, carries restricted Hodge index, RR, Bézout and ampleness, and is the whole source iff RH. Every scale-shift-invariant Weil-nonnegative test space is blind.
- **Coupled isotropy.** For channels coupled by divisor-multiplier operators on a carrier closed under diagonal point convolution, positivity forces the fibres at `ρ` and `ρ*` to be orthogonal for the coupling matrix; positivity on all tuples forces it to vanish at every off-line zero (`coupled_isotropy`). A positive convolution ideal without sharp stability is half-blind; sharp stability gives full blindness. The left-blind ideal is positive, not blind, and equals the whole source iff RH (`leftBlindIdeal_eq_top_iff`).
- **Why.** These are the cyclic-span laws of §1.1: every carrier invariant under multiplicative correspondences sees each off-line pair through a boost, and boost-invariant positivity is isotropy. Finite separating reflection spectra have cyclic positivity iff pairwise half-blindness (`halfBlind_iff_cyclicForm_nonneg`).
- **Topology and synthesis.** The blind ideal is closed in the natural Fréchet topology, closed in a critical-data topology iff RH; critical jets plus the Poisson boundary synthesize the full-jet blind ideal, which is the value-blind ideal iff every off-line zero is simple, and the whole source iff RH.
- **Faithful variants.** Faithful positive degrees, the Hilbert–Schmidt reserve and the bounded-orbit carrier reach RH only together with simple zeros. Origin-`L²` supports no continuous faithful reading.
- **Common pattern.** Every unconditional positivity theorem in the corpus is positivity on a blind, half-blind or isotropic carrier, positivity on average over heights, positivity on a non-localizing carrier valid for every prime weight, or positivity on nonnegative tests shared by every dominated twin. `ArithmeticForcesBlindness` transfers sources supported outside a zero-free region into the blind carrier; that is a transfer, not forcing.

### 1.8 Positive Poisson pairs and the successor

- **Both sides of the explicit formula.** The damped prime measure is finite and positive with characteristic function `Re(−ζ'/ζ)(1+x+iu)`; positive spectral measures for every `C²` test exist iff RH. The prime-free gap sits on the side of the known positivity.
- **Gap rigidity.** A positive tent-self-dual measure with gap `(−1,1)∖{0}` is a Dirac comb; a wider gap forces zero; narrower gaps admit dual-lattice non-combs. With the gap on one side only, a uniform local mass bound.
- **Integer positive-definite functions** on every abelian group are sign characters of subgroups; isolation forces `δ₀` iff the group has no 2-torsion.
- **Two-prime receiver.** RH iff the cubic-spline correlation on `ℤ log p + ℤ log q` is positive definite on `ℤ²`, equivalently the Fourier sequence of a positive measure on `T²`.
- **Affine group.** Affine positivity on `Aff(ℚ)` is induced from the dilations. A prescribed integer successor forces the Hecke weight `(nd)^{−1/2}` and is incompatible with any dilation part continuous at `1`; Hecke states are positive iff `s ≥ 1/2` and Haar-singular for `s ≤ 1/2`; Bost–Connes at `β > 1` forces `(nd)^{−β/2}`.
- **Regularity classes.** For every positive-definite `φ` on `Aff(ℚ)`, `|φ(x ↦ x + rb) − φ(x ↦ x + b)| ≤ 2 φ(1)^{1/2}(2 Re(φ(1) − φ(x ↦ x/r)))^{1/2}`: an archimedean dilation part makes the successor continuous on `ℚ ∖ {0}`, so arithmetic successors (with jumps) and archimedean dilation correlations live in different regularity classes (`norm_successor_dilate_sub_le`).
- **Atoms and continuous spectra.** Atomic archimedean dilation spectra admit only blind successors (`successor_blind_of_atomic_archimedean`); every absolutely continuous one is seen by a nonconstant successor (`successor_sees_autocorrelation`). The extensions of Weil's correlation to `Aff(ℚ)`, read on positive slopes, are exactly the points of the box `Π_γ [0, w_γ]` over the critical zeros (`weil_extension_classification`, `weil_extension_exists`): the non-commutative carrier adds one parameter per zero and no constraint. The zeros are atoms, and the successor is unipotent on their polar fibres (§1.1).
- **Prime-torus split.** Positive-definite functions on `ℚ_{>0}` split uniquely as `f_arch + f_null` (`kronecker_decomposition`); integer and Bost–Connes successors force the null part only.
- **Curve calibration.** Purity ⇔ positive definiteness of the trace sequence on `ℤ` ⇔ Hasse–Weil ⇔ span Hodge index; Künneth–Adams and symmetric-power count positivity is point-count positivity, passed by the golden datum.

### 1.9 Invariants, pole order and completed positive systems

**Degree-one rigidity.** A Borel measure `ν ≥ 0` on `[1, ∞)` with `∫u⁻² dν < ∞` whose theta transform satisfies Riemann's degree-one law is `(−2 Re α) Σ_{n≥1} δ_n`; finite-order completed version with strip decay by Phragmén–Lindelöf; Beurling systems with the completed FE are `ζ`'s. **Stability:** an `L¹` critical-line defect `g` bounds the off-lattice mass by `(6/π)‖g‖₁` and every unit-tent mass within `(18/π + 4κ/π²)‖g‖₁` of `2 Re β`; finite-height prime recovery from small defects.

**The pole-budget-one class is `ℝ^× · ζ`** [L]. Positive-definite vertical sections with `Re(−F'/F)(x) ≤ C√x` make `F` completely monotone, `F = ∫ u^{−s} dμ` with `μ ≥ 0` (`exists_dirichletMeasure_of_posDef_sections`); every `CompletedPositiveSystem 1 d F Λ` has `d = 1`, `F = Kζ`, `Λ = 2Kξ`, `K ∈ ℝ^×`, and conversely (`completedPositiveSystem_one_iff`); its completion vanishes at critical points of arbitrarily large height.

**Relaxation models.**

| Invariant relaxed | Model | Off-line zeros |
|---|---|---|
| Simple pole (pole order 2) | `ζ·(s−β)(s−1+β)/(s(s−1))`, a `CompletedPositiveSystem 2 1` | real pair `β, 1−β` |
| Simple pole, one critical refund | remove Hardy's pair, insert the quartet of `1/2 + a + iγ₀`, `0 < a ≤ 1/4`; a `CompletedPositiveSystem 2 1` | complex quartet |
| Simple pole (pole order 3) | `ζ·quartet/(s(s−1))²` | complex quartet |
| Holomorphy of the completion in the strip | `ζ·quartet/((s−1/2)²−c²)⁴` | quartet, strip poles |
| Riemann's FE | over-regular positive Beurling systems | zeros in `1/2 < Re s < 2/3` |
| Coefficient positivity | self-dual character combinations | uniqueness fails |
| Sign of `ζ` on `(0,1)` | `ζ(s)/ζ(s + 1 − β)` | real zero at any `β < 1` |

**Pole order and zeros.**

- **Conservation.** For finite reflection-antisymmetric deformations, `(Weil-index increment) = (pole-order increment) + R_crit − I_crit`; the absolute inequality `ind₋ ≤ ord₁F − 1` is false.
- **Pole order one is rigid.** A nonzero entire `E` with `E(1−s) = εE(s)` and `−E'/E + ξ'/ξ = Laplace(ν)`, `ν ≥ 0`, on a right ray is `cξ`.
- **Real-zero budget.** `4 ord_{1/2}Λ + 8Σ_{x∈X} ord_x Λ + 5d < 9κ` for every finite `X ⊂ (1/2, 1]`; `κ ≥ 1`, `κ = 1` forces `d = 1`, a simple-pole system has no real zeros.
- **Gauge collapse.** An entire finite-order `E = (s(s−1))^κ G` with the FE, `G` bounded on a right half-plane and `G(σ) → 1`, is a monic polynomial of degree `2κ`.
- **Zero contractions.** The midpoint symmetric-square multiplier `M_β(s) = (s − 1/2)²/((s − β)(s − 1 + β))` has nonnegative Laplace density and contracts a real off-critical pair of any `CompletedPositiveSystem κ d` onto `1/2` at `Δκ = 0`; finitely many steps remove all real off-critical zeros (`CompletedPositiveSystem.contractRealPair`, `exists_real_offCritical_free`). A complex quartet at `1/2 ± a ± iγ` contracts onto the line at pole cost `Δκ = 1` for `a ≤ 1/4` and `Δκ = 2` for `a < 1/2` (`contractComplexQuartet_of_le_quarter`, `contractComplexQuartet`). These are sufficient costs. A contraction of complex quartets at `Δκ = 0` applied to `ζ` would produce a pole-budget-one system different from `ℝ^× · ζ`, hence would prove RH; the complex-quartet multiplier has Laplace density `2e^{t/2} cos(γt)(e^{at/2} − e^{−at/2})²`, which changes sign and grows, so no positive-density contraction at `Δκ = 0` is expected [R].
- **Threshold.** Pole order one is rigid, pole order two admits every off-line type; pole order pays for inserted zeros, not for `ζ`'s own.

**Boundary (MPG).** Nonnegative weights, integer divisor, simple pole and pole isolation force `D = δ₀`, each invariant necessary. A pole of order `k` carries at most `⌊k/2⌋` boundary zeros, every placement realized; every locally finite even positive-definite configuration is the boundary divisor of one Dirichlet series `Σ Λ(n) g(log n) n^{−s}` and of an integral Euler product; the primes of one residue class already realize every summable configuration (`progression_realizes`). For families over a finite abelian group the only unforced configuration is the two-torsion (Siegel) exception. The boundary does not see the interior.

**Completed systems (SBWF).** Sharp collar capacity: every finite set `Z` of zeros with `0 < Im z ≤ T` and `Re z > 1 − w(κ, d, T)`, `w ≍_κ 1/(d log(3 + T))`, satisfies `2Σ_{z∈Z} ord_z Λ ≤ κ`, no separation (`two_mul_sum_order_collar_zeros_le_poleOrder`); sharp at odd `κ`. At `κ = 1` the whole collar `|Im z| ≤ T` is zero-free. A class theorem whose content is boundary capacity and a dlVP-scale collar; no interior rate.

**Interior capacity of finite certificates.** `a₁ ≤ 2cos(π/(K+2)) a₀`; width `(√B − √A)²/G`; cap `(3 − 2√2)/(2L)`; multi-channel certificates split into rational fibres; admissible zero orders `m ≤ (√A + √(Gη))²/B`, with `b(1/2) ≥ 1` for every Fejér certificate once `L ≥ 0.17`. The dlVP region is an instance and optimal for its input.

### 1.10 Heat and divisor geometry

- **Local geometry.** Complete at model level: repair cones, the sharp Hermite root barrier, optimal first heat `a/(2h_{m+2}²)`, universal reflectors (positive monomials only).
- **Large heights.** Every positive heat repairs every sufficiently high radius head.
- **Positive time.** Zeros are real and simple beyond `2π exp((27/40+ε)/t)`; `Λ < 1/8`.
- **Residual.** A bounded-height × small-heat region whose height bound grows like `exp(C/λ)`.

### 1.11 Cofactor modules and escape

On every common limit of the actual cofactor Grams at `0 < ε < 1/2`:

- **Structure.** A cyclic critical-Wiener module. Admission gives a unique full-sequence limit, faithful and infinite-dimensional; escape gives paid ideal ⊆ annihilator and module hull ⊆ obstruction hull. Some actual limit has `K_pp ≥ p^{2ε−2} > 0`; kernel families are singletons or continua; contractions are actual limits; eigencharacters have augmentation modulus or `|χ(p)| = p^{−s}`, `s ≥ 1/2`; visible interior multiplicities and boundary poles bound `dim(A/I_paid)` from below.
- **The cofactor Gram is a translation Gram** [S]. With the log profile `g(u) = e^{−u/2} v(⌊e^u⌋)`, `⟨D_j v, D_k v⟩_T = (√j√k)⁻¹ ∫_0^{log(T+1)} g(u − log j) g(u − log k) du`: dilation is translation, the pronic measure is Lebesgue measure on the log scale (`pronicPairing_rowDilate_eq_translationGram`). Exponential profiles give power characters, so a translated-zero row `n^{ρ−ε}` has Gram `j^{−(ρ−ε)} k^{−(ρ̄'−ε)}` (`translationGram_exp`). Escape states are determined modulo energetically subdominant remainders (`tendsto_normGram_sub_of_subdominant`).
- **The Laplace form** [S]. The Laplace transform of the cofactor profile tends, after the boundary term, to `G(s) = ζ(s)(1/ζ(s + ε) − Re(1/ζ(1+ε)))/s` on `Re s > 1` (`tendsto_laplace_cofactorProfile`); its singularities in `Re s > 1/2` are the translated zeros `ρ − ε`, the pole of `ζ` cancelled by the centering.
- **Escape rows are translated zeros.** On power rows the renormalized cofactor acts by `ζ(s + ε)`; on every finite exponent window the power-log eigenspace has dimension `Σ ord_{s+ε} ζ` (`powerLogRows_global_renormalizedInversion_iff_order`). For `1/2 < Re s < 1 − ε`, `ζ(s + ε) = 0` iff there is a zero-origin row of infinite pronic energy with finite-energy errors in both dilation laws at `2` and `3` and in renormalized inversion (`riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow`). Nonresonant finite-rank escape rows on a common line are sums of zero powers, and a zero-free translated line forces finite energy (`exists_finiteRank_zeroPower_decomposition`).
- **Spectral reading.** The critically normalized asymptotic part of every actual escape kernel is a finite positive measure on the prime torus of mass `≤ 1`, Haar iff its off-diagonal coefficients vanish (`exists_actualCofactorLimit_spectralMeasure`); its mass is `inf_d dK(d,d)`, equal to `1` under admission and `0` under two-sided power growth of the energy (`TheGaugeMassOfAnEscapeStateIsItsEnergyRatio`). Gauge-mass criterion [P]: RH iff every actual common cofactor limit at every `0 < ε < 1/2` has positive gauge mass; the extraction of a zero-mass limit from energy that is not subpower is not formalized.
- **Completeness reduced to an energy split** [S]. Every escape state of the actual row is generated by translated-zero rows exactly when the row splits as a finite or summable combination of those rows plus a remainder of negligible pronic energy against the row's; equivalently, after the residue exponentials of `G` are removed, the remaining profile has subdominant energy. Without such a split nothing forces completeness: a white-noise remainder of comparable energy satisfies every proved kernel constraint.
- **Euler laws.** The eta transform is pole-free with symbol `η(s + ε)`; Euler laws at `2` and `3` determine the pole trace; one law leaves a periodic ghost; twisted laws force tied exponents.

### 1.12 Vaughan calibration and the half-damping transition

- **Above half damping.** A common critical-Wiener majorant pays every centred piece; the infinite Gram of the limiting rows is PSD of rank two.
- **At half damping.** Finite moving Gram limits are `G_{1/2} + ℓ·ssᵀ`, every `ℓ ≥ 0` realized; the product horizon selects `ℓ = 0`.
- **Below half damping.** Leading-order limits are classified; the residual below `T^{1−2ε}` is open, and every power improvement of it is a fixed strip.
- **Long moduli** [S]. The centered divisor prefix is a short sawtooth plus the actual long-modulus quadrature, the harmonic tail retained with its sign; at the square-root cutoff the short part has bounded pronic energy with exponent `(1−ε)/2` and explicit constants; the long-modulus function is integrable with integral the full harmonic tail, and its integer samples count hyperbola incidences (`LongModulusExactDecomposition`, `LongModulusShortEnergy`, `LongModulusIntegrableProducer`). The open part of small-damping admission is the signed control of this long-modulus quadrature.
- **Endpoint invariants.** Tail-rate suprema are `1 − Θ` and `4(1 − Θ)`; attaining the endpoint forces simple boundary zeros; the endpoint tail oscillates.
- **Hypercube.** `Q_{1/2}(P)` is bounded over every squarefree `P`; sub-half paid multiplicative patterns have integer local exponents.

### 1.13 Payment domains and observation

- On the normalized one-prime coefficient space the payment domain `{g : partial sums ∈ ℓ²}` is not closed; its closure is the kernel of total evaluation, the continuous dual of the quotient is one-dimensional and the closure gap has Hamel dimension continuum. Payment is controlled by the graph norm, not by closure.
- **Closed-cycle observation** [S]. On controlled classes of actual smooth sources, finite closed-cycle data recover the correlation up to an explicit mesh error, with noise amplification linear in the order (`controlled_mesh_recovery`, `derivative_correlation_recovery`); inside one constructed singular-energy class the exact floor-plus-one detection ambiguity persists (`ControlledSharpCycleSources`). Observation is recovery, not a sign.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, incoming-deficit, critical-energy and coprime cross-work receivers read `Δ` exactly, endpoint attained; RH ⇔ `E` bounded ⇔ cross-work bounded below ⇔ `∫₀ᵀE = O(1+T)`. Zero copies with `|γ| ≥ e^{T/2α}` contribute `O(1)`, so `E` reduces to a finite low-zero head. The filtered deficit decays like `Γ^{−1/2}` on frequency averages over `[Γ, 2Γ]` for `α < 2/3`. Two primes suffice on mixed lags. Compact logarithmic producers converge in physical `L²`; finite closed-cycle data recover correlations on controlled sources [S].
**(a)** W2–W4. W7(i): an averaged bounded-energy statement from the high-zero tail and the filtered law. W6: the filtered deficit on short windows.
**(b)** B1.1 (bounded `E`). B2.1 (any fixed rate `σ < 1/2`). B1.4 (from frequency averages to the actual head).
**Walls:** 1.0, 1.1, 1.15, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; shell flux = frozen relaxation + arithmetic jump bracketed by collar correlations; on the prime-threshold ladder RH ⇔ cumulative relaxation `≤ μ(3/10)`. Ground rate = polar rate. Short-window averaged positivity and the off-line-field floor apply to the complete form; the local part of Hodge index (short windows `≤ 3/10`) holds (§1.3).
**(a)** W2/W5: certified low-sector matrices and further windows. W7(ii): one rate dictionary. W4: the short-window, zero-ordinate and short-cycle theorems in RW's ground-energy coordinates.
**(b)** B1.3 (sign at every aperture; equivalently the Lefschetz part on short cycles). B3.6 (signed collar estimate on the moving ladder). B3.1 (`polarRate = Δ`). B1.4.
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
**Status.** Current, Bernstein-mismatch and signed-moment receivers are RH-equivalent. Each fixed Hausdorff order is positive beyond its shift threshold; RH ⇔ nonnegativity at every order below its threshold. The centred order-24 finite moment sign closes through kernel-checked integer cell certificates.
**(a)** W2/W5: further orders.
**(b)** B1.5: low shifts across unbounded orders. B3.12: order-uniform thresholds.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; either one-sided `O(√x)` bound forces RH with simple zeros. Proved: prime-root and composite-order minor arcs, all-modulus `Q^{−δ/32}` saving, diagonal reduction, balanced and centred-prime bands ⇔ `Θ < 1`, the Vaughan picture of §1.12, the visible-pole index on the Liouville orbit. On the gauge orbit of `μ` the half-power law holds almost surely, its exceptional set is comeager and Haar-null and contains the Liouville twin, and at the point `0` it is RH; the charged harmonic-tail receiver is critical at `σ = 1/4` for twisted mean squares.
**(a)** W3/W4: apply row estimates in their ranges.
**(b)** B2.1 (band saving is exactly quasi-RH). B1.1 (global cancellation, equivalently typicality of the gauge point `0`). B2.6 (power-saving sign correlations). B3.24 (a charged estimate at `0` beyond the threshold).
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
**Status.** Exact forcing-sign dictionaries; prime-blind receivers are RH-equivalent; finite `D` is even and RH ⇔ `D < 2`. One prime tower carries the whole Hodge defect at all but finitely many primes. The one-prime Lefschetz receivers of §1.3 apply in full: one-sided bounds at one prime, short cycles with the local part proved, one fixed shift `v`. Full-cone source selection identifies `Λ`; positive-measure rigidity identifies the source among positive measures with the theta law. The two-prime orbit is a Bochner problem on `T²`. In correspondence terms (§1.2) the scaling surface carries normalized graphs with the theorem of the square and a free budget; HF's sign is the L5 layer.
**(a)** W2, W4.
**(b)** B1.3 (the pairing sign; equivalently the Lefschetz part on short cycles, or sufficiency of the budget). B1.7 (`D < 2`). B1.9 (fixed tensor loss). B2.2 (finite index). B3.10 (compatible oriented families). B3.5 (a section count on the correspondence surface).
**Walls:** 1.3, 1.4, 1.17, 3.13, 14.2, 14.4, 14.18.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state lies above `1/2`; one-signed bound states vanish, sign-changing ones are not excluded. Fixed-aperture completion, sharp cuts, generator-domain preservation and window nodal convergence are proved.
**(a)** W3/W4; W4 for the short-window averaged and short-cycle forms.
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
**Status.** Cofinal small-damping admission and global Haar approximation are RH-equivalent. The size-truncated receiver equals the full natural form; its exterior is paid; `ε = 1/2` is paid for every squarefree support. The cofactor structure of §1.11 holds: translation-Gram and Laplace forms with symbol `G(s)` [S], rank-one escape rows ⇔ translated zeros, finite-rank escape decomposition [S], prime-torus spectral reading and gauge mass. Polynomial energy growth translates zeros, and subpower energy at every damping is RH [S]. The centered divisor prefix splits into a bounded short sawtooth and the long-modulus quadrature [S]. Reconstruction from (residual, trace) is injective but only algebraic.
**(a)** W3/W4: Vaughan bookkeeping. W7(viii): the energy-rate law of the damped receiver. W12: integration of the translation-Gram, Laplace-form, long-modulus and finite-rank sources.
**(b)** B1.2 (signed small-damping energy; equivalently signed control of the long-modulus quadrature). B3.2 (escape completeness as an energy split). B3.3 (quantitative coercivity). B3.11 (sub-half forward interior). B3.16 (paid ideal on escape).
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
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; literal positivity on high dyadic, polynomial and lacunary windows; full-cone source selection; finite-level existence ⇔ RH; critical Nyquist finite-part tools with explicit signed witnesses.
**(a)** W2–W5.
**(b)** B1.3: low and mixed modes on an RH-complete cone.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay is RH-equivalent; an off-line zero forces a late positive charge floor; truncations converge strongly.
**(a)** W2.
**(b)** B1.5: rank-uniform decay from the source.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity is RH-equivalent; continuum light-cone variation positive; reflected-prime source positive on nonzero odd tests; fixed-support subunit collar paid; lattice Schur payment reduces to a finite head. The odd `181/500` window is the first certificate that reads a prime; it is weight selective at the atom `2` only (§1.5).
**(a)** W2–W5. W8: the odd window for the Liouville twin.
**(b)** B1.3: full reflected-prime and polar payment.
**Walls:** 1.3, 1.18, 3.4.

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
**Status.** One fixed-width late-lag family decides RH at every admissible width; smooth detector at aperture `Cδ^{−2}(4+|γ|)²`; the single-height phase-selective law holds; eventual all-height saving is refuted; phases recur syndetically. The one-prime Lefschetz receivers of §1.3 apply (one-sided at one prime, short cycles, one shift). On short windows almost every height and almost every zero ordinate is nearly positive (§1.6).
**(a)** W3/W4; W6.
**(b)** B1.4 and B1.1 (horizon containment and the late-lag sign). B1.3 (the Lefschetz part on short cycles). B1.9 (fixed tensor loss). B3.20 (signed near-coincidence cancellation at one height).
**Walls:** 1.17, 3.1, 3.2, 3.14.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift `a > 0` against all even compact profiles decides RH; antisymmetric light-cone kernel positive; subunit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3: one shift must pay the reflected half-collar for every profile.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation up to `Ke^r e^{−c√r}` (rate `1/2`); horizon-uniform Schur payment to a finite head; active cosets and top-octave dominance; exact shared-budget descent (excess `kB`). The Rosati trace form is one budget for the whole correspondence ring; frustration is its negative index (ACP §6.10).
**(a)** W2/W5.
**(b)** B1.3 (one shared signed budget). B3.8 (nonlocal frustration calculus).
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Exact source identity; RR exact at every aperture; reserve boundary rigidity; positive majorants give Bézout and ampleness, never RR; finite readings with mass never give Bézout.
- Maximal blind ideal with its geometry, topology and synthesis; coupled carriers isotropic; positivity beyond isotropy only without localization (§1.6, §1.7).
- Averaged positivity on windows `Γ^{99/100}`, the off-line-field floor, positivity at almost every zero ordinate for nonnegative tests (shared by dominated twins).
- Lefschetz receivers at one prime and the local–global split (§1.3).
- Weil's layers over `ℤ`: theorem of the square and budget free; kernel counts blind to complex quartets; exterior counts force unitarity over `𝔽_q`; symmetric-square spectrum is the sign; tensor loss is the base (§1.2).
- Invariants: degree-one rigidity and stability; relaxation models; conservation; κ = 1 rigidity and `ℝ^× · ζ` class; real-zero budget `5d < 9κ`; sharp `⌊κ/2⌋` collar; real zero pairs contract at `Δκ = 0`, complex quartets at `Δκ ≥ 1` in the constructions (§1.9).
- Rankin–Selberg square: for a finite polar source `F = Σ m_j/(s − z_j)`, `F² = Σ m_j²/(s − z_j)² + Σ 2m_jE_j/(s − z_j)` with the field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`; `Re E_j = 0` on critical configurations, `Re E_j > 0` at the deepest off-line point with its reflection present (`re_fieldAt_pos_of_deepest`).
- Zero census: simple-or-critical fraction `≥ 0.8876`; distinct critical ordinates `≥ 0.8042`; TTPC `N₀* ≥ (29/36 − β − ε)N`, where the surplus `β` is gauge charge.

**(a)** W1 (battery). W7(iv): effectivity as exhaustion. W7(v)–(vii): the harmonic collar from the MPG/SBWF calibration, conservation for infinite corrections, one capacity law. W11: optimal cost of complex contraction.
**(b)**
- B1.6: forcing or exhaustion by an input outside the exhausted classes.
- B1.8: faithful variants need simplicity.
- B1.9: fixed tensor loss.
- B3.5: a section count on the correspondence surface.
- B3.25: a localizing carrier with non-hyperbolic local symmetry.
- B3.27: an arithmetic exterior count.
- B3.28: the Rankin–Selberg field for the actual source.
- B3.18: the even-`κ` equality case of collar capacity.
- B2.5: the coalescent surplus at the gauge point `0`.

**Walls:** 1.3, 1.15, 1.17, 3.8, 3.14, 3.18, 14.4, 14.8, 14.10–14.19.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6: construct the object before its sign and prove the sign independently. Seven theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight (§1.6, §1.7);
- a carrier built from multiplicative correspondences acts hyperbolically at every off-line pair and can force at most isotropy; the successor is unipotent and forces nothing (§1.1);
- positivity on nonnegative tests is shared by every dominated twin of `ζ` (§1.5);
- finite multiplicative certificates are capped by growth input; completed systems carry only boundary capacity and a `1/log T` collar (§1.9);
- a mechanism must separate `ζ` from the relaxation models of §1.9, which keep `Λ ≥ 0` and the exact FE at pole order two; pole order pays only for inserted zeros;
- a mechanism built from multiplicative data alone proves its conclusion for the whole gauge orbit (§1.5);
- a kernel-count (determinant) effectivity is blind to complex quartets, hence to every strip zero of `ζ` (§1.2).

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

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read `Re ρ = 1/2` with exact depth laws; in local-type language they read whether the Hecke symbol of a zero is elliptic. They detect blindness; they do not force it. FEL is the zero-side analogue of the Hamburger squeeze: a nonnegative functional vanishing exactly on critical zeros, without the arithmetic upper bound that would force it to zero. RFHM, SC and the candidates fed by multiplicative weights (W1C couplings, MSC) must also state which gauge-charged datum they use and the local type of their symmetries at off-line pairs.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; diagonal reduction; balanced and centred-prime bands ⇔ `Θ < 1`; Kloosterman Parseval; the half-damping transition (§1.12); every power improvement ⇔ a fixed strip. | W4 | B2.1; B1.2 |
| **ADR / AOT** cofactor modules | §1.11: record minima, contraction calculus, eigencharacter moduli, finite hulls, visible-pole index, ζ- and η-symbols, translated-zero eigenstates, rank-one and finite-rank escape rows, two-factor pole trace. | W12 | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates, long moduli | §1.6; the long-modulus decomposition of the centered divisor prefix [S]. | W7(ii), W12 | B3.6, B3.1; B1.2 |
| **ACS / Meyer** | §1.3, §1.6, §1.7. | W7(iv) | B3.5, B3.25; B1.6, B1.8 |
| **ACP** correspondence positivity | §1.1, §1.2: normalized graphs and the free theorem of the square; free budget and its sufficiency; determinant versus Rosati; local types; successor unipotent; non-localizing positivity; worst twin; base as fixed loss; affine maps of genus zero; resolution = length; finite budgets against hyperbolic pairs; sparse annihilators; Rankin–Selberg field; exterior counts; zero contractions; translation-Gram and Laplace forms of the cofactor [S]; family-average loss [S]. | W8, W9, W11, W12 | B3.25, B3.27, B3.28, B3.29, B3.30; B1.3 in Rosati form |
| **APD** positive duality | §1.8 and the invariant half of §1.9: Poisson rigidity, sign characters, lattice and `ℚ_{>0}` Bochner, affine induction, Hecke and Bost–Connes states, Kronecker split, successor regularity, Weil extensions = box over critical zeros, quantum budget, blind-ideal topology and synthesis, coupled isotropy, theta-law stability, curve calibration. | W12 | its third forcing instance is B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, regularity, decay law, families and the Siegel exception, arithmetic and integral Bochner, progression realization; interior capped (§1.9). | W10 | — (complete below RH strength) |
| **SBWF** strip Bochner–Weil forcing | Coupled height form and its shadows; completed-system capacity with sharp `⌊κ/2⌋` collars; κ = 1 exception-free collar; reflection identity and `5d < 9κ`; gauge collapse; κ = 1 rigidity; complete monotonicity of positive-definite sections; the κ = 1 class `ℝ^× · ζ`; κ = 2 realizations. | W7(vii) | B3.18 |
| **ACG** correlation geometry | §1.5: gauge invariance, a.e. square-root cancellation, comeager-null exceptional set, prime source typical modulo its pole, gauge charge of successor, pair and surplus statistics, archimedean-line threshold, linear loss law, Möbius boundary separation, witness persistence, escape spectral measures and gauge mass, energy-growth translation of zeros [S]. | W9, W12 | B1.9, B3.20, B3.24 |
| **AKT** Künneth theory | Product receivers see depth only through total length; product moments diagonal below the threshold; Künneth positivity = point-count positivity. | W9 | B3.27 |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; spline orbit; base theta `h⁰` with RR and Mellin. | W4 | B3.10, B3.5; B2.2 |
| **ALDG** local divisor heat | §1.10. | W7(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; wide windows; grid tents; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering, observation | Endpoints; high-zero tail; filtered deficit; compact logarithmic producers converge in physical `L²`; closed-cycle recovery on controlled sources [S]; finite-window doubling incidence on perturbed nodes [S]. | W6, W7(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt; boxes. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3` and lag-2 `1/4` floors exact; complex floor in `[−1/2, −1/3]`; zero-defect signs have `f(2) = −1`; half-damping hypercube endpoint. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half damping. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure (§1.13); chirp phase group. | — | B3.3 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`; the surplus is gauge charge. | — | B2.5, B2.7, B3.24 |
| **Analytic inputs** | Guth–Maynard; 30/13 and Ingham–Huxley density; Selberg near-line density on windows `U^{99/100}`; Heath–Brown all-length; sharp `S₂`; KKL; dlVP, Littlewood, VK; FE/count fluctuation; Hamburger rigidity and stability. | W6, W10 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - Whether a correspondence ring over `ℤ` has a theorem of the square: normalized graphs have one, for free; it holds on the golden datum and carries no budget. The Hecke scale map has none; scale addition is not ring addition.
  - Whether `ℤ` lacks a budget: the budget is free (similitude law); its sufficiency at every scale is RH.
  - Positivity beyond isotropy: exists on non-localizing carriers, for every prime weight; localizing multiplicative carriers are hyperbolic at off-line pairs, hence isotropic; the successor is unipotent.
  - Kernel counts as effectivity: blind to complex quartets; only the spectrum of symmetric squares, or exterior counts over `𝔽_q`, see them.
  - The base at receiver level: fixed tensor loss ⇔ RH; linear loss ⇔ the strip.
  - Archimedean–finite coupling through the successor: never reaches atomic (zero) spectra; Weil's extensions are a box over the critical zeros; arithmetic successors and archimedean dilations live in different regularity classes.
  - The pole-budget-one completed class: `ℝ^× · ζ`.
  - One prime suffices for one-sided Lefschetz bounds; short cycles suffice; one shift suffices; local positivity on short cycles holds.
  - Family averages and gauge moments as amplification: linear loss; zero loss iff flatness (unitarity on curves).
  - Invariant completeness in degree one; the absolute pole-order budget (false); the rigidity threshold (pole order one rigid, two admits every off-line type); interior multiplicative forcing beyond growth input (excluded); coupled height channels (boundary capacity and `⌊κ/2⌋` collar).
  - Closedness and spectral synthesis of the blind ideal; coupled positivity on point-stable carriers (isotropy); successor coordinates as a coupling to Weil's correlation (none).
  - Averaged positivity on windows `Γ^{99/100} ≤ H ≤ Γ/8`; translated zeros as cofactor eigenstates on finite windows and as rank-one escape rows; the cofactor Gram as a translation Gram of the profile with Laplace form `G(s)`.
  - Summation-scope "defects": none ever existed (Mathlib parses the `∑` body at precedence 67).
  - Polar versus full ground-energy rate: equal.
- **Completed constructions.** Filtered and short-window averaged coercivity; zero-ordinate and positive-measure height positivity for nonnegative tests; CHMD generator domain and sharp windows; Suzuki compact-`L²` and moving-window limits; Heath–Brown all-length and sharp `S₂`; the smooth detector; endpoint attainment; base theta `h⁰`; Hermite optimal heat; large-height head repair; the maximal blind ideal, its topology and synthesis; the left-blind ideal; boundary forcing, capacity, regularity and arithmetic Bochner realization; the exact Fejér barrier, growth-to-forcing law and quantum budget; positive-measure rigidity and stability; Poisson gap rigidity; lattice and `ℚ_{>0}` Bochner; affine induction; Hecke and Bost–Connes states; the Kronecker split; the sharp collar and κ = 1 collar; the real-zero budget; the κ = 1 class; real-pair zero contractions; normalized graphs and the budget law; determinant and Rosati degrees; local-type laws; exterior counts over `𝔽_q`; the half-damping hypercube endpoint; the Vaughan transition; record-minimum cofactor limits, contraction calculus, visible-pole index, ζ/η symbols and eigenstate classification; one-prime Lefschetz receivers and short cycles; sparse-spectrum annihilators; finite-level existence ⇔ RH; the PA order-24 finite moment sign.
- **Excluded mechanisms.**
  - positive exponential aperture floors; eventual all-height phase saving;
  - non-monomial universal reflectors; finite readings, with or without mass, as Bézout sources; origin-`L²` faithful cohomology;
  - PSD, dilation and antipodality as escape exclusion; augmentation as the unique escape state;
  - permanently frozen finite prime families; finite-dimensional affine-unitary successor carriers;
  - single-channel sharp-stable positive ideals, coupled point-stable carriers, and non-localizing carriers, as forcing carriers;
  - free affine extension, prescribed integer successors and the successor in general as constraints on Weil's correlation;
  - harmonic positivity without pole simplicity or with harmonic poles; more frequencies or height channels against a fixed growth payment;
  - decaying count error under the FE; `Λ ≥ 0` plus the exact FE without the simple pole or strip holomorphy;
  - pole order as payment for `ζ`'s own off-line zeros; Wiener closure as a substitute for payment;
  - multiplicative (gauge-invariant) data, moments, family averages and tensor products as sources of a sublinear loss; Künneth or symmetric-power count positivity as purity;
  - the theorem of the square, a fixed budget, or determinant (kernel-count) effectivity as the missing ingredient of Weil's argument;
  - positivity on nonnegative tests as a `ζ`-specific sign;
  - gauge-averaged or almost-sure cancellation as a bound at the gauge point `0`;
  - averaged or almost-every-height positivity as exclusion of an individual zero above the zero-spacing scale.
- **Substitutions that do not hold.** Orthant for signed positivity; cone positivity for self-adjoint confinement; finite for all ranks; local payments for one budget; finite-aperture for global index; averages for selected heights; nonnegative tests for the full cone; algebraic for bounded inverses; zero-indexed objects for pre-divisor constructions; imported for forced regions; a zero-free-region transfer for a forcing law; boundary capacity for interior depth; isotropy for blindness; the gauge orbit for the gauge point; product positivity for correspondence positivity; determinants for Rosati traces; a free budget for its sufficiency; global positivity for fibre information without localization.
