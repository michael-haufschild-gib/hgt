# Producer loop (Opus session 2026-10-12) — working log

- **ID:** producer-loop-opus-2026-10-12
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP LEDGER (one row per cycle)
- **Statement:** Attack the missing producer of a live route by conjecture → proof/kill → next. Formalize every
  dependency-closed positive survivor (unconditional, standard axioms, wired into `RHTower.lean`).

## Big picture (corpus-derived, 2026-10-12)
- Every live route ends in an RH-strength producer; the corpus card `producer-needs-saturation-2026-10-11`
  records that no producer Need is both non-RH-strength and significant.
- Common obstruction: one resolution limit. Weil positivity of Λ has no slack (`μ_a ≤ exp(−e^{2a})`), so a
  producer must be exact; exact identities with known error annihilate the zeros they would detect
  (detection–knowledge duality); every known positivity over ℚ that is not Weil positivity itself is capped
  (1-line, averaging, parity, statistical).
- Kill-standard countermodels exist for every ingredient subset except FE ∧ Euler ∧ Λ≥0 ∧ tempered.
- Ladder [L]: RH ⟹ FOL ⟹ ZAL ⟺ (LH ∧ cosine-KKL) ⟹ LH ∧ quasi-RH. Large-height producers are capped at ZAL.
- HF split [L]: RH ⟸ existence (PBAP: Γ and {log n} only) + uniqueness U. Existence ⟺ ∃ integer λ whose
  `H_λ(s) = Σλ(n)n^{−s} − 1/(s−1)` is analytic on `Re s > ½` with `Re H_λ ≤ Re(Γ_ℝ'/Γ_ℝ(s) + 1/s)` there.

## Cycle ledger
| # | Conjecture | Attack | Verdict | Lesson |
|---|---|---|---|---|
| 1 | PBAP controllability: at aperture a there are e^{2a} free atom weights but only ≈4a/π negative archimedean directions, so admissible weights exist at every level | Perturb Λ near an off-line zero at height γ₀ by δλ(n) ∝ n^{½}cos(γ₀ log n)w(n); its effect on tests at height τ is a Dirichlet kernel in τ−γ₀ with negative lobes | **KILLED [P]** | No slack: margins at other heights are ≤ exp(−e^{2a}) under any RH-like profile, so no finite-level control repairs an off-line zero. Existence arguments must be exact. |
| 2 | Dilation virial at first contact (RW): the null vector f at the first contact aperture a₁ cannot exist | For λ>1, `Q(f_λ) = Q(f_λ−f)` (null vector, `f_λ−f` in the aperture), while the dilation formula gives `Q(f_λ) = O(λ−1)`; an edge jump J gives `Q(f_λ−f) ≥ cJ²ε log(1/ε)` from the log-Lévy kernel | **SURVIVOR [P], not RH** | First-contact null vectors have no edge jump and zero virial `∫|f̂|²uŴ'(u)du = 0` when Hölder at the edge; log-Laplacian boundary killing gives the edge law `f(x) ≈ 2R(a₁)/log(1/(a₁−x))`. Consistent with corpus boundary roughness; no contradiction. |
| 3 | Lee–Yang fake zeta: D(s) = P((p^{½−s})_p) with P polydisc-stable gives a Weil-positive integer weight system | Stability puts all zeros on Re s = ½ and log D has integer support | **KILLED [P]** | On the line the a.c. part of Re D'/D is the constant −½ log N (N = Π p^{deg_p}); Weil positivity needs ½A(t) − ½ log N ≥ 0 a.e., false for small t, and finite P has no pole at 1. For ζ under RH the same density is exactly −½A(t): ζ is a Lee–Yang object with effective conductor e^{A(t)}. Covered by W1C field-density laws. |
| 4 | Two-point Schwarz–Pick inequality for ξ'/ξ with respect to Re s > ½ holds at all points with Re s ≥ 1 | Zero expansion: critical zeros give rank-one PSD blocks, an off-line zero gives D(J − (2β−1)C)D* | **KILLED as unconditional [P]** | A zero at depth (log t)^{−2/3} below the 1-line makes the off-line block ≍ (log t)^{4/3}, above the critical background ≍ log t. Only Re s ≥ 1+η at large height survives: insignificant. |
| 5 | Laguerre–Bochner: each higher Laguerre expression of Ξ is a positive-definite function of t | `L_k(t) = c_k∫e^{itw}K_k(w)dw`, `K_k(w) = ∫z^{2k}Φ((w+z)/2)Φ((w−z)/2)dz ≥ 0` | **BRIDGE [P]** | RH ⟺ every K_k is positive definite. Classical Csordas–Varga representation; no sign. |
| 6 | Jensen + integrality with resonance-chosen centres excludes zeros in near-line discs | Jensen count < 1 forces 0 | **KILLED [P]** | Needs O(1) control of log|ζ| variation on the disc; near the line log max|ζ| ≳ μ log t. |
| 7 | Existence via λ ≡ 1 on n ≥ 2 (H = ζ − 1 − 1/(s−1) entire) | Herglotz test | **KILLED (corpus MUST-815)** | Resonance peaks exp(c(log t)^{1−σ}/log log t) beat ½ log t; any Weil-positive λ needs fake zeros on the line (Conjecture Ω). |
| 8 | Heated positivity at t ≥ κ/log x excludes off-line pairs via collision times | Zero dynamics `ż_k = 2Σ 1/(z_k − z_j)` | **KILLED [P]** | The real-zero background pulls every pair to the axis at rate ≈ ½ log x, so all pairs collide by time O(depth/log x): heat positivity is depth-blind (corpus agrees). |
| 9 | Log-concavity of Φ forces the first Laguerre inequality for Ξ (excluding isolated near-double pairs) | Perturb a log-concave kernel with an LP transform having a double zero | **KILLED (corpus `LaguerreKernelCounterexample`)** | Positivity, evenness and log-concavity of the kernel are blind to the Laguerre sign. |
| 10 | Integrality with harmonic weights: count zeros in a near-line disc by Green's identity with Δφ supported where log|ξ| is explicit (σ > 1, σ < 0), and use the sub-unit bound | φ harmonic on the strip with φ ≥ 1 on the disc | **KILLED [P]** | Harnack spreading: a harmonic weight ≥ 1 on a disc at depth δ is ≳ 1 on a region of size ≍ ½ containing ≍ log t critical zeros, so the weighted count is ≫ 1. A convex weight ψ(σ) = (σ−½)²/δ² kills the critical zeros but turns the count into Littlewood's depth moment, whose Jensen bound is the Selberg-type (T/4π) log log T (wall 2: mean vs uniform). |
| 11 | MSS interlacing families / real stability: Ξ(√x) is an expected characteristic polynomial of an arithmetic random PSD ensemble | Mixed characteristic polynomials are real-rooted for any independent rank-one ensemble | **KILLED [P]** | Coefficients of a real-rooted genus-0 function are elementary symmetric functions of its reciprocal roots; any ensemble realising Ξ's moments b_k must encode the zeros (circular). Cosine mixtures E[cos(tU)] have no common interlacer unless U is deterministic. Consistent with CANNOT-497 (Ξ is LP-maximal: no slack for any stability-preserving construction). |
| 12 | PBAP on the cone of nonnegative autocorrelations (φ = f⋆f̃ ≥ 0, f signed): the arch+pole form is ≥ 0 on every nonnegative PD φ, with no blindness needed | Pointwise relaxation gives −0.154; triangles give min ≈ +0.156 at width 0.6; Gaussians ≈ +0.12; dual certificates h ≤ 2cosh(x/2) with ĥ ≥ −A fail (band–height trade-off) | **OPEN, numerically delicate** | True infimum is a few percent of |A(0)| = 5.372; settling it needs certified enclosures (computation), so it is parked. If true it would contain the corpus window inequality. |
| 13 | JAS thin-prime compensation: for every finite large-prime set P with Σ_{p∈P} p^{−½} ≤ K, the dressed aggregate is PSD at σ = 1 | Torus mean of the aggregate is Σ_ρ 1/(ρ(1−ρ)) = 2+γ−log 4π > 0; fluctuation per zero ≤ (e^{CK}−1)/|ρ|² | **KILLED as unconditional [P]** | Bounding the fluctuation needs to know which zeros are critical; without zero verification the off-line block cannot be separated from the critical mean. |
| 14 | PBAP-full as a positive-definite uncertainty principle: every PD φ with φ(0)=1 vanishing on log ℕ≥2 has I(φ) = 2∫₀^∞[ω(1−φ) + 2cosh(x/2)φ]dx ≥ |A(0)| = 5.372 | Relaxations: √(1−φ) subadditive, |φ| ≤ 1, pinning at log n | **REDUCED [P]** | Relaxed minimum ≈ 5.3 < 5.372 (blindness is never active at the minimiser, which has support < log 2), so the full Bochner structure and the cosh-weighted negative lobes decide; the dual is existence of weights (circular). New reading: Ξ-divisible blind tests ((N1) witnesses) are exactly the equality cases of PBAP, so HF's two producer inputs are one extremal problem; no slack. |
| 15 | Blind-test pole identity: for prime-blind F, ∫ζ(½−iτ)|F(τ)|²dτ = ∫|F|² − 2πF(i/2)F^#(i/2) | Σ_n φ(log n)n^{−s} ≡ φ(0) on Re s > 1, continue in s across the pole of ζ(s−iτ) | **SURVIVOR [P], dictionary** | The pole term of a blind test is a critical-line ζ-moment; PBAP-full becomes ∫|F|²[κA(τ) + κ'(1 − Re ζ(½+iτ))]dτ ≥ 0 on blind tests. Exact, but it is the regularised statement that blind tests annihilate Σ_{n≥2} n^{−½−iτ}: no new sign. |
| 16 | TG partial producer, quantitative: at every fixed distance c > 0 from the line, the right discs D_n(σ₀, r) containing a zero of ξ number ≪ X^{(A(½+c)+ε)(½−c)} (Ingham–Huxley), uniformly in σ₀, r | Inject one zero copy per exceptional disc into dyadic Ingham–Huxley boxes | **PROVED [L]** | Module `RHTower/XiRightDiscSeamContractionInghamHuxley` (standard axioms, wired): `exists_card_badUniformDiscs_le_inghamHuxley`, `exists_card_badUniformDiscs_le_rpow_lt_one`, and the reusable cumulative count `exists_ncard_zeroCopyRange_le`. Exponent 1 − 4c/3 + O(c²) near the line, replacing the corpus 1 − c/28 (near line) and (16/5)(1 − σ₀ + r) (σ₀ ≥ 0.7). Modest: it does not touch TG's open critical-scale need, where the T^ε loss of Ingham–Huxley is fatal. |
| 17 | LA partial producer at fixed abscissa: on every line Re s = σ > ½ the Hadamard receiver `Re(ξ'/ξ) ≥ 0` holds at all heights in [T, 2T] outside a set of measure ≪ T^{(A(σ)+ε)(1−σ)} | Disc locality: an obstructing zero or its reflection has real part ≥ σ and ordinate within ½; cumulative Ingham–Huxley count | **PROVED on paper, Lean draft written; compile pending** | Draft module `XiLogDerivRePositivePowerSaving` waits for a concurrent rebuild of its dependency chain (memory pressure; no second Lean process started). |
| 18 | Riemann–Siegel phase monotonicity: θ(t) + arg Σ_{n≤√(t/2π)} n^{−½−it} is increasing whenever the half-sum is not tiny; this would exclude dips of Z, hence shallow off-line pairs | Phase derivative = θ' + Re(D'/D) = Re(U W̄)/|W|² with W the half-sum and U its log(N/n)-Riesz mean | **REDUCED, not believed [P]** | Exact reformulation: monotone phase ⟺ the Riesz centroid U of the partial-sum path and its endpoint W make an acute angle. The form Re(U W̄) is a rank-2 indefinite form ½(α1ᵀ + 1αᵀ), α_n = log(N/n), on the vector (n^{−½−it}); resonant t can make it negative, and monotonicity is sufficient but not necessary for no dips (|W| varies). No producer. |
| 17 (closed) | (row 17) | | **PROVED [L]** | Module `RHTower/XiLogDerivRePositivePowerSaving` (standard axioms, `lake --old env lean` clean, wired): `exists_volume_hadamardFailure_le_inghamHuxley`, `exists_volume_hadamardFailure_le_rpow_lt_one`, `exists_copy_of_mem_hadamardFailureHeights`. |
| 19 | Heat deep-zero budget: for a real polynomial p and heat time a > 0, the non-real roots of e^{−aD²}p number at most #{roots r : abs(Im r) > √(2a)} (heat analogue of the cosine budget `sum_zeroMult_cosShiftXi_le`) | Quartic p = (z²+1)(z²+100): e^{−aD²}p = z⁴ + (101−12a)z² + (100−202a+12a²); at a = 51/100 both coefficients are positive, so no real root and 4 non-real roots, while only ±10i have abs(Im) > √(2a) | **KILLED [P]**; positive survivor **[P]** | A deeper pair above a shallow one delays its collision (time y²/2 + y⁴/Y² + …). Survivor (Lyapunov law): with V = Σ_{Im z_k>0}(Im z_k)², the root flow ż_k = 2Σ_{j≠k}1/(z_k−z_j) gives dV/da ≤ −2m(a) (upper–upper pairs give −4(y_k−y_j)²/abs(z_k−z_j)², real and lower roots only pull down, the partner gives −2), hence 2m(a) ≤ Σ_{non-real r}(Im r)²/(2a). Sharp for one pair. For Ξ the global V diverges; localisation fails at the window edges, and the heat lane cannot reach RH (Rodgers–Tao). Not formalised: insignificant for RH. |
| 20 | Landau one-sided positivity for the Laguerre sign: (ζ'/ζ)'(s) = ΣΛ(n)log n·n^{−s} has nonnegative coefficients and Re(ζ'/ζ)'(½+it*) > 0 at critical points t* of Z is (B') | Landau's theorem on nonnegative series (with 1 + cos(t log n) twists) places the abscissa at the first real singularity | **KILLED [P]** | The first real singularity is always the pole at s = 1; subtracting it destroys positivity (same wall as 3-4-1 at the FE line). |
| 21 | Derivative visibility: some Ξ^{(k)}, k ≥ 1, sees isolated shallow off-line pairs | Model p = (z²+δ²)q, q real-rooted, δ below the local spacing: p' has its two would-be non-real roots replaced by one real wrong-sign critical point inside the Jensen disk; Laguerre's Z_C(f') ≤ Z_C(f) propagates real-rootedness to all higher derivatives | **KILLED [P] (classical: Jensen disks, Craven–Csordas–Smith)** | Isolated shallow pairs are invisible to every derivative; on shadow-free windows #nonreal(Ξ) = #nonreal(Ξ') + 2·#(wrong-sign real critical points) + O(1). This is why Conrey's ξ' proportions say nothing about ξ; it agrees with the 75% loop's adversary. |
| 22 | Riesz-mean form of (B'): with c_n = n^{−½}cos(θ − t log n), s_n = n^{−½}sin(θ − t log n), w_n = log(N/n), N = √(t/2π), at Σw_n s_n = 0 one has (Σc_n)(Σw_n²c_n) > 0 (sharp and second Riesz means agree in sign) | Same rank-two indefinite structure as row 18; signs are configurable on any bounded prime set (Kronecker), and the constraint is one linear condition | **REDUCED, not believed [P]** | New observation only: N = √(t/2π) makes full alignment of all n ≤ N impossible (Dirichlet needs t ≥ (2π/ε)^{π(N)}), so the RS sum is not a free random configuration; no inequality follows. |
| 23 | Hadamard receiver needs only shallow-relative zeros: Re(ξ'/ξ)(σ+it) < 0 forces a zero with σ < β ≤ σ + C/((σ−½)log t) near t, or a cluster | A pair (ρ, 1−ρ̄) is net negative at (σ,t) iff (t−γ)² < (β−σ)(β+σ−1); every zero or partner within height 1 gives ≥ c(σ−½), and N(t+1)−N(t−1) ≫ log t unconditionally, so the background is ≥ c(σ−½)log t | **SURVIVOR [P], INSIGNIFICANT** | A lone deep zero cannot break the receiver; but weak-type counting gains only 1/log t over the module of row 17, which T^ε absorbs. The shadow criterion itself is the corpus's `re_logDeriv_xi_pos_of_disk_bound`. |
| 24 | Local Jensen excludes deep clusters: for σ ≥ ½ + η₀, a unit height window holds at most C(σ)log t zeros with β ≥ σ and C(σ) < c₀(σ−½) (the Hadamard background), so the receiver of row 23 fails only within O(1/log t) of zeros in the strip (σ, σ + C/log t] | Jensen on discs centred at 1 + κ with convexity μ(σ) ≤ (1−σ)/2 | **SURVIVOR for σ near 1 [P], INSIGNIFICANT** | The failure measure drops from #zeros to #zeros/log t; the thin-strip count is no smaller than N(σ,T), so the power-saving exponent is unchanged. |
| 25 | Bohr–Jessen small-ball exclusion: the random Euler model Π(1 − X_p p^{−s})^{−1} has no zeros for σ > ½, so the critical-scale zero set of ζ is a large-deviation event of the Bohr flow | Zeros are events of measure zero in t; the model controls densities only | **KILLED [P]** | Statistical; pointwise exclusion is Bagchi's strong recurrence (route BAG), RH-equivalent. |
| 26 | Hardy–Selberg sign-change comparison at critical scale excludes shallow pairs in each window of length C/log T | Mollified ∫Z vs ∫abs(Z) windows | **KILLED [P]** | Gives sign changes in a positive proportion of windows only; a window holding one shallow pair has the same Z-mass as a Gram failure with on-line zeros. |
| 27 | Index law for the LA split as a producer: on shadow-free windows #nonreal(Ξ) = #nonreal(Ξ') + 2·#wrong, so a Conrey-type ξ' proportion plus a Rolle count of real critical points gives (B') | #wrong = o(N) ⟺ nonreal(Ξ') ≥ nonreal(Ξ) − o(N) ⟺ N^{real}(Ξ') ≤ N₀(Ξ) + o(N); Rolle only gives N^{real}(Ξ') ≤ N(T) + O(log T) | **CIRCULAR [P]** | An upper bound for real critical points in terms of real zeros is (B') itself. The only nontrivial direction would be a lower bound for off-line zeros of Ξ', which no method supplies. |
| 28 | Row 19 formalised: the heat analogue of the cosine depth budget, Z_c(e^{−τD²}p) ≤ 2·#{roots w : Im w > √(2τ)}, for all real polynomials | p = (X²+1)(X²+9): e^{−τD²}p = X⁴ + (10−12τ)X² + (9−20τ+12τ²) has no real root for τ < 1 and equals (X²−1)² at τ = 1 | **KILLED [L]** | Module `HTGeometry/PolynomialHeatDepthBudgetFailure` (standard axioms, `lake --old env lean` clean, wired): `twoPairQuartic_depthBudget_fails` (½ ≤ τ < 1: 4 nonreal roots against budget 2), `not_forall_nonrealRootCount_polyHeat_le_depth`, `polyHeat_one_twoPairQuartic`. Collective collapse: the shallow pair is delayed from ½ to 1, the deep pair accelerated from 9/2 to 1. Exact dissipation identity [P]: for W = Σ_k(Im z_k)² over all roots, dW/dτ = −4Σ_{k<j}sin²arg(z_k − z_j) (from dΣz² = 2n(n−1)dτ and dΣabs(z)² = 4Σcos 2arg(z_k−z_j)dτ); each conjugate pair contributes −4, which is the Lyapunov law of row 19. Not formalised (needs root dynamics). |
| 29 | WD below the size-only floor: for every κ > 0, heated slice coefficients at heat κ/log t are positive for all t ∈ [T,2T] outside a power-saving set, by localising the interior-Lindelöf argument (local fourth-moment size bounds, local lower bound in the window from the absence of nearby zeros with β ≥ ½+κ) | Tilt heuristic: Gaussian heat κ/log t evaluates the local defect product at κ + n/log t, so detection ⟺ offset > κ (constant one); corpus check | **SUBSUMED (corpus) [L]** | `XiSliceHeatCoshSharpThreshold` already proves the sharp model law (heat κ/L detects an offset δ iff κ < δ/2, i.e. an every-height rate κ < ¼ is a zero-free strip (2κ, ½)), and `XiSliceHeatFromAbscissa` gives positivity at every heat ≥ c/log²t outside εU of each window. Power saving at rate κ/log t is impossible by density: the obstructing depth √(κ/log t) → 0, where Ingham–Huxley only gives e^{−c√(κ log T)}. The size-only window needs σ = ½+κ > 1 (Euler region), which is why the floor is ½ under LH and 2/3 with Weyl: the floor equals the trivial strip. |
| 30 | Slice route (LA/route 3), fixed-ratio orders: for every η > 0, c_{2k}(t) > 0 for all k ≥ η log t at every t ∈ [T,2T] outside a set of measure T^θ, θ < 1 (corpus had o(T)) | The corpus strip-saddle theorem `exists_xiSliceCoeff_pos_of_typical` needs only typical heights (no zero with Re ≥ ½+η/4 within height 2; abs ζ ≤ T^ε near t). Zero shadows: 4 per zero copy + cumulative Ingham–Huxley count; large values: corpus mean-square cell bound with threshold T^ε gives T^{1−ε} | **PROVED [L]** | Module `RHTower/XiSliceTypicalOrderPowerSaving` (standard axioms, `lake --old env lean` clean, wired): `exists_volume_xiSliceCoeff_nonpos_le_rpow`, `exists_volume_not_zetaTypicalHeight_le_rpow` (reusable: every consumer of `zetaTypicalHeight` now has power saving), `exists_volume_zetaZeroShadow_le_inghamHuxley`, `exists_volume_zetaLargeNear_le_rpow`. Power saving is impossible at the critical-scale orders k ≍ log log t (`XiSliceLogLogOrderDensity`), where the obstructing depth tends to 0. |
| 31 | Heat horizon from Weyl's bound: zeros of H_t with abs(Re z) ≥ 2π e^{(3/2+ε)/t} (and ≥ X₀) are real and simple, improving the corpus 1 + √3/2 | Only the strip terms change: Weyl's bound interpolated across ½ ≤ Re s ≤ 1+η gives exponent ρ(½+η−w), ρ = (1/6+η)/(½+η); with λ = 2ρ the Gaussian strip exponent is ≤ −c²λ(2−λ) + 2cλ(1+η) after completing the square in w − y, negative once c > 2(1+η)/(2−λ) → 3/2 | **PROVED [L]** | Module `RHTower/KiKimLeeWeylHorizon` (standard axioms, `lake --old env lean` clean, wired): `riemannHeat_zeros_real_weyl`, `riemannHeat_zeros_real_simple_weyl`, reusable `exists_norm_xiLine_le_strip_weyl`, `weyl_strip_terms_le`, `re_slope_pos_weyl_window`. The window estimates are stated for 2tα ≥ 3/2, so Bourgain-type exponents need a new window argument to go below 3/2. Large-height producer: improves a constant, not the ZAL cap. |
| 32 | Euler-product sign at critical points: on the multiplicative torus e(n) = n^{−it} (completely multiplicative), the wrong-sign condition Re(e^{iθ}A)·Re(e^{iθ}B) < 0, A = Σn^{−½}e(n), B = Σw_n²n^{−½}e(n), at Re(ie^{iθ}C) = 0, C = Σw_n n^{−½}e(n), is excluded by gcd (Selberg Λ²/Smith) positivity | Expand: (Σc)(Σw²c) = ½[Re(AB̄) + Re(e^{2iθ}AB)]. The averaged part Re(AB̄) is a pairing of two different vectors, and the full condition is a product of two real linear functionals | **KILLED [P]** | No Gram or gcd structure: a product of two different linear forms is indefinite on any set with enough freedom, and multiplicativity only fixes e on composites, leaving all e(p), p ≤ √(t/2π), free. Side remark (also killed): in the Gram variable τ = θ(t)/π the RS sum is bandlimited to [0, π], so Z is approximately sine-type with maximal real-zero density; maximal density gives only o(R) non-real zeros, and FOL needs the count to O(1), which is circular. |
| 33 | Stepanov/Bombieri auxiliary function for ψ(x): an entire function of controlled type vanishing to order k at every log p, p ≤ x, bounds ψ(x) − x by x^{½+ε} as in the function-field proof | Jensen for exponential type: vanishing to order k on π(x) points of [0, log x] (density e^u/u) needs type ≳ k e^u/u, so the bound is trivial | **KILLED [P]** | The function-field method pays only q^{n/2} because the Frobenius polynomial X^{q^n} − X vanishes at all rational points for free. Over ℤ no identity vanishes at the primes cheaply. This is the missing Frobenius, already recorded by the corpus F₁ audit. |
| 34 | Carathéodory–Toeplitz positivity: RH ⟺ every Toeplitz matrix of the Taylor coefficients at s = 3/2 of the Cayley-transformed Re(ξ'/ξ) (computable from primes and Γ) is PSD | Herglotz ⟺ PSD Toeplitz; first minors are Li-type coefficients | **BRIDGE [P]** | A receiver; the minors are explicit but signless (Li lane, TG Toeplitz index). |
| 35 | Cosine-shift sum Lyapunov step (would give the heat Lyapunov law of row 19 by iteration cos(aD)^n → e^{−τD²} and corpus Hurwitz transfer): Σ_{upper w of cos(aD)p}((Im w)² + a²) ≤ Σ_{upper z of p}(Im z)² | Threshold matching (#{Im w ≥ v} ≤ #{Im z ≥ √(v²+a²)}) would prove it; check on two pairs at one abscissa | **Matching FALSE [P]; sum version survives the test** | For (z²+y₁²)(z²+Y²) with Y² − y₁² > 4a² the shallow root of cos(aD)p sits deeper than √(y₁² − a²): the deep pair attracts it under the cosine shift (the heat-flow collapse of row 28 in one step). The sum still drops by 2a² per pair, so a proof needs majorisation, not matching. Insignificant for RH; not pursued. |
| 36 | Level-curve topology (X-ray) excludes shallow pairs: arcs of {Im ξ = 0} entering from Re s = +∞ (≈ N(T) of them on a window) must all end at real critical points of Ξ, so none can end at an off-line zero | By Cauchy–Riemann the arcs of {Im ξ = 0} are gradient lines of Re ξ, so abs(ξ) is strictly monotone along them. A wrong-sign critical point has abs(ξ) decreasing in σ, so its arc cannot reach +∞ and ends at the off-line zero (which has 4 arc ends). Count ends: C = N₀ − 1 + 2P critical points, R = N₀ + 2P arcs from +∞, 4P ends at zeros | **KILLED [P]** | The end counts balance for every P, and the configuration (two arcs from +∞ into ρ, ρ joined to t* and to a neighbouring critical point) is realisable. Topology encodes only the argument principle plus the corpus curve criterion `riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero`. |
| 37 | Shallow pair forces a large negative value of Re(ζ'/ζ)' on the line (≈ −2/δ² at the midpoint), forbidden by mean values of (ζ'/ζ)' | On-line zeros give large positive values ≈ Σ1/(t−γ)²; the sign condition Re(ζ'/ζ)'(½+it) ≥ −O(1/t) is the first Laguerre inequality | **CIRCULAR [P]** | Same receiver as (B'); mean values cannot see the sign at isolated points. |
| 38 | Λ ≥ 0 at the shifted point: for nonnegative tests f the prime term of the Weil form is ≤ 0, so Σ_ρ ĝ(z_ρ) ≤ arch(f) + pole(f); an off-line zero adds 2Re f̂(γ−iδ)² which, for f ≥ 0 concentrated where cos(γx)cosh(δx) is large, beats the slack | For f on [−a,a] the off-line gain is ≍ e^{2δa}abs(f̂(γ))², the slack (the prime term) ≍ Σ_{n ≤ e^{2a}}Λ(n)n^{−½}g(log n) ≍ e^a | **KILLED [P]** | Detection needs e^{2δa} ≳ e^a, i.e. δ ≥ ½: the resolution limit again. Positivity of Λ makes the prime term a slack for nonnegative tests, never a detector. (ζ² = L(π×π̃) for trivial π adds nothing: same zeros, doubled Λ.) |
| 39 | Degree theory for exceptional points: Φ(h,x) = (Re ξ, Im ξ')(½+h+ix) has Jacobian Re(ξ' conj ξ'') = Re ξ'·Re ξ'' at its zeros; if every zero has positive orientation and the boundary winding vanishes, there are no exceptional points (RH via the corpus curve criterion) | Model ξ ≈ c(w² − δ²): the only zero of Φ is ρ itself, Jacobian 4c²h > 0. Boundary: left side Φ ≈ (Ξ, −Ξ'), whose winding counts sign changes and backtracks at wrong-sign critical points; right side winds with arg ξ ≈ N(T)/2 | **CIRCULAR [P]** | The boundary winding equals (N − N₀)/2-type data, i.e. the off-line pair count; showing it is 0 is RH. Orientation positivity is plausible, but it only makes the accounting exact, which the corpus already has (`windowDefectCount_zero_le_exceptional_mass`). |
| 40 | Orientation law for exceptional points: every zero of Φ = (Re ξ, Im ξ') in ½ < Re s < 1 has positive Jacobian Re(ξ' conj ξ''), so the exceptional-point count is an exact index (winding) | Derived: at an exceptional point (ξ = ib, ξ' = a real) the Jacobian is b²·u_t·u_{σt}, u = log abs(ξ); for one pair the Φ-zero sits at ρ with Jacobian 4c²δ > 0. Two pairs at one height: ξ ≈ c(w²−δ₁²)(w²−δ₂²), δ₁ < δ₂, Φ-zeros at w = δ₁, δ₂ with Jacobian ξ'ξ'' = 2c²δ₁(δ₁²−δ₂²)(10δ₁²−2δ₂²) at δ₁ | **FALSE [P]** | For δ₂ < √5·δ₁ the shallower zero carries a negatively oriented Φ-zero (stable under perturbation). Exceptional points are created and annihilated in ± pairs, so degree counting cancels and cannot replace the corpus mass inequality. Clustered pairs are again the obstruction. |
| 41 | Upper-semivariance Jensen correction for Levinson/Littlewood: with Y = log abs(ζM)², m = E Y, e^z ≥ 1 + z + z₊²/2 gives m ≤ log E abs(ζM)² − log(1 + ½E(Y−m)₊²); in the log-normal model this recovers half of Levinson's loss (all of it with exponential-moment control) | Corpus check: `JensenGapSecondMomentNoGo` (mean and variance never bound the Jensen gap; two-point laws), the Poisson–Jensen lower-tail deficit (0.0783T vs 0.0805T) and the Littlewood weight classification (CANNOT-295, 303, 304) | **SUBSUMED / (L)-hard [P]** | The upper semivariance of Y lives on the primes above the mollifier length T^θ. Moment methods give only E abs(S)² for those prime sums (length ≤ T allows k = 1), which bounds the variance but not the semivariance. Anti-concentration of the unmollified primes is the (L) wall itself. Also checked: Jessen's convexity makes (1/T)∫log abs(Ψ(½+it)) ≥ −o(T) for every detector Ψ with b₁ = 1, so the corpus's open successor 2 (∫log abs(Ψ) ≍ −T) is impossible in the Bohr limit. |
| 42 | (Mode switch) Pick an exact, unconditional, unowned open successor from the corpus and close it | Survey: 2357 in-progress cards. Paper-complete ones are mostly other sessions' universality-law series. TH's "C5 enriched clock current on 0 < t < 2" (`ThetaCuspC5OuterClockCurrent`: proved only for t ≥ 2) sits in a 3300-module theta chain. HF T5 (Weil positivity on a log 2 window) has margin ≈ 10⁻³ for smooth nonnegative bumps, because the prime 2 enters exactly at length log 2, so it needs a numeric certificate. KKL below 3/2 needs Bourgain 13/84 (card open, decoupling) and a window relaxed from c ≥ 3/2 to the Chernoff floor 4/3 | **NO CHEAP TARGET [audit]** | The remaining exact open items are RH-strength, numeric certificates at a boundary, or deep in another session's chain. Next: the KKL window relaxation 3/2 → 4/3 is exact and local to my own module family, and would matter once any μ(½) < 1/6 enters the corpus. |
| 42b | KKL window relaxation | The c ≥ 3/2 hypothesis enters only through u = y + c ≥ 1, i.e. the comparison point must lie in Re s ≥ 3/2, where the corpus lower bound for ζ applies. Using abs(ζ(σ+it)) ≥ ζ(2σ)/ζ(σ) for σ > 1 lowers it to c > 1 + δ; the Chernoff tail then binds at 4/3 | **DEFERRED [P]** | With Weyl the strip bracket already binds at exactly 3/2, so the relaxation gains nothing until a subconvexity exponent below 1/6 is in the corpus (Bourgain would give 2/(2 − 26/42) ≈ 1.448). Recorded so that it is not rediscovered. |
| 43 | Joint ξ/ξ' statistics: a shallow pair forces an extra (max, dip, max) triple of real critical points inside one sign-change gap, excluded by Ξ' gap statistics | As δ → 0 the triple converges to the critical-point pattern of an on-line double zero (max, double zero, max); gaps between critical points stay ≍ spacing/2 | **KILLED [P] (continuity barrier)** | Every continuous statistic of the (ξ, ξ') zero configuration is blind to the limit pair → double zero; sign counting is blind too (a double zero has no sign change). The functional must be non-smooth in δ at 0 (first order in abs(δ)), which is Littlewood's ∫log abs(ζ(½+it)) = 2πΣ(β−½)⁺ + O(log T), i.e. (L). |
| 44 | RS split of (L): ζ(½+it) = A(1 + e^{iφ}) with A = Σ_{n≤√(t/2π)} n^{−½−it} and e^{iφ} = χĀ/A unimodular, so log abs(Z) = log 2abs(A) + log abs(cos ψ), ψ = θ + arg A; Jessen gives E log abs(A) = κ > 0 (zeros of D_N right of ½), and RH forces E log abs(cos ψ) = −log 2 − κ + o(1) | Uniform ψ would give E log abs(Z) = κ > 0, contradicting RH, so ψ must linger near π/2 + πℤ in a way correlated with abs(A) | **CIRCULAR [P]** | The phase–modulus correlation of a length-√T Dirichlet polynomial is accessible only through moments with N^{2k} ≤ T, i.e. k ≤ 2. log abs(A) and arg A need the full distribution: the (L) wall in RS form. The consistency relation E log abs(cos ψ) = −log 2 − κ under RH is a sharp quantitative prediction, but no producer. |
| 45 | Distributional input for (L): Selberg's CLT or a Gonek-type small-ball bound lowers the off-line moment beyond the moment methods | Corpus search: no Selberg-CLT module; small-ball / Poisson–Jensen lower-tail deficit gives 0.0783T vs 0.0805T (memory: steinhaus-jensen-floor, CANNOT-303); the CLT lives at scale √(½ log log T) | **SUBSUMED / INSUFFICIENT [P]** | The CLT fixes the distribution of log abs(ζ) at scale √(log log T), while (L) needs its mean to o(1); an O(1) mean shift is invisible to any CLT. Small-ball refinements are per-cent improvements of μ. Neither moves the core. |
| 46 | Cuspidal positivity (Selberg trace formula for SL₂(ℤ)): the scattering density −φ'/φ(½+ir) = 4Σ_ρ(1−β)/((1−β)² + (2r−γ)²) is a positive Poisson sum over ζ-zeros with widths 1−β, and Σ_j h(r_j) ≥ 0 bounds its h-average by the geometric (class-number geodesic) side; narrow h amplifies an off-line pair by 1/(1 − 4δ²) | Excess ≍ 16δ²·mass versus slack = Σ_j h(r_j) over cusp forms near r = γ/2, of size ≍ (γ/12)·w by Weyl's law | **KILLED [P]** | The positivity is genuine (self-adjointness), but it sees depth only at second order (Poisson widths ½ ± δ) and its slack is the whole cuspidal Weyl mass. Consistent with the dead HB lane: the zeros enter at the second sheet / scattering poles ρ/2. |
| 47 | The Jessen constant of the moving partial sums: κ = lim E_{t∈[2πN²,2π(N+1)²]} log abs(D_N(½+it)) exists and is computable; if κ = 0, RH reduces to E log abs(cos ψ) = −log 2 (uniform RS phase) | Window length ≈ 4πN against the Bohr resolution N, so the window mean approximates Jessen's φ_N(½) = 2π∫_{½}^∞ c_N. In the Bohr–Jessen random model, log abs(Σ_{n≤N}X(n)n^{−½}) differs from the log of the truncated Euler product by an O(1) multiplicative-chaos correction (Harper-type), so κ_N = O(1) with unknown sign and limit | **OPEN / NOT A PRODUCER [P]** | Even an exact κ only fixes the RH-forced phase statistic E log abs(cos ψ) = −log 2 − κ. Computing E log abs(cos ψ) independently needs the joint phase–modulus law of a length-√T polynomial (moments k ≤ 2 only). Recorded as a sharp prediction, not a route. |
| 48 | First Laguerre (slice order 1) fails only near shallow zeros: c₂(t) < 0 forces an off-line zero in its cone with depth ≤ C√(K/log t), K the number of locally deep zeros, since each critical or non-cone term contributes ≥ (12/25)/u² and N(t+1) − N(t−1) ≫ log t | c₂/c₀ = Σ_ρ(u²−δ²)/(u²+δ²)², u = γ − t, δ = β − ½; negative terms ≥ −1/δ² | **SUBSUMED (corpus) [L]** | `XiLaguerreSeparation.laguerre_offLine_has_companion` / `laguerre_offLine_separation` already prove it, with local scale (16(C + log(abs(γ)+4)))^{−1/2}, and `XiLaguerreOffLineNeighbourhood` gives the converse (failure when δ²S < 24/25). The 1/√(log t) scale is the unconditional limit: the heuristic 1/log t needs fine-scale zero spacing (background ≍ (log t)²), which is pair-correlation strength. |
| 49 | Search-first protocol on the three residual items: (i) fine-scale spacing, (ii) (L), (iii) arithmetic separator; attempt only a strict improvement of the corpus's strongest unconditional statement | (i) corpus has no Selberg/Fujii S(t)-moment module. With Fujii's unconditional short-window variance (log A)/π², almost every window of length A/log T holds A/2π ± O(√log A) zeros, so the first-Laguerre background is ≥ c(log t)²/A² off a proportion O(log A/A²). (ii) Jessen floor and Jensen no-go present. (iii) `XiSliceCoeffNearDoublePositivity`, `XiReciprocalSliceNearDoubleDominance` present; no separator | **NO STRICT IMPROVEMENT [P]** | (i) Localising first-Laguerre failures to depth ≤ CA/log t does not reduce their measure: the shadows of zeros of depth ≤ ε have measure ≤ 2ε·#(off-line zeros) ≍ (CA/3π)T, worse than the corpus's 2·offLineMoment. Local on-line counts cannot be extracted from the global 2/3. Also checked: Redheffer's det R_n = M(n), with M(n) = Σ_k(−1)^k D_k(n) over ordered-factorisation counts, is a literature reformulation (Vaughan); the alternating cancellation of k-dimensional divisor errors is RH-strength. |
| 50 | Kac–Rice exactness: N₀(T) = lim_{ε→0}(1/2ε)∫1{abs(Z)<ε}·abs(Z')dt, so a lower bound on the joint density of (Z, Z') at Z = 0 matching N(T) gives N₀ = N (RH and simplicity) | Corpus: only model two-point Kac–Rice intensities (`GreedyBumpQuarticKacRice`) and the local off-line constraint `hardy_joint_constraint_at_offline_zero` (at an off-line zero (Z, Z') at the ordinate lies in an O(δ²) disc) | **KILLED [P]** | The density at Z = 0 at scale ε → 0 is the sign-change count itself (circular); at fixed ε it is statistical (Hardy–Selberg proportions). Kac–Rice also needs simplicity, strictly more than RH (continuity barrier of row 43). |
| 51 | Stieltjes electrostatics: the zeros of Ξ are the equilibrium of a log-gas with arithmetic external field, and equilibria of real-weight log-gases lie on ℝ | Stieltjes needs a second-order linear ODE AP'' + BP' + CP = 0; Ξ is hypertranscendental (corpus HT lane, Ostrowski/Hölder). The only native gradient structure is the de Bruijn–Newman flow ż_k = 2Σ1/(z_k − z_j), whose stationary states would be crystals | **KILLED [P]** | No ODE, and stationary configurations are excluded by the corpus anti-crystal law (`not_rigidOrdinates`): the zero set is not an equilibrium of any such flow. |
| 52 | Eneström–Kakeya for Riemann–Siegel sums: Z(t) = 2Σ_{n≤N} n^{−½}cos(θ − t log n) has decreasing amplitudes and frequencies θ' − log n ∈ [0, θ'], so an EK/Fejér-type theorem confines its zeros or forces sign changes between consecutive frequency nodes | EK needs integer (lattice) frequencies; for frequencies log n the analogue fails: D_N(s) = Σ_{n≤N}n^{−s} has zeros with Re s > 1 for large N (Montgomery), so no decreasing-coefficient zero-free half-plane exists | **KILLED [P]** | Positivity of decreasing-amplitude cosine sums (Fejér) uses convexity in the lattice of frequencies; the logarithmic frequencies of an Euler product break that structure (corpus: no `Eneström`-type module; partial-sum obstructions exist). |
| 53 | Complete monotonicity on the real axis: F(y) = Ξ(i√y) = Σ b_k y^k (b_k > 0, order ½), and RH ⟹ 1/F is completely monotone on y > 0 (a generalised gamma convolution: the inverse Laplace transform is a convolution of Exp(γ_k²) densities). Conjecture: this CM property holds unconditionally (it allows complex poles, so it is strictly weaker than RH) | Sufficient: (log F)' = F'/F = Σ_ρ 1/(y + t_ρ²) completely monotone, i.e. the zero heat trace Σ_ρ e^{−s t_ρ²} ≥ 0 for every s > 0; off-line pairs contribute 2e^{−(γ²−δ²)s}cos(2γδs) | **SUBSUMED (corpus) [L]** | TH proves "heat-trace complete monotonicity is another RH receiver" and HCF owns the Gaussian heat trace Σ_ρ e^{−s t_ρ²} with its explicit-formula (Gaussian prime side) evaluation. CM of 1/F itself (weaker than CM of F'/F) is a falsifier implied by RH, but its unconditional truth would need the heat-trace sign at all s, i.e. the HCF receiver. |
| 54 | Unconditional complete monotonicity of 1/ξ(½+√y) on y > 0 (implied by RH, strictly weaker: it allows complex poles), via the Euler product and the Γ-factor without zero locations | Inverse Laplace density g(s) = Σ_ρ A_ρ e^{−t_ρ² s}: positive at small s (decay e^{−c√y}) and governed at large s by the lowest zero. An off-line zero below every on-line zero makes g oscillate at large s; at large height the off-line terms are swamped. Euler factors 1 − p^{−½}e^{−√y log p} are increasing in y, hence not CM factorwise | **KILLED as a producer [P]** | CM of 1/ξ(½+√y) is essentially "RH for the lowest zeros" (a finite verification) plus weak large-height constraints. Corpus already owns the strong forms (`riemannHypothesis_iff_completelyMonotoneOn_xiGaussianHeatTraceReal`, Gamma-shape CM extension). No unconditional route without computation. |
| 55 | Arithmetic monodromy: the continued prime-log current has a quantised integer charge at each zero right of the line, so an integer invariant counts off-line zeros | Corpus: `PrimeBoundaryMonodromyEscape.primeBoundary_monodromy_charge` (residue = multiplicity), `XiSymmetricDiscIndexParity.even_offLine_sum` | **SUBSUMED (corpus) [L]** | The charge is readable only by continuing log ζ to the zero itself (local); globally readable prime data reaches it only through depth-weighted sums (terminal-classification pattern, door 2). |
| 56 | Ergodic rigidity for one disc: B²-almost periodicity of ζ in Re s > ½ forces return to a fixed disc at a positive density of shifts τ, so a zero there recurs, contradicting N(σ,T) = o(T) | That is Bagchi's strong recurrence, RH-equivalent; almost periodicity gives returns for almost all discs (averaged over centres), not for the disc around a given zero | **CIRCULAR (BAG lane) [P]** | Same as the corpus BAG core (row 707): ζ is the non-generic point z = 1 of its Bohr lift. |
| 57 | ζ(s)ζ(1−s) = abs(ζ)² on the line as a positivity source visible to the explicit formula | Corpus: blind-test pole identity (row 15), killed "period positivity (only abs(ζ)²)", Jensen-gap no-go | **SUBSUMED [P]** | abs(ζ)² positivity enters only through mean values; log abs(ζ) (the (L) object) is not a positive functional of abs(ζ)². |
| 58 | Higher-rank twist: L(s,f×f̄) = ζ(s)L(s,sym²f) has FE, Euler product, Λ_{f×f̄}(p^k) = log p·abs(α_p^k + β_p^k)² ≥ 0 and is tempered (Deligne), i.e. the unkilled ingredient set; averaging its Weil forms over a Petersson family isolates ζ's zeros with a positivity ζ alone lacks | E_f[Weil(f×f̄)] = Weil(ζ) + E_f[Weil(sym²f)]; the ζ part is family-independent, so averaging only adds the sym² one-level density (Fourier support < 1, Iwaniec–Luo–Sarnak) | **KILLED [P]** | The family adds no information about ζ's zeros beyond ζ's own explicit formula; GRH positivity for each f×f̄ is itself RH-strength. Matches corpus kills (quadratic-family averaging, Deligne amplification obstruction). |
| 59 | Zero-side parity barrier: Selberg's parity obstruction has a dual that rules out shallow pairs (sieve weights correspond to tests blind to zero depth, so a parity-sensitive test is depth-sensitive) | λ(n) ↔ ζ(2s)/ζ(s): parity sensitivity at x^{½+ε} is RH itself; sieve weights give the Λ²-type tests that are already blind | **KILLED [P]** | The dual of parity sensitivity is a pointwise Liouville or Möbius bound at the half power (route MC), RH-equivalent. |
| 60 | Near-line large values (Guth–Maynard-type additive energy) beat Ingham near σ = ½ | At σ = ½ + a/log T the detector threshold V ≈ √N sits where the mean-value theorem is already sharp; Guth–Maynard gain only for large V (σ ≈ 3/4); near ½ Ingham's 3/(2−σ) is the best known and Selberg-type rates govern the critical scale | **KILLED [P]** | No near-line gain is available from large-value methods. |
| 61 | Cosine-step sum inequality (CSS, row 35) toward a dependency-closed proof: Σ_{UHP roots w of cos(aD)p}((Im w)² + a²) ≤ Σ_{UHP roots z of p}(Im z)² | New checks: (z²+1)(z−1) at a = ½ gives 0.822 ≤ 1; z⁴ + 4 gives √(4+a⁴) − a² ≤ 2 for a < 2^{−¼} and 0 beyond. Representation: with K_q(y) = Σ_r abs(y − Im r) = (1/π)∫_ℝ log abs(q(x+iy)/q(x))dx + K_q(0), one has V(q) = ∫_0^∞(K_q(y) − ny)dy and m(q) = (n − K_q'(0⁺))/2, so CSS is an inequality between horizontal log-integrals of A = ½(p(·+ia) + p(·−ia)) and of p | **OPEN, plausible [P]** | All tested configurations hold with slack 0 for one pair. A proof needs a mean-value inequality for ∫log abs(½(u+v)) along horizontal lines where abs(v/u) crosses 1 (the Hermite–Biehler phase); root-by-root matching is false (row 35). Payoff if proved: the heat Lyapunov law (row 19) via cos(√(2τ/n)D)^n → e^{−τD²} and the corpus Hurwitz transfer, formalisable with `nonrealRootCount_shiftAvg_le`-style tools. RH-relevance low. |
| 62 | Mixed Hermite–Biehler pair (ξ, ξ''): some real combination E = Ξ − iκΞ'' (or with Ξ') is HB unconditionally | Ξ − iεΞ' ≈ Ξ(t − iε) is HB iff all zeros satisfy abs(Im) < ε (circular); Ξ − iκΞ'' has the same problem at second order | **CIRCULAR [P]** | HB-ness of any finite-order differential combination is a zero-location statement for Ξ (corpus: LP-maximality, no LP preimage under real-rooted symbols). |
| 63 | Selberg-class axioms supply a depth-sensitive invariant (e.g. Selberg orthonormality Σ_{p≤x}abs(a_F(p))²/p ~ n_F log log x) | Orthonormality and degree are prime-side statistics; zeros enter only through explicit formulas with harmonic weights | **KILLED [P]** | Same wall as row 10 (Harnack) and the terminal classification: axioms that are globally readable are depth-weighted. |
| 64 | Close CSS (row 61) by deformation: F(a) = Σ_{UHP w of A_a}((Im w)² + a²), A_a = cos(aD)p, is non-increasing in a | With B_a = sin(aD)p, ∂_aA_a = −B_a', so ẇ = B_a'(w)/A_a'(w) and dF/da = 2Σ_w(Im w·Im(B'/A')(w) + a), which is 0 for one pair (ẇ = −ia/v); a pair leaving the UHP drops F by a² ≥ 0 | **OPEN [P]** | The sign of Σ_w Im w·Im(B'/A')(w) is not controlled by the Hermite–Biehler phase argument (it mixes zeros of A' and of B'). The heat analogue works because e^{−τD²} is a semigroup with ż_k = 2Σ1/(z_k − z_j); cos(aD) is not. CSS stays open; the heat Lyapunov law (row 19) keeps only its root-dynamics proof, which Lean lacks the infrastructure to formalise cheaply. |
| 65 | Pair correlation beyond 1 via an averaged prime-pair upper bound: F(α) ≤ 2 on [1, 4/3] (sufficient for 3/4 on-line, 75% loop) from Var(ψ(x+h) − ψ(x)) ≤ (2 + ε)·½hX log(X/h) for h ≥ x^{1/4} | Unconditional short-interval variance (Huxley-type density) gives ≪ h²X(log X)^{−A}, larger than hX log X by a factor h/polylog; Selberg's bound ≪ hX log²X needs RH | **RH-STRENGTH [P]** | Any constant-factor variance bound at power-scale h is Selberg-under-RH strength; it is the (L)/pair-correlation wall, recorded in the 75% loop as a prime-pair upper bound with constant 2. |
| 66 | Gram-block parity law: FE + Euler force a parity or mod-4 constraint on the wrong-sign critical points of Z in a Gram block with good endpoints | At Gram points ζ(½+ig_n) = (−1)^n Z(g_n) is real, so S(g_n) = N(g_n) − n − 1 is even at good points; hence N(block) ≡ m − n ≡ N₀(block) mod 2. Mod 4 needs arg ζ(½+ig_n) mod 4π, which endpoint signs do not fix, and N₀ mod 4 is not readable from endpoints. Davenport–Heilbronn (FE, no Euler) has the same pairing | **KILLED [P]** | Parity is automatic: off-line pairs and on-line double zeros both contribute even counts (corpus `even_offLine_sum`). No finite-modulus constraint separates ζ from FE-only countermodels. |
| 67 | Kronecker-resonant heights: at heights where p^{−it} ≈ ε_p (prescribed phases) for all p ≤ P (corpus `primeTorus_kronecker_dense`, `exists_dirichlet_simultaneous`), the RS sum is dominated by its P-smooth part, which fixes the sign pattern of Z and excludes shallow pairs nearby | Resonant heights have density ≍ ε^{π(P)} (Dirichlet: t ≲ (1/ε)^{π(P)}), and control of the P-smooth part leaves the primes in (P, √(t/2π)] free | **KILLED [P]** | The heights reached are a sparse set; a shallow pair at a non-resonant height is untouched. Even at resonant heights the large primes carry variance ≍ log(log t/log P), comparable to the controlled part unless P ≥ t^c, which Dirichlet cannot reach. This is the multiplicative-independence form of the (L) wall. |
| 68 | CSS (rows 61/64) for stacked pairs p = Π_{j≤k}(z² + y_j²): write A = cos(aD)p = Q(z²). Vieta (the z^{2k−2} coefficient drops by a²k(2k−1)) gives UHP sum = V₀ + P₊ + Σ_{complex u-pairs}(abs(u) + Re u), V₀ = Σy_j² − a²k(2k−1), P₊ = sum of positive u-roots (squares of real roots of A) | CSS ⟺ P₊ + Σ_{complex pairs}(abs(u) + Re u) + a²m(A) ≤ a²k(2k−1): a fixed budget shared by real roots, near-axis complex roots and a² per UHP root. Equality case p = z^{2k}: cos(aD)z^n = Re(z+ia)^n has the real roots a·cot((2j+1)π/(2n)), and Σ_{j<k}cot²((2j+1)π/(4k)) = k(2k−1) exhausts the budget | **REDUCED, OPEN [P]** | Exact Vieta budget form for one-abscissa stacks; k = 1, 2 and the z^{2k} endpoint verified; general k is open (it needs the budget to dominate the abs(u) + Re u terms of complex u-pairs). Still a heat-flow side lemma of low RH value; recorded so it can be resumed. |
| 69 | Atomic decompositions of CSS. (a) LDB/WMJ: layered de Bruijn N_A(h) ≤ N_p(√(h²+a²)) and weak majorization {v_w²+a²} ≺_w {y_r²}. (b) FS: Σ_{UHP roots w of p+λp'}(v_w²+λ²) ≤ V(p). (c) LS: V(p−cp'') + 2c·m ≤ V(p); with cos(aξ) = Π_k(1−c_kξ²), Σc_k = a²/2, LS ⇒ CSS, and LS ⇒ heat law. (d) DS: for the roots w of p+λp' (λ real), π_{wk} = abs(w−r_k)^{−2}/Σ_j abs(w−r_j)^{−2} is doubly stochastic; v_w = Σ_k π_{wk}y_k holds exactly (Im Σ1/(w−r_k) = 0). DS would give 2V(q) = 2V(p) − Σ_w Var_{π_w}(y). | (a) layered form FALSE for (z²+1)(z²+9): the shallow root gets v²+a² ≈ 1 + a²/2 > 1 (the deep pair drags it). WMJ holds there. (b) FS FALSE: p = (z²+1)(z²−L²), λ² > ½, gives V+λ²m = 1 + 4λ²(2λ²−1)/L² + O(L^{−4}); far real roots push the pair root up. (c) LS FALSE: same p, c ∈ (2/5, ½): V+2c = 1 + (20c²−8c)/L²; certificate L² = 100, c = 9/20, Q(−1/10) = −9/20 < 0. (d) DS proved for real-rooted p (bilinear Cauchy orthogonality UUᵀ = diag(−R′(w_j))) and n = 2; FALSE in general: (z−1)(z²+1), λ = 1 gives column sum 1.19. CSS itself holds on the new family: V+a²m = 1 − 4a²(1−a²)/L². | **KILLED (a,b,c,d); CSS survives** | The cosine step cannot be split into Laguerre or first-order steps: each factor alone violates the budget, and only the full product cos(aD) satisfies it. Any proof of CSS must use the translation structure ½(p(z+ia)+p(z−ia)) as a whole (de Bruijn's dipole sign X+v²+a²−y²). Lorentzian reading of de Bruijn: every nonreal A-root w = u+iv has a p-root with y² − (x−u)² > v²+a² (a timelike future cone of proper time √(v²+a²)). |
| 70 | (a) Lorentzian de Bruijn for Ξ: off-line zeros of F_a(s) = ξ(s+a)+ξ(s−a) at height u are witnessed by ξ-zeros of depth > √(a²+(γ−u)²) — a producer seed for shallow pairs? (b) Finite free reading of CSS: A = cos(aD)p = p ⊞_n Q_a with Q_a = cos(aD)zⁿ real-rooted (roots a·cot((2j+1)π/2n), Σc² = a²n(n−1)); Vieta = additivity of the second finite free cumulant. Conjecture FFC: for every real-rooted centred q, V(p ⊞_n q) + s_q·m ≤ V(p), with s_q = Σc²/(n(n−1)) = −φ″(0) for q = φ(D)zⁿ. | (a) SUBSUMED: corpus `XiCosineShiftHeatStrip.cosineShift_deBruijnNewman_bounds`, `DeBruijnNewmanCosineShift`, `LindelofOffLineSparse.eventually_strip_of_lindelof_of_cosShiftXi_real` (real-rooted cosine level ⇒ eventual strip under LH). The cone adds only a horizontal localisation, which density transfers already cover. (b) FFC FALSE: q = (1−cD²)zⁿ (one Laguerre factor, s_q = 2c) is the row-69 LS counterexample. FFC holds for the Hermite q (heat law) and, conjecturally, for Q_a. By cumulant ratio Σc_k²/(Σc_k)²: heat 0, cosine 2/3, single Laguerre 1. The far-real-root margins are not additive over factors (cosine exact 8S−16S² against 8S−(40/3)S² from summing), so validity is a second-order property near the equality configurations. | **SUBSUMED (a); FALSE (b, general FFC)** | Open side question, with no RH content: which even Laguerre–Pólya φ satisfy V(φ(D)p) − φ″(0)·m ≤ V(p)? The heat and cosine kernels qualify; single Laguerre factors do not. |
| 71 | Three attempts at an exact first-order producer. (a) Positive Landau regularisation: find weights w ≥ 0 with Λ(n)/log n − w_n ≥ 0 such that Σ w_n n^{−s} carries exactly the log(1/(s−1)) singularity, so that Landau's theorem pushes the abscissa of log((s−1)ζ) to ½. (b) Real-rootedness of polar Weil ground states (corpus `WeilGroundStateRealZeros`, via the Blaschke exchange ĝ ↦ ĝ·(z−z̄₀)/(z−z₀), which keeps abs(ĝ) on ℝ and the support) as a positivity producer: does real-rooted ĝ force W(g) ≥ 0? (c) PBAP window: decomposition of the corpus `WindowPositive` form into Dirichlet part + potential + pole on the nonnegative cone. | (a) CIRCULAR: w ≤ Λ/log n forces w to live on prime powers with w_p ≤ 1, and a prime-supported series with singularity exactly log(1/(s−1)) and holomorphic remainder on Re s > ½ is the PNT with RH-quality error. (b) FALSE as a producer: for an off-line pair at γ₀ ∓ iδ, the zero side contributes 2Re ĝ(γ₀−iδ)² (ĝ real). A real-rooted ĝ with ĝ(γ₀) = 0 makes it −2δ²ĝ′(γ₀)² + O(δ³) < 0, so ground states stay real-rooted while using off-line pairs for negative energy. Real-rootedness is unconditional and RH-neutral, and RW needs convergence to Ξ, not root reality. (c) Recomputed from scratch: Ω_{log 2} = ∫_{log 2}^∞ω ≈ 1.4968 (tail 2.994‖h‖²); flat h gives 2.994 + 1.163 (jump) + 1.400 (pole) = 5.557 > abs(A(0)) ≈ 5.372; the potential V(u) = 2Ω + κ(u) − abs(A(0)) is ≈ −1.52 at the window centre. A copositivity certificate needs 2m₊m₋ ≥ abs(λ₀) for the ground pair (λ₀, φ₀) of the Dirichlet form + V, with m± = min e^{±u/2}/φ₀. | **CIRCULAR (a); FALSE (b); (c) reconnaissance in another agent's HF lane — not pursued** | (b) explains exactly why the RW receiver needs ground-state convergence to Ξ/Ξ(0), not real-rootedness: the Blaschke exchange is blind to the sign of 2Re ĝ(γ−iδ)². |
| 72 | (a) Deuring–Heilbronn repulsion at the critical line: a shallow off-line pair would push other zeros away beyond Littlewood's gap ≪ 1/log log γ, a contradiction. (b) Grace–Walsh–Szegő form of the cosine step: A(z) = Φ(z−r₁,…,z−r_n) with Φ(X) = ½[Π(X_k+ia) + Π(X_k−ia)] symmetric multiaffine, Φ(ζ,…,ζ) = Q_a(ζ). (c) Energy law for even Laguerre–Pólya φ = 1 − Sξ² + Pξ⁴ − … on the family p = (z²+1)(z²−b²): V(φ(D)p) + 2S·m ≤ V(p). | (a) KILLED: Deuring–Heilbronn needs the positive Euler-product side near σ = 1. At s = ½+η+iγ the only sign input for Σ Re 1/(s−ρ) is the zero sum itself, so there is no repulsion. (b) Weak: Walsh coincidence gives only the strip bound v ≤ max y_k, because Q_a's roots are real. (c) EXACT (by hand): the law holds iff Q_φ(2S−1) ≥ 0, and Q_φ(2S−1) = 8S − 20S² + 24P = 8S − 8S² − 12Σc_k² for φ = Π(1−c_kξ²). It is independent of b, so the row-69 LS failure holds for every b, not only far real roots. Cosine (Σc² = ⅔S²): margin 4a²(1−a²), exactly zero at pair death a = 1. Single Laguerre factor (Σc² = S²): fails for S > 2/5. Heat (Σc² = 0): 8τ(1−τ). Sinc (Σc² = 0.4S²) and J₀ (Σc² = ½S²) pass. | **(a) KILLED; (b) WEAK; (c) PROVED (degree-4 family)** | New phenomenon: on this family the cosine operator is EXTREMAL for the energy law. The cumulant ratio Σc_k²/S² = ⅔ is exactly the threshold that holds up to pair death. This explains why only the full product cos(aD), and no Laguerre factor alone, satisfies CSS, and suggests CSS is sharp. Proving general CSS should use an extremal or critical argument, not a step-by-step one. Low RH value. |
| 73 | Probabilistic reading of row 72: for a symmetric real random variable X, φ(ξ) = E cos(Xξ) and φ(D)p = E p(z+iX) (vertical random shift). Conjecture RVS: if φ ∈ LP, then V(E p(·+iX)) + E[X²]·m ≤ V(p). X = ±a gives CSS, X Gaussian gives the heat law, X uniform gives sinc, X = a·cos U gives J₀. | Degree-4 test on p = (z²+1)(z²−b²): S = EX²/2, P = EX⁴/24, so the margin is 8S − 20S² + 24P = 4m₂ − 5m₂² + m₄ ≥ 4m₂ − 4m₂² by Cauchy–Schwarz (m₄ ≥ m₂²), with equality iff X² is constant, i.e. X = ±a. So every admissible X passes the family, and the cosine is the unique extremal. The margin is concave in the law of X² (Jensen), so on this family margin(mixture) ≥ average of cosine margins. The LP restriction is needed: p = z⁴ with m₄ > 9m₂² makes E(z+iX)⁴ non-real-rooted. In the stacked case A(0) = p(ia), so pairs die exactly at a = y_k (equality in ∫₀^∞ 2a·m(a) da ≤ V_p, a direct consequence of the corpus depth budget m(a) ≤ N_p(a)). | **SURVIVES (RVS conjecture; cosine = extremal case)** | CSS is the hardest case of RVS. If the energy margin is concave in the law of X² in general (true on the degree-4 family), then CSS for all a implies RVS for all LP-admissible X, and the heat law becomes a corollary. No RH content; this records the structure of the survivor. Open core: CSS for general p. |
| 74 | Formalise rows 72–73 (degree-4 family). | **[L] `HTGeometry/VerticalShiftEnergyQuarticFamily`** (standard axioms; `lake --old env lean` clean; olean built; appended to `HTGeometry.lean`): `evenQuarticStep_pairRealPairQuartic` (T p_B = Q(X²)), `evenStepQuadratic_two_mul_sub_one` (Q(2S−1) = 8S−20S²+24P for every B), `sq_add_two_mul_le_one_iff_of_evenStep_root` (exact law: v²+2S ≤ 1 ⟺ margin ≥ 0, one non-real pair, 2S < 1), `sq_add_moment_le_one_of_verticalShift_root` (every vertical average with m₂² ≤ m₄, m₂ < 1 obeys v²+m₂ ≤ 1), `cosineStep_margin` (= 4a²(1−a²), the extremal case), `exists_laguerreStep_root_energy_gt` (q − (9/20)q″ on X²(X²+1) has a root iv with v²+9/10 > 1). Lint errors at audit time come from other agents' unwired modules only. | **PROVED [L]** | Survivor bookkeeping for CSS. On this family, the cosine step is the extremal vertical average and a single Laguerre step breaks the energy law. No RH content. |
| 75 | Proof structure for CSS. (a) Cubics: p = (z+2b)((z−b)²+y²) (centred), A = p − 3a²z. (b) Stronger law CSS+: V(cos(aD)p) ≤ Σ_{y_k>a}(y_k² − a²). With the corpus depth budget m(A) ≤ N_p(a), CSS+ ⇒ CSS. (c) Path argument: scale heights y_k → t·y_k. Ψ(t) = Σ_{ty_k>a}(t²y_k²−a²) − V(A_t) is continuous (births and deaths happen at v = 0) with Ψ(0) = 0, so CSS+ follows from RIC: in the pencil A(Y) = cos(aD)(((z−x_k)²+Y)s) = A₀ + Y·cos(aD)s, dV(A(Y))/dY ≤ 1 for Y > a² and ≤ 0 for Y < a². (d) Identities: dV/dY = ½(1 − Re J), J = Σ_w w̄ C(w)/A′(w) = −(1/π)∬ C/A dA, Σ_w C(w)/A′(w) = 0, Σ_w wC(w)/A′(w) = 1. So RIC ⟺ d/dY Σ(Re w)² ≤ 0 (deep) / ≤ −2 (shallow). | (a) PROVED for all real cubics: with a pair, A = (z+2β)((z−β)²+v²), v² = y² − 3a² + 3(β²−b²), 4β³ + Kβ = b(b²+y²) (K = y²−3a²−3b² > 0, f increasing, β ≥ b). CSS ⟺ β² ≤ b²+⅔a² ⟺ F(s) = (u+⅔s)(u+1−s/3)² − u(u+1)² ≥ 0 (u = b², s = a², y = 1), and F(0) = 0, F′(s) = ⅔(u+1−s/3)(1−s) > 0 for s < ⅓. (b) CSS+ checked: stacked i,3i (10−6a² ≤ 10−2a² for a < 1; for 1 < a < 3, Q(a²−9) = 4a²(9−a²) ≥ 0), the (z²+1)(z²−b²) family, all cubics. (c) RIC checked on cubics (dV/dY = 1 + 6β(b−β)/(12β²+K) ≤ 1; V ≡ 0 below a²) and on the drag family (∂V/∂Y₁ = −(Y₂−s−V)/abs(Q′) ≤ 0 ⟺ CSS+). FALSE generalisations: pencil slope ≤ 1 for arbitrary real F + YC (z³ + Y(z−c): Σ(Re w)² rises from 0 to c²); convexity of Y ↦ V(A(Y)) (the drag family decreases on (−∞, a²]). | **PROVED (n = 3); SURVIVES (CSS+, RIC)** | The survivor now has a sharper statement (CSS+), a reduction (RIC ⇒ CSS+ ⇒ CSS) and a proof for degree 3. Open core: RIC for general s. It needs the cosine structure of both A₀ and C; general pencils fail. |
| 76 | (a) Pseudo-Laplacian route to the core: a Friedrichs/Krein restriction of the modular Laplacian (Colin de Verdière constant-term truncation, closed-geodesic or CM-point functionals) whose secular equation is ξ(s)·(zero-free factor) = 0, so self-adjointness places every zero on the line. (b) CSS survivor, product form SUB: V(cos(aD)(fg)) ≤ V(cos(aD)f) + V(cos(aD)g) for real f, g. Iterating over single pairs and real linear factors gives CSS+. Commutator identity: cos(aD)((z−x)²+Y)s = (z−x)²C − 2a(z−x)S̃ + (Y−a²)C, with C = cos(aD)s and S̃ = sin(aD)s. Real-root insertion: cos(aD)(f·(z−c)) = (z−c)C_f − a·S_f = ½[F+F^#], F = f(z−ia)(z−ia−c). | (a) KILLED by structure. The truncation secular equation is a^sξ(2s)+a^{1−s}ξ(2s−1) = 0 (Lagarias–Suzuki zeros, on the line by self-adjointness), not ξ. Krein-type restrictions give eigenvalues at zeros of a regularised Green function θ((Δ−λ)^{−1}θ), which interlace with the existing spectrum (rank-one law). A self-adjoint realisation of all ζ zeros by this design would have to match their pair correlation, which is the Bombieri–Garrett obstruction. Corpus SZ already has the Weil–Friedrichs realisations (`SuzukiFriedrichsExtension`). (b) SUB checked: (z²+1)² (V = 2−4a² ≤ 2−2a²), z⁴+4 (√(4+a⁴) − 3a² ≤ 2−2a² ⟺ 0 ≤ 4a²), drag i·3i (10−6a² ≤ 10−2a²; 4a²(9−a²) ≥ 0 for 1 < a < 3). Real-root insertion V(T(f(z−c))) ≤ V(Tf) for f a pair = the row-75 cubic theorem. | **(a) KILLED; (b) SUB SURVIVES** | SUB is the cleanest form of the survivor: the cosine-step imaginary energy is subadditive over factors. Open cores: (i) inserting a real root never raises the energy, for general f; (ii) the pair-multiplication step. For Ξ (locally finite version), SUB would give an energy-level de Bruijn law for F_a(s) = ξ(s+a)+ξ(s−a): its off-line energy is at most Σ over ξ-zeros of depth > a of (depth² − a²). |
| 77 | All-or-nothing law for the restricted Weil ground energy: inf_a μ₀(a) ∈ {0, −∞}. Under ¬RH, a test whose transform vanishes at the on-line ordinates near an off-line pair γ₀ ∓ iδ while ĝ′(γ₀) ≠ 0 gives W ≈ −2δ²ĝ′(γ₀)², and Bernstein scaling gives μ₀(a) ≲ −cδ²a² → −∞. So any aperture-uniform lower bound, however weak, would prove RH. | REDISCOVERED: corpus `CCMGroundEnergyZeroSumBound` (module doc: "the ground energy is antitone in the aperture and unbounded below under ¬RH"), with `ccmRestrictedWeilGroundEnergy_antitone` and `PaperRestrictedWeilGroundThreshold.all_zeroRank_iff_riemannHypothesis`. The weakened target (uniform lower bound) is the same receiver. | **REDISCOVERED** | Search the CCM module docstrings before proposing RW dichotomies. |
| 78 | (a) Maass–Selberg positivity: ‖Λ^T E(·,s)‖² = (T^{2σ−1} − abs(φ(s))²T^{1−2σ})/(2σ−1) + (φ(s̄)T^{2it} − φ(s)T^{−2it})/(2it) ≥ 0 with φ(s) = ξ(2s−1)/ξ(2s), as a sign source that sees ζ zeros (poles of φ at s = ρ/2). (b) Holomorphic-moment barrier: explicit formulas give only Σ_ρ h(γ_ρ) with h analytic, while the depth energy Σ(β−½)² needs (Re γ)², which is not analytic. (c) CSS survivor, real-root insertion (SUB(i)) in Blaschke form: Q_g = Q_f·B, B = (z−c+ia)/(z−c−ia), abs(B) > 1 on the upper half-plane. | (a) KILLED: the norm identity constrains poles of φ only where E(·,s) is L²-holomorphic (Re s > ½, real poles, only s = 1 for SL₂(ℤ)). The poles at ρ/2 lie in Re s < ½, where the truncated norm just blows up like abs(s−s₀)^{−2} and gives no sign information. (b) STRUCTURAL: off-line zeros enter analytic statistics as h(γ₀ − iδ), a continuation with no positivity. Every RH-detecting functional must be sesquilinear (Weil, Hermite, Hankel), so the producer must be a positivity of a sesquilinear arithmetic form. This matches the corpus receiver inventory. (c) PROVED (argument principle): every upper-half-plane root of T(f·(z−c)) lies in Ω₋(f) = {abs(f(w+ia)) < abs(f(w−ia))}, and each component Ω_j strictly inside the half-plane contains exactly n_j such roots (n_j = number of charges r_k − ia in Ω_j), the same count as the roots of Tf on ∂Ω_j. For a single pair, Ω₋ is the half-disc of radius √(y²−a²), which gives the cubic theorem. | **(a) KILLED; (b) BARRIER RECORDED; (c) PROVED (localisation); SUB(i) still open in general** | SUB(i) now reduces to a height comparison between the n_j interior roots and the n_j boundary roots in each basin Ω_j. |
| 79 | Stress SUB(i) and SUB: look for a configuration where inserting a real root, or multiplying two factors, raises the cosine-step energy. | Found the RESONANCE (frozen-root) law: if f has roots r, r′ with r − r′ = 2ia, then w = (r+r′)/2 is a root of cos(aD)(h·f) for every polynomial h, since h(w+ia)f(w+ia) and h(w−ia)f(w−ia) both vanish. Example: f = (z²+1)(z²+9), a = 2: Tf = (z²+1)(z²−15) and T((z−c)f) = (z²+1)(z³ − cz² − 31z + 15c) for every c, so V(T((z−c)f)) = V(Tf) = 1 for all c, an equality case of SUB(i). Resonant products for SUB: f = z²+y₁², g = z²+y₂² with y₁+y₂ = 2a, y₁ < a < y₂ give a frozen pair at height y₂−a, other roots real, and V(T(fg)) = (y₂−a)² ≤ y₂²−a² = V(Tg). SUB survives every resonance test. | **SURVIVES** (equality cases found) | Equality cases of SUB(i) come from resonant root pairs (vertical separation exactly 2a). A proof of SUB(i) must be tight on them, which suggests an argument that tracks roots of f(w±ia) jointly, such as a matching between the zeros of h(w+ia)f(w+ia) and h(w−ia)f(w−ia). For Ξ, resonances are vertical zero separations of exactly 2a; an off-line pair ½±δ+iγ gives only a real frozen root of cos(δD)(hΞ) at t = γ, so there is no RH content. |
| 80 | Lévy–prime reading of the restricted Weil form at aperture length L, from the corpus Lévy form (`WeilArchReLevyPoleForm`): W(g) = ∫_0^∞‖g−τ_xg‖² dM_L(x) − c_L‖g‖² + 2P(g), with jump measure M_L = ω(x)dx + Σ_{n≤e^L} Λ(n)n^{−½}δ_{log n} (positive, so the primes enter as Markov jumps) and c_L = abs(A(0)) + 2Σ_{n≤e^L}Λ(n)/√n. Is the only non-Markov part, the pole kernel 2cosh((u−v)/2) > 0, removable, so that Beurling–Deny gives positive ground states at all apertures? | Every term except the pole is a Dirichlet form, so the RH sign is a principal-eigenvalue (survival-rate) inequality for a killed jump process with arithmetic jumps. But for uniform g on [0,L] the Dirichlet part minus c_L is ≈ −8e^{L/2}/L, and only the pole term 2(∫ge^{u/2})(∫ge^{−u/2}) ≈ +8e^{L/2}/L cancels it at leading order. Off-diagonal sign: −ω(x) + 2cosh(x/2) changes sign at x ≈ 0.28 (the corpus Markov horizon log(plastic constant)). A Doob h-transform cannot fix this: conjugating by a positive weight preserves the sign of every off-diagonal kernel entry. | **KILLED (Markov repair)** | The pole is not a perturbation: it cancels the leading 8e^{L/2}/L. Any Markov or survival-probability producer must carry the rank-two pole jointly with the prime jumps. |
| 81 | Conjecture CVX: a ↦ μ₀(a) (restricted Weil ground energy) is convex on (0,∞). Since μ₀ is antitone and, under ¬RH, unbounded below superlinearly (the pair construction gives ≲ −cδ²a²), CVX would imply RH. CVX holds near 0: corpus Suzuki Thm 1.4 gives λ_a = log(1/a) + const + O(a). | FALSE at prime-power entries. By the corpus log-soft entry law (`ArchimedeanWeilSoftPrimeEntry`: end-window mass M_ε ≤ 4E/log(1/(10ε))), the overlap ⟨g, τ_{log n}g⟩ after entry by ε is O(1/log(1/ε)), so the new prime term changes μ₀ by up to C/log(1/ε), which has infinite one-sided slope at ε = 0. When the overlap is positive this is a concave kink, so convexity fails at every entry 2a = log p^k. The log(1/a) convexity of the small-aperture regime cannot persist past a = ½ log 2. | **FALSE** | Ground-energy shape receivers (convexity, log-convexity) are broken by the arithmetic entry kinks. Shape conditions would have to be prime-aware, e.g. convex between consecutive entries with controlled entry drops, and that is again the prime-error question. |
| 82 | (a) HF reduction RH ⟸ PBAP + (N1) as a prime-free target. (b) Arithmetic Poincaré form of RW positivity at aperture L: with pole = 2⟨g,cosh(u/2)⟩² − 2⟨g,sinh(u/2)⟩², RH ⟺ for every L and every g supported on an interval of length L, Σ_{jumps}‖g−τ_xg‖²·dM_L(x) + 2⟨g,cosh⟩² ≥ c_L‖g‖² + 2⟨g,sinh⟩², with c_L = abs(A(0)) + 2Σ_{n≤e^L}Λ(n)/√n. This is a spectral-gap inequality for a killed jump process with arithmetic jump rates, where the cosh rank-one term controls the flat mode. | (a) NOT PRIME-FREE: (N1) asks F̂(γ_ρ) = 0 at all ζ zeros plus zero-faithfulness (memory n1-voronoi; corpus `WeilConeXiDivisibleBlindTest`, `riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindTest`). Under RH, (N1) = NULL + zero-faithfulness, already pursued in the HF loop (rows 1012–1046), so I left it. (b) STRUCTURAL: the constant is exactly tight as L → ∞ (μ₀ → 0 under RH), so every lossy spectral-gap technique (Cheeger, Lyapunov, coupling, comparison) loses a constant factor and fails. Same verdict from the corpus rigidity facts: full Weil-positive perturbations of Λ with small deviation equal Λ (shared constraint `WeilLittleOVonMangoldtRigidity`), Λ_dBN = 0, μ₀ → 0. RH is a boundary or rigidity statement, so any producer must be an exact identity (a sum of squares W = Σ_k abs(L_k g)² with arithmetic L_k, or an equality-case argument), not an estimate with slack. | **(a) OTHER LANE; (b) STRUCTURAL BARRIER RECORDED** | Big-picture conclusion: the missing producer is an exact arithmetic sum-of-squares decomposition of the Weil form. The function-field analogue gets it from dimension counts (Riemann–Roch / Castelnuovo); over ℤ the nearest positivity source is integrality (abs(n) ≥ 1), as in transcendence methods. |
| 83 | Stepanov–Siegel auxiliary Dirichlet polynomial: assume ζ(ρ) = 0 with β > ½. Siegel's lemma gives integer a_n (n ≤ N, not all 0) with Σ a_n n^{−ρ}(log n)^j = 0 for j < J; then use integrality of the coefficients of P·ζ (a*1)(n) ∈ ℤ against analytic smallness near ρ. | KILLED: the integrality has nowhere to land. Over F_q, Frobenius-invariance (x^q = x) makes the auxiliary function vanish at all rational points, and the zero count ≤ degree gives the bound. Over ℤ no endomorphism fixes the primes with a known count; the corpus already killed Stepanov over ℤ (row 34). Turán power sums are the analytic-number-theory version of this idea and give only density and Ω results. Integrality (abs(m) ≥ 1) enters only through Dirichlet coefficients of size ≥ 1, and at Re s = β < 1 those sums do not converge, so no lower bound comes out. | **KILLED** | An integrality producer needs an arithmetic point count whose deviation is the zero sum, i.e. a Frobenius analogue. The corpus HF/Deninger lanes hold that structure (scaling flow); constructing it is the "new field". |
| 84 | Exact SOS / Krein extension. Fourier form of the restricted Weil form: W(g) = ∫abs(ĝ(r))²·S(r)dr + pole, with S(r) = A(r) − 2Re Σ_n Λ(n)n^{−½−ir}, defined modulo lag frequencies outside [−2L,2L]. By Krein's extension theorem, W_L ≥ 0 ⟺ some positive measure μ_L has μ̂_L equal to the Weil kernel on [−2L,2L] (an exact SOS ∫abs(ĝ)²dμ_L). Candidate K1: μ_L = σ_P(r)dr with the finite-Euler symbol σ_P(r) = 2Re(ξ_P′/ξ_P)(½+ir), ξ_P = Γ_ℝ(s)·Π_{p≤P}(1−p^{−s})^{−1}, P ≥ e^{2L}. It has exactly the right lag data up to 2L, since prime powers above e^{2L} do not interact. K2: an atomic extension μ_L = πΣδ over the zeros of a real-rooted approximant whose explicit formula matches ζ up to lag 2L. | K1 FAILS. σ_P ≥ 0 pointwise is the Gonek purity gate Re Σ_{p≤P}(log p)p^{−½−ir}/(1−p^{−½−ir}) ≤ ½log(r/2π). It fails for r < 2π (A(r) < 0 there; only the pole term can compensate) and for P ≫ (log r)² (large values; the moment method reaches only (log r)^{1−ε}, row-71 analysis). Compensation must come from lag-frequency corrections beyond 2L, which is the extension problem itself. K2: Gonek approximants are not Euler products and their log-derivatives are not Dirichlet series, so their explicit formulas do not match ζ's. A real-rooted entire function matching ζ's explicit-formula data on [−2L,2L] for every L is the corpus Hamburger/cone receiver (HF: cone ⊆ {Λ}). | **K1 FALSE; K2 CIRCULAR** | Krein's extension is the exact form of "Weil positivity = existence of a positive spectral measure". A producer would have to construct the extension, e.g. a de Branges/canonical-system structure (corpus SZ lane, Suzuki screw). Finite Euler products give the correct lag data but not positivity, because the purity gate fails at low r and at long lengths. |
| 85 | (a) SZ / de Branges lane: Krein-extension producer from canonical systems. (b) Formalise the row-75 cubic theorem. | (a) The corpus SZ open step ("source Wronskian law…", screw nonnegativity) is the Suzuki screw positivity, equivalent to RH. The one-prime test of a finite-Euler de Branges structure fails at r = 0: σ₂(0) = A(0) − 2log2·(1/√2)/(1−1/√2) ≈ −5.37 − 3.35 < 0, so only the pole can compensate and positivity of the extension is not structural. (b) **[L] `HTGeometry/CubicCosineStepEnergy`** (standard axioms; `lake --old env lean` clean; olean built; appended to `HTGeometry.lean`): `sq_im_add_sq_le_of_cubicCosineStep_root`. For every real cubic p = (X−c)((X−b)²+y²), every root w of p − (a²/2)p″ with Im w > 0 satisfies (Im w)² + a² ≤ y². Reusable: `cubicCosineStep_core` (centred form v² = 3u²+K, 4u³+Ku = d(d²+y²) ⇒ v²+a² ≤ y²), `cubic_key_ineq`, `cubic_binom_ineq`. | **(a) RH-EQUIVALENT; (b) PROVED [L]** | CSS (= CSS+ in degree 3) is now a theorem for all real cubics. No RH content. |
| 86 | (a) RIC in rational-function form: with Φ = cos(aD)((z−x)²s)/cos(aD)s = (z−x)² − a² − 2a(z−x)·S̃/C, the pencil roots are Φ^{−1}(−Y), and RIC ⟺ Σ_{w∈Φ^{−1}(−Y), Im w>0} Im w·Im(1/Φ′(w)) ≥ −½ (Y > a²) or ≥ 0 (Y < a²). Single pair: equality (w = iR, 1/Φ′ = −i/2R). (b) Localised heat Lyapunov law for Ξ: nonreal zeros of H_t up to height T ≲ Σ_{γ≤T}(β−½)²/(2t) ≤ 0.034T/t, using the corpus off-line moment ≤ 0.067T. (c) Prime-sign cone: Weil positivity on tests with k(log n) ≤ 0 for all n ≥ 2 reduces to arch + pole ≥ 0 there (prime-free). | (a) REFORMULATED, OPEN: Φ ~ z² − a²(2n−3) at ∞, and Herglotz-type behaviour of Φ would forbid upper-half-plane roots. The sign of Im(1/Φ′) at roots off the Herglotz region is uncontrolled. (b) SUBSUMED: Ki–Kim–Lee (corpus `KiKimLeeWeylHorizon`) already gives finitely many nonreal zeros for each fixed t > 0, far stronger than ≪ T/t. (c) NOT A PRODUCER: the cone {k(log n) ≤ 0} contains the prime-blind tests (PBAP, HF lane) and adds prime-negative tests, which only help positivity. Positivity there is a strengthened PBAP and still does not reach all tests. RH needs every test, or the HF rigidity witness (N1). | **(a) OPEN; (b) SUBSUMED; (c) INSIGNIFICANT** | — |
| 87 | Explicit Krein extension at small aperture, read from the corpus √2 certificate (`PoleVanishingWeilPositivityHalfLogTwo`: pole-vanishing tests, 14 frequency shells, trace certificate α = 3/10). Pole-vanishing ĝ = (r²+¼)ĥ with h supported in the same interval, so polar positivity ⟺ ∫S(r)(r²+¼)²abs(ĥ)² ≥ 0 on PW_a, S(r) = A(r) − 2Re Σ_{n≤e^{2a}}Λ(n)n^{−½−ir}. Krein: ⟺ S̃ = S·(r²+¼)² = (positive measure) + (distribution with Fourier support outside [−2a,2a]). | The explicit extension is a Beurling–Selberg-type one-sided correction P (spectrum off [−2a,2a], mean zero) with S̃ + P ≥ 0. Its canonical form is the de Branges/Krein structure dr/abs(E_a)², with E_a Hermite–Biehler ⟺ W_a ≥ 0, which is the corpus SZ/Burnol/Suzuki lane. The √2 certificate is not an explicit measure. It is a trace bound that uses the near-collinearity of e_ξ with span e^{±x/2} at low ξ (L² distance O(ξ²)); the (r²+¼)² weight is the same mechanism. An analytic certificate past ½log 2 has no slack: the negative dip region abs(r) < 2π against aperture a gives a·r₀ ≈ 2.2 at the first prime, so only numerical shells close it (computation, pod-only). | **REDISCOVERED (de Branges / Beurling–Selberg form)** | The finite-aperture producer is computational at each aperture and RH-equivalent in the limit; "explicit Krein extension" names the same object as the SZ lane. Do not re-open without an analytic family of minorants that is uniform in the aperture. |
| 88 | Deep corpus search (`research --mode deep`, query "exclude off-line zero pair near critical line from Euler product and functional equation") for ingredients not yet used on the shallow-pair core. Side check: Gaussian wave-packet tests g_{σ,t}. An off-line pair contributes 2e^{−σ(u²−δ²)/2}cos(σuδ) (u = γ₀−t), which is positive at u = 0 and negative only for abs(u) > π/(2σδ), where it is bounded by e^{−π²/(8σδ²)+σδ²/2}. | Only ingredient set returned: `HTGeometry.frame_zero_exclusion` (FiniteAmplifierFrame). That is the finite-amplifier barrier: every finite positive-pattern (3-4-1-type) derivation excludes zeros only to width δ𝔏 < C(pattern), i.e. de la Vallée Poussin shape C/log t, and the detection/pole ratio must exceed 1. Not a near-line ingredient. Wave packets detect a pair only at widths σ ≫ 1/δ² (aperture ≫ 1/δ), against an on-line background e^{−σ(γ−t)²/2} of density log t. This is the corpus HCF/TH Gaussian heat-Hankel receiver (negative index = off-line count, ordinate horizon O(N√log N)). | **NO NEW INGREDIENT (corpus confirms barriers)** | Every positivity-from-Euler-product ingredient in the corpus is a σ ≥ 1 − C/log t device. The near-line problem has no corpus ingredient beyond RH-equivalent receivers. Record: the deep search is exhausted on this query; vary the query toward integrality, Frobenius analogues or exact identities next time. |
| 89 | Second deep search (query on integrality / exact identities / Frobenius analogue / sum of squares of the Weil form). It surfaced only `finiteWeilCoupling_pairing` (finite NN couplings, WeilLogShift lane), Euler-characteristic exact sequences and `HTGeometry.GarlandLocalization`. Conjecture tested: Garland-type local-to-global positivity, W = Σ_v W_v with each place a "link", where local spectral gaps above a threshold would force global Weil positivity. | KILLED. (i) There is no simplicial complex: the local Weil terms W_p(g) = −Σ_k (log p)p^{−k/2}(k_g(k log p) + k_g(−k log p)) are not link Laplacians, and none is positive (each is a signed shift form). (ii) The natural complexes (S-arithmetic quotients of Bruhat–Tits trees × ℍ) carry ζ only through Eisenstein series, whose Hecke eigenvalues p^{s−½} + p^{½−s} are tempered on Re s = ½ by construction. ζ zeros are scattering poles, not Hecke spectrum, so Garland/property-T gaps give Selberg/Ramanujan-type cusp-form bounds, not RH. | **KILLED** | Both deep-search directions (positivity ingredients; integrality/exact identities) are exhausted in the corpus index. |
| 90 | Read the newest corpus split (`AsymptoticAbscissaLawProducers`, `PrimeSideRiemannHypothesisSplit`): RH ⟺ ZAL (zeros approach the line: finitely many right of ½+h for each h > 0) ∧ AAL (asymptotic abscissa law: finitely many right of ½+h forces none; equivalently, no attained top). Attack AAL alone as a rigidity statement: an attained top β₀ = Θ > ½+h with finitely many zeros above ½+h makes ψ(x) − x a finite power-wave Σ c_j x^{β_j}cos(γ_j log x + φ_j) + O(x^{½+h+ε}). Look for an elementary or sieve constraint on primes that forbids a pure finite top wave. | KILLED for all inputs I tried. (i) Positivity Λ ≥ 0: d/dx[x − 2Re(x^{ρ₀}/ρ₀)] = 1 − 2x^{β₀−1}cos(…) > 0 for large x, so monotonicity holds. (ii) Brun–Titchmarsh ψ(x+y) − ψ(x) ≤ (2+ε)y for y ≥ x^ε: the wave changes counts by ≍ y·x^{β₀−1} = o(y), consistent. (iii) Short-interval lower bounds (y = x^{0.525}): consistent. (iv) Elementary-error sequences (μ²: Σ_{n≤x}μ²(n) = 6x/π² + O(√x) unconditionally) see ζ zeros only through ζ(2s), i.e. at ρ/2 with Re ≤ ½, so they say nothing. (v) Multiplicativity (ζ², ζ(s)ζ(s∓iγ₀) with nonnegative coefficients) only gives Landau singularities at σ_c = 1. The corpus already records that one isolated off-line copy needs a relative power-saving prime-error input to contradict (frontier map WL). | **KILLED** | AAL and ZAL are independent halves, and every unconditional prime constraint (positivity, sieve, elementary counts) is blind to a finite top wave of exponent < 1. AAL is a genuine rigidity question with no corpus or literature producer: is the supremum of Re ρ attained? |
| 91 | Weak AAL (finite-top exclusion): if Θ = sup Re ρ > ½ is attained, infinitely many zeros attain it. Mechanism sought: an attained finite top makes −ζ′/ζ − 1/(s−1) + Σ_{top}1/(s−ρ_j) continuous up to Re s = Θ (away from height-infinity accumulation), so a Wiener–Ikehara step gives ψ(x) = x − 2Re Σ_{top} x^{ρ_j}/ρ_j + o(x^Θ): a pure finite sinusoid at the top exponent. Look for a contradiction from multiplicative identities (μ*1 = δ, Λ = μ*log) or inequalities (abs(μ) ≤ 1, λ = ±1, μ² density). | KILLED. Identities are automatically consistent, since both sides come from the same ζ. Inequalities: M(x+y) − M(x) ≤ y is met by an x^{Θ}-wave with derivative O(x^{Θ−1}); the Liouville and μ² sums have generating functions ζ(2s)/ζ(s) and ζ(s)/ζ(2s), whose extra singularities sit at ρ/2 (Re ≤ ½) and are consistent with elementary O(√x) errors. Ingham's two-sided Ω(x^Θ) amplitude 2/abs(ρ₀) is matched exactly by the sinusoid. No unconditional prime or Möbius constraint distinguishes "finite top" from "infinite top". | **KILLED** | The finite-top question is as open as AAL. Every unconditional arithmetic inequality has slack o(x) or O(√x)-for-shifted-zeros and cannot see a sub-x top wave. |
| 92 | ζ as a limit of RH-true functions through the Lagarias–Suzuki family a_y(s) = y^s ξ(2s) + y^{1−s} ξ(2s−1). For y ≥ 1 every zero lies on Re s = ½ (self-adjointness of the pseudo-Laplacian). As y ↓ 0 the zeros leave the line and converge to 1 − ρ/2 and ρ/2, with real parts 1 − β/2 and β/2. Conjecture: the zero flow s(y) in log y has Re s = ¾ as an attractor, so the endpoints are forced onto ¾ and ¼ (⟺ RH). | CIRCULAR: the roots satisfy y^{2s−1} = −ξ(2−2s)/ξ(2s), so ds/d(log y) = (2s−1)/(Φ′/Φ(s) − 2log y) → 0 as log y → −∞. The limit points are the zeros of ξ(2−2s), whatever their real parts; the flow carries no monotone quantity, and Re s(y) just interpolates from ½ to 1 − β/2. The same holds for every known RH-true family that converges to ζ (cosine levels a → 0, Gonek X → ∞, Pólya/Ki truncations): the endpoint is ζ's own divisor, so the limit transfers nothing. | **CIRCULAR** | A Hurwitz-limit producer needs a family whose zeros stay on the line all the way to the limit, uniformly. Every known family leaves the line exactly where its approximation of ζ becomes faithful, which is the same "purity ends where faithfulness starts" boundary recorded in WD row 316. |
| 93 | Euler-preserving deformation as a Hurwitz producer: find a continuous family F_λ that keeps the Euler product (and the functional equation), has zeros provably on the line for λ in an open set, and tends to ζ. Candidates: (i) prime damping ζ_λ = Π_p(1 − λp^{−s})^{−1}; (ii) Bohr-torus points F(s;z) = Π_p(1 − z_p p^{−s})^{−1}, z ∈ T^∞; (iii) twist averages Σ_τ w(τ)ζ(s+iτ), w ≥ 0. | KILLED. (i) On σ > ½, ζ_λ = ζ(s)^λ·H_λ(s) with H_λ holomorphic and zero-free there, so ζ zeros become branch points of ζ_λ (λ ∉ ℤ); the family has no functional equation and no real-zero structure. (ii) Generic F(·;z) is zero-free on σ > ½ almost surely (Kolmogorov, exp of an a.s. convergent series), but ζ and its vertical shifts are the measure-zero Kronecker orbit z_p = p^{−iτ}. "ζ is generic" is Bagchi strong recurrence ⟺ RH (corpus BAG). (iii) A sum of Euler products is not an Euler product, so Davenport–Heilbronn-type off-line zeros occur. Structural reason: the Selberg class in degree 1 is rigid (ζ(s+iθ), L(s+iθ,χ)), so the only continuous Euler-and-FE-preserving deformation of ζ is the trivial vertical shift. | **KILLED** | Together with row 92: any limit producer must break the Euler product or the functional equation, and then zeros leave the line ("purity ends where faithfulness starts"). Rigidity of the Selberg class closes the deformation-producer class. |
| 94 | Extend the cubic theorem to every degree with one non-real pair: p = ((X−x)²+y²)·g, g real-rooted. Mechanism: the Blaschke localisation of row 78(c) applied to all real roots at once. Each real factor satisfies abs(w+ia−r) ≥ abs(w−ia−r) (difference of squares 4a·Im w), so abs(g(w+ia)) ≥ abs(g(w−ia)) and therefore abs(q(w+ia)) ≤ abs(q(w−ia)). The pair identity F(v+a) − F(v−a) = 8va(u²+v²+a²−y²) then confines w to the disc. | **[L] `HTGeometry/PairTimesRealRootedCosineStep`** (standard axioms; `lake --old env lean` clean; olean built; appended to `HTGeometry.lean`; uses the corpus `shiftAvg`): `sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_root`. For a > 0, g ≠ 0 with only real roots, every root w of (p(z+ia)+p(z−ia))/2 with Im w > 0 satisfies (Re w − x)² + (Im w)² + a² ≤ y². Reusable: `normSq_eval_sub_le_add_of_real_roots` (real-rooted factors grow upward), `normSq_pair_add_sub_normSq_pair_sub`. With the corpus depth budget (≤ one non-real pair survives) this gives CSS and CSS+ for every polynomial with exactly one non-real pair, any degree. Supersedes the cubic module in content. | **PROVED [L]** | The open part of CSS is now confined to two or more non-real pairs (the drag/resonance interactions). No RH content. |
| 95 | Shallow pairs act like real roots: for y_j² ≤ a² and Im w ≥ 0, abs(q_j(w−ia)) ≤ abs(q_j(w+ia)), since F(v+a) − F(v−a) = 8va(X + v² + a² − y_j²) ≥ 0. So the one-deep-pair disc law extends to p = q·g·∏ shallow pairs. | **[L] added to `HTGeometry/PairTimesRealRootedCosineStep`** (standard axioms; audit clean; olean rebuilt): `normSq_shallowPair_sub_le_add`, `shallowPairs`, `normSq_eval_shallowPairs_sub_le_add`, `sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_shallow_root`. Every upper-half-plane root of cos(aD)p, with p = ((X−x)²+y²)·g·∏_{j∈s}((X−x_j)²+y_j²), g real-rooted, y_j² ≤ a², lies in the disc (Re w − x)² + (Im w)² + a² ≤ y². With the corpus depth budget (≤ one surviving pair), CSS+ holds for every real polynomial with at most one pair of height > a. | **PROVED [L]** | Open core of CSS/CSS+ is now exactly the configurations with ≥ 2 deep pairs (height > a). There every root lies in Ω ⊂ ∪_k D_k (D_k = disc of radius √(y_k²−a²)), but the drag example puts two roots in one disc, so a joint (sum) argument is needed. No RH content. |
| 96 | Two-pair resolvent bound for CSS+. Centred p = ((X−ξ)²+Y₁)((X+ξ)²+Y₂); on quartics cos(aD) = 1 − (a²/2)D² + (a⁴/24)D⁴. If cos(aD)p = ((X−u)²+V₁)((X+u)²+V₂), then with t = u² and T₀ = ξ²+2a², ψ(τ) = τ(2τ+b)² − (ξ(Y₁−Y₂))²/4 − c₀τ (b = c₂/2) has ψ(t) = 0, ψ(T₀) = 2a²((Y₁+Y₂)T₀ + (Y₁−Y₂)²/4) ≥ 0, and ψ(t) − ψ(T₀) = (t−T₀)[(2a²(Y₁+Y₂) + (Y₁−Y₂)²/4 + 4T₀(2T₀+b)) + 4(t−T₀)(t+2T₀+b)] with 2T₀+b = ξ²+a²+(Y₁+Y₂)/2 > 0. So t ≤ T₀, i.e. V₁+V₂ ≤ Y₁+Y₂−2a². | **[L] `HTGeometry/QuarticTwoPairCosineStep`** (standard axioms; audit clean; olean built; appended to `HTGeometry.lean`): `add_le_of_evenQuarticStep_twoPair` (no sign hypothesis on V₁, V₂ needed), core `twoPair_resolvent_bound`. Paper corollary: CSS+ holds for every real quartic. Two surviving pairs use this theorem. One surviving pair lies in D₁ ∪ D₂, since outside both discs every pair factor strictly grows upward (row 95 mechanism), so v² ≤ max(y_k² − a²). No surviving pair is trivial. | **PROVED [L] (two-pair case); CSS+ for degree ≤ 4 complete on paper** | Open core of CSS+: ≥ 2 deep pairs in degree ≥ 5, i.e. extra real roots or shallow pairs alongside two deep pairs, or three or more deep pairs. The resolvent mechanism (half-separation u² ≤ ξ² + 2a²) suggests the general law "the cosine step spreads the deep pairs' horizontal variance by at most 2a² per pair". No RH content. |
| 97 | (a) Weil cone nonemptiness as a positive Guinand–Weil quasicrystal problem. Find any λ on integers (n = 1 allowed) such that h ↦ ĥ(i/2) + ĥ(−i/2) + ∫A ĥ − Σλ(n)n^{−½}(h(log n) + h(−log n)) is a positive measure ν on ℝ. Then the corpus HF rigidity (an (N1) witness forces cone ⊆ {Λ}) would give λ = Λ and RH. (b) CSS+ horizontal-spread form X_A − X_p ≤ a²(n(n−1) − 2N_deep) − 2Σ_shallow y², tested on the quintic z·((z−ξ)²+Y)((z+ξ)²+Y). | (a) CIRCULAR: the pole term needs Σλ(n)n^{−½}δ_{log n} ≈ e^{x/2}dx to RH precision. A positive ν is an RH-true degree-1 object with ζ's Gamma factor; even primitive Dirichlet characters change only the n = 1 mass (conductor term log q·δ₀) and need GRH. Non-atomic ν cannot absorb the exponential pole growth, and GL(1) rigidity leaves no other source. (b) SURVIVES. A = z·B(z²), B(t) = t² + (2(Y−ξ²)−10a²)t + ((ξ²+Y)² − 6a²(Y−ξ²) + 5a⁴). Complex roots of B: V_A = √γ + β/2, and CSS+ ⟺ γ ≤ (Y+ξ²+3a²)² ⟺ 0 ≤ 12a²Y + 4a⁴. Real negative roots: V_A = 2(Y−ξ²) − 10a² ≤ 2Y − 2a². | **(a) CIRCULAR; (b) SURVIVES (degree 5, symmetric)** | Cone nonemptiness is a "positive Fourier quasicrystal with prescribed smooth part" problem and is RH-strength through GL(1) rigidity. |
| 98 | MC route producer via sieve: the receiver Σ_{s<N}(ψ(s²) − s²) ≤ BN² is the one-sided weighted bound Σ_{n<N²}Λ(n)(N−√n) ≤ N³/3 + O(N²), with relative error X^{−½} at X = N². Can Selberg/Brun upper-bound sieves, which are one-sided, supply it? Also: CSS survivor bookkeeping. | KILLED: sieve upper bounds lose a constant factor (≤ (2+ε)·main for short weights; parity barrier). For long smooth weights the only unconditional bound is the PNT with zero-free-region error, and one-sided exponent bounds equal two-sided ones (Landau–Ingham: ψ(x) − x ≤ Cx^θ ⇒ Θ ≤ θ). The receiver needs RH-precision cancellation. Bookkeeping: created card `1-in-progress/cosine-step-imaginary-energy-law.md` (CSS+), collecting the proven cases ([L] one deep pair any degree; [L] two-pair quartic; [L] cubics; [L] degree-4 extremality; [paper] all quartics), the falsified strengthenings and the open core. | **KILLED (MC sieve); card created** | Every live-route "Needs" I re-read (FU, RP, PA, MC) is a one-sided bound at RH precision. Unconditional one-sided tools (sieves, positivity) lose constant factors, and unconditional two-sided tools (zero-free regions) lose powers of log. |
| 99 | Wall audit of rows 70–98 against the corpus RH-core walls catalogue (memory `rh-core-walls-catalogue`, walls 1–10). Plus CSS+ check for three deep pairs (even sextic (z²+Y₀)((z−ξ)²+Y)((z+ξ)²+Y)) at first order in a². | Audit: rows 76 (pseudo-Laplacian, wall 4), 78/83 (Maass–Selberg, Stepanov: walls 6, 5), 80/81/87 (Markov, convexity, Krein: Weil-affine wall 8), 84/92/93 (finite-Euler and deformation limits: walls 4, 6 and "purity ends where faithfulness starts"), 88/89 (amplifier, Garland: walls 6, 5), 90/91 (AAL inputs: wall 1), 97 (quasicrystal: wall 9 temperedness and GL(1) rigidity), 98 (MC sieve: wall 1). No attempt named an input passing a wall, so they were wall rediscoveries. Sextic: to first order cos(aD) = heat at τ = a²/2 and ΔV ≈ −a²Σ_{k<j}sin²arg(z_k−z_j) ≤ −3a² (the three conjugate pairs contribute 1 each), consistent with CSS+. Higher order is not checked by hand. | **AUDIT (no new RH input); CSS+ consistent at first order** | Process rule (saved in memory): before an RH-core cycle, name the wall and the concrete input that passes it, or skip the attempt. Live inputs not yet tried against walls: temperedness used quantitatively (wall 9), and Connes' scaling flow as a Frobenius (wall 5). |
| 100 | The two inputs left untried by row 99. (i) Wall 9 (temperedness used quantitatively): the countermodel ζ(s−a)ζ(s+a) has Euler product, FE and growth but log-derivative coefficients Λ(n)(n^a + n^{−a}). Does a bound abs(λ(n)) ≤ C log n inside the Weil form give a sign? (ii) Wall 5: Connes' scaling flow as Frobenius. | (i) In the Weil form, temperedness fixes only the leading order: the prime terms Σ_{n≤e^{2L}}Λ(n)n^{−½}(…) cancel the pole term e^{L/2} (PNT level). For the countermodel the pole moves to s = 1 ± a and the prime sum grows like e^{L(½+a)}, consistently. The RH content is second order, and the known quantitative users of temperedness (mollifiers with abs(μ) ≤ 1, Zeta23 Gram/pair-correlation traces with Σ Λ(n)²/n) produce proportions, which is wall 7. Tempered Euler product + FE ⇒ RH is degree-1 Selberg-class GRH, so no producer comes from the input alone. (ii) Positivity of the scaling-flow trace formula is Weil positivity (corpus HF/Connes lanes), so this is circular. | **(i) WALL 9 → WALL 7; (ii) CIRCULAR** | Both catalogue inputs are already absorbed: temperedness yields only statistical producers, and the Frobenius analogue only restates Weil positivity. None of the ten walls has a known passing input in the corpus. |
| 101 | (a) Wall 6 input attempt: Euler-factor positive-definiteness. Each local factor (1 − p^{−σ−it})^{−1} = Σ_k p^{−kσ}e^{−ikt log p} is positive definite in t for every σ > 0, including the strip, and finite products stay positive definite. (b) Exact energy identity for the cosine step via log|½(P₊+P₋)| = (f₊+f₋)/2 + ½log((cosh U + cos Φ)/2), with U + iΦ = log(P₊/P₋) = Σ_k L_k, L_k = log((z−r_k+ia)/(z−r_k−ia)). | (a) KILLED (wall 6 restated): the positive-definite limit as P → ∞ is the measure Σ n^{−σ}δ_{log n}, which is not tempered for σ < 1 (growth e^{(1−σ)x}, the s = 1 pole). log ζ has nonnegative coefficients only for σ > 1, and the pole-regularised series has signed coefficients (Λ(n)−1)/log n with abscissa ½ ⟺ RH (corpus DR). Positive-definiteness does not survive past absolute convergence. (b) DERIVED, but circular: V(A) − V(p) = (1/2π)∬[log abs(cosh(½Σ_k L_k)) − Σ_k log abs(cosh(½L_k))]dA (x-first strips). The single-root term integrates exactly to −πa², i.e. ∫(abs(t) − ½abs(t−a) − ½abs(t+a))dt = −a², which cancels na²/2. The defect integrand equals log abs(A/p), the area identity of row 69. | **(a) KILLED (wall 6); (b) REFORMULATION, no new content** | The "non-additivity of log cosh over the dipole field" view says CSS+ is a superadditivity defect, but proving its sign is the open core again. |
| 102 | Disc localisation for any number of pairs (refined de Bruijn): every root w with Im w > 0 of (p(z+ia)+p(z−ia))/2, p = g·∏_{k∈s}((X−x_k)²+y_k²), g real-rooted, lies in some closed disc (Re w − x_k)² + (Im w)² + a² ≤ y_k². | **[L] added to `HTGeometry/PairTimesRealRootedCosineStep`** (standard axioms; audit clean; olean rebuilt): `exists_disc_of_shiftAvg_pairs_root`, `normSq_pair_add_sub_sub`. Proof: outside all discs each pair factor grows strictly upward (8va(X + v² + a² − y²) > 0) and the real roots grow weakly, so abs(p(w+ia)) > abs(p(w−ia)), contradicting the root equation. A vanishing lower factor forces a vanishing upper pair factor, placing w + ia on a pair root and w inside that disc (margin 2av). This sharpens de Bruijn's strip bound (Im w)² + a² ≤ max y_k² to a union of discs centred on the real axis below each pair. Completes on paper the last formal gap for quartics: a single surviving root of two deep pairs satisfies v² ≤ max(y_k² − a²). | **PROVED [L]** | CSS+ open core unchanged: two or more surviving roots inside one disc (drag). The sup form is now complete; the open problem is the sum form. |
| 103 | (a) RIC check on the two-pair quartic via the resolvent. With φ(t;Y₁) = 0, dt/dY₁ = −∂_{Y₁}φ/∂_tφ and ∂_{Y₁}φ = 2(t−ξ²−a²) + (Y₁−Y₂)(t−ξ²)/(2t), so RIC (dV/dY₁ ≤ 1 ⟺ dt/dY₁ ≤ 0) ⟺ ∂_{Y₁}φ ≥ 0. (b) Disc law for Ξ: off-line zeros of F_a(s) = ξ(s+a)+ξ(s−a) lie within horizontal distance √(δ²−a²) of an off-line ξ-zero of depth δ > a (forward transfer ξ → F_a). (c) Wall 5 input: the Hodge index on the square of the Connes–Consani arithmetic site. | (a) Symmetric case Y₁ = Y₂: t ≈ ξ² + a²(Y+2ξ²)/(Y+ξ²) > ξ² + a², so ∂φ > 0 and RIC holds. Asymmetric with t ∈ [ξ², ξ²+a²] and Y₁ < Y₂ has an uncontrolled sign. Since CSS+ is proved for all quartics, RIC may be strictly stronger than needed; the path argument stays sufficient but unverified. (b) A forward transfer only. RH needs F_a → ξ, which the corpus already has under LH (`LindelofOffLineSparse`). It refines the corpus cosine strip (`XiCosineShiftHeatStrip`) but is not a producer, so not pursued. (c) KILLED: no Hodge-index-capable surface exists. Connes–Consani give Riemann–Roch for Spec ℤ-bar on the arithmetic site, not an intersection theory on its square, and scaling-flow positivity is Weil positivity (row 100(ii)). | **(a) PARTIAL; (b) NOT A PRODUCER; (c) KILLED (wall 5)** | — |
| 104 | Census of positivity sources as cheap conjectures on the common open step ("positivity must be created"), each checked against the walls catalogue: (1) abs(ζ)² ≥ 0; (2) Λ ≥ 0; (3) abs(μ) ≤ 1, μ² ≤ 1; (4) Φ(u) > 0 (Ξ positive definite in t); (5) θ(iy) > 0 and E(z,u) > 0; (6) Nyman–Beurling Gram matrices; (7) Hecke self-adjointness; (8) Lee–Yang ferromagnetism; (9) Bost–Connes KMS/Gibbs states; (10) random Euler products; (11) Hodge index; (12) total positivity of Φ; (13) Hermite–Biehler interlacing; (14) Hilbert–Pólya self-adjointness; (15) log-convexity of abs(ξ) in σ. | All absorbed: (1) wall 2 (quadratic, not log); (2) wall 6 (σ > 1 only); (3) walls 1/9 (bounds lose constants); (4) Ξ(0) ≥ abs(Ξ(t)) only, and Pólya needs PF structure while Φ is not PF₅ (corpus TH/LA); (5) wall 6 (u > 1 only); (6) positivity automatic, RH = completeness (receiver); (7) cusp spectrum only, ζ zeros are scattering poles (row 89); (8) Lee–Yang fake zetas killed (early rows); (9) KMS states exist only for real β > 1 (wall 6); (10) wall 7; (11) wall 5; (12) PF₅ fails (certified, corpus); (13) and (14) are RH-equivalent receivers (corpus HJ/SZ/HF); (15) holds on the real axis only (Hadamard: log abs(1 − σ/ρ)² is convex where abs(σ−β) < abs(γ)). | **ALL KILLED / ABSORBED** | Every known positivity source is either confined to the region of absolute convergence or is a receiver. No source creates positivity at σ = ½ with first-order sensitivity to the depth of an off-line pair. |
| 105 | (a) CSS+ via heat × residual: cos(aD) = M(D)·e^{−a²D²/2} with M(ξ) = e^{a²ξ²/2}cos(aξ) = Π_k(1−c_kξ²)e^{c_kξ²}. M preserves single pairs (V unchanged), so if V(M(D)q) ≤ V(q) for all q, the heat Lyapunov law would give CSS+. (b) Quintic reformulation (two deep pairs + one real root): CSS+ ⟺ X_A − X_p ≤ 16a² = a²(n(n−1) − 2N_deep). (c) Wall 4 input "work on the axis": Gram-point sign patterns (−1)^n Z(g_n) > 0 as a deterministic on-line counter. | (a) FALSE: on quartics M(D) = 1 − (a⁴/12)D⁴. For q = (z²+1)(z²−L²), q − 2a⁴ has Q(−1) = −2a⁴ < 0, so the negative u-root lies below −1 and V(Mq) > 1 = V(q). The residual increases energy, so the factorisation cannot prove CSS+ (it does give V(Mq) = V(q) for stacked pairs). (b) Reformulation only; the real-rooted value is 20a², and pairs must reduce the spread by 4a². (c) KILLED: Gram's law fails for a positive proportion of Gram points (Titchmarsh; about 27%), and Rosser's rule fails eventually (Lehman). Axis sign counts give lower bounds (Hardy, Selberg, Levinson, proportions), never N₀ = N deterministically. | **(a) FALSE; (b) REFORMULATED; (c) KILLED (wall 4)** | Axis-based methods pass wall 4 only as lower bounds, which is wall 7 again. |
| 106 | SUB(i) via an exact height formula. The roots of G_c = T(f·(z−c)) = (z−c)C − aS are the level set R(w) = c of R = w − aS/C. With log Q = log(f(w+ia)/f(w−ia)) = U + iθ, one has S/C = tan(ψ/2) for Q = e^{iψ}, hence Im(S/C) = −sinh U/(cosh U + cos θ) and Im R = v + a·sinh U/(cosh U + cos θ). | DERIVED (exact): every upper-half-plane root of T(f·(z−c)), for every real c, has height v = a·sinh(−U(w))/(cosh U(w) + cos θ(w)), with U < 0 (so w ∈ Ω₋(f), matching row 78). As c → ∞ the root tends to the 0/0 point U = 0, θ = π, a root of Tf. SUB(i) ⟺ Σ over the level-c points of [a·sinh(−U)/(cosh U + cos θ)]² ≤ V(Tf); the bound a·sinh(−U)/(cosh U − 1) = a·coth(−U/2) alone is not enough. Not closed. | **REFORMULATED (exact height formula); SUB(i) open** | The height is the "dipole field" value at the root. A proof of SUB(i) needs a monotonicity of v along the level curves Im R = 0 from the boundary ∂Ω₋ (c = ∞) inward. No RH content. |
| 107 | SUB(i) (inserting a real root never raises the cosine-step energy: V(T(f·(z−c))) ≤ V(Tf)), tested at large abs(c). For large c, the surviving root near each upper root ω of C = Tf moves by w − ω = κ/c + O(c^{−2}), with κ = −aS(ω)/C′(ω) = −1/Σ_k ((ω−r_k)² + a²)^{−1} (from (log Q)′ = −2iaΣ_k((z−r_k)²+a²)^{−1} and E^#(ω) = −E(ω)). | FALSE. For f = (z²+1)(z−r₀), r₀ ≠ 0 and small a: δω = −(a²/2)(2r₀ + i(3+r₀²))/(1+r₀²) and Im κ ≈ 2a⁴r₀/(r₀²+1)² + O(a⁴)·(…) ≠ 0 generically. Taking sign(c) = sign(Im κ) and abs(c) large, the surviving root's height exceeds v(Tf), so V(T(f(z−c))) > V(Tf). Symmetric configurations (a single pair, stacked pairs, the two-pair quartic family) have real κ, which is why every earlier test passed. SUB (subadditivity over factors) is therefore FALSE as well (take g linear). CSS+ is unaffected: its bound is per deep pair (Σ(y_k² − a²)), and the [L] disc theorem gives V(T(f(z−c))) ≤ 1 − a² here. | **FALSE (SUB(i), SUB)** | Correct the survivor: compare against the per-pair bound Σ_deep(y_k² − a²), never against V of a sub-product. Open core of CSS+ unchanged: ≥ 2 deep pairs with ≥ 2 surviving roots in one disc. Card `cosine-step-imaginary-energy-law.md` needs SUB moved to "falsified strengthenings". |
| 108 | (a) RIC after the row-107 failure. Shallow branch: raising a shallow pair's Y moves the surviving deep root by dw/dY = −(q₂(w) − a²)/A′(w) (quartic, q₂ = the other pair), whose imaginary part is ≤ 0 in the stacked case (row 75) but uncontrolled for x₁ ≠ x₂. (b) Robustness of CSS+ itself: is the margin small anywhere? (c) Wall 8 input (nonlinear in Λ): prime pair-correlation and variance positivity (Montgomery F(α) ≥ 0, short-interval variances). | (a) SUSPECT: like SUB(i), the shallow branch of RIC rests on the same symmetry that made κ real, so it probably fails for asymmetric configurations. The path proof of CSS+ is therefore not available in general, but quartic CSS+ stands by the resolvent (row 96) and the disc localisation (row 102). (b) Two-pair margin φ(T₀) = 2a²((Y₁+Y₂)T₀ + (Y₁−Y₂)²/4) is O(a²) relative, and the asymmetric real-root effects are O(a⁴/c), so no counterexample is in sight near known equality cases (a single pair is the only tight family). (c) KILLED: F(α) ≥ 0 is a squared modulus only when every γ is real (it assumes RH for its definition), and the prime-side second moments are statistical (wall 7). | **(a) SUSPECT; (b) CSS+ ROBUST; (c) KILLED (walls 8 → 7)** | — |
| 109 | Joukowski structure of the cosine step on a product with one distinguished pair. From T(fg) = Tf·Tg − Sf·Sg (T = cos(aD), S = sin(aD), i.e. cos(a(D₁+D₂))), with q = (z−x)² + y² one gets T(q) = (z−x)² + R², S(q) = 2a(z−x), R² = y² − a². So cos(aD)(q·f) = 0 ⟺ J(z−x) = tan_f(z), with Joukowski map J(ζ) = (ζ + R²/ζ)/(2a) and tan_f = S(f)/T(f) = −i(Q_f−1)/(Q_f+1). | DERIVED: Im J(ζ) = Im ζ·(1 − R²/abs(ζ)²)/(2a), negative exactly inside the deep disc D. Im tan_f = (1 − abs(Q_f)²)/abs(Q_f+1)², positive exactly on Ω₋(f) = {abs(f(w+ia)) < abs(f(w−ia))}. So every upper root of cos(aD)(q·f) lies in D Δ Ω₋(f), the symmetric difference of the new pair's disc and the old negative region. With f's pairs this gives the Cayley form: Π_k (J_k + i)/(J_k − i) = −1, and Σ_k log abs(κ_k) = 0 is de Bruijn's dipole balance. Pairs-only CSS+ ⟺ the upper energy of Re Π_k((z−x_k+ia)² + y_k²) is ≤ Σ R_k². Two stacked pairs: J₁J₂ = 1 ⟺ (z²+R₁²)(z²+R₂²) = 4a²z², energy R₁² + R₂² − 4a² (drag, rows 69/75). | **STRUCTURE (new localisation: symmetric difference)** | Sharper than the union-of-discs theorem: a root inside the new pair's disc must lie outside the old negative region, and vice versa. A joint energy argument may run by induction on pairs through the Joukowski map. No RH content. |
| 110 | (a) Simplify the row-109 localisation. (b) Formalise the wall-9 temperedness countermodel ξ(s−a)ξ(s+a) (Euler product, FE, growth, off-line zeros). | (a) The symmetric-difference law is a one-line corollary of the modulus balance: for any factorisation p = f·g and any upper root w of cos(aD)p, abs(f₊)abs(g₊) = abs(f₋)abs(g₋) with h± = h(w ± ia), hence (abs(f₊)² − abs(f₋)²)(abs(g₊)² − abs(g₋)²) ≤ 0. With g = (z−x)² + y², abs(g₊)² − abs(g₋)² = 8va(X + v² + a² − y²). The Joukowski/Cayley machinery of row 109 is not needed for the localisation; it is needed only if an energy induction is attempted. (b) ALREADY IN CORPUS: `RHTower/SymmetricShiftFunctionalEquation` (`xi_symmetricShiftProduct_criticalZero_pair_off_critical_line`, `hasLineSchwarzFunctionalEquation_symmetricShiftProduct`) and `RHTower/EntireFunctionalEquationOffLine` (`lambdaPositive_entire_functionalEquation_not_criticalLine`: an entire, FE-symmetric, Λ-positive system with off-line zeros). | **(a) SIMPLIFIED; (b) REDISCOVERED** | Search the corpus before planning any barrier formalisation; the wall countermodels are already in Lean. |
| 111 | Shallow-pair rarity, the crux in statistical form: show unconditionally that the off-line pairs of depth < ε/log T number ≤ c(ε)·N(T) with c(ε) → 0, via small-gap upper bounds. A shallow pair is a near-double zero at scale 2δ, so bound #{(γ,γ′): 0 < abs(γ−γ′) < ε/log T} through the unconditional bandwidth-≤1 Weil/Montgomery data (Zeta23 traces) and a Beurling–Selberg majorant of 1_{abs(x)<ε}. | KILLED (bandwidth-one Nyquist wall, memory `bandwidth-one-nyquist-wall`): a majorant of an interval of length 2ε with Fourier support in [−1,1] has integral 2ε + 1, so the off-diagonal bound carries a slack of order N(T) that does not vanish as ε → 0. Also, by the continuity barrier, shallow pairs and on-line double zeros enter Gram/inertia counts identically (Zeta23 bounds both together by 1/6 of zeros). Decay in ε needs pair-correlation data beyond bandwidth 1 (wall 7 plus Nyquist). | **KILLED** | Shallow-pair rarity is as hard as small-gap rarity, and both sit beyond the Nyquist bandwidth. |
| 112 | First-order (or zeroth-order) separation of a shallow off-line pair from an on-line double zero by an exact, non-statistical invariant. Candidates: integer counts N(½+η, T) (zeroth order, discontinuous in the configuration, so they escape the continuity barrier), computed by the argument principle as (1/2π)[∫_0^T Re(ξ′/ξ)(2+it)dt − ∫_0^T Re(ξ′/ξ)(½+η+it)dt + horizontal edges]. | CIRCULAR: RH ⟺ σ ↦ ∫_0^T Re(ξ′/ξ)(σ+it)dt is constant on (½, 2] up to edge terms. Since Re(ξ′/ξ) = ∂_σ log abs(ξ) is harmonic off the zeros, σ-independence ⟺ no zeros in between. The left-edge integral needs exact values of ξ at σ = ½+η, and the only exact access off σ > 1 is the explicit formula. Localising to height T at depth η needs test functions of support ≍ log T (prime sums of length T^c) evaluated to precision η, which is the corpus detection–knowledge duality and beyond Lindelöf-strength input. | **CIRCULAR** | Exact invariants exist (counts are discontinuous, so they pass the continuity barrier), but every route to evaluating them goes through prime sums of length T^c at depth precision. That is the same wall from the "knowledge" side. |
| 113 | Named input against the bandwidth-one (Nyquist) wall: levels of distribution beyond ½ (Bombieri–Vinogradov ½; Zhang/Polymath ½ + 7/300 for smooth moduli; the corpus Iwaniec 10/49 law) feeding Goldston–Montgomery prime pair correlations, to extend unconditional knowledge of F(α) past α = 1 and reach shallow-pair rarity. | KILLED as an RH producer. Level ½ + η gives at most a fixed extension of F past 1, i.e. bounded bandwidth 1 + η′. The corpus Zeta23 audit already prices this: support 1.04/1.26/1.70 buys proportions 0.70/0.80/0.90 of simple critical zeros. Shallow-pair rarity with c(ε) → 0 needs bandwidth → ∞ (row 111), and any bounded bandwidth only improves a proportion (wall 7). | **KILLED (Nyquist → wall 7)** | Even a passing input for Nyquist yields proportions, because RH needs unbounded bandwidth. |
| 114 | AAL (no attained top) through Herglotz rigidity. If Θ = sup Re ρ > ½ is attained at ρ₀, then ξ′/ξ is Herglotz on Re s > Θ, anti-Herglotz on Re s < 1−Θ by the FE, and has a pole on the boundary line. Does the Nevanlinna representation (positive boundary measure ν on Re s = Θ with an atom at γ₀) clash with the FE reflection or with growth ½log t? | KILLED: ν = Σ_ρ Poisson_{Θ−β}(t−γ)dt + Σ_{β=Θ}πδ_{γ} is automatically positive, and the linear term matches ½log t. The FE maps it to the mirror half-plane with the opposite sign, with no overlap (the strip 1−Θ < Re s < Θ carries the zeros). A Herglotz structure with a boundary atom is consistent for every attained top, so Herglotz rigidity gives no constraint beyond "Θ = sup". The corpus `AsymptoticAbscissaLawProducers` lists all known AAL producers (bounded lags along one progression, twisted plateau Weil energies, JAS positivity), and each is RH-strength input. | **KILLED** | AAL has no rigidity producer from analytic structure alone. Its known producers are arithmetic one-sided bounds (wall 1). |
| 115 | Inequalities at σ = ½ with unbounded bandwidth: the large sieve / Montgomery–Vaughan mean value theorem Σ_r abs(Σ_{n≤N} a_n n^{−it_r})² ≤ (N + T/δ)Σ abs(a_n)² for δ-spaced t_r ∈ [0,T]. It holds for all lengths N relative to T, so the bandwidth N/T is unbounded. Can it bound a detector Dirichlet polynomial at an off-line pair's ordinate tightly enough to exclude the pair? | KILLED (wall 7): the inequality is an upper bound on the sum over all points. One exceptional ordinate costs only its own term, so an off-line pair is excluded only in measure. The resulting zero-density estimates (Ingham, Huxley, Guth–Maynard large values) give power savings in counts (corpus `exists_ncard_zeroCopyRange_le`, `XiRightDiscSeamContractionInghamHuxley`), never zero. Pointwise exclusion would need a lower bound on a positive quantity at each ordinate, and the large sieve gives none. | **KILLED (wall 7)** | Unbounded-bandwidth inequalities exist, but they are upper bounds on aggregates: statistical by construction. |
| 116 | Inputs claiming pointwise positivity at σ = ½: (i) lower bounds for abs(ζ(½+it)); (ii) Λ(n) ≥ 0 pointwise on the prime side; (iii) Eisenstein data E(z₀, ½+it) on the unitary line (Fourier expansion, constant term 2Re(y^{½+it}ξ(1+2it)), K-Bessel tail with τ_{it}(n)). | KILLED. (i) No pointwise lower bound exists on the line, since it vanishes at the zeros; the only lower bounds are on σ ≥ 1 (1/ζ(1+it) ≪ (log t)^{2/3}, VK). (ii) It signs the prime term only for tests with k(log n) of one sign, giving the cone of row 86(c) (a strengthened PBAP), not all tests. (iii) On the unitary line E(z,s) is holomorphic and its data involve ξ(1+2it) on the 1-line; ζ zeros enter only as scattering poles at s = ρ/2, off the unitary line (rows 76, 89). Positivity there is Lagarias–Suzuki-type and blind to ζ zeros. | **KILLED** | No known input gives pointwise positivity at σ = ½. The three candidate classes are blind to ζ zeros (iii), restricted to a cone (ii), or nonexistent (i). |
| 117 | Heat version of the survivor (heat-CSS+): V(e^{−τD²}p) ≤ Σ_k (y_k² − 2τ)_+, the Gaussian member of the vertical-average family (row 73). Attempted proof by the dissipation identity V′ = −2Σ_{j<k}sin²arg(z_j−z_k) and the potential Φ(τ) = Σ_k(y_k²−2τ)_+ − V(τ), with Φ(0) = 0 and Φ′ = −2N_due(τ) + 2Σ_{j<k}sin²(…). | Test (z²+1)(z²+9) under heat (the corpus `PolynomialHeatDepthBudgetFailure` quartic): imaginary-root phase τ < 2/3, V = 10 − 12τ ≤ 10 − 4τ (τ < ½) and ≤ 9 − 2τ (τ ≥ ½); complex phase 2/3 < τ < 1, V = √(12τ²−20τ+9) − 6τ + 5 ≤ 9 − 2τ ⟺ 0 ≤ 4τ² + 52τ + 7; real-rooted from τ = 1. SURVIVES. Proof gap: Φ′ ≥ 0 needs m(τ) + (cross dissipation) ≥ N_due(τ). Early deaths through real-root or pair collisions (e.g. z²(z²+1) dies at τ = 1/6) make m < N_due, and the cross sin² terms are not shown to compensate. | **SURVIVES (heat-CSS+); proof open** | Heat-CSS+ would follow from CSS+ via cos(√(2τ/n)D)^n → e^{−τD²}, but CSS+ is not iteration-stable (the bound is per deep pair of the current polynomial), so neither implies the other directly. No RH content. |
| 118 | Heat-CSS+ through the root ODE ż_k = 2Σ_{j≠k}(z_k − z_j)^{−1} (from ∂_τp = −p″). Facts: no births (forward heat is Pólya–Schur, so the nonreal count m(τ) is nonincreasing); per pair, d(y²)/dτ = −2 + 4y·Σ_{others}Im(z−z_j)^{−1}, where real roots and lower pairs pull down and higher pairs pull up (drag); V′ = −2D with D = Σ_{j<k}sin²arg(z_j−z_k) ≥ m. | REDUCED: with N_due(s) = #{k : y_k(0)² > 2s} one has V(0) = 2∫_0^∞D = 2∫_0^∞N_due = Σ y_k², so heat-CSS+ ⟺ ∫_0^τ D(s)ds ≥ ∫_0^τ N_due(s)ds for all τ ("dissipation is front-loaded relative to the solo schedule"). Checked: drag quartic (D = 6 ≥ 2 = N_due for τ < ½) and z²(z²+1), which dies at τ = 1/6 (solo ½), with V(τ) = [(1−12τ) + √(1−16τ+96τ²)]/2 ≤ 1 − 2τ. Gap: early deaths make m < N_due afterwards, and the excess cross dissipation before the death must pay for it. | **REDUCED (front-loading inequality); open** | No RH content. The heat Lyapunov structure is complete except for this front-loading inequality; any proof must account for interaction-driven early deaths. |
| 119 | Heat-CSS+ by top-j majorisation. Let h₁(τ) ≥ h₂(τ) ≥ … be the heights of the upper roots of e^{−τD²}p, E_j = Σ_{i≤j}h_i², F_j = Σ_{i≤j}(y_(i)² − 2τ)_+ (y_(i) the initial heights, decreasing). Claim: E_j(τ) ≤ F_j(τ) for all j and τ; j = all gives V(τ) ≤ Σ_k(y_k² − 2τ)_+. | **PROVED (paper).** With ż_i = 2Σ_{k≠i}(z_i−z_k)^{−1}, d/dτ Σ_{i∈S}h_i² for the current top set S splits into three kinds of term. (i) Own conjugate: 2h_i·2Im(1/(2ih_i)) = −2 each. (ii) Roots outside S, all at height ≤ h_i (lower upper roots, real roots, every LHP root including the other conjugates): 4h_i Im(z_i−z_k)^{−1} ≤ 0. (iii) Pairs inside S: 4(h_i−h_k)Im(z_i−z_k)^{−1} = −4(h_i−h_k)²/abs(z_i−z_k)² ≤ 0. So D⁺E_j ≤ −2min(j, m(τ)) (forward heat has no births). Barrier with F_j + ε(1+τ), by induction on j. If m(τ) ≥ j at a touching point, D⁺E_j ≤ −2j ≤ F_j′. If m(τ) < j, then E_j = V = E_m ≤ F_m ≤ F_j < F_j + ε(1+τ) by the induction hypothesis, so no touching. Collisions are finitely many (the discriminant is a polynomial in τ) or are removed by perturbing p and passing to the limit. Deaths (h → 0) keep E_j continuous. Checked against rows 117–118 (drag quartic, z²(z²+1)). | **PROVED (paper): heat-CSS+ with weak-majorisation strengthening** | New structural law: under the heat flow the vector of squared heights is weakly submajorised by the solo schedule (y_(i)² − 2τ)_+. The top-j mechanism is "everything outside the top set pulls down, everything inside cancels by symmetry". It needs an ODE, so it does not transfer to the discrete cosine step (cos(√sD) is not a flow). Formalisation needs root-ODE infrastructure (simple roots, implicit function, Dini derivatives); it is a sizeable Lean project. No RH content: for Ξ it is de Bruijn's Λ ≤ ½·(max depth)², summed. |
| 120 | (a) Transfer the row-119 top-j majorisation to the de Bruijn–Newman flow H_t (zero ODE ż = 2Σ(z−z_k)^{−1}, a symmetric conditionally convergent sum; Csordas–Smith–Varga). (b) Discrete cosine analogue: conjecture the cosine top-j law Σ_{i≤j}v_i² ≤ Σ_{i≤j}(y_(i)² − a²)_+. (c) Formalisation decision for row 119. | (a) Valid for Ξ, since every top root is pulled down by all lower zeros. The squared depths of the off-line zeros of H_t are weakly submajorised by (δ_(i)² − 2t)_+, which contains de Bruijn's Λ ≤ ½δ_max². FORWARD-ONLY: it constrains H_t given ξ, never ξ given H_t (t > 0). RH needs the backward direction (Λ ≤ 0), so this is not a producer (walls 4/7). (b) Top-1 is the [L] disc theorem; top-2 holds on the drag quartic (9−5.5a² ≤ 9−a²; 10−6a² ≤ 10−2a²) and the quartic resolvent family. No proof: the cosine step is not a flow (cos(√sD) has no generator), and cosine is the extremal vertical average (row 73), so the heat mechanism has the least slack there. (c) Deferred: Lean for row 119 needs implicit-function root dynamics, Dini derivatives of top-j sums and a barrier lemma, all new infrastructure, for a result without RH content. | **(a) FORWARD-ONLY; (b) OPEN (cosine top-j conjecture); (c) DEFERRED** | — |
| 121 | Backward de Bruijn–Newman (dual to Rodgers–Tao Λ ≥ 0): suppose Λ > 0 and derive a contradiction. Ingredients: Ki–Kim–Lee (finitely many nonreal zeros of H_t for each t > 0, real above exp(c/t), corpus `KiKimLeeWeylHorizon` with c = 3/2+ε); the row-119/120 majorisation (top root dies by δ_max²/2); collision at t = Λ. | CIRCULAR: Λ > 0 forces nonreal zeros of H_t for t < Λ only at heights ≤ exp(c/t), which is consistent with every unconditional statement. Excluding them needs RH verified up to height exp(c/t) for every t > 0, i.e. at all heights. Rodgers–Tao's direction works because Λ < 0 would force excessive regularity of real zeros, contradicting unconditional statistics. Λ > 0 only forces finitely many low collisions, which no statistical theorem forbids (walls 7 and 4). | **CIRCULAR** | The backward heat direction reduces to finite-height verification at unbounded heights: the corpus "real-rooted heat times have no open neighbourhood of zero" receiver. |
| 122 | Pointwise (not statistical) input at σ = ½ beyond bandwidth one: Baker/Matveev lower bounds for linear forms in logarithms of primes (corpus `general-baker-closed`, `effective-baker-matveev-project`), used to forbid simultaneous phase alignment t log p ≈ 0 mod 2π for p ≤ X. That would cap the large values of Σ_{p≤X}p^{−½−it} pointwise and feed the Gonek purity gate or a shallow-pair separator. | KILLED: Matveev gives abs(Σ_{i≤N} m_i log p_i) ≥ exp(−C^N·Π_i log p_i·log M), superexponential in the number N of primes. For N ≍ π(X) with X = (log t)^A this is far below every scale that matters, so no alignment is excluded at any useful height. The only effective regime is N bounded, where Dirichlet/Kronecker already decide alignment. Pointwise Diophantine control exists, but only for boundedly many primes, which is again bounded bandwidth (Nyquist / wall 7). | **KILLED** | The two candidate input classes at σ = ½ beyond bandwidth one, aggregate (large sieve, row 115) and pointwise Diophantine (Baker), fail in opposite ways: the first is statistical, the second effective only for boundedly many primes. |
| 123 | Cosine top-j law via the shift flow A_s = ½(p(z+is) + p(z−is)), s ∈ [0,a]: a genuine ODE in s, ẇ = S_s′(w)/A_s′(w) = −i(L₊+L₋)/(L₊−L₋), with L± = Σ_k (w ± is − r_k)^{−1}. The target differential law D⁺E_j(s) ≤ −2s·min(j, m) would integrate (barrier argument as in row 119) to Σ_{i≤j}v_i² ≤ Σ_{i≤j}(y_(i)² − a²)_+. | DERIVED, but no proof: a single pair gives d(v²)/ds = −2s exactly (equality). Unlike the heat ODE (a sum of pairwise terms 2(z−z_k)^{−1}), the shift-flow velocity is a nonlinear ratio of two root sums. There is no pairwise interaction decomposition, so "outside pulls down, inside cancels" is unavailable. Top-1 holds cumulatively (the [L] disc theorem gives v_max² ≤ y_max² − s²), but the instantaneous rate is uncontrolled. The drag example shows individual roots rising, so top-j for j ≥ 2 needs a non-local argument. | **REFORMULATED (shift-flow ODE); open** | The heat/cosine dichotomy is structural: the heat flow is a pairwise gradient-like flow (provable majorisation), while the cosine shift flow is a Möbius-ratio flow (no decomposition). No RH content. |
| 124 | (a) Selberg trace formula on SL₂(ℤ)\ℍ as a σ = ½ positivity source. Its continuous-spectrum term (1/4π)∫h(r)(−φ′/φ)(½+ir)dr with φ(s) = ξ(2s−1)/ξ(2s) has −φ′/φ(½+ir) = 4Re(ξ′/ξ)(1+2ir) > 0 unconditionally. (b) Formalisation plan for the row-119 heat majorisation without root ODEs: small steps p ↦ p − δp″ with an O(δ²) top-j error, composed and passed to the limit via continuity of roots. | (a) KILLED (wall 6): the positivity lives at Re = 1 (the image of the unitary line under s ↦ 2s), where Re(ξ′/ξ) > 0 because every β < 1. ζ zeros enter only as scattering poles at s = ρ/2 (rows 76, 89). (b) DEFERRED: the single step fails at finite δ (row 69 LS counterexample), and the O(δ²) error is not uniform near root collisions, so the discrete route needs the same collision analysis as the ODE route. Mathlib also lacks continuity of root multisets in coefficients. | **(a) KILLED; (b) DEFERRED** | — |
| 125 | Turán's power-sum method as a pointwise lower-bound input (second main theorem: max_{ν∈[m,m+n]} abs(Σ b_j z_j^ν) ≥ (n/(8e(m+n)))^n·min abs(partial sums of b)), applied to the explicit-formula zero sum near a hypothetical off-line pair, to force a prime-side Ω contradiction at RH precision. | KILLED (wall 3): Turán's lower bounds lose (n/(8e(m+n)))^n, so they control zeros only when the number of relevant zeros is bounded and well separated. Near the critical line the local zero count is ≍ log t per unit height (wall 3, local clustering), and the power-sum bound degenerates. Turán's method yields zero-free regions and density near σ = 1 and Ω-results for ψ − x (Θ-dependent), never exclusion at σ = ½. Turán's own RH route (sections of ζ zero-free in σ > 1) is false (Montgomery). | **KILLED** | — |
| 126 | HCF/TH "rank-uniform Hankel positivity" via complete monotonicity of the heat trace ν(a) = Σ_ρ e^{a(ρ−½)²}, read through the Gaussian explicit formula: ν(a) = pole term (≍ e^{a/4}) + arch term − Σ_n Λ(n)n^{−½}(4πa)^{−½}e^{−(log n)²/(4a)}. Conjecture: the prime-side expression is completely monotone in a term by term after a pole–prime pairing. | KILLED (walls 8 and 6): the pole term e^{a/4} is not completely monotone (it grows), and the prime Gaussian sum cancels it only at PNT level. Complete monotonicity needs the cancellation to hold in every derivative order uniformly in a, which is the corpus receiver "heat trace CM ⟺ RH" (`XiGaussianHeatTraceCompleteMonotonicity`). Pairing terms is affine in the weights (wall 8): any λΛ enters linearly, so no term-wise sign survives the pole subtraction. The corpus window aN ≤ κ is the unconditional, bounded-rank part. | **KILLED** | — |
| 127 | Lean route for the row-119 heat majorisation through existing corpus infrastructure (`PolynomialHeatNonrealCount`: heat steps 1 − aD², locally uniform limit `tendstoLocallyUniformly_eval_heatStepOp_pow`, Hurwitz isolating discs `exists_isolating_discs`), as required by the no-go closure discipline for the survivor of `PolynomialHeatDepthBudgetFailure`. | FEASIBILITY: a single step a = τ/n violates the energy law only when some pair's height² is comparable to a (the row-69 LS counterexample, excess ≍ ε(20c² − 8c)). That happens only within O(1) steps of each death, so the total excess is O(τ/n) → 0. The plan is to prove E_j(heatStep^n p) ≤ F_j + o(1) with a per-step error bound, pass to the limit by Hurwitz root convergence on isolating discs, and use continuity of the top-j sum of squared heights. Missing pieces: (i) a uniform per-step error bound in terms of the minimum height and the step (a new estimate, not yet proved on paper); (ii) Lean continuity of top-j height sums under root convergence. | **PLAN (Lean deferred; paper step (i) open)** | Survivor status recorded on card `cosine-step-imaginary-energy-law.md`: heat law proved on paper by the ODE route; the Lean route via discrete steps needs the per-step error estimate (i). |
| 128 | (a) First-order detector from reflection-odd tests: ĥ(z) = z·g(z)², so an off-line pair contributes 2Re[(γ₀+iδ)g(γ₀+iδ)²], which has a term linear in δ. (b) Per-step error estimate for the row-127 Lean route: the root displacement of p − ap″ is w = r + 2aΣ_{k}(r−r_k)^{−1} + O(a²·Σabs(r−r_k)^{−3}), equal to the heat ODE to first order. | (a) KILLED (shared constraint "Orientation"): on-line zeros contribute γ·g(γ)², which carries the sign of γ, so the odd form has no definite sign even under RH. Reflection-odd functionals give orientation, not positivity (CANNOT-399/405/407 in the frontier-map shared constraints). (b) OPEN: the O(a²) remainder involves inverse cubes of root separations and blows up at collisions, so a uniform per-step bound needs a collision-insensitive form of the top-j energy error. Not found. | **(a) KILLED; (b) OPEN** | — |
| 129 | (a) Heat as a mixture of cosine steps: for symmetric X, E p(z+iX) = E_{abs(X)}[cos(abs(X)D)p], so e^{−τD²}p = ∫cos(aD)p dν(a). Can the cosine laws ([L] disc theorem, CSS+ cases) transfer to the heat flow by mixing, avoiding root ODEs? (b) Speiser/Levinson–Montgomery input: zeros of ζ′ left of ½ are equinumerous with off-line zeros of ζ (N₁⁻(T) = N⁻(T) + O(log T)), so zero-freeness of ζ′ in 0 < σ < ½ is RH. | (a) KILLED: zeros of a mixture of polynomials are not controlled by the zeros of its components. The disc law rests on a modulus comparison of p(w+ia) and p(w−ia) at one a, and across different a these terms can cancel. A finite Laguerre step already breaks even the top-1 (max-height) law (row-69 LS: one pair, height² > 1 − 2c), so neither mixtures nor discrete steps give the heat law without a limit analysis. (b) KILLED: equinumerosity transfers counts both ways (RH-equivalent), and the corpus has the Speiser disks (`exists_xi_zero_disk_of_xiHermiteBiehler_eq_zero`, `LevinsonDetectorRightCount`). There is no independent ζ′ zero-free input in the strip. | **KILLED (a, b)** | — |
| 130 | (a) Cosine sum form (two deep pairs + real-rooted g) at the equality boundary: if v₁² + v₂² = R₁² + R₂² with the two surviving roots in different discs, both must sit at the disc tops x_k + iR_k. (b) Hardy Z extremum alternation (all local extrema of Z alternate in sign ⟺ no wrong-sign critical points) via the exact Riemann–Siegel remainder. | (a) PARTIAL: a root at the top of D₂ but outside D₁ has the q₁ factor strictly growing and g weakly growing, so the product ratio is > 1 and the root equation fails. Equality with roots in different discs is therefore impossible, which leaves the single-disc (drag) configuration as the only route to equality. That case is not resolved; it is consistent with every row-69/75 example having margin ≥ 4a². (b) KILLED: it is the corpus receiver `XiRealCriticalPointSignLaw` (holds outside off-line cones and over ≥ 86.6% of heights). The RS main term alone has wrong-sign extrema at partial-sum zeros (WD row 316), so the exact remainder must repair them: a pointwise σ = ½ positivity (rows 115/116). | **(a) PARTIAL (equality only via a single disc); (b) KILLED** | — |
| 131 | Single-disc (drag) case of the cosine sum form: two surviving roots inside D₂. Count them by Rouché on ∂(D₂ ∩ UHP) with A = ½(P₊ + P₋), P = q₁q₂g, P± = P(z ± ia). | DERIVED (count): on the upper arc of ∂D₂ the q₂ factor is balanced, and if the arc avoids D₁ then q₁ and g grow, so abs(P₋) ≤ abs(P₊) there; on the real segment abs(P₊) = abs(P₋). Off the equality set, #roots of A in D₂ ∩ UHP = #{charges r_k − ia ∈ D₂}. The drag configuration is exactly the case where D₂ also contains pair 1's charge r₁ − ia, i.e. (x₁−x₂)² + (y₁−a)² < y₂² − a². This gives a natural assignment of one root per enclosed charge. Energy bound for the assigned roots (v₁² + v₂² ≤ R₁² + R₂²) not proved; the stacked quartic and resolvent families satisfy it with margin ≥ 4a²·(…) > 0. | **PARTIAL (charge-count assignment); energy open** | A proof would need a per-charge energy comparison within one basin: a two-charge version of the single-pair disc identity F(v+a) − F(v−a) = 8va(X + v² + a² − y²). No RH content. |
| 132 | Even (stacked) family for the cosine sum form: p(z) = Q(z²) with K deep pairs ±iy_k and J real pairs ±c_j (n = 2K+2J), A = cos(aD)p = R(z²). Vieta: Σ_R u = −Σy_k² + Σc_j² + a²n(n−1)/2, and V_A = −Σ_R u + P₊ + Σ_cp(abs(u) + Re u), with P₊ = Σ positive u-roots and cp = complex u-pairs. | REDUCED: CSS+ ⟺ P₊ + Σ_cp(abs(u) + Re u) ≤ Σ_j c_j² + a²(n(n−1)/2 − K), a fixed budget that must cover (i) the squared real roots of A, (ii) the off-axis complex terms, (iii) the a² per deep pair. With J = 0 this is the row-68 budget a²K(2K−2). Real-rooted even part: Σ(real roots of A)² = Σ_j c_j² + a²·(spreading), so the budget is consistent with the real roots' Vieta growth. A proof needs to show that the deep pairs' complex terms and the real spreading cannot exceed a²(n(n−1)/2 − K) jointly. Not closed. | **REDUCED (even family budget); open** | The budget form makes the open core a single scalar inequality on the even resolvent R. Candidate tool: the Bessel operator L = 4uD_u² + 2D_u (cos(aD) on even polynomials corresponds to cos(a√L) in u). No RH content. |
| 133 | Relation between the cosine and heat top-j laws through de Bruijn's product e^{−τξ²} = lim_n cos(√(2τ/n)ξ)^n. | DERIVED: cosine top-j (squared heights of cos(aD)p weakly submajorised by (y_(i)² − a²)_+) implies heat top-j, because weak submajorisation is preserved by the increasing convex map x ↦ (x − a²)_+. So n iterated steps give (y_(i)² − na²)_+ = (y_(i)² − 2τ)_+, and Hurwitz convergence (corpus `PolynomialHeatNonrealCount` infrastructure) passes to e^{−τD²}. Hence cosine top-j is the master conjecture and row 119 is its heat shadow. The top-1 case is already in Lean (disc theorem), so the polynomial de Bruijn strip law (Im w)² ≤ (y_max² − 2τ)_+ for e^{−τD²}p is formalisable now by iteration and Hurwitz. It is a known theorem (de Bruijn 1950), so new in Lean but not new knowledge. | **REDUCTION (cosine top-j ⇒ heat top-j)** | The open core of the whole side program is one statement: cosine top-j for j ≥ 2. No RH content. |
| 134 | Where can cosine top-2 be tight? From the [L] two-pair resolvent: V = Y₁+Y₂−2ξ²−6a² + 2t*, with t* ≤ ξ²+2a². | DERIVED: stacked pairs (ξ = 0) give V = R₁²+R₂²−4a², the minimum. As the horizontal separation ξ → ∞ the pairs decouple and V → R₁²+R₂² (the bound). So the energy bound is approached only in the separated limit. That limit is exactly the case already covered by the [L] disc theorem: roots in different discs have v_k² ≤ R_k² individually, for any degree and any real or shallow cofactor. The remaining same-disc (drag) case happens only for horizontally close pairs, where the interactions lower V; every example has margin ≥ cR₁² + 4a²-type. Lower root above its own disc (drag: 1 − a²/2 > 1 − a²) is compensated by the upper root's deficit (4.5a² vs 0.5a²). | **STRUCTURE: CSS+ proved whenever the surviving roots lie in distinct discs; open only for shared discs, where the margin is positive in all examples** | The shared-disc case needs a quantitative "upper root deficit ≥ lower root excess" inequality. No RH content. |
| 135 | Spectral flow of the restricted Weil family Q(a) (corpus RW: compact self-adjoint pencil, finite negative index ν(a,0), μ₀ antitone in a). Since ν(a,0) is nondecreasing in a, its value at aperture A equals the spectral flow over [0,A]. An APS-type index formula (η-invariant + local integral + boundary term) would compute it as an exact integer; showing it is < 1 would give RH. | KILLED (circular / TG route): an exact integer count needs the local density to be evaluated. The corpus TG route already has this structure (integer trace < 1 ⇒ RH; Wiener–Hopf index = winding; cone K₁ ≅ ℤ) with Needs "E_base = E_residual + Tr T_D with E_residual ≥ 0", i.e. a positivity of the residual. An index formula moves the problem from "count negative eigenvalues" to "sign a residual density", which is the same positivity (wall 8 / the HF Hodge positivity). | **KILLED** | Topological invariants (spectral flow, index, winding) are exact and integer-valued, so they pass the continuity barrier. But every known index formula has a positivity-requiring remainder, so the producer gap reappears as a residual sign. |
| 136 | Batch of four cheap inputs, each named against a wall: (i) arithmetic QUE / Hecke equidistribution (Lindenstrauss; Watson–Ichino links QUE to triple-product L-values); (ii) Rankin–Selberg / symmetric-power positivity via functoriality (Ramanujan-type bounds); (iii) CFKRS moment conjectures with lower-order terms as positive moment matrices; (iv) a CUE characteristic polynomial (RH automatic) realised arithmetically. | All KILLED. (i) Equidistribution is a limit-in-measure statement (wall 7); its quantitative form needs subconvexity, which is weaker than Lindelöf, so it gives no zero exclusion. (ii) Corpus memory `deligne-amplification-obstruction`: GL(1) has no symmetric-power tower (ζ^k has the same zeros), so amplification is vacuous (wall 5). (iii) Moment asymptotics, even with full lower-order terms, are averages (wall 7), and moment matrices are positive automatically, like Gram matrices. (iv) This is the Hilbert–Pólya construction itself (corpus SZ/HF realisations; constructing the operator = RH). | **KILLED (walls 7, 5, 7, construction)** | — |
| 137 | Batch of three: (i) a sieve "renormalisation flow" in the prime cutoff P, ζ_P(s) = ζ(s)·Π_{p≤P}(1 − p^{−s}) (zeta of integers coprime to P), as P → ∞; (ii) bootstrap from GRH-in-families (twists by characters of all conductors, one-level densities) to ζ itself; (iii) local Weil positivity place by place (p-adic factors W_p). | All KILLED. (i) ζ_P has exactly ζ's strip zeros plus zeros of finite Euler factors on Re s = 0, so the flow never moves the zeros and carries no information on Re ρ. (ii) Family statistics (one-level densities, Katz–Sarnak) are averages over conductors (wall 7) and cannot pin one member; the corpus already killed GL(2) family averaging. (iii) The local terms W_p(g) = −Σ_k(log p)p^{−k/2}(k_g(k log p)+k_g(−k log p)) are signed shift forms with no individual positivity (row 89). Positivity exists only globally (arch + pole + all p), which is Weil positivity. | **KILLED (trivial / wall 7 / wall 8)** | — |
| 138 | Shared-disc check in degree 5: stacked pairs plus a central real root, p = z(z²+Y₁)(z²+Y₂) (S = Y₁+Y₂, P = Y₁Y₂). A = cos(aD)p = z·B(z²), B(t) = t² + (S−10a²)t + (P − 3a²S + 5a⁴). | SURVIVES: real negative roots of B give V = S − 10a² ≤ S − 2a² (margin 8a²); complex roots give V = √(P−3a²S+5a⁴) + (S−10a²)/2 ≤ S − 2a² ⟺ P ≤ S²/4 + 6a²S + 4a⁴, true since P ≤ S²/4 (AM–GM), margin 6a²S + 4a⁴. Far real roots perturb by O(a⁴/c) (row 107) against the stacked margin 4a². No counterexample in any tested shared-disc family; margins are always ≳ a²·(sum of squared heights). | **SURVIVES (degree-5 shared disc)** | Evidence supports CSS+ with a positive shared-disc margin, but the general proof is still missing. No RH content. |
| 139 | Two complex-analytic inputs: (i) Phragmén–Lindelöf with harmonic majorants built from abs(ζ(1+it)) and the FE, to force log abs(ζ) > −∞ (no zeros) in ½ < σ < 1; (ii) Jensen counts on discs centred at 1+it with radius ½+ε, to separate on-line from off-line zeros. | KILLED. (i) Phragmén–Lindelöf controls upper bounds of log abs(ζ) (convexity, Lindelöf-type) and never gives lower bounds, since a zero is a −∞ of a subharmonic function, invisible to majorants. Even the Lindelöf hypothesis does not imply RH (corpus: LH is one of three independent pillars in `PrimeSideRiemannHypothesisSplit`). (ii) Jensen discs reaching across σ = ½ count on-line and off-line zeros together; their difference needs the argument along σ = ½+η, which is the circular count of row 112. | **KILLED** | — |
| 140 | Coverage audit of rows 99–139 against the ten-wall catalogue plus the continuity barrier, Nyquist bandwidth and detection–knowledge duality. Also the Nyman–Beurling positive cone (approximate 1 by nonnegative combinations of ρ_{1/n}). | Every RH-core input class I can name has been tested: Euler-product positivity (6), sieves (1), Diophantine (Baker, bounded primes), large sieve (7), Turán (3), Herglotz/Nevanlinna (circular), Phragmén–Lindelöf/Jensen (circular), index/spectral flow (residual sign), trace formulas (6), automorphic/QUE/moments/families (7), Frobenius/F₁/Hodge (5), temperedness (9 → 7), deformation and limit families ("purity ends where faithfulness starts"), quasicrystals (9 + GL(1) rigidity). Nyman–Beurling positive cone: the Báez-Duarte approximants need signed μ(n). Nonnegative combinations of ρ_{1/n}(x) = {1/(nx)} − {1/x}/n are pointwise bounded below and cannot cancel the constant's L²(0,1) component orthogonal to them (the cone is closed and misses 1), so this is not an RH route (KILLED). | **AUDIT: no untested input class remains in my repertoire; Nyman–Beurling positive cone killed** | Loop state for future cycles: the RH core needs a new mathematical structure (exact positivity at σ = ½ beyond bandwidth one). The side program's single open core is the cosine top-j master conjecture (card `cosine-step-imaginary-energy-law.md`). |
| 141 | Side program open core (cosine top-j, ≥ 2 deep pairs). New idea: realize cos(aD)p = Re E, E = p(·+ia), as the characteristic polynomial of T = [[diag(x,s) + K, B], [C, diag x]] with K the sign coupling i·sgn(v−u)√(c_u c_v), B/C pair couplings β_jγ_j = −(y_j² − a²). Then Im T is the Hermitian dilation of the couplings √(y_j² − a²), and Ky Fan (via Schur triangulation and a projection-weight argument) gives the majorization. | **PROVED and FORMALIZED.** For every real p and a ≥ 0, the upper-root heights of cos(aD)p are weakly submajorised by √(y_j² − a²); squared form gives CSS+. Lean: `SignCouplingDeterminant`, `PairCoupledImaginaryKyFan`, `RealPartProductRealization`, `CosineStepHeightMajorization` (standard axioms, wired). Also covers pair-dependent shifts and arbitrary lower roots; exact defect identity V = ΣR_j − ½(‖Re T‖² − Σ(Re λ)²). | **THEOREM [L]** (card moved to 3-formalized) | No RH content (polynomial root dynamics). The card's "horizontal-spread form" is Schur's inequality for this T. Next: heat top-j in Lean by iteration + limit; RH core only with a named wall-passing input. |
| 142 | RH-core use of the row-141 realization. (a) Krein realization of A_h = cos(hD)Ξ: off-line pairs of Ξ are automatically vertical pairs (ρ, 1 − ρ̄ share γ), so T_h exists with couplings √((β−½)² − h²) and A_h's defects are majorized by them. (b) Real-stability / interlacing (MSS mixed characteristic polynomial) producers. (c) Reverse direction along the corpus Poisson flow A_h = [cos(hD)/cos(HD)]A_H (`XiCosineShiftPoissonFlow`). | (a) Wall 4: "B = 0 for every h" is RH restated; majorization only runs forward (Ξ → A_h), the producer needs A_½ → Ξ. (b) Wall 6: stable data are Euler factors, whose products converge only for Im t < −½; any stability transport into the strip is the functional equation, i.e. HB (wall 4). Corpus W1C already excludes the unitary Euler shortcut. (c) The backward multiplier sec(HD) is a Pólya-frequency (variation-diminishing) smoothing; zero-loss through it is exactly the PTR need and uses the exact arithmetic of A_½ = Re ξ(1 + iv) (sech-weighted approximate functional equation). | **KILLED (walls 4, 6; (c) = PTR need, unchanged)** | Positive survivor (paper, corollary of row 141 via Hurwitz): square-root birth law. As h decreases below the depth δ of an off-line pair, the defects of A_h born from it have heights ≤ √(δ² − h²), top-j majorized, whenever only finitely many zeros are deeper than h. Receiver only. |
| 143 | Zero-loss through the sech port, restated with the row-141 count/majorization law. Ξ = cos(aD)F_a with F_a = sec(aD)Ξ = ∫Φ(u) sech(au) cos(tu) du (a sech smoothing of Ξ, entire because Φ decays super-exponentially). Conjecture C143: for some a > 0 every zero of F_a satisfies abs(Im t) ≤ a. By `nonrealRootCount_shiftAvg_le` and the majorization this implies RH; it is weaker than F_a ∈ LP, which the corpus excludes (damping Φ ↦ Φ/φ(iu), CANNOT-499). Companion fact (paper): sech-smoothing ξ(1 + iv) gives κ*F = F_½(· − i/2), so "κ*F Hermite–Biehler" is the a = ½ case of C143. | **FALSE in the two-tone model.** f = cos t + c cos 3t is real-rooted iff c ≥ 1/3. Here sec(aD)f = cos t / cosh a + c' cos 3t with c' = c·cosh a / cosh 3a < 1/3 for large a, and its lost zeros sit at height arcsinh(√((1 − 3c')/(4c'))) ≈ a + ½ log(1/c) > a. Secant smoothing of a real-rooted source pushes the lost zeros beyond depth a, by the log of an amplitude ratio over the frequency gap. So the count law cannot be reversed, and no universal strip for F_a holds even under RH. | **KILLED (countermodel)** | Positive survivor: depth excess law in the model, excess = log(1/c)/(λ₂ − λ₁) beyond a; real-rootedness of f equals a model-dependent strip a + Θ for F_a. Any zero-loss producer for A_½ must use the amplitude ratios of ξ's frequency components, i.e. the size of ζ(1 + iv) at scale 1 (corpus PTR need). Not formalized; corpus two-tone port counterexample covers the same phenomenon. |
| 144 | Ky Fan / metric freedom for the Hedenmalm source inverse (corpus `metricOperator_commutator_compactSourceInverse`: D·B − B†·D = iP, D = M_{1/q}, P kernel 1 − t − u = (1−t)⊗(1−t) − t⊗t, signature (1,1)). (i) Ky Fan: Σ_{Im λ>0} Im λ ≤ μ₊(½D^{−1/2}PD^{−1/2}). (ii) Dissipativity producer: find a metric D′ > 0 with i(B†D′ − D′B) of one sign; then all eigenvalues −1/z_ρ have one-signed imaginary part, and conjugate symmetry gives RH. | (i) Vacuous: D^{−1/2}(1−t) and D^{−1/2}t have norms M∫F² = ∞ and M∫(1−F)² = ∞ (only the mixed term M∫F(1−F) is finite), so μ₊ = ∞. (ii) For every multiplication metric D′ = M_{r/q} the defect kernel is K_r(t,u) = g(t∨u) − h(t∧u) with g = r(1−t), h = rt, whose diagonal r(t)(1 − 2t) changes sign at the quantile median for every r > 0. So no local metric works, and this obstruction is independent of the density k, as it must be: generic densities have non-real Fourier zeros. A nonlocal metric must use specific properties of Riemann's density; that is the corpus positive-metric / boundary-darkness criterion (RH-equivalent). The rank-two signature-(1,1) defect is a 2×2 J-inner characteristic function, i.e. a canonical-system / de Branges structure (wall 4). | **KILLED (walls 4, 8-type metric no-go)** | Positive survivor: universal median obstruction. Every multiplicative metric for a quantile source inverse has defect diagonal r(t)(1 − 2t), so dissipativity forces a nonlocal metric. NO POSITIVE SALVAGE beyond this. |
| 145 | Extend the row-141 law to every real polynomial and to products of cosine steps (vertical Rademacher averages E A(z + iX), X = Σ a_k ε_k), as the first half of the heat-flow law. | **FORMALIZED** `HTGeometry/CosineProductSquaredMajorization` (standard axioms, wired): `exists_eq_pairRootPoly` (every real polynomial is κ∏((X − Re u)² + (Im u)²)∏(X − r) over its upper and real roots), `sum_roots_shiftAvg_im_sub_pos_le_upperRoots` (height majorization in terms of the upper roots), `sum_max_sq_sub_le_of_majorization` (weak majorization ⇒ squared majorization at every threshold s, via ((t⁺)² − s)₊ = ((t − √s)₊)² + 2√s(t − √s)₊), `sum_roots_cosProd_sq_sub_le` (Σ_w((Im w)⁺² − s)₊ ≤ Σ_{u∈U(A)}((Im u)² − Σa_k² − s)₊ for cos(a₁D)⋯cos(a_nD)A). | **THEOREM [L]** | Contrast with corpus `HeatFlowDepthCountFails` / `not_heat_depthCountLaw`: the depth count fails for heat, but the squared-energy law is the iterable one. Remaining: the limit cos(√(2τ/n)D)^n → e^{−τD²} with root-sum continuity (heat law). No RH content. |
| 146 | Heat-flow law in Lean via cosine steps + limit. | **FORMALIZED** (standard axioms, wired). `HTGeometry/PolynomialRootSumSemicontinuity`: `sum_roots_le_of_tendstoLocallyUniformly` (weighted root sums with continuous Ψ ≥ 0 are lower semicontinuous under locally uniform convergence; isolating discs + argument-principle count). `HTGeometry/HeatFlowSquaredMajorization`: `cosProd_replicate_eq_sum` (n cosine steps = Σ_m c_{n,m}(−D²)^m with c_{n,m} the coefficients of the cos-series power), squeeze C(n,m)(τ/n)^m ≤ c_{n,m} ≤ τ^m/m! from 1 + (s/2)Y ≤ cos-series ≤ e^{(s/2)Y} (2^k k! ≤ (2k)!), `tendstoLocallyUniformly_eval_cosProd_replicate`, and **`sum_roots_polyHeat_sq_sub_le`**: Σ_w((Im w)⁺² − s)₊ ≤ Σ_{u∈U(p)}((Im u)² − 2τ − s)₊ for e^{−τD²}p. | **THEOREM [L]** | Heat analogue of CSS+ with top-j (row 119 paper result) now in Lean, without the root ODE. Complements the corpus heat count no-go. No RH content. |
| 147 | (a) Lift the energy laws to Ξ via Hadamard approximants plus the new root-sum semicontinuity. (b) Use them on the corpus three-pillar split MUST-1356 (RH ⟺ LH ∧ cosine finiteness at every level ∧ lag bounded above): attack "cos(hD)Ξ has finitely many non-real zeros" for fixed h > 0, by analogy with Ki–Kim–Lee for H_t, t > 0 (corpus `PhotonicLosslessHeatCosineFiniteDefect` for cos(hD)H_t). | (a) Vacuous: the polynomial laws are global, so the Ξ-level right side Σ_ρ((β−½)² − h² − s)₊ is finite only if finitely many zeros are deeper than √(h² + s), i.e. only under zeros-approach-the-line. A local law would need localization of the Schur vectors, which the method does not give. (b) The cosine level h reads the phase of ξ along σ = ½ + h. Its speed θ′_σ + Re(ζ′/ζ)(σ + it) ≈ ½ log t + Re ζ′/ζ, so a defect needs Re ζ′/ζ ≲ −½ log t, i.e. a zero just right of σ: cosine finiteness at level h = zeros approach the line there (corpus eventual-positivity equivalence). The Ki–Kim–Lee mechanism is unavailable: the heat flow pushes the effective abscissa of the Riemann–Siegel series to ½ + (t/4) log(x/4π), which grows with height, so the series is eventually dominated by its first term; the cosine shift moves it only to the fixed ½ + h. | **KILLED (ZAL; KKL push absent at t = 0)** | Positive survivor: precise reason the cosine pillar is strictly harder than KKL. The finiteness mechanism needs an effective abscissa → ∞ with height; at fixed h it equals ZAL at level h. |
| 148 | Asymptotic abscissa law (AAL, the other half of the corpus RH split): rigidity of isolated off-line zeros. Then, in my own program, Conjecture E: every vertical average E p(z + iX) whose characteristic function φ(ξ) = E cos(ξX) has only real zeros obeys the squared-energy law with budget E X² (row-73 RVS in CSS+ form). | AAL: producers need a lag progression Φ(mℓ) bounded above (MUST-1363/1365), i.e. √x-precision prime counting along b^m (wall 1); no new input, KILLED. **Conjecture E FALSE [L]** `HTGeometry/ThreePointVerticalAverageStripFailure`: X with P(0) = 1/4, P(±1) = 3/8 has φ = 1/4 + (3/4) cos ξ (only real zeros), E X² = 3/4, but q = (1/4)p + (3/4)cos(D)p with p = (X² + 3/4)³ has a root iv, 0 < v < 1/5 (`exists_threePointAverage_root_im_pos`); every root of p has squared height exactly 3/4 (`threePointBase_root_sq_im`). On the axis q(iv) = Q(−v²), Q(Z) = Z³ − 9Z² + (45/16)Z + 3/32, Q(0) > 0. For P(0) = 1 − μ, ½ < μ < 1, Q(0) = μ(2μ − 1)(1 − μ) > 0, so the whole family fails. | **KILLED (AAL: wall 1); Conjecture E FALSE (countermodel in Lean)** | Positive survivor: even de Bruijn's strip shrinking by √(E X²) needs Gaussian–Rademacher structure, not just LP. The weaker depth-budget form V + E X²·m ≤ V(p) survives on the example (0.032 + 0.75 ≤ 2.25). Characterization conjecture: X satisfies the squared-energy law for all real polynomials iff X = σG + Σ a_k ε_k (independent). Proven: "if" [L]; open: "only if" (the 3-point family is the first test). |
| 149 | Transfer the heat energy law from polynomials to the actual de Bruijn–Newman flow H_t (the corpus "finiteness transition" upgraded from counts to energies, unconditionally). | **FORMALIZED** (standard axioms, wired): `HTGeometry/EntireZeroSumSemicontinuity` (`exists_isolating_ball_entire`, `sum_zeroMult_mul_le_of_tendstoLocallyUniformly`: Σ_{w∈S} mult_f(w)Ψ(w) ≤ liminf Σ_{roots F_n}Ψ for any finite S and entire nonzero limit f). `RHTower/DeBruijnNewmanEnergyTransition`: `tendstoLocallyUniformly_polyHeat_xiRealApprox`, `sum_upperRoots_xiRealApprox`, **`riemannHeat_upper_energy_le`**: for 0 < t with 8St < 1 (S = 2Σ_ρ abs(ρ)⁻², `xiApproxGrowth`), every c ≥ 0 and every K bounding all finite partial sums of Σ_{zeros ρ of Ξ, Im ρ>0}((Im ρ)² − 2t − c)₊, the zeros of H_t satisfy Σ_w mult(w)((Im w)⁺² − c)₊ ≤ K (unconditional); `riemannHeat_upper_energy_le_of_finite` (finite case). | **THEOREM [L]** | First energy-level statement about the actual H_t zeros in the corpus: squared heights of the off-line zeros of H_t are weakly majorized by those of Ξ reduced by 2t. Receiver (de Bruijn–Newman lane), not a producer. |
| 150 | Combine the row-149 dissipation law with corpus de Bruijn–Newman facts to look for a producer. (i) Backward use from negative time: Ξ = forward heat of H_{−τ}. (ii) Count/energy interplay on (0, 1/8): E(t) ≥ E(t′) + 2(t′ − t)N(t′) together with the corpus strip abs(Im) ≤ ½ (`abs_im_le_half_of_riemannHeat_eq_zero`), right-continuity of N at 0 and reality for t ≥ 1/8. (iii) Monotonicity between two positive times via approximants polyHeat t₁ R_n. | (i) Vacuous: by MUST-1364, H_{−τ} has zeros of height ≥ τ log Re z − C, so Σ_{H_{−τ}}((Im)² − 2τ − c)₊ = ∞ for every c (Newman's obstruction in energy form). (ii) Only consistency relations (e.g. 2(s − t)N(s) ≤ N(t)(¼ − 2t)), all compatible with off-line zeros; RH ⟺ E ≡ 0 on (0, 1/8) is the corpus count criterion restated. (iii) Fails: spurious nonreal roots of the approximant flows may escape to infinity with bounded height, so the right side is not upper semicontinuous, even if Ξ has finitely many off-line zeros. | **KILLED (receiver only; Newman obstruction)** | Positive survivor: the row-149 theorem already covers the whole nontrivial range, since 1/(8S) > 1/8 and H_t is real-rooted for t ≥ 1/8; no all-t extension is needed. NO POSITIVE SALVAGE beyond this. |
| 150a | Correction to row 150. "1/(8S) > 1/8" needs S < 1. This is expected from Σ_ρ abs(ρ)⁻² = 2 + γ − log 4π ≈ 0.046, but the normalization of `xiSpectralPoint` is unchecked and nothing is proved in Lean. Treat the coverage of all of (0, 1/8) as unverified. | — | **OPEN (bookkeeping)** | Lean task: bound `xiApproxGrowth` explicitly. |
| 151 | (a) Bookkeeping from 150a: bound the growth constant S. (b) RH-core probe: typical-height cluster law (MUST-1362) plus local Krein/Ky Fan realizations, aimed at zeros approaching the line. | (a) **FORMALIZED** `RHTower/DeBruijnNewmanEnergyUnitTime`: `xiApproxGrowth_lt` (S = 2·xiShiftAbsoluteMass 0 < 1/10, from the corpus mass ≤ (85/84)M₀ and M₀ < 0.04623) and `riemannHeat_upper_energy_le_of_le_one` (energy law for all 0 < t ≤ 1, no horizon hypothesis), standard axioms. Row 150a closed. (b) KILLED, wall 7: typical-height box data control Re ξ′/ξ only off an exceptional set of measure ≤ CT e^{−κ/c}; an off-line zero makes its own height atypical, so zeros approaching the line need every height. | **(a) THEOREM [L]; (b) KILLED** | — |
| 152 | Anti-crystal law (`not_rigidOrdinates`) against the energy/dissipation law, plus persistence: can dissipation force a lower bound on near-collision energy that only off-line zeros pay, or, with the Ki–Kim–Lee horizon (real zeros beyond 2π e^{(3/2+ε)/t}), give a zero-free region abs(β − ½) ≲ (log γ)^{−1/2}? | Newman in disguise. The energy law only bounds heights from above; under RH it is the trivial 0 ≤ (anything). The persistence route needs off-line pairs to survive heat time ≈ δ²/2, but real neighbours at spacing ~1/log γ accelerate absorption (d(y²)/dt ≈ −2 − 4y²Σ abs(z − z_j)⁻², so y² decays at rate ~(log γ)²). Absorption time ≪ 1/log²γ, where the Ki–Kim–Lee horizon e^{c log²γ} ≫ γ is no constraint. | **KILLED (Newman; no persistence)** | Positive survivor (paper): the neighbour-acceleration heuristic explains the Ki–Kim–Lee horizon exponent (window e^{c/t} ↔ absorption time ~1/log² of the height). NO POSITIVE SALVAGE in Lean. |
| 153 | Wall 2 (|ζ|² vs log|ζ|): look for an untested exact identity for log|ζ| on σ = ½ (outer / Hardy factorization of (s−1)ζ(s)/s, Poisson–Jensen at a point σ₀ > 1 where ζ is known exactly). Side check: the JAS constant-vector aggregate (`jasPhaseAggregate`, RH ⟺ constant vectors positive on dyadic prime sets). | Wall 2 fully mapped by the corpus. Poisson–Jensen at σ₀: RH ⟺ ∫ log|ζ(½+it)| P_{σ₀}(t) dt equals an explicit constant (BSY form; the gap is Σ_{β>½} log|ρ/(1−ρ)|, corpus bound ≤ ½ log(log 2π − γ) in `ZetaCriticalLineWeightedSecondMoment`). Detecting an off-line zero at height γ needs the tail ∫_γ log|ζ|/t² to precision ~(β−½)/γ², while it fluctuates at size ~√(log log γ)/γ, i.e. pointwise information. Mollified Jensen gaps (`OuterDecompositionLawMollifiedProduct`, `ZetaPoissonJensenInequality`) are the Selberg/Levinson density method, capped by the mollifier-length barrier (mean square ≥ (1 + c e^{−a})T for length < T). The JAS aggregate is a zero-side sum Σ_ρ ∏_p(Bernoulli factors)/(ρ(1−ρ)), i.e. Weil positivity on Euler vectors (walls 6/8). | **KILLED (wall 2 mapped; JAS = walls 6/8)** | NO POSITIVE SALVAGE: every exact log identity on the line is a Poisson–Jensen identity whose evaluation needs pointwise log|ζ|. |
| 154 | Conjecture H: the unsquared heights of the upper roots of e^{−tD²}p are weakly majorized by √(y_j² − 2t). True for one cosine step [L]; checked on paper for two on-axis pairs under heat. Also an RH-core brainstorm of new input classes: tensor-power trick, Hilbert–Pólya/scattering, Stepanov polynomial method, o-minimality, deformation without collisions / gap persistence. | **H: proof route blocked, conjecture open.** Root ODE ż_k = 2Σ(z_k − z_j)⁻¹ gives d/dt Σ_S h_k = −Σ_S 1/h_k + (cross terms ≤ 0 from outside S). At a touching point h ≺ ρ with equal sums, and Karamata for the convex 1/x gives Σ1/h ≤ Σ1/ρ, the wrong direction; so the barrier fails without the cross terms. For two pairs the cross terms add −4Σ/(d² + Σ²) to the total (Σ = h₁ + h₂, d = horizontal offset), which competes with the deficit; no counterexample found. **Brainstorm: all KILLED.** Tensor powers act on local parameters (Ramanujan), not on zeros (wall 5). Scattering/Hilbert–Pólya is wall 4. Stepanov needs Frobenius (wall 5). o-minimality: the zero set is infinite discrete, so not definable, no handle. Gap persistence under backward heat is RH ⟺ Λ ≤ 0 restated; the corpus collision/pair-kernel Lyapunov modules sit at wall 3 (local clustering). | **H OPEN; brainstorm KILLED** | No RH content. H stays as a side question (heights vs squared heights). |
| 155 | Second-sheet majorization (HB burden): treat the resonances ρ/2 of φ(s) = ξ(2s−1)/ξ(2s) as eigenvalues of the dissipative Lax–Phillips generator and use Ky Fan / Krein majorization of their real parts to pin Re = ¼. | Killed by the corpus general-Fuchsian barrier (`hb-general-fuchsian-barrier`). Ky Fan / Krein majorization is group-independent operator theory: it holds verbatim for every cofinite Fuchsian group, and for generic groups the resonances are not on Re s = ¼ (Petridis–Risager Fermi golden rule). A group-independent majorization therefore cannot pin the line; it would prove a false statement. The only arithmetic input left is Hecke positivity, whose slack ∝ (1 − p^{σ−1}) saturates only at σ = 1. | **KILLED (general-Fuchsian barrier)** | Positive survivor: the barrier applies to every operator-inequality mechanism in this session (Ky Fan, Krein realization, energy majorization). They are group- and arithmetic-independent, hence receivers by construction. |
| 156 | Arithmetic specific to ζ that passes the three countermodels (generic Fuchsian, Davenport–Heilbronn, ζ(s−a)ζ(s+a)): a_n ≡ 1. (i) Landau's theorem: log ζ has nonnegative coefficients Λ(n)/log n; look for a nonnegative-coefficient Dirichlet series D with D − log((s−1)ζ(s)) analytic on Re s > ½ and no real singularity above ½ — Landau would then force RH. (ii) Redheffer matrix (det A_n = M(n)): small-eigenvalue product. | (i) KILLED, wall 6. Every nonnegative series encoding the primes (P(s), Σ_p (1 − 1/log p)p^{−s} + prime powers, …) is singular at s = 1 (prime number theorem), so Landau gives σ_c = 1. Removing that singularity needs −log(s−1)-type terms with negative coefficients (the corpus pole-regularized series Σ((Λ(n) − 1)/log n)n^{−s} ⟺ RH, DR route); the corpus Landau machinery (`LandauSummabilityTransfer`, `LandauRelativeRigidity`, `MertensSquareRootOmega`) already gives only Ω-results. Note: modularity + Euler product + FE do not separate ζ from ζ(s−a)ζ(s+a) (the Eisenstein L-function); only temperedness does, and temperedness of local parameters is free for ζ (α_p = 1), so it cannot imply RH by itself. (ii) KILLED, wall 10: the nontrivial Redheffer characteristic factor has divisor-chain-count coefficients, and M(n) = Σ(−1)^k S_k(n) is the cancellation problem itself. | **KILLED (walls 6, 10)** | Positive survivor (paper): in the Selberg-class view, ζ's distinguishing data (Euler product, temperedness, FE, finite order) are exactly the GRH-for-Selberg-class axioms; any producer is a proof of that conjecture's ζ case using only these axioms. NO POSITIVE SALVAGE in Lean. |
| 157 | JAS constant-vector positivity on one dyadic prime set P (fixed small y): can Krein/Ky Fan give a zero-location-free certificate? | A single P is a finite verification, not a producer (corpus kill standard). By `jasDressedPSD_iff_weilEulerForm_nonneg` the aggregate for P is Weil's lag form on one Euler vector, so by the explicit formula it is a finite arch + prime computation. RH needs every large P, and the family is affine in the weights (wall 8). Ky Fan bounds eigenvalue imaginary parts of an operator; here there is no operator whose spectrum is the zero set with a sign-definite imaginary part, and the aggregate's sign is the Weil-form sign itself. | **KILLED (finite check / wall 8)** | Redirected to a structural generalization of the row-141 realization (row 158). |
| 158 | Generalize the row-141 realization from vertically aligned pairs to any matching of upper roots α_j to strictly deeper lower roots β_j (Im α_j + Im β_j < 0): Hermite–Biehler with defects, quantitative. | **FORMALIZED** (standard axioms, wired). `HTGeometry/RealPartProductRealization` refactored to general pair factors (z − x)(z − v) + R + ic(z − v) (`realPartMatrixGen`, `realPartFactorGen`, `charpoly_realPartMatrixGen`, `sum_roots_realPartGen_im_sub_pos_le`; the vertical API is now a specialization; all dependent oleans rebuilt). `HTGeometry/HermiteBiehlerDefectMajorization`: `pairNode` v = Im(αβ)/(Im α + Im β), `pairCoupling` R = (v − α)(v − β) ∈ ℝ, `pairFactor_eval`, **`sum_roots_hermiteBiehlerDefect_le`**: for E = ∏(z − α_j)(z − β_j)∏(z − w_k), Im w_k ≤ 0, the roots of (E + E^#)/2 satisfy Σ(Im − σ)₊ ≤ Σ_j(√R_j − σ)₊; R_j = abs(v_j − α_j)·abs(v_j − β_j) when positive. | **THEOREM [L]** | Quantitative Hermite–Biehler for arbitrary polynomials: defect heights ≺_w the geometric-mean distances from the real nodes v_j to each matched pair; the vertical case gives √(η_α η_β), and with no pairs it is Hermite–Biehler. No RH content (general-Fuchsian barrier, row 155). |
| 159 | Apply the row-158 Hermite–Biehler-defect theorem to Levinson's structure: on the line Z(t) ≈ Re(2e^{iθ(t)}F(½+it)), F = ζ + ζ′/L. Wrong-side zeros of F, matched to deeper correct-side zeros (non-vertical pairs), would bound the off-line heights of ξ by geometric means √(abs(v − α)·abs(v − β)). Does this improve Levinson's proportion or the corpus off-line moment μ ≤ 0.17? | No producer gain. (1) The theorem bounds heights (a moment), not counts; Levinson's proportion needs counts, and #defects ≤ #wrong-side zeros is already the classical count law. (2) For the off-line moment, the theorem is global: the right side sums over all matched pairs (infinite for ζ). A window version needs localization, which the realization does not give (the sign coupling K couples all factors at strength √(c_u c_v), so Schur vectors are not local); only the top-1 disc law is local. (3) √(d_α d_β) ≤ (d_α + d_β)/2 against Littlewood sums for F on both sides reproduces the Littlewood/Selberg off-line-moment mechanism (corpus μ ≤ 0.17, mollifier-capped). | **KILLED (counts vs heights; global vs local; wall 7)** | Open technical question (side): a local energy law — defect energy in a window controlled by pairs within distance ½ of it. True for top-1 (disc law); the sum version is open. |
| 160 | Local defect count / local energy law for cos(hD)Ξ. | The local count is already in the corpus: the sharp transport law `windowDefectCount_le_transport` (defects in shadow-free windows ≤ 2·#{ξ = 0 in window, Re ρ ≥ ½ + h} + 2, `XiCosineShiftExceptionalOnset`), with Selberg-density consequences (`XiCosineShiftCriticalScaleDefectCount`) and ~30 PTR-lane modules. A local energy law would be a receiver inside another agent's lane. | **REDISCOVERED (local count); energy version deferred (receiver, owned lane)** | Process rule reinforced: search the lane module list (`ls RHTower | grep <lane>`) before planning lane-adjacent work. |
| 161 | Fourier interpolation with the zeros as nodes (Radchenko–Viazovska / Bondarenko–Radchenko–Seip type): an exact identity "beyond bandwidth one" in which the zeros appear as nodes. Is any positivity from such a basis RH-selective? | Not in the corpus (search found only Lagrange/Gauss interpolation, `exists_entire_interpolation`, Bondarenko–Seip Gál sums). Structurally the interpolation formula f = Σ_ρ f(γ_ρ)a_ρ + Σ_n f̂(log n/2π)b_n is the Weil explicit formula written in a basis. It is an exact identity with no sign; positivity would need sign information on the basis functions a_ρ, which are built from the same zeros (circular). Any positivity read through it is Weil positivity, affine in the weights (wall 8). | **KILLED (explicit formula in a basis; wall 8)** | Building the interpolation basis in Lean would be a large receiver project with no producer content; not started. |
| 162 | Characterization of energy-law multipliers among three-point laws: for X ∈ {0, ±1} with P(X=±1) = μ/2, is the squared-height majorization with budget E X² = μ true exactly when the law is a Rademacher sum? | **Yes for three-point laws (Lean).** `ThreePointVerticalAverageStripFailure` (rewritten, general μ): symbol 1 − μ + μ cos ξ has only real zeros iff μ ≥ ½ (`threePointSymbol_zero_im_eq_zero`); μ = ½ is cos(D/2)² (`threePointAverage_half_eq_cosProd`), μ = 1 is cos(D) — both obey the law; for every ½ < μ < 1, p = (X² + μ)³ (roots at squared height μ) has an average with a root iv, 0 < v < 1 (`exists_threePointAverage_root_im_pos`, profile μ(1−μ)(2μ−1) > 0 at v = 0, < 0 at v = 1). Standard axioms; lake --old audit clean. | **PROVED (rigidity among three-point LP laws: law ⇔ μ ∈ {½, 1})** | Supports the conjecture "energy-law multipliers = Gaussian–Rademacher sums". Receiver/side mathematics: no RH producer content (multiplier theory is group-independent, row 155). |
| 163 | Hecke-equivariant positivity (aimed at the HB general-Fuchsian barrier, row 155): T_p is arithmetic, so the T_p-spectral measure of the truncated resonant state Λ^Y E*(·, ρ/2) of an off-line zero might have to leave spec(T_p) ⊂ [−2, 2] ∪ {p^{½} + p^{−½}}. Second probe: Landau's nonnegative-coefficient theorem applied to −ζ′/ζ − D with a prime thinning 0 ≤ d ≤ Λ, to remove the pole at 1. | (1) Already in the corpus: the Eisenstein transform of the truncated resonant state is a Cauchy kernel with poles at distance abs(Re u) = (1 − β)/2 (`EisensteinResonantSpectralKernel`). The first two T_p moments are the Breit–Wigner moments p^u + p^{ū} and 2 + p^{2u} + p^{2ū} (`EisensteinHeckeResonantMoment`, `EisensteinHeckeSecondMoment`). A Cauchy law pushed forward by r ↦ 2cos(r log p) is a positive measure on [−2, 2] for every width, so Hecke positivity holds at every β and is not RH-selective. The partner angle law (`EisensteinResonantPartnerAngle`, sin = abs(2β − 1)) is a receiver. (2) The thinning exists iff ψ(x) ≥ x − O(x^{½+ε}), by a greedy construction. That is the one-sided Landau law (`GaussianPrimeBudgetOneSidedLaw`), wall 1. Any nonnegative-coefficient Dirichlet series built from ζ has positive mean b(p), hence the pole at 1 and σ_c = 1 (wall 6). | **REDISCOVERED (HB lane owns the resonant Hecke moments; Landau thinning = one-sided Landau, wall 1/6)** | Survivor (side, not RH): the full T_p moment sequence of the truncated state should be the Cauchy pushforward for k ≤ log Y / log p, with the constant-function component of relative size Y^{−1} above that range. This is a receiver identity. |
| 164 | Measure rigidity for resonant states (Lindenstrauss-type): the microlocal lifts of high resonant states E*(·, ρ/2) are Hecke-recurrent and carry a geodesic transport with damping (1 − β)/2. Conjecture: Hecke recurrence plus conformal transport forces damping ¼, i.e. RH. | FALSE as stated. E(z, σ + it) is a Hecke eigenfunction for every σ (eigenvalue p^{s−½} + p^{½−s}), resonance or not. Its bulk lifts give Hecke-recurrent conformal measures with damping abs(σ − ½) for every σ, so bulk dynamics plus Hecke cannot pin σ. The resonance condition is that the constant term has only the outgoing y^{1−s} part. That is a cusp boundary condition, the scattering matrix ξ(2s − 1)/ξ(2s), i.e. ζ itself. | **FALSE (bulk/Hecke blind to the cusp boundary condition; HB barrier extended to Hecke-recurrent measures)** | Structural lesson: every input living in the bulk of Γ\H (Δ, Hecke, QUE, entropy) sees all s alike. RH content sits only in the constant term, the scattering matrix. Any modular-surface producer must act on the constant term. |
| 165 | "Only if" direction of the multiplier characterization (row 162): a necessary condition for a finitely supported law X to obey the energy law with budget E X². | **PROVED (Lean)**, `HTGeometry/VerticalAverageExtremalBalance`. On the imaginary axis A(X² + m)ⁿ(iv) = Σ w_i (m − (v + x_i)²)ⁿ (`eval_verticalAverage_pairPower`). An odd n with E(m − X²)ⁿ > 0 gives a root iv, v > 0 (`exists_verticalAverage_root_im_pos`), while every root of (X² + m)ⁿ has squared height m (`pairPower_root`). Large odd moments are positive under the extremal imbalance min X² + max X² < 2m with the minimum charged (`exists_odd_pos_moment_of_extremal`, `exists_verticalAverage_root_of_extremal`). An atom at 0 forces max X² ≥ 2 E X² (`exists_verticalAverage_root_of_atom_zero`). Standard axioms; lake --old audit clean; wired. | **PROVED (necessary balance law min X² + max X² ≥ 2 E X²; sharp for Rademacher pairs)** | Explains row 162 conceptually: for three-point laws the balance gives μ ≤ ½ and LP gives μ ≥ ½. Side mathematics (group-independent multiplier theory), no RH content. |
| 166 | Mayer's transfer operator for the Gauss map (a structure absent from the corpus: no Mayer/transfer-operator modules). L_s f(z) = Σ_{n≥1} (z+n)^{−2s} f(1/(z+n)) gives Z_Selberg(s) = det(1 − L_s)det(1 + L_s) for PSL₂(ℤ), and the scattering resonances s = ρ/2 are eigenvalue ±1 points of L_s. Perron–Frobenius positivity of L_s (leading eigenvalue λ₁(s), λ₁(1) = 1, decreasing) might exclude eigenvalue ±1 off Re s = ¼. | Killed. Positivity and nuclearity of L_s hold only where Σ (z+n)^{−2s} converges, i.e. Re s > ½. The resonances sit at Re s = β/2 < ½, where L_s exists only through the Hurwitz continuation L_s f = Σ_k f^{(k)}(0)/k! · ζ_H(2s + k, z + 1), with no cone preserved (wall 6). In Re s > ½ the eigenvalue ±1 points are only Maass parameters; the partner 1 − ρ/2 is not a zero of Z. The eigenvalue condition at ρ/2 is ζ(2s) = 0 again, i.e. the constant term (row 164). For non-arithmetic surfaces the same operator formalism places resonances anywhere in Re s < ½ (HB barrier). | **KILLED (wall 6 + HB barrier; transfer-operator positivity lives in Re s > ½)** | New entry for the walls map: dynamical zeta functions of the modular surface see ζ only through scattering resonances in the non-convergent half-plane. |
| 167 | TH heat trace through the modular trace formula: the continuous-spectrum term of the PSL₂(ℤ) heat trace is Σ_ρ ∫ e^{−tr²} P_w(r − γ_ρ) dr (Lorentzians from −φ′/φ). It is completely monotone unconditionally, while the bare heat trace Θ(t) = Σ_γ e^{−tγ²} is completely monotone iff RH (TH receiver). Can one deform the Poisson width w → 0 while keeping complete monotonicity? | Killed. The analytic continuation of a width-w Poisson kernel to an off-line zero at displacement δ is again a Poisson kernel of width w ∓ δ. So Θ_w is completely monotone iff every displacement satisfies abs(δ) ≤ w. Unconditionally that holds for w ≥ ½; for every w > 0 it is RH. "Θ_w CM ⟺ zeros in the strip of width w" ⟺ Re ξ′/ξ > 0 on Re s > ½ + w: the LA receiver and the cosine family (wall 4). The Lorentzian positivity of HB is RH-blind for the same reason (memory: trace-formula reading, Hejhal 1976). | **KILLED (TH = LA = cosine family under Poisson smoothing; wall 4)** | Unifying remark: Poisson width in the spectral variable = horizontal distance in s = cosine shift h = de Bruijn strip. All width-deformation producers are one family. |
| 168 | Higher-rank Langlands contour shift: in GL₃ (or any rank ≥ 2), shifting the minimal-parabolic Eisenstein series from the convergent chamber to the unitary axis crosses regions where ζ(λ_i − λ_j) appears. An off-line zero might create a pole there whose residue would be an L² automorphic form with non-real Laplace eigenvalue, contradicting self-adjointness. | Killed. The normalized constant terms are ratios ξ(λ_i − λ_j)/ξ(λ_i − λ_j + 1). The shift crosses 0 < Re(λ_i − λ_j) < 1, where the denominators have arguments with real part in (1, 2) and are zero-free. Zeros of the numerators are zeros, not poles, and the only crossed poles are the ξ(1) residual hyperplanes (constants and Speh-type residues). The spectral decomposition never meets ζ zeros on the first sheet; they live in the meromorphic continuation past the unitary axis, as in rank one (rows 164, 166). | **KILLED (wall 6: the crossed region is where the L-function denominators converge; Moeglin–Waldspurger residual spectrum is ζ-zero-free)** | Same lesson in every rank: L² spectral theory sees ζ only through denominators at Re > 1. Zeros enter only as second-sheet resonances. |
| 169 | "Second-sheet positivity" (HB producer burden) as inner-function rigidity. φ̃(s) = φ(s)(s − 1)/s is inner in Re s > ½ (Lax–Phillips contractivity) with zeros at (1 + ρ)/2. RH ⟺ every Blaschke zero sits at distance ¼ from the boundary. Does the Dirichlet-series form φ = G(s)·Σ φ_E(n) n^{−2s} (Euler totient; φ_p = (1 − p^{−2s})/(1 − p^{1−2s})) together with innerness force the zeros onto one line? | Killed. (1) Innerness is equivalent to positivity of the boundary phase derivative −φ′/φ(½ + ir) = Σ Lorentzians of widths β/2 and (1 − β)/2. That is the RH-blind time-delay positivity (memory: trace-formula reading); any width in (0, ½) is allowed. (2) The local factors φ_p are not unimodular on Re s = ½, so there is no local inner structure to multiply. (3) Structural reason the Hecke layer is a receiver: on the continuous spectrum of PSL₂(ℤ)\ℍ, T_p = 2cos(log p · √(Δ − ¼)) (multiplicity one, eigenvalue p^{ir} + p^{−ir}). Hecke operators there are functions of Δ, so every Hecke positivity on Eisenstein or resonant data is Laplacian positivity, which is group-independent. This explains the Breit–Wigner moments (rows 163, MUST-368/369) without computation. | **KILLED (innerness = width positivity; Hecke = f(Δ) on the continuous spectrum; HB barrier)** | Wall-map addition: on the continuous spectrum the Hecke algebra collapses to functions of Δ. Arithmetic information beyond Δ lives only in the cuspidal spectrum (Hecke eigenvalues not determined by Δ) and in the constant term. Any modular producer must couple the cuspidal Hecke data to the constant term. The trace formula does this (Hejhal: cusp sum gives only an upper bound on the Weil functional, memory row 10). |
| 170 | Unification check: where exactly does the modular (HB) picture see ζ? | Exact: −φ′/φ(½ + ir) = 2ξ′/ξ(1 + 2ir) + 2ξ′/ξ(1 − 2ir) = 4 Re ξ′/ξ(1 + 2ir) = 4 Σ_ρ (1 − β)/((1 − β)² + (2r − γ)²). The PSL₂(ℤ) continuous spectrum, Maass–Selberg, time delay and the amplified trace formula (amplifier A(r) = Σ c_n η_n(r) gives ∫ h·abs(A)²·(−φ′/φ) ≥ 0) all read ζ through Re ξ′/ξ on the 1-line, a Poisson smoothing of the zero measure at width 1 − β ≈ ½. That is the unconditional horizon producer cos(½D)Ξ = Re ξ(1 + it) of the PTR/W1C routes (h = ½), which is real-rooted unconditionally. RH is the width-0 limit (rows 160, 167; R:XiCosineShiftWindowRHCriterion). | **UNIFIED (HB modular spectral theory = cosine/Poisson family at h = ½; the RH gap is ½ → 0)** | All four families are one statement: HB/Eisenstein (width ½, free), PTR/W1C cosine (h ≥ ½ free, h → 0 RH), TH/HCF heat trace (Poisson width w, row 167), LA (Re ξ′/ξ on Re s = ½ + w). A producer must lower the width below ½ with an input that is not a positivity of the h = ½ object. No known arithmetic object lives at width < ½ with positivity (wall 6: Euler-product positivity needs width > ½, i.e. Re s > 1). |
| 171 | Search for a producer class outside the width family (row 170) and the heat family. Candidate classes: (i) height-indexed families (Li coefficients, Turing-style P(T), finite-aperture Weil positivity); (ii) extremal / LP-duality families with a magic-function certificate (Cohn–Elkies/Viazovska type); (iii) operator (Hilbert–Pólya). Test (ii) on the corpus's PBAP sub-problem `WindowPositive` (`PrimeBlindNonnegativeConeReduction`: abs(A(0))‖h‖² ≤ J(h) + 2P(h) for h ≥ 0 on (0, log 2); unproved in the corpus, "numeric, margin ≈ 0.15"). | (i) Height-indexed families reduce to wall 1 at each scale: RH up to T gives the PNT with √x error only for x ≤ T², and that detects nothing new. Finite-aperture Weil positivity at aperture a detects off-line zeros up to height about e^{2a} at any displacement: a mixed height/width family. (ii) This is a genuine third class, and it is the HF/PBAP lane: RH ⟸ PBAP + (N1); PBAP ⟺ the Weil cone is nonempty. For WindowPositive, in ψ-form W/‖h‖² = A(0) + ∫_0^∞[2ω(1 − ψ) + 4cosh(x/2)ψ]. Pointwise bound (ψ ∈ [0, 1], crossover x* ≈ 0.281): A(0) + 2∫_{x*}^∞ ω + 8 sinh(x*/2) ≈ −5.372 + 4.087 + 1.129 = −0.157, which fails. Subadditivity of d = ‖h − h(· + x)‖/‖h‖ (u ≥ 2/⌈L/x⌉²) recovers only about 0.025, giving about −0.13. Exact LP-dual certificate (paper; Plancherel plus the Gauss–Lévy identity A(τ) − A(0) = 2∫ω(1 − cos τx)): an even M with M̂(τ) ≥ −A(τ) for all τ and M(x) ≤ 2cosh(x/2) on abs(x) ≤ log 2 implies WindowPositive. Necessary conditions: ∫_{abs(x)>log 2} M ≥ 5.372 − 8 sinh(½ log 2) = 2.544, and the window part alone fails for τ ≥ 4 (paper table: −A = 5.37, 2.03, 1.16, 0.74, 0.45, 0.23, 0.05 at τ = 0..6 versus K̂_in = 2.83, 2.60, 1.99, 1.16, 0.34, −0.29, −0.61). | **PARKED (certificate design needs numerical optimization; pod-only rule requires authorization). Class (ii) identified as the only non-width, non-heat producer class in the corpus** | Survivor: the precise LP-dual form above, as a ready sub-problem for the HF lane. Significance is limited: the nonnegative cone only. Full PBAP needs signed tests, and (N1) remains. |
| 172 | Hand design of the LP-dual certificate for `WindowPositive` (row 171): M with M̂ + A ≥ 0 and M ≤ 2cosh(x/2) on the window. Natural candidate: M = 2cosh(x/2) on abs(x) ≤ log 2 and ω(abs(x)) outside. | Paper evaluation (digamma via ψ(z) = ψ(z + 2) − 1/z − 1/(z + 1) plus Stirling; ω-tail FTs via the geometric series ω = Σ_k e^{−(2k+½)x}). Slack S(τ) = A(0) + 2∫_L^∞ω + 2∫_0^L ω(1 − cos τx) + K̂_in(τ). Values at τ = 0..8: +0.45, +0.37, +0.15, −0.12, −0.36, −0.48, −0.43, −0.23, +0.07. The symbol condition fails on τ ∈ (2.5, 7.8). A nonnegative inner correction g = c(δ_{x₀} + δ_{−x₀}), x₀ = 0.63, c = 0.22 nearly closes the gap: residual failures ≤ 0.10, at τ ∈ {4, 5, 6, 7, 8}. Feasibility therefore looks plausible with a few more parameters, but finishing needs a numerical LP, plus rigorous digamma enclosures for a Lean proof. | **PARKED (near-feasible; needs a numerical LP, which requires authorization under the pod-only rule)** | Payoff assessment: WindowPositive gives PBAP on the nonnegative cone only. The real target is signed PBAP plus (N1), so this sub-problem has limited producer value. Recorded so the HF lane can pick it up with the certificate shape and the slack table. |
| 173 | Signed PBAP (the existence half of class (ii)) via Herglotz functions. PBAP ⟺ the Weil cone is nonempty ⟺ some real weights λ(n), n ≥ 2, make h(s) = arch(s) + 1/s + 1/(s − 1) − Σ λ(n) n^{−s} Herglotz (Re h ≥ 0) on Re s > ½. Can a simple fake von Mangoldt sequence work? | Paper. The Herglotz condition forbids interior poles, so Σ λ(n) n^{−s} must carry the pole 1/(s − 1) exactly: λ has mean 1 with RH-quality partial sums Σ_{n≤x} λ = x + O(x^{½+ε}). This matches the frontier fact "full positivity ⇒ Σ λ = N + O(N^{½+ε})". On the line the condition is Re Σ λ(n) n^{−½−iτ} ≤ ½A(τ) + O(1) ≈ ½ log(τ/2π). (a) λ ≡ 1 (G = ζ − 1, PNT with O(1) error) fails: Re ζ(½ + iτ) is unbounded beyond log τ (Bondarenko–Seip size). (b) Shifted von Mangoldt weights Λ(n) n^{−ε} put the pole at 1 − ε, giving a second interior pole, so they fail. (c) Finite truncations need predominantly negative weights (Σ λ n^{−½} ≤ A(0)/2 ≈ −2.69) and then fail the almost-periodic return argument (row 171). Λ is the edge solution: Re ξ′/ξ = 0 on the line except at zeros. | **OPEN (no fake λ found; every natural candidate dies from line-growth or interior poles)** | Sharpened statement: PBAP asks for a Dirichlet series with frequencies log n, the exact ζ pole, and real part on the critical line bounded above by the archimedean ½ log τ. Under RH only Λ qualifies (corpus rigidity), so the existence half is RH-strength in practice. Combined with row 171, all three producer classes now have their core: width → quasi-RH; heat → Newman; extremal → the existence of a Herglotz Dirichlet series. |
| 174 | Direct attack on the asymptotic abscissa law (AAL: if only finitely many zeros lie right of ½ + h, then none do; RH ⟺ ZAL ∧ AAL, `riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`). Can a finite nonempty set S of zeros right of a vertical line be ruled out unconditionally? | Not with available tools. (1) ¬AAL ⇒ ¬weak recurrence near the top zero, by Hurwitz: for large τ the shifts ζ(· + iτ) are zero-free on a disc K around ρ₀ ∈ S, so their limits are zero-free or ≡ 0, and ζ is not. Corpus `asymptoticAbscissaLaw_of_weaklyRecurrent` is the same statement read forwards, so AAL is BAG-core-hard (ζ as a recurrent point of the Bohr flow in the strip, where F(s; ω) is discontinuous). (2) Finite S is internally consistent: ψ(x) − x = −Σ_S x^ρ/ρ + O(x^{½+h+ε}). Positivity of Λ, Landau's theorem applied to ζ(s)²ζ(s + iγ₀)ζ(s − iγ₀) (nonnegative coefficients, double zero at β₀) and the Deuring–Heilbronn transfer to ζ_K give no contradiction. | **OPEN (AAL = recurrence at the top zero; no isolated-zero contradiction exists in the positivity toolkit)** | Precise residual: show that one off-line zero forces infinitely many with real part ≥ β₀ − ε. That needs a recurrence mechanism for ζ itself in the strip, i.e. the BAG core. |
| 175 | Why every Λ ≥ 0 argument stops at width ½ (structural lemma for the row-170 unification). | For a nonnegative test k, the pole functional ∫k(x)e^{±x/2}dx > 0 cannot vanish. Hence any zero bound derived from Λ ≥ 0 carries the pole kernel cosh(x/2), which dominates the off-line contribution cosh(δx) for every δ < ½. Removing the pole (polar-constrained tests) forces sign changes in k, and then Λ ≥ 0 no longer applies; one needs signed prime cancellation (wall 1). Sharpness: Beurling systems (nonnegative Λ_B, simple pole at 1, PNT; Diamond–Montgomery–Vorhauer type, corpus `GeneralizedPrimeCountermodel`, Beurling modules) have off-line zeros at any δ < ½. Width beyond the pole requires the exact integer structure (Hamburger/FE) or cancellation. | **STRUCTURAL (paper; consistent with corpus Beurling countermodels)** | Producer requirement restated: an input carrying signed cancellation of Σ Λ(n) n^{−½−it} beyond what positivity gives. Classically: zero-free regions from exponential sums (Littlewood in Lean; Vinogradov–Korobov not in Lean). The width frontier as a function of height is δ_max(γ) ≤ ½ − c(log γ)^{−2/3−ε}. |
| 176 | (N1) existence by convex duality (ζ-free after the divisor transfer, `ExactNullCertificateLogRoomGrowth`): find R ≥ 0 on the critical line (analytic, symmetric) with G(½ + it)²R integer-blind (moments L_n(R) = 0 for all n ≥ 2). Farkas: no witness ⟺ some Dirichlet series D(s) = Σ_{n≥2} a_n n^{−s} has Re[Γ_ℝ(½ + it)²P(t)D(½ + it)] ≥ 0 for all t. | Paper. (1) No finite certificate exists. e^{2iϑ(t)} = Γ_ℝ(½ + it)²/abs(Γ_ℝ)² rotates at speed ϑ′ ~ ½ log t, while a finite D has bounded phase speed and abs(D) ≥ c on a set of positive density, so the real part changes sign. Hence the moment cone at every finite level N is all of ℝ^{N−1}, and finite-level witnesses exist (Carathéodory point masses smoothed by Gaussian bumps e^{(s − ½ − it_j)²/ε}: entire, positive on the line, symmetric). The corpus already has this (HF: "one actual Gram test realizes every prescribed finite coefficient vector"). (2) The natural infinite certificate ζ² − 1 nearly works: Γ_ℝ²ζ² = Z̃(t)² ≥ 0, but the removed n = 1 term leaves −Re Γ_ℝ², uncontrolled at the critical zeros. (3) The infinite level is an escape-of-mass problem. By log-Carlson, witnesses must grow at least e^{(π/2)abs(t)/log abs(t)}, so finite-level witnesses with fixed decay cannot converge; one needs cutoff-uniform tail control in the room below e^{π abs(t)/2}. | **REDISCOVERED (finite level) / OPEN (uniform tails)** | Residual stated sharply: build blind witnesses whose mass escapes to infinity at the log-Carlson rate with uniform control. This is the HF Needs item "finite Gram feasibility supplies no cutoff-uniform cost". |
| 177 | Explicit (N1) witness family. Ingredients: the elementary positive integer-blind measures ν = W(t)·abs(A(t))², with A = Σ_{X<m≤2X} a_m m^{−it} and Ŵ supported in (−1/(4X), 1/(4X)), exactly blind because no ratio nm/m′ (n ≥ 2, m, m′ ∈ (X, 2X]) lies within e^{±1/(4X)} of 1; the divisor transfer (Ξ²R blind ⟺ G²R blind); and the chirp identity G(½ + it) = χ̃(t)·conj G(½ + it), χ̃ = G(s)/G(1 − s). Set abs(G)²R = abs(A)²W. | Then G²R = χ̃·abs(A)²W, and χ̃ is multiplicative convolution with a cosine kernel K_c (Mellin of cos 2πx). Blindness becomes ∫h(y) K_c(n/y) dy/y = 0 for n ≥ 2, where h is the inverse Mellin of abs(A)²W: narrow bumps at the Farey-type ratios m′/m ∈ (½, 2). In the narrow-bump limit: Q_n(a) = Σ_{m,m′} a_m ā_{m′} K_c(nm/m′) ≈ 0 for every n ≥ 2, infinitely many quadratic conditions on finitely many a's (escape of mass again). If the weights depend only on the reduced denominator q of m/m′, Q_n becomes a Ramanujan expansion Σ_q f(q) c_q(n). The demand Σ_q f(q) c_q(n) = [n = 1] forces (Möbius inversion in the multiple direction) f(q) = q^{−1} Σ_m μ(qm)/m, which vanishes identically by the PNT (Σ_{(m,q)=1} μ(m)/m = 0). So the denominator-only ansatz is degenerate: the n = 1 mass is lost exactly as the blind conditions are met. | **KILLED (denominator-only ansatz degenerate by the PNT; general ansatz = escape-of-mass core)** | New link (paper): (N1) blindness through the Gamma chirp is a Farey/Ramanujan-sum problem. "Blind at n ≥ 2 but not at n = 1" collides with Σ_q c_q(n)/q = 0 for all n (Ramanujan), so a witness must break the denominator symmetry. The witness must use numerator information (Kloosterman-type phases): corpus Estermann/Kloosterman lanes. |
| 177a | Correction to row 177. | The Möbius inversion in the multiple direction, f(d) = Σ_m g(dm)/(dm) with g = μ, needs Σ_m abs(μ(dm))/(dm) < ∞, which fails. So "denominator-only weights are degenerate" is a formal statement, not a proof. Rigorous form: no absolutely summable f admits an absolutely convergent inversion with Σ_q f(q)c_q(n) = [n = 1]; conditionally convergent Ramanujan expansions of δ_{n,1} are not excluded. | **DOWNGRADED (formal heuristic)** | Do not cite row 177 as a theorem. |
| 178 | Estermann/Kloosterman-phase plan (row 177) recast exactly. (N1) in the cleanest form (paper, consistent with `ExactNullCertificateDivisorTransfer`): find P(t) = 𝓜ρ(½ + it) > 0 (P = abs(G)²R) with chirped moments ∫P(t) cos(2θ(t) − t log n) dt = 0 for every n ≥ 2. Equivalently, on the boundary: ρ even, 1-periodization Σ_k ρ(ξ + k) = B cos 2πξ (A = 0 is forced by the polar condition ∫ρ = 0), inversion symmetry ρ(1/ξ) = abs(ξ)ρ(ξ), and a positive Mellin symbol. Chain: χ̃ = G(s)/G(1 − s) = 2𝓜[cos 2πx]; Ψ_R(n) = ρ̂(n), the cosine transform of ρ(ξ) = h(1/ξ)/ξ. | Stationary phase: 2θ′(t) = log n at t_n = 2πn, and near t_n, cos(2θ(t) − t log n) ≈ cos((t − t_n)²/(4πn) − π/4), a Fresnel packet of width about √n. For P > 0 varying slowly on scale √n the n-th moment is ≈ P(t_n)·2π√n > 0. So every witness must oscillate at scale √t at every height and cancel each Fresnel packet at t_n = 2πn, n ≥ 2, while keeping the n = 1 packet (t ≈ 2π) and the log-Carlson floor P ≳ e^{−(π/2)t/log t}. Kloosterman/Estermann weights enter only through the numerators of the Farey ratios m/m′ (row 177). The packet-cancellation requirement says the needed object has Riemann–Siegel geometry (packets at 2πn ↔ the terms n^{−½−it}), i.e. P must be "orthogonal to every Riemann–Siegel term except the first". | **OPEN (sharpened: local Fresnel-packet cancellation at every 2πn, n ≥ 2)** | Lean candidate (infrastructure, several cycles): formalize the cosine-kernel identity certKernel R = (2cos 2πx) ⋆_mult h and the periodization equivalence (Poisson summation), turning the corpus (N1) open core into the T/S functional-equation form in Lean. |
| 179 | (N1) in factorized form (paper). Parametrize the positive symbol as P = abs(𝓜f(½ + it))² with f real on (0, ∞). Then H = 𝓜f(s)𝓜f(1 − s), h = f ⋆ f̌ (f̌(x) = f(1/x)/x), and since χ̃ = 2𝓜[cos 2π·], k ⋆ f̌ = Cf (Cf(w) = 2∫f(z)cos(2πzw)dz). So the corpus kernel factorizes as Ψ_R = Cf ⋆_mult f: Ψ(x) = ∫f(y)(Cf)(x/y)dy/y. Substituting z = ry gives Ψ(n) = 2∫_0^∞ A_f(r) cos(2πnr) dr, with the dilation autocorrelation A_f(r) = ∫_0^∞ f(y)f(ry) dy. | (N1) ⟺ there is f (decay class, 𝓜f zero-free on Re s = ½, ∫f = 0 for the polar condition) whose dilation autocorrelation A_f, extended evenly, has 1-periodization equal to b·cos 2πr with b ≠ 0. A_f has the inversion law A_f(1/r) = r A_f(r) and a positive Mellin symbol abs(𝓜f)² for every f, so the S-symmetry and positivity of row 178 are automatic. Only the T-condition (periodization) remains, and it is quadratic in f. Immediate exclusions: f ≥ 0 is impossible (A_f ≥ 0 cannot periodize to b cos 2πr); support of f in [α, β] needs β/α − α/β ≥ 1 for the translates of supp A_f ⊂ [α/β, β/α] to cover ℝ. | **REFORMULATED (positivity removed; (N1) = a quadratic periodization equation for one function f)** | This is the cleanest form so far: positivity is built in by the factorization, leaving one quadratic constraint family. Possible route: a fixed-point or implicit-function argument in f around a near-solution, or an exact solution from Hecke-type self-similar f. Lean target: the x-space identity Ψ(n) = 2∫A_f cos(2πn·) plus the inversion law (Fubini on compactly supported f), and the Poisson periodization criterion (Mathlib `Real.fourierCoeff_tsum_comp_add`). |
| 180 | Formalize the factorized (N1) form of row 179 (x-space part). | **PROVED (Lean)**, `RHTower/DilationAutocorrelationPeriodization`. For continuous f supported in [α, β], 0 < α ≤ β: dilation autocorrelation A_f(r) = ∫_0^∞ f(y)f(ry) dy with inversion law A_f(1/r) = r A_f(r) (`dilationAutocorr_inv`); Cf ⋆ f = 2∫_0^∞ A_f(r) cos(2πxr) dr (`cosDilationKernel_eq`, substitution plus Fubini on [α, β] × [α/β, β/α]); even-extension form (`cosDilationKernel_eq_integral_abs`); A_f continuous and supported in [α/β, β/α] (`continuous_dilationAutocorr`, `dilationAutocorr_eq_zero_of_not_mem`); 𝓕[A_f(abs ·)] = Ψ_f (`fourier_evenDilationAutocorr`); Poisson periodization: if Ψ_f(n) = 0 for every abs(n) ≥ 2 then Σ_k A_f(abs(x + k)) = Ψ_f(0) + 2Ψ_f(1) cos 2πx (`tsum_dilationAutocorr_abs_eq`, via Mathlib `Real.tsum_eq_tsum_fourier`). Standard axioms; lake --old audit clean; wired into RHTower. | **PROVED (Lean infrastructure for the HF (N1) core)** | Missing link to the corpus kernel: certKernel R = cosDilationKernel f for R = 𝓜f(s)𝓜f(1 − s)/(archXi(s) archXi(1 − s)), the Mellin step using χ̃ = 2𝓜[cos 2π·]. With it, `logNode_blind_iff_certKernel_vanishes` plus this module turn (N1) into "find f whose even dilation autocorrelation periodizes to b cos 2πx". Next Lean target. |
| 181 | Mellin link for the factorized (N1) form: identify Cf ⋆ f with the inverse Mellin transform of χ̃(s)𝓜f(s)𝓜f(1 − s), the shape of the corpus kernel 𝓜⁻¹[G²R] for R = 𝓜f(s)𝓜f(1 − s)/archXi(s)². | **PROVED (Lean)**, `RHTower/CosDilationKernelMellinInversion`. For f smooth and supported in [α, β] ⊂ (0, ∞): Cf = 𝓕 of the even Schwartz extension (`fourier_halfLineEvenExt`); local functional equation on the critical line, Γ_ℝ(½ + iτ)𝓜[Cf](½ − iτ) = Γ_ℝ(½ − iτ)𝓜f(½ + iτ) (`Gammaℝ_mul_mellin_halfLineCosTransform`, from corpus `soninMellinEvaluation_fourier`); absolute integrability of the Mellin integrand on (0, ∞)² (`integrable_cosDilationMellinIntegrand`); Mellin factorization 𝓜[Cf ⋆ f] = 𝓜f·𝓜[Cf] on Re s = ½ (`mellin_cosDilationKernel`); Mellin convergence and vertical integrability (`mellinConvergent_cosDilationKernel`, `verticalIntegrable_mellin_cosDilationKernel`, using corpus `IsTest.exists_norm_mellin_le_decay`); inversion: Cf ⋆ f(x) = 𝓜⁻¹_{1/2}[(Γ_ℝ(s)/Γ_ℝ(1 − s))𝓜f(s)𝓜f(1 − s)](x) for x > 0 (`mellinInv_gammaRatio_mellin_eq_cosDilationKernel`). Standard axioms; lake --old audit clean; wired. | **PROVED (Lean)** | Remaining link: the corpus `certKernel R = mellinInv 3 (archXi² R)` with `logNode_blind_iff_certKernel_vanishes` needs R holomorphic on ½ ≤ Re ≤ 3 (removable double pole at s = 1 once ∫f = 0) and strip bounds (ζ² growth times Gamma-ratio growth against the all-order Mellin decay of f). Together with rows 180–181 this makes (N1) for smooth compactly supported multipliers ⟺ "even dilation autocorrelation of f periodizes to b cos 2πx". |
| 182 | Existence of a compactly supported (N1) witness via a perturbation (implicit-function) argument in the factorized form. In log coordinates: find an even PD Φ = F ⋆ F̃ (F compactly supported, F̂ zero-free) whose coefficients c_m(Φ) = 2∫Φ(u)e^{u/2}cos(2πm e^u)du vanish for m = 0 and every m ≥ 2, with c_1 ≠ 0. | Paper. (1) **Linear part = Mayer's transfer operator at s = ½.** With G(r) = Φ(log r)r^{−½} supported in (½, 2) and h(x) = G(1 + x), periodization to a target τ reads h(x) + h(1 − x) + x^{−1}h(1/x − 1) = τ(x) on (½, 1): the n = 1 branch of the Gauss map with weight abs(T′)^{1/2}. Larger supports bring in all branches, giving the Mayer operator L_{1/2} of row 166. Its eigenvalue-±1 obstruction at s = ½ comes from E(z, ½) only (SL₂(ℤ) has no Maass form at λ = ¼), matching the corpus finding "exceptional space from E(τ, ½) only". (2) **Farkas form.** No witness exists ⟺ ∃(a_m) with −(φ_1^e + Σ_{m≠1} a_m φ_m^e), φ_m^e(u) = ½(e^{u/2}cos 2πm e^u + e^{−u/2}cos 2πm e^{−u}), positive-definite-extendable from the window (Krein). (3) Mean-value heuristic: a certificate Re[χ̃(½ + it)(1 + Σ_{m≥2} a_m m^{−½−it})] ≤ 0 forces 1 + Σ a_m m^{−s} = −χ·(nonnegative) = −ζ²U with U real on the line and u_1 = −1. Real-on-line Dirichlet series with the Bohr mean property are constant, so no almost-periodic certificate exists. The closure question (window completeness of {φ_m^e}_{m≠1}, i.e. the image {u + u∘S}) is the corpus packet identity. | **REDISCOVERED structure (corpus rows 1013–1021) + new Mayer link; existence still OPEN** | Where (N1) stands: the linear part is Fredholm (Mayer at ½, E(z, ½) obstruction); the positivity/closure part decides existence. Compactly supported witnesses sit far above the log-Carlson threshold, so that theorem does not exclude them. |
| 183 | Complete the Lean link from the corpus blindness theorem to the factorized (N1) form. | **PROVED (Lean)**, `RHTower/CosDilationKernelBlindnessLink`. For f smooth, supported in [α, β] ⊂ (0, ∞), with 𝓜f(1) = 0: the resolved multiplier R_f(s) = 4𝓜f(s)𝓜f(1 − s)/(s²(s − 1)²Γ_ℝ(s)Γ_ℝ(1 − s)) (`cosDilationCertMultiplier`, dslope plus Γ((3 − s)/2)) is holomorphic on Re s > 0. It satisfies archXi²R_f = (Γ_ℝ(s)/Γ_ℝ(1 − s))𝓜f(s)𝓜f(1 − s). Strip bounds on ½ ≤ Re ≤ 3 for archXi²R_f and ξ²R_f follow from the Gamma-ratio growth bound (`exists_bound_norm_Gammaℝ_div_strip`, via reflection plus the corpus Γ strip decay), ζ strip growth, and all-order Mellin decay (`IsTest.exists_norm_pow_mul_norm_mellin_le`, Euler-derivative induction). The corpus kernel is the cosine–dilation kernel (`certKernel_cosDilationCertMultiplier`). **Main theorem** `logNode_blind_iff_cosDilationKernel_vanishes`: the positive Ξ²-divisible test ĝ = Ξ²R_f is blind at every log n, n ≥ 2, iff (Cf ⋆ f)(n) = 0 for every integer n ≥ 2. With `tsum_dilationAutocorr_abs_eq` this is "the even dilation autocorrelation of f periodizes to Ψ_f(0) + 2Ψ_f(1)cos 2πx". Standard axioms; lake --old audit clean; wired. Reused the corpus `RHTower.differentiableAt_Gammaℝ_of_re_pos` and `HTGeometry.norm_sin_le_exp_abs_im` instead of duplicating them. | **PROVED (Lean): (N1) blindness for smooth compactly supported multipliers reduced to a periodization identity for one function** | Remaining to reach the corpus `XiDivisibleBlindTest` Prop: F with F̂ = ζ·𝓜f-type, its exponential decay class, and 𝓜f zero-free on the critical line. Remaining mathematically: a witness f (rows 176–182; the linear part is Mayer at s = ½). |

## Row 184 (2026-10-13) — (N1') witness geometry: short cores are rigid; existence = linear-conic problem
- Reformulation (paper, checked): with A_f(r)=∫f(y)f(ry)dy and B(u)=e^{u/2}A_f(e^u), the set {A_f : supp f ⊂ [1,R]}
  is a CONVEX cone (Krein–Akhiezer factorization of nonnegative type-2L entire functions), so (N1') at support ratio R
  is a LINEAR feasibility problem: find B even, PD (B̂>0), supp ⊂ [−log R, log R], with
  ∫B(u)e^{u/2}cos(2πn e^u)du = 0 for n ∈ {0,2,3,...}.  Dual certificate = positive measure ν with
  ν̌|[−log R, log R] = e^{u/2}Λ(e^u)+e^{−u/2}Λ(e^{−u}), Λ even 1-periodic with no first harmonic.
- Sum rules for any witness: Σ_k A_f(|x+k|) = 2Ψ_f(1)cos2πx; for every q ≥ 2, Σ_{j≥1} A_f(j/q) = 0.
- DOF count: constraint density per degree of freedom at every frequency = 1/(R − 1/R); overdetermined iff
  R < golden ratio. Riesz-sequence heuristic for the chirps cos(2πn r) on [1/R,R] needs the same R − 1/R > 1.
- [L] NEW `RHTower/CosDilationShortSupportRigidity`: `eq_zero_of_cosDilationKernel_blind_of_le_two_mul`
  (f continuous, supp ⊂ [α,β], β ≤ 2α, Ψ_f(0)=0, Ψ_f(n)=0 ∀n≥2 ⇒ f ≡ 0), via periodization at x=0, ½:
  A(1)=Ψ(1), A(3/2)=−Ψ(1), and 2|ab| ≤ a²+b² ⇒ |A(3/2)| ≤ (5/6)A(1). Also `cosDilationKernel_zero_of_integral_eq_zero`,
  `dilationAutocorr_eq_zero_of_not_mem_Ioo`, `cosDilationKernel_int_eq_zero`. Standard axioms, audited, wired.
- Corpus check: `ExactNullCertificateLogRoomGrowth` (log-Carlson) forces witnesses to have
  ∫|𝓜f(½+it)|² e^{(π/2)|t|(1−1/log|t|)} = ∞; compactly supported f satisfy this automatically.
- Complement to corpus `volume_pos_le_log_two_of_primeBlind` (nonnegative blind tests have log-support ≤ log 2):
  Ξ-divisible blind tests of the form ζ·𝓜f need Möbius core f of log-length > log 2.
- Verdict: BRIDGE-level structural fact (necessary condition). Existence of (N1') witnesses for large R: OPEN,
  heuristically true (no almost-periodic dual certificate; DOF count), architecture = finite-level witness for low n
  + edge-cascade corrections (residual at x-frequency m corrected at the support edge, mirrored, frequency drops by R²).

## Row 185 (2026-10-13) — KILL of the (N1') compact-core program; centre-dominance no-go (paper)
- Conjecture C185a (N1' existence for large R; DOF count 1/(R−1/R) < 1): FALSE (paper proof architecture
  complete; card `compact-mobius-core-never-blind.md`). The degree-of-freedom heuristic ignored PD centre dominance.
- Mechanism: in u = log r, a PD B has its largest local spectral content at the centre u = 0 (r = 1)
  (Cauchy–Schwarz for the PSD form). In the periodisation identity Σ_k A_e(x+k) = a + b cos2πx near x = 0, the centre
  enters with positive weight μ(τ) (exact for multiplicatively positive-type windows). The only competitors are windows at
  r = k ≥ 2, which see B near log k at frequency kτ and are bounded by √k·μ(kτ). Super-polynomial decay plus a maximiser of
  μ(τ)τ^N e^{−T/τ} forces exponential decay of B̂, hence B is analytic, so B ≡ 0 under compact support.
- Finite-order variant (independent algebraic proof): the jump of P^{(2j+1)} at 0 is ⟨D, μ⋆D⟩ with
  μ̂(χ) = Re L(2j+3/2, χ) > 0 for every unitary character χ of ℚ_{>0} (|arg L(σ,χ)| ≤ Σ_p arcsin p^{−σ} < π/2).
  Correction to my own row 184 Schur estimate: Σ_{k≥2} k^{−3/2} = ζ(3/2) − 1 = 1.612, not 0.612. The
  character argument replaces it.
- No-go closure: positive survivor = "an (N1) witness core has A_f(r) ≠ 0 for arbitrarily small r (infinite support
  ratio); the centre r = 1 is balanced only by the r ≈ 0 window (left tail of B against slow chirps)". This links to
  log-Carlson: witnesses are analytic-critical objects, and the compact class is empty.
- Lean status: special case β ≤ 2α done (row 184). Full theorem needs Gaussian-window lemmas W1–W3
  (complex Gaussians, correlation Cauchy–Schwarz, local contour shift) + maximiser + analyticity ⇒ multi-module project.
- **Row 185 correction (same day):** the full compact-core no-go is NOT proved. The backward window at r = 1 is
  chirped by the parabolic map r ↦ 1/(2−r), and the maximiser cannot control frequencies below τ. Rigorous
  replacement (A2), via the integrated identity with weight τ^s e^{−a(T−τ)_+/√T}: a blind compact core has
  ∫_T^∞ B̂ ≤ C e^{−a√T} (Gevrey-2 forced). (A1) finite-order breaks excluded. Open: Gevrey 1 < s < 2. The threshold
  s = 2 matches the parabolic chirp τ^{(2−s)/s} and exact parabolic anti-invariant profiles e^{−c/|r−1|}sin(π/(r−1))
  (B̂ ≍ e^{−2√(cξ)}). New conjecture C186: witnesses ⟷ positive-definite B with Gevrey-2, parabolic-anti-invariant
  singular parts at all Farey points (quantum-modular structure at s = ½).

## Row 186 (2026-10-13) — Lean: piecewise-linear Möbius cores are never blind (all support ratios)
- [L] NEW `RHTower/PiecewiseLinearCoreBlindnessRigidity`: `plCore_coeff_eq_zero_of_cosDilationKernel_blind`.
  For f = Σ_j e_j (x − y_j)_+ (continuous, piecewise linear, compact support in (0,∞)), blindness of
  Ψ_f = Cf ⋆ f on ℕ_{≥2} forces f ≡ 0, for every support ratio.
  Mechanism (new): closed form A_f(r) = (r/12)Σ e_j e_l |y_j − y_l/r|³. At x = 0 the periodization equals
  (analytic) + |x|³·W(x). P = Ψ(0) + 2Ψ(1)cos 2πx is analytic, so by the identity theorem W ≡ 0 left of 0,
  hence W(0) = 0. Then W(0)/2 = Σ_k k^{−2} Σ_{y_l = k y_j} e_j e_l y_j³ ≥ Σ e_j² y_j³/(K+1) by AM-GM and
  Σ 1/((n+1)(n+2)).
- Extends row 184 (β ≤ 2α, continuous f) to all ratios on the piecewise-linear class. Together with the paper
  results (A1) and (A2): a blind compact core can have no finite-order corner and must be Gevrey-2 smooth.
- Conjecture C187 (existence programme, paper): twisted saddle construction Ψ = −sin²(πx)·Ψ₀ (positive on iℝ:
  sinh²) plus a J-even correction interpolated at the integers (subcritical ×2), aiming at a non-compact (N1)
  witness. Open core: uniform saddle bounds and interpolation norms.

## Row 187 (2026-10-13) — duality check (REDISCOVERED) + Lean: step-function cores are never blind (ratio < 11)
- Certificate idea: a witness is excluded by any c (c_1 = 0) with Re[e^{2iθ(t)} D_c(½+it)] ≥ 0. Identity:
  e^{2iθ}ζ(½+it)² = |ζ(½+it)|². The certificate D_c = −ζζ' (c_n = ½ d(n) log n, c_1 = 0) gives
  Re[e^{2iθ}D_c] = |ζ|²·½(Re ψ(¼+it/2) − log π) unconditionally, because Re Λ'/Λ(½+it) = 0.
  This is the gamma bracket (A(0) = −5.37), i.e. the arch+pole Weil energy. Verdict: REDISCOVERED — the corpus
  `archPoleEnergy_eq_zero_of_xiDivisibleBlindTest` (witnesses = PBAP equality cases).
- Interrogation: certificates of the form ζ²(W + λV) need Re V(½+it) > 0 on |t| < t₀ ≈ 6.3 with spectrum ⊂ {log n ≥ log 2}.
  A spectral gap of log 2 suggests sign changes at interval length ~2π/log 2 = 9.1 < 12.6, so there are no such
  low-frequency fixes. This is heuristic support for existence of (N1) via Hahn–Banach. Not pursued further.
- [L] NEW `RHTower/DilationAutocorrelationPeriodizationBounded`: `tsum_dilationAutocorr_abs_eq_of_bounded`
  (Poisson periodization for bounded measurable cores with continuous A_f; no continuity of f).
- [L] NEW `RHTower/StepCoreBlindnessRigidity`: `stepCore_coeff_eq_zero_of_cosDilationKernel_blind`.
  Statement: f = Σ d_j 1_{x ≥ y_j}, Σd = 0, y distinct positive, y_l < 11 y_j; blind on ℕ_{≥2} ⇒ d ≡ 0.
  Ingredients:
  - closed form A_f(r) = −Σ d_j d_l (y_l/r − y_j)_+;
  - |x|-corner decomposition with V(|x|) and the identity theorem, which gives V(x)+V(−x) = 0 and hence V(0) = 0;
  - Schur with AM-GM 2√k|d_j d_l| ≤ d_j² + k d_l² and the certified bound Σ_{k=2}^{10} 1/(k√k) < 0.996.
  Standard axioms, audited, wired.

## Row 188 (2026-10-13) — C188 (no compact witness at any Gevrey class): local analysis exhausted
- Exact local reformulation. ρ(u) = log(2 − e^u) is an analytic involution with ρ'(0) = −1. With φ = (u − ρ)/2,
  ρ becomes v ↦ −v. Then A(1+x) + A(1−x) is analytic at 0 ⟺ the even-in-v part of e^{−u/2}B(u) is analytic.
  Combined with B even in u, this says the non-analytic part of B is anti-invariant (mod analytic) under the parabolic
  ψ(u) = −log(2−e^u).
- Formal Taylor map b ↦ e (B ↦ twisted even part) is unipotent-triangular, so it is bijective on formal series. Divergent B can
  still have convergent twisted-even part: the inverse is an alternating parabolic sum Σ_j (−1)^j G∘ψ^j, whose
  expansion has Euler-number (Gevrey-2) coefficients and Borel singularities at ±iπ (Stokes chirps e^{±iπ/u}).
- PD signs: (−1)^n b_n ≥ 0 is compatible with the alternating Euler-type leading terms, and Gevrey-2 g with compact support
  exists, so there is NO local contradiction. Verdict: C188 is not decidable locally. Compact witnesses ⟺ a
  global PD B whose singular structure at every Farey point is a Borel-summable alternating parabolic sum
  (quantum-modular at s = ½). Kept as an open conjecture; no further local attacks.

## Row 189 — [L] blindness ⟺ Mayer transfer equation at s = ½ (Gauss map)
- `RHTower/BlindCoreMayerTransferHalf`: for continuous compactly supported f on [α,β] ⊂ (0,∞),
  (∀|n|≥2, Ψ_f(n)=0) ⟺ ∃ a b, (1+σ)L Q_{A_f} = a + b cos 2πx on (0,1), where Q_A(t)=A(t/(1−t))/(1−t),
  (LQ)(x)=Σ_{m≥1}Q(1/(m+x))/(m+x) (Mayer/Gauss transfer at s=½), σx=1−x. Profile symmetry Q(1−t)=Q(t) ⟺ inversion law.
- Standard axioms; lake --old audit clean; wired. Collision avoided: renamed to `integral_cos_two_pi_nonzero_int_mul`.
- Meaning: compact (N1') witnesses = solutions of an inhomogeneous Lewis–Zagier-type equation with a Q that is
  t↦1−t symmetric and supported in [1/(1+R), R/(1+R)]. The 3-term Lewis equation ψ(x)=ψ(x+1)+(x+1)^{-2s}ψ(x/(x+1))
  is the homogeneous version; here the right side is a degree-1 trigonometric polynomial, not 0.

## Row 190 — C190 rotated-K₀ cone and the harmonic-measure model
- The positive cone R(½+it) = ∫2cosh(φt)dμ(φ)/(¼+t²)² gives Ψ_R(n) = ∫Re[e^{−iφ/2}K₀(2πne^{−iφ})]dμ.
  Leading order: (2√n)^{−1}Re q(φ)^n with q = exp(−2πe^{−iφ}).
- The model curve closes into a loop around 0 exactly at φ = π/6 (half period). Harmonic measure from 0 is a
  model witness; below π/6 Runge/Mergelyan certificates exist (model rigidity).
- Exactness via the line model: the rotated cone = complexified diagonal translates of the spherical vector.

## Row 191 — [P] THEOREM A: (N1) holds at the logarithmic edge (card n1-log-edge-modular-arc-witness)
- Real points of ℍ: φ_z(x) = (Im z/|x−z|²)^{1/2}, with φ̂_z(n) = 2W_{−n}(z), W_n = √yK₀(2π|n|y)e^{2πinu}.
- Key lemma (maximum principle for div(y∇v) = 0 on the cylinder above the bottom arc A of the fundamental
  domain): no nonzero decaying ¼-combination is ≥ 0 on A. Farkas + compactness then give a probability μ on A
  annihilating every W_n with n ≠ 0. On A, S = (z ↦ −z̄), so the symmetrized μ is S-invariant.
- PD on |z| = 1 by Mehler–Dirichlet: (cosh v + cos θ)^{−1/2} = (2/π)∫_0^θ k_φ (cosφ − cosθ)^{−1/2}dφ, with
  k̂_φ ∝ cosh(tφ)/cosh(πt) > 0.
- Result: an even, S-invariant, strictly PD line-model vector with constant periodization. R > 0, R = O(e^{(π/6)|t|}),
  Ψ_R(n) = 0 ∀n ≥ 1, and the only defect is double poles of R at s = 0, 1 (tail c/|x|, c = ∫√y dμ > 0).
- Consequences:
  - no absolutely convergent Farkas certificate exists;
  - decay-class (N1) = removing the ζ-pole, a codimension-2 slice ℓ₁ = ℓ₂ = 0;
  - on A the blind space is 2-dimensional (Green fluxes ν₀, ν₁) and the slice is generically {0};
  - witnesses must leave |z| = 1.
- C191 (pole removal) is open. Lean programme L1–L5 opened.

## Row 192 — [L] L1 of Theorem A: no nonnegative decaying Whittaker combination on the modular arc
- `HTGeometry/ModularArcMinimumPrinciple`:
  - `nonneg_of_isLocalMin_of_hasDerivAt`: the second-derivative test;
  - `nonneg_of_nonneg_on_modularArc`: minimum principle for y(v_uu+v_yy)+v_y = 0, periodic and decaying,
    v ≥ 0 on {u²+y²=1, |u| ≤ ½} ⇒ v ≥ 0 at heights y ≥ 1. Proof: barrier εe^y, compact region above three arcs.
- `RHTower/ModularArcWhittakerPositivity`, `whittakerArc_coeff_eq_zero`: if Σ_{n<N} K₀(2π(n+1)y)(a_n cos + b_n sin)
  is ≥ 0 on the bottom arc, then all a_n = b_n = 0. Uses the minimum principle at y = 2, zero horocycle mean
  and orthogonality.
- Reuses corpus `RHTower.BesselKZero.kMoment` (K₀, derivatives, ODE, decay). My duplicate `HTGeometry/CoshMomentBesselK`
  was deleted before wiring.
- Lesson: search `rg "cosh t \^ j"` / "Macdonald" in module headers before building special functions.
- Standard axioms; both modules pass the lake --old audit and are wired. Next is L2 (Farkas + compactness → probability on A).

## Row 193 — [L] L2: a probability measure on the modular arc annihilating every Whittaker mode
- `RHTower/ModularArcAnnihilatingMeasure`, `exists_probabilityMeasure_arc_annihilating`: there is a μ ∈
  ProbabilityMeasure([−½,½]) with ∫K₀(2π(n+1)√(1−u²))cos(2π(n+1)u)dμ = ∫…sin… dμ = 0 for every n.
- Finite stage: Hahn–Banach separation in (Fin N → ℝ)² + L1. Limit: Prokhorov (compact ProbabilityMeasure)
  with nested closed sets T_k.
- Standard axioms; audited; wired. Renamed arcHeight → modularArcHeight; it was ambiguous with the
  SelbergMaassTraceStokes namespace.
- Open: L3 (Mehler–Dirichlet PD) and L4 (Basset FT) — classical dictionary; parked behind C191.

## Row 194 — [L] THEOREM A complete in Lean: positive, self-dual, Whittaker-blind measure on the modular arc
- `HTGeometry/SymmetricCoshKernelPositiveDefinite`, `integral_cos_mul_symCoshKernel_pos`: for |c| < 1,
  ∫cos(τv)[(cosh v + c)^{−½} + (cosh v − c)^{−½}]dv > 0.
  Proof: even binomial series with C(−½, 2j) > 0, plus the corpus FT of (cosh)^{−s} at complex frequency.
  This replaces Mehler–Dirichlet.
- `RHTower/ModularArcLogEdgeWitness`, `exists_arcWitness`: there is a finite measure ν ≠ 0 on the bottom arc with
  - ν symmetric under u ↦ −u (= S on the arc);
  - ∫√yK₀(2π(n+1)y)cos(2π(n+1)u)dν = ∫…sin…dν = 0 for every n;
  - ∫cos(τv)B_ν(v)dv > 0 for every τ, where B_ν = ∫(y/2)^{½}(cosh v − u)^{−½}dν is the log-scale Poisson profile.
- Construction: L2 measure, reweighted by y^{−½}, symmetrized; Fubini with L3.
- Standard axioms; all audits clean; wired. Classical dictionary not in Lean (L4, Basset):
  φ̂_z(ξ) = 2√yK₀(2π|ξ|y)e^{−2πiξu}.

## Row 195 — [L] Theorem A in line-model (N1) form, complete
- `RHTower/PoissonVectorFourierWhittaker`, `integral_mul_rpow_sin_eq_kMoment`: ∫x(x²+y²)^{−3/2}sin(kx)dx = 2kK₀(ky).
  This is the derivative form of Basset's integral. Proof: Gaussian subordination (Γ(3/2)), Gaussian sine transform
  (integration by parts + corpus `GaussZeroSum.integral_cos_affine_mul_gaussDensity`), Fubini, s = e^t
  substitution + shift, then corpus `integral_exp_neg_mul_cosh`.
- `RHTower/ModularArcLineModelBlind`, `exists_arcLineWitness`: there is a finite ν ≠ 0 on the bottom arc such that
  h_ν(x) = ∫(y/((x−u)²+y²))^{½}dν satisfies:
  - h even, h(1/x) = |x|h(x);
  - h' = arcLineDeriv is integrable and is the derivative;
  - ∫h'(x)sin(2π(n+1)x)dx = ∫h'(x)cos(2π(n+1)x)dx = 0 for every n (no nonconstant periodization mode);
  - e^{v/2}h(e^v) is strictly PD.
- Standard axioms; audited; wired. This is the corpus's first positive, self-dual, integer-blind line-model vector
  (the log-edge (N1) witness). The decay class (C191) remains open.

## Row 196 — [P] Theorem B: decay-class (N1) holds at every finite level; the open core is analytic compactness
- Spectral form of (N1): a positive B̂ on ℝ (B̂ = |G|²R) with chirp moments ∫B̂(t)κ_n(t)dt = 0 (n ≥ 2), where
  κ_n(t) = cos(2θ(t) − t log n). Decay class = B̂ analytic in |Im t| < ½+δ with B̂(±i/2) = 0, i.e. fast decay plus Ψ(0) = 0.
- Corollary of Theorem A [P]: no nonzero real chirp polynomial Σ_{n=2}^N c_n κ_n(t) is ≥ 0 on ℝ. Pair it with the
  arc witness spectrum B̂_ν > 0, whose chirp moments vanish for every n ≥ 1, and use linear independence.
  This kills every absolutely convergent Farkas certificate.
- Density [P]: f_K(t) = 1 − (1+K(t²+¼))e^{−K(t²+¼)} is entire, > 0 on ℝ, has double zeros at ±i/2, and
  sup_ℝ|1 − f_K| ≤ (1+K/4)e^{−K/4}. So decay-class positive spectra (f_K·B̂, B̂ any positive, even log-edge) are
  uniformly dense in positive spectra on ℝ.
- THEOREM B [P]: for every N there is a nonzero decay-class, strictly PD, self-dual multiplier R (analytic in the strip,
  R > 0 on ℝ) whose chirp moments vanish for 2 ≤ n ≤ N.
  Proof: the moment image K_N of the decay cone has dual cone {0} (density + Corollary), so cl K_N = ℝ^{N−1}, hence
  K_N = ℝ^{N−1}; this gives v, −v ∈ K_N and the sum of their preimages.
- So the ζ-pole is not an obstruction at any finite level. Full (N1) = the N → ∞ limit. The danger is degeneration to
  the log edge, since the analytic condition B̂(±i/2) = 0 is not stable under real-line weak limits.
- Equivalent obstruction: the chirp Gram matrix ∫wκ_nκ_j is badly conditioned (log n has infinite density).
- C192 (sharpened): do the decay witnesses of Theorem B stay away from the log edge uniformly in N?
  Equivalently, is the moment cone of the decay class open at 0 in a sequence topology finer than the one
  where the f_K-defects ε_n(K) ~ (1+K/4)e^{−K/4}n^{−½} live?

## Row 197 — [P] The arc operator 𝔐 and the uniform-degree question (C193)
- On ¼-eigenfunctions, Δ_H = sin²α (D² + ∂_α²) with D = r∂_r the dilation generator (it commutes with Δ_H).
  So on the arc A, (¼ − D²)F = 𝔐F with 𝔐 = ∂_α² + ¼ + 1/(4 sin² α), and (¼ − D²)² = 𝔐².
- Fixed decay multiplier (¼+t²)² with arc measures ν ≥ 0. A witness for all n ≥ 2 exists iff no even Whittaker trace
  F = P_e|_A (modes ≥ 2) has 𝔐²F > 0 on A (Farkas + Prokhorov, as in L2). This is C193; if true, (N1)-decay holds
  and the corpus gives RH ⟺ PBAP.
- With multipliers (¼+t²)²|q|² (deg q ≤ d): for each N there is d_N with no certificate, by compactness of the even
  P-sphere and the limiting PD argument (L1 + (ST)³). Whether d_N stays bounded is the open core.
- Heuristic: d = 0 likely admits certificates. The obstruction would need a clamped positive ψ with 𝔐²ψ ∈ Ann(𝒱),
  and that boundary-value problem is overdetermined (6 conditions vs 4 + dim Ann).

## Row 198 — [P] Arc rigidity for the decay class; C194 (possible (N1) no-go)
- Even annihilator of the Whittaker traces on A: Ann_even(A) = span{ν₀, ν₁}, 2-dim, from cusp-side threshold fluxes.
  Funnel-side solutions would need Φ|_A ∈ cl(𝒱) with exponentially convergent Whittaker expansions below A, so
  generically there are none.
- Hence no decay witness is supported on A: the 2 decay conditions cut the 2-dim Ann to {0}.
- Convex-order PD mechanism [P]:
  - If 𝒫_t(α) = P_{−½+it}(cos α) + P_{−½+it}(−cos α) is convex in τ = log sin α (still to check), then every
    √y-weighted second-order convex-order measure on A is PD with zero tail and zero Ψ(0).
  - That needs d_A ≥ 3 to meet Ann, so it fails on A.
- Iteration from the log edge collapses: Σ_j f_K g_K^j B̂_ν = B̂_ν, since g_K(±i/2) = 1 brings the pole back.
  The f_K-defects are uniformly small in n (≤ (1+K/4)e^{−K/4}n^{−½}), but cancelling them is the same problem again.
- Conjecture C194 (pole rigidity): every nonzero S-invariant, log-PD, integer-blind (|n| ≥ 2) vector in the room has a
  positive 1/|x| tail, i.e. R has a pole at s = 1. That would mean (N1)-decay FAILS and the HF route needs a different object.
  - Certificate form: a Dirichlet series Q regular at 1 with q₁ ≤ 0, Re Q(½+it) ≥ 0 nontrivially, linear growth or
    strip singularities (the mean-value lemma forbids sublinear entire ones).
  - Evidence for: arc rigidity; the collapse above. Evidence against: Theorem B at every finite level; no certificate known.

## Row 199 — [P] Only one pole condition is genuinely analytic
- On the integer-blind space V (signed, S-invariant, in the room), the Voronoi positivity identity
  f(1) − [E'(1) + 2c₀E(1)] = (1/2π)∫Λ₂E (Λ₂ = (Γ_ℝζ)²) represents π' := E'(1) + 2c₀E(1) by real-line integrals.
  So π' is bounded on V in every weighted sup norm ‖B̂‖_M with ∫|ζ|²M < ∞.
- Hence decay class ⟺ E(1) = 0 (tail) and Ψ(1) = (1/2π)∫Λ₂E (a real-line identity). The only genuinely analytic
  condition is the tail E(1) = 0.
- Perturbation criterion: a decay witness h = h₁ + w (h₁ = Theorem A, w ∈ V) needs B̂_w ≥ −B̂_{h₁} on ℝ (one-sided),
  ρ(w) = −ρ(h₁) and π'(w) = −π'(h₁) = (1/2π)∫Λ₂E_{h₁} > 0. With a two-sided small w this is impossible (π' is bounded),
  so the correction must be large but one-sided.
- Unconstrained by blindness, the residue functional is unbounded w.r.t. real-line norms: r e^{−K(t²+¼)}/(½+it) is
  tiny on ℝ with residue r. Whether V keeps that unboundedness under the one-sided constraint is the sharpened open core.
- Theorem B generators B_{u,K} = k_u − ǧ_K⋆k_u decay like e^{−(3/2−ε)|v|} (B̂ is analytic in |Im t| < 3/2, with zeros at ±i/2).

## Row 200 — [P] Corrections, the corpus room law, and Theorem B′ (arc-generator proof)
- **Correction (Theorem A is ζ-free blind only).** For the log-edge `R` the contour shift crosses the double pole at
  `s = 1`. So the A-kernel of `Ξ²R` is `a(n) = −Res_{s=1}[ζ²γh̃ n^{−s}] = (ρ₂ log n − ρ₁)/n` with `ρ₂ ∝ c > 0`, not 0.
  Theorem A is blindness of the ζ-free kernel `Ψ_R = ĥ` at every `n ≥ 1`; the A-form and ζ-free form agree only in the
  decay class (`logNode_blind_iff_certKernel_vanishes`).
- **Pole dichotomy (full blindness).** In the decay class `∫Ξ²R ∝ Ψ_R(1)` (`integral_xi_sq_eq_certKernel_one`), so a
  nonnegative decay-class `R` with `Ψ_R(n) = 0` for all `n ≥ 1` is 0. Theorem A gives such `R > 0` at the log edge, so
  the pole at `s = 1` is necessary and sufficient for full ζ-free blindness.
- **Corpus room law** (`ExactNullCertificateLogRoomGrowth`): blind `Ξ²R` with `G²R` integrable against
  `e^{(π/2)(|t| − |t|/log|t|)}` has `∫Ξ²R = 0`. So (N1) witnesses need `B̂ = |G|²R` with
  `∫B̂ e^{(π/2)|t|(1−1/log|t|)} = ∞`, i.e. heavy spectral tails, like Theorem A's `e^{−(π/3)|t|}`.
- **Line-model decay class:** `h ∈ L¹` with `|e^{v/2}h(e^v)| ≲ e^{−(½+δ)|v|}`, `∫h = 0` (⟺ `B̂(±i/2) = 0`), and
  `ĥ(n) = 0` for `|n| ≥ 2`. `ĥ(±1)` is free and forced `> 0` by the `E*` identity `ĥ(1) = (1/2π)∫Z²B̂`.
  Equivalently `Σ_k h(x+k) = λ cos 2πx` with `λ > 0`.
- **A-form certificates (C194).** `Q = Σ q_n n^{−s}` with `q₁ ≤ 0`, regular at 1, `Ξ² Re Q ≥ 0` on the line. Under RH a
  Herglotz argument excludes certificates whose only singularities are simple poles with positive residue. Double poles at
  the zeros, with leading coefficient `κ_γ > 0`, contribute 0 to the mean. These are the only possible certificates.
  Explicit trials `(ζ'/ζ)' − (ζ'/ζ)² + 2γ_E ζ'/ζ` (Re Q(½) = −0.37) and `(ζ'/ζ)' + ζ'W` fail.
- **Theorem B′ (paper, complete).** For each `N` there is a decay-class line-model witness blind for `2 ≤ n ≤ N+1`.
  - Generators: `h_{u,K} = ψ_u − ∫ǧ_K(w) e^{−w/2} ψ_u(x e^{−w}) dw`, where `ψ_u` is the sum of the arc Poisson vectors
    at `±u + i√(1−u²)` and `ǧ_K = 2e^{−K/4}g_K − e^{−K/2}g_{2K}` (`g_t` the variance-`2t` Gaussian).
  - Spectrum: `(1 − e^{−K(τ²+¼)})² Q̂_u(τ) > 0`.
  - Decay: `|P| ≲ e^{−3|v|/2}`.
  - Moments: `W_n(u) + O(‖ǧ_K‖₁)` uniformly in `u`.
  - Dual: L1 gives `cl cone{W(u)} = ℝ^N`. Finitely many points, then the cross-polytope perturbation at one large `K`
    gives an exact finite combination.
  - Needs neither Theorem A's measure nor Prokhorov.
- **Mechanism of the N→∞ gap.** The filter's moments at `n` are `√n (ǧ_K ⋆ β̃_u)(log n)`: log-normal in `n`, decaying
  only like `e^{−(log n)²/4K}`. Arc Whittaker moments decay like `e^{−π√3 n}`. Cancelling the filter tail needs generators
  with slowly decaying high-`n` moments, i.e. mass near the real axis.
- Lean programme B′: A `GaussianPoleFilter`, B `FilteredArcGenerator`, C `FilteredArcMoments`, D `FiniteLevelDecayWitness`.

## Row 201 — [L] Theorem B′ formalized: decay-class line witnesses blind at every finite level
- `RHTower/FiniteLevelDecayWitness.exists_decayClass_lineWitness`, plus four supporting modules (`GaussianPoleFilter`,
  `FilteredArcGenerator`, `FilteredArcGeneratorDecay`, `FilteredArcGeneratorMoments`).
- Standard axioms; all five `lake --old` clean; wired into `RHTower.lean`.
- Remaining lint errors are other agents' unwired modules.
- Card `n1-log-edge-modular-arc-witness` corrected: Theorem A is ζ-free blind only, with A-kernel residue
  `(ρ₂ log n − ρ₁)/√n`. Pole dichotomy recorded.
- Reusable Lean assets:
  - Gaussian pole filter with exact transforms;
  - ray-dilated Poisson superpositions with Fubini/derivative control;
  - the `λ → ½` zero-mean argument;
  - the uniform K₀ bound `√r K₀(r) ≤ √(π/2)`;
  - the Whittaker cone density from L1;
  - signed-basis robustness.

## Row 202 — [L] C208: finite vs infinite dichotomy for decay-class line witnesses (both halves in Lean)
- **Finite levels are finite-point** (`RHTower/FinitePoissonDecayWitness.exists_finitePoisson_decayWitness`).
  - Every level N has a decay-class witness that is a finite superposition of s=½ Poisson vectors at finitely many
    points of ℍ.
  - The witness is even, S-invariant, ∫h=0, with rate-3/2 profile decay, blind for 2≤m≤N+1, strictly PD.
  - Generators use two-atom pole filters c=(δ_b+δ_{−b})/(2cosh(b/2)), with weights m=δ−2c+c⋆c on dilations
    0,±b,±2b.
  - Multiplier: (1−cos(bτ)/cosh(b/2))² > 0. Tilt: (1−cosh(λb)/cosh(b/2))², a double zero at λ=±½.
  - Moment error 4√(π/2)√c(2/C+1/C²) → 0 as b→∞.
- **No exact finite-point witness** (`RHTower/FinitePoissonBlindRigidity.eq_zero_of_finitePoisson_blind`).
  - Suppose points are pairwise not related by integer translation, and Σa_iφ_{z_i} has vanishing sin and cos moments
    of h' at all frequencies 2π(n+1), n≥n₀. Then all a_i=0.
  - Proof: the lowest height dominates, since K₀(cq)/K₀(cq₁) ≤ e^{−c(q−q₁)} (corpus `kMoment_le_exp_mul`).
    Then a discrete exponential-sum lemma: Σb_i e^{2πinθ_i} → 0 with θ distinct mod 1 forces b=0, by removing
    one frequency via F(n+1)−e(θ_L)F(n).
- Standard axioms; the three new modules are `lake --old` clean and wired.
- **Insight.** An exact (N1) line witness must be an infinite (continuous) Poisson superposition, like Theorem A's
  arc measure.
- **Compactness reduction (paper, row 202).** For any compact family of atomic or compactly supported pole filters,
  Prokhorov makes the N→∞ limit automatic. So C191 ⟸ GL1 for some compact filter family.
  - GL1: the dual certificate condition "∫U(e^w z) dm_c(w) ≥ 0 on the arc ∀c ⟹ U=0" for Whittaker sums U.
  - Runge-type flexibility of Whittaker sums on non-wrapping curves (lower dilates e^{−w}A) suggests that
    certificates exist for 1D (lattice) filter families. So only 2D (continuous-radius) families can work.
  - Open: GL1 for the full admissible family 𝒜_a (Krein-PD radial profiles modulo cosh(w/2), w sinh(w/2)).

## Row 203 — [P] (N1) dual: gamma-twisted Dirichlet positivity (C214); ζζ′-certificate family dead (C213)
- **Exact dual of (N1).** Witness ⟺ no admissible `Q = Σ q_n n^{-s}` (abs. conv. Re s>1, ≤ double pole at 1,
  polynomial growth on Re s ≥ ½) with `q₁ ≤ 0` and `Re[Γ_ℝ(s)²Q(s)] ≥ 0` on Re s = ½, ≢ 0. Only θ (Gamma phase)
  enters; ζ enters only through choices of Q.
- **ℍ-form.** `Re Γ_ℝ²Q ≥ 0` ⟺ `v ↦ U(ie^v) + U(ie^{-v})` is positive definite, where `U = Σ q_n W_n` plus constant
  terms (the double pole). So C214 says: the first Whittaker coefficient is ≥ 0 on the cone of T-periodic
  ¼-eigenfunctions whose S-symmetrised axis profile is PD, and it vanishes only on the trivial element.
- **C214 (conjecture, Hamburger-type positivity rigidity):** every admissible `Q` with `Re[Γ_ℝ²Q] ≥ 0` on the line
  has `q₁ ≥ 0`, and `q₁ = 0` forces `Re[Γ_ℝ²Q] ≡ 0`. C214 plus closure ⟹ C191.
- Test cases:
  - Dirichlet polynomials and AP series fail C214's hypothesis, by phase rotation (θ′ → ∞).
  - `L(s,χ)²` fails: the conductor factor `N^s` breaks integer frequencies.
  - `ζ²(ζ′/ζ)′` has pole order 4; its low-height Re(ζ′/ζ)′ < 0 on t ≈ (1.5, 7.5).
  - Pole-cancelled variants (`+ζ′`, `−ζ²w`) fail at large t on large values of ζ.
- **C213 [P], unconditional.** Let `κ > 0` and `M₁ = Σ_{n≥2} r_n n^{-s}` be nice (L¹_loc tempered boundary values,
  analytic on Re s > ½). Then `Re M₁(½+it) ≤ κθ′(t)` fails for some t.
  - Proof: pair with `K ≥ 0` where `K̂ = (1−|ξ|/log 2)₊`. Then `∫Re M₁·K = 0` (spectral gap), while
    `∫θ′K = ½(J − γ − log π) ≈ −0.60`, with `J = ψ(¼)+γ + ∫_0^{2a}e^{-u/4}(u/2a)/(1−e^{-u}) + Σ_k 4^{-k-¼}/(k+¼) ≤ 0.52`.
  - So the C209 super-decay certificate `−ζ²M₁ − κζζ′` does not exist.
  - Principle: certificates must carry Laguerre-type double poles at zeros of ζ (FP(1/(t−γ)²) boundary
    singularities). Simple-pole and AP certificates are blind to the spectral-gap test only when residues are negative.
- User directive (2026-10-13): no pivots. Stay on C191/C214 until solved.

## Row 204 — [P] (N1) attack: one-sided node form, Herglotz split, tail/low decomposition (C219)
- **One-sided node form (corrects row 724's "±log n").** `f(n) = n^{-½} G(−log n)` with
  `G := FT⁻¹[Γ_ℝ(½+it)² E(½+it)]` real, not even. (N1) ⟺ `G(−log n) = 0` (n ≥ 2), `G(0) = f(1) > 0`,
  `Ĝ/Γ_ℝ² = E > 0`, decay class. The nodes `{−log n}` are one-sided.
- **Gamma kernel geometry.** `G = k ⋆ e` with `k(x) = 2e^{-x/2}K₀(2πe^{-x})`.
  - k is super-exponentially small on the node side (`k(−log 2) ≈ 3.5·10⁻⁶`) and has an `e^{-x/2}x` tail on the other.
  - The tail nodes (n ≥ N₀) only see the far tail of `e = FT⁻¹E`. The low nodes sit in k's transition zone.
  - This is the scale clash of row 724, now localized to n ≲ e^{O(1)}.
- **C219 (decomposition conjecture).** (a) For large N₀ there are S-symmetric, decay-class, strictly PD vectors exactly
  blind at all n ≥ N₀. (b) The low-moment cone of such vectors contains 0 with `f(1) > 0`. (a)+(b) ⟹ C191.
  - Candidate for (a): `g = B_{N₀}·f` with `B_{N₀}` the strip Blaschke product of `{−log n : n ≥ N₀}`.
    Near the origin `log B ≈ −c N₀^{1−2p} cosh 2px`, so the scale separation holds.
  - Risk: B's boundary phase rotation `e^{2p|x|}` against f's decay. This needs `2p < 5/2`, since Γ̃² is analytic in `|Im t| < 5/2`.
  - (b) is the obstruction: B′/C208 finite-level witnesses spread to `|v| ~ 8π√3 N₀ ≫ log N₀` and collide with B's nodes.
    Needed: finite-level witnesses concentrated in `|v| ≲ c log N` (C220).
- **Herglotz split of certificates (under RH).** `M = Q/ζ² = Λ_A + H`, with Laguerre part `Λ_A = (A·ζ′/ζ)′`
  (double poles `−A(ρ)/(s−ρ)²`) and a regular H.
  - The certificate condition is `Re H ≥ −Σ Re A(ρ)/(t−γ)²`, not `Re H ≥ 0`, so no Phragmén–Lindelöf contradiction is available.
  - Regularity at s = 1 forces a ζ′-type double-pole term N whose large values on the line occur in large zero gaps.
    So a certificate needs joint value/gap control.
  - Heuristic: C214 is true and (N1) holds. The certificate ζζ″ − 2ζ′² + 2γζζ′ fails both at t = 0 (−0.37) and at
    every large-t maximum of |Z| (≈ −2γθ′Z²).
- **Blindness is cheap.** The horocycle smear `∫_0^1 cos(2πt)(T_t)_*μ dt` is blind at every |n| ≠ 1 and kills the zero mode.
  Equivalently `ĥ = s(ξ)Ĝ` with `s(ξ) = ξ sin πξ/(1−ξ²)`. Everything hard is S-symmetry plus PD.

## Row 205 — [P] C219a reduced to a twisted minimum principle (M4) on the arc; winding heuristic
- **PD decay-class generators on A.** Put `G_α := (−∂_v² + ¼)² p_α = 𝔐_α² p_α`, where p_α is the arc-pair log profile
  (S-pair at e^{iα}) and `𝔐 = ∂_α² + ¼ + 1/(4 sin²α)`; the identity is the eigen-equation `(r∂_r)² + ∂_α² + 1/(4sin²α) = 0`.
  - Spectrum `(τ² + ¼)² M_α(τ) > 0`.
  - The double zero at τ = ±i/2 kills both the pole and the value, so G_α is decay class (profile `O(e^{−3|v|/2})`).
  - G_α is S-symmetric.
  - Every κ ≥ 0 on [π/3, 2π/3] gives a strictly PD decay-class S-symmetric vector `h_κ = ∫G_α dκ`.
- **Moments.** `ĥ_κ(n) = 2∫ (𝔐²W_n^c)(e^{iα}) dκ(α)`.
- **Reduction (Theorem-A style, Hahn–Banach + Prokhorov on compact A).** C219a ⟸ (M4).
  - (M4): for some N₀, no nonzero `U = Σ_{N₀≤n≤N} c_n W_n^c` has `𝔐_α²(U|_A) ≥ 0` on A.
  - The resulting h_κ is blind at every n ≥ N₀, decay class, S-symmetric, and strictly PD.
- **Even kernel of 𝔐².** It is span{√sin α, √sin α · log sin α}, i.e. exactly the constant-term traces √y and √y log y.
  The odd kernel element of 𝔐 is √sin α · log tan(α/2).
- **Winding heuristic for (M4).**
  - High modes are approximately holomorphic: `W_n ≈ c n^{−½} Re e^{2πinz}` and `r∂_r ≈ z∂_z`.
  - So `𝔐²U ≈ Re[z⁴ H]` with H T-periodic holomorphic and `O(q^{N₀})` at the cusp.
  - On A, z⁴ = e^{4iα} rotates by 4π/3. Re[z⁴H] ≥ 0 confines arg H to a band of width π whose centre moves by 4π/3
    around the loop q(A), so the winding of H lies in [π/3, 7π/3]/2π = {1}.
  - H has winding ≥ N₀ ⇒ contradiction for N₀ ≥ 2 in the holomorphic model.
  - The true trace must allow some U at low modes (arc rigidity), so the low-mode deviation from holomorphy carries the
    obstruction. For large N₀ the approximation error is O(1/N₀), and (M4) is expected.
- **Insight.** (N1)-type existence on A is dual to a *twisted argument principle*: a positivity twist `e^{ikα}` from the
  pole-killing multiplier `(τ²+¼)^{k/2}` against the cusp vanishing order of Whittaker sums. The (N1) threshold
  (modes ≥ 2, n = 1 free) sits exactly at winding 1 of the k = 4 twist.
- Next: prove (M4) for large N₀ (control the non-holomorphic remainder of high-mode Whittaker sums on A), then Lean.

## Row 206 — [P] Exact Abel form of (M4); the holomorphic model is a solvable Riemann–Hilbert problem
- **Exact Abel identity.** `√y K₀(2πny) e^{2πinu} = √y ∫_y^∞ q^n(u+iY) dY/√(Y²−y²)` and `r∂_r = z∂_z` on holomorphic
  functions give, for `U = Re Σ c_n W_n` and `f = Σ c_n q^n`:
  - `𝔐²U(z) = √y ∫_y^∞ Re[(L²f)(u+iY)] dY/√(Y²−y²)`, with `L = ∂_z z² ∂_z`;
  - `L² q^n = (x⁴z⁴ + 8x³z³ + 14x²z² + 4xz) q^n`, with `x = 2πin`.
  So (M4) is positivity on A of Abel averages of Re Φ along vertical rays, where `Φ = z⁴H₄ + 8z³H₃ + 14z²H₂ + 4zH₁`
  and `H_k = Σ c_n(2πin)^k q^n` is T-periodic holomorphic.
- **Vector-level lift.** `φ_z = (2√y/π) ∫_y^∞ P_{u+iY} dY/√(Y²−y²)`, where P is the s = 1 (harmonic) Poisson kernel.
  The s = ½ Poisson vectors are Abel averages of harmonic Poisson kernels. The lift commutes with translations and
  dilations but not with S.
- **Holomorphic model is exactly solvable.** Take positivity `Re[e^{4iα}ℋ] ≥ 0` on q(A), with ℋ = O(q^{N₀}).
  - Winding: `−4π/3 + 2π(N₀ + Z_int) ∈ [−π, π]`, so N₀ + Z_int = 1. Every N₀ ≥ 2 is excluded.
  - Dual (exact annihilators): we need `e^{4iα}ρ dα = φ dq` with ρ > 0 and pole order ≤ N₀ at 0. This is a
    Riemann–Hilbert problem `arg ψ = 4α` on the loop with a corner of interior angle 2π/3.
  - Index: a simple zero of ψ at the corner absorbs the 4π/3 jump. The particular solution ψ₀ has a simple pole at
    the cusp, so φ has pole order 2.
  - The general solution is `ψ₀·R` with R a positive real trigonometric polynomial in the uniformizer, deg R ≤ N₀ − 2.
    Annihilators exist for every N₀ ≥ 2 (an open cone for N₀ ≥ 3), and ρ vanishes linearly at the corner.
- **Consequence.** Arc rigidity (exact, N₀ = 2 impossible) shows that the non-holomorphic low-mode corrections
  (K₀ vs exponential, lower Touchard terms) carry the (N1) obstruction on A. The holomorphic threshold is exactly the
  (N1) threshold.
- **C221 (conjecture).** For N₀ ≥ N* the exact moment functionals `𝔐²W_n|_A` (n ≥ N₀) admit a positive annihilator κ
  that perturbs the RH model annihilator. This gives C219a: exact cofinite blindness, decay class, strict PD,
  S-symmetry.
  - Difficulty: the high modes concentrate at the corner, exactly where the model annihilator vanishes.

## Row 207 — [P] (N1) is exactly critical: the holomorphic model has a unique annihilator at N₀ = 2
- **Twist is topological.** For any curve from ρ to ρ+1 in ℍ, arg z runs from 2π/3 to π/3. So the dilation twist
  z^k rotates by −kπ/3 for every closing curve, independent of the curve.
- **Model threshold.** Positivity `Re[z^k ℋ] ≥ 0` forces `N₀ + Z = round(k/6)`. Decay class forces k ≥ 4 (the pole and
  the value at ±i/2). For k = 4 and k = 6 the model allows positivity only at cusp order 1, so annihilators exist for
  every N₀ ≥ 2.
  - With k = 6 the twist closes (rotation −2π), and the annihilator density no longer has a forced corner zero beyond
    the intrinsic r^{½} harmonic-measure factor.
- **Criticality.** At N₀ = 2 the model annihilator is unique up to scale (R = positive constant; deg R ≤ N₀ − 2 = 0).
  For N₀ ≥ 3 the annihilators form an open cone.
  - So (N1) (blind from n = 2) sits exactly at the rigid threshold of the leading-order problem. Existence is decided
    by the sign of the subleading non-holomorphic correction (K₀ vs exponential, lower Touchard terms, the y-dependence
    of the Abel kernel) paired with the unique model annihilator.
  - On the arc A this sign is wrong or degenerate (arc rigidity, exact). Cofinite blindness (C219a/C221, N₀ ≥ 3) has
    open-cone slack.
- **Reading.** This explains the corpus-wide "zero slack / critical scaling / same scale" findings for (N1)
  (rows 593, 718–726): the integer nodes from n = 2 sit exactly at the winding threshold of the dilation-twisted Gamma
  phase.
- **C222 (criterion conjecture).** For an S-symmetric closing configuration C, decay-class (N1) witnesses supported on C
  (dilation-twisted generators) exist iff `Δ(C) := ⟨ρ₀^C, first-order correction⟩ > 0`. Here ρ₀^C is the unique
  N₀ = 2 model annihilator; Δ(A) ≤ 0. Next: compute Δ for the arc to see the mechanism, then deform.

## Row 208 — [P] RETRACTION of "no decay witness on A" (rows 198, 205–207); (N1)-on-arc reduced to one sign (C224)
- **Retraction.** Arc rigidity (row 198) holds only for *measures* on A. The corner of D at ρ ~ ρ+1 has interior angle
  2π/3. That angle is forced by S-symmetry for every S-symmetric closing curve (the order-3 elliptic point).
  - It gives corner-singular functionals: `c_{3/2}(F)` is the coefficient of `r^{3/2} sin(3θ/2)` in the T-periodic
    Dirichlet solution with data F (and likewise c_{9/2}, …).
  - c_{3/2} is a distribution of order about 3 on A. It annihilates the trace of every T-periodic eigenfunction that
    is analytic at the corner (all W_n with n ≠ 0, and √y), but `c_{3/2}(√y log y) = −s₀ ≠ 0`.
  - So, among distributions, `Ann_{n≥2,even}(A) ⊇ span{ν₀, ν₁, c_{3/2}}` (3-dim). The two decay conditions leave the
    unique `σ* = s₀ν₁ + β₁c_{3/2}`: blind at all n ≥ 2, decay class, S-symmetric, with `a₁ = s₀`.
  - The rows 205–207 claim "exact fails at N₀ = 2 on A" is withdrawn; it misapplied measure rigidity.
- **PD via generators.** `σ* = 𝔐^{*2}κ*` with `κ* := (𝔐^{*2})^{−1}σ* ∈ L¹(A)`, which is unique and even.
  - It exists because σ* ⊥ ker 𝔐² = span{√sin α, √sin α log sin α}, which is exactly the decay class.
  - Near the corners `κ* ~ C r^{3/2}`, matching the RH model annihilator `ρ₀ ~ r·r^{½}` of row 206.
  - If κ* ≥ 0, then `h := ∫ G_α dκ*(α)` with `G_α = 𝔐²(arc pair)` has spectrum `(τ²+¼)² ∫ M_α dκ* > 0`. So h is a
    decay-class, S-symmetric, strictly PD vector blind at every n ≥ 2, i.e. **(N1) holds**.
- **Equivalence.** By Hahn–Banach + Prokhorov on compact A: κ* ≥ 0 ⟺ (M4)₂′, i.e. for no N does
  `U = Σ_{n=2}^N c_n W_n^c` satisfy `𝔐²U > 0` on A.
  - Proof sketch: a U with 𝔐²U = w > 0 has trace `𝒦w + a√y + b√y log y`. That trace is C⁴-approximable by finite
    sums iff the single linear functional `Λ(w) = ⟨κ*, w⟩` (from c_{3/2} and the ±1 mode) vanishes. So such a U
    exists iff κ* changes sign.
- **C224 (main conjecture).** κ* has constant sign on A; equivalently (M4)₂′; equivalently (N1).
  - Evidence: the leading-twist holomorphic model (row 206) is exactly solvable and gives the positive unique
    annihilator ρ₀, with the same r^{3/2} corner law.
  - Exact corrections: K₀ vs exponential is about 1.1% at n = 2, y ≈ 0.87. The 1/(4sin²α) term in 𝔐 is about 0.3%
    of ∂²; the lower Touchard terms are exact holomorphic parts.
  - On the ODE side, `𝔐² = (−∂² − V)²` with `V = ¼ + 1/(4sin²α)` and `−∂² − V > 0` (Dirichlet, length π/3).
    κ* is a clamped-type (r^{3/2}) Green potential of σ*.
- **Next.**
  - (i) Rigorous construction of c_{3/2} and the identity `⟨c_{3/2}, U|_A⟩ = 0` for corner-analytic periodic U.
  - (ii) Prove κ* ≥ 0, by perturbation from ρ₀ with explicit corner control or by a positivity principle for the
    clamped Green function.
  - (iii) Lean: generator lemma, the HB/Prokhorov equivalence (Theorem A machinery), and the implication
    (M4)₂′ ⟹ (N1)-witness.

## Row 209 — [L] (N1) reduced in Lean to the twisted arc minimum principle
- **New modules** (standard axioms, `lake --old` clean, wired):
  - `HTGeometry/TwistedCoshKernel`: `T_k = (cosh v − c)^{−1/2−k}` calculus.
    - Derivatives `T_k′ = −(k+½) sinh T_{k+1}` and the `(¼−∂²)` recursion.
    - `twCoshKernel = (¼−∂²)²T_0` (explicit 4-term form).
    - `integral_cos_mul_twSymCoshKernel` (Fourier multiplier `(¼+τ²)²`), `integral_cos_mul_twSymCoshKernel_pos`
      (strict PD via the corpus `integral_cos_mul_symCoshKernel_pos`), `integral_exp_half_mul_twSymCoshKernel`
      (mean zero), and the decay `T_1 ≤ 8e^{−3|v|/2}`-type bounds.
  - `RHTower/TwistedArcGenerator`: the x-space twisted arc vector
    `g_u = √y(τ_u + τ_{−u})`, `τ_c(x) = 4cxQ^{−3/2} + (42c²−18)x²Q^{−5/2} + 120c(c²−1)x³Q^{−7/2} + 105(1−c²)²x⁴Q^{−9/2}`.
    - Even and S-invariant; explicit derivative.
    - `|g_u| ≤ 9000/(1+x²)` and `|g_u′| ≤ 260000/(1+x²)`.
    - Log profile `√(y/2)(¼−∂²)²𝒦_u`; `∫g_u = 0`; strictly PD log profile; sin/cos moment integration by parts.
  - `RHTower/TwistedArcN1Reduction`:
    - `TwistedArcMinimumPrinciple`: for no N and a is `Σ_{n<N} a_n M_n(u) > 0` on all of `u ∈ [−½,½]`, where
      `M_n(u) = ∫ g_u cos(2π(n+2)x)`.
    - Separation + Prokhorov give `exists_probabilityMeasure_twArc_annihilating`.
    - **`exists_decayClass_fullLineWitness_of_twistedArcMinimumPrinciple`**: under the principle there is an h that
      is even, S-invariant, ∫h = 0, with profile `O(e^{−3|v|/2})`, strictly PD log profile, and
      `∫h′ sin(2πmx) = 0` for **every** m ≥ 2. This is the full (N1) line witness (the corpus B′ format with ∀n).
- **Meaning.** The HF producer core (N1) is now an explicit twisted minimum principle on the compact bottom arc. It is
  a statement about finite sums of Whittaker modes and a fixed 4th-order operator 𝔐², like Theorem A's minimum
  principle, and has no RH-equivalent content in its form.
  - In the holomorphic model it holds with winding margin, but it sits at the critical threshold (rows 206–208).
  - Low-mode checks (rows 208/209 hand calculations, 2–3 modes, sample points 60°–90°) found no positive combination.
- Open (core): prove `TwistedArcMinimumPrinciple`. Equivalently, the unique corner-singular annihilator κ* has
  constant sign.

## Row 210 — [P] TAMP: the unique annihilator, the BRS link, a sign decomposition, j-uniformization
- **BRS link (C226).** The ζ-free decay-class blind space is 1-dimensional and spanned by σ*. The witness
  ν* = Ξ²R_{σ*} lies in the BRS interpolation class (exponential decay of ν and ν̂). By BRS uniqueness
  (loop rows 569/571, rh-goal-loop), `ν* = ν̂*(0)·V₁`. Consequences:
  - V₁ (the BRS dual basis function at n = 1) vanishes **doubly** at every zero of ζ. This corrects the row 571
    heuristic "V₁ vanishes only simply".
  - (N1) in the BRS class ⟺ V₁ ≥ 0 ⟺ the arc spectrum of σ* is positive. TAMP (κ* ≥ 0) is sufficient, not necessary.
- **Signs of the structure constants** (min principle for `div(y∇v) = 0`, `v = V/√y`).
  - V₀ > 0 in D, so its corner coefficient p₀ > 0, so `a₁(σ*) = s₀ = p₀ > 0` (rigorous).
  - The dual corner solution S* (`r^{−3/2} sin(3θ/2)`, vanishing on A, decaying at the cusp) is > 0 in D, so its flux
    `∂_n S* > 0` on A. Hence c_{3/2} is a **positive functional** on data vanishing to second order at the corners.
  - Near the corners `κ* ≈ β₁(3/π) r^{3/2}`, with `β₁ = −a₁(V₀)`. Then β₁ > 0 if V₀ restricted to y = 1 increases
    in |u| (plausible).
- **Sign decomposition.** `κ*(α) = ∫ G(α,β) ∂_n V*(β) dβ`, where G is the clamped Green function of 𝔐² (beam type,
  presumably ≥ 0) and `V* = s₀V₁ + β₁S*`.
  - The S* part is positive; the V₁ part is positive mid-arc and negative near the corners.
  - The corner term dominates near the corners (r^{3/2} vs r²). Positivity of κ* in between is a single quantitative
    comparison.
- **Hand LP check (exact-holomorphic model with the full Touchard terms, modes 2–4, sample points 60/70/75/80/90°).**
  A positive annihilator exists, e.g. weights (0.07, 0.343, 0.451, 1.033, 1), feasible for a ∈ [0.046, 0.097].
  The K₀/Abel factors only rescale rows and columns positively, plus about 1% corrections. Evidence for TAMP;
  hand estimate, not a proof.
- **j-uniformization.** j maps D (the cusp region above A, with T-identified sides) conformally onto ℂ ∖ [0, 1728].
  - A ↦ the two sides of the slit, the corner ρ ↦ 0 (triple zero: angle 2π/3 ↦ 2π), i ↦ 1728.
  - Composed with the Joukowski map, D ≅ {|w| > 1}, and the corner r^{3/2} expansions become smooth in w.
  - At s = 1 (harmonic; W_n = πq^n exactly, twist `(1 + ∂_α²)²`) TAMP is an exactly holomorphic problem with an
    explicit annihilator space span{dφ, cos φ dφ} ⊕ (corner point functionals).
- **Next.** Positivity of the clamped Green function of `(∂² + V)²`; the mid-arc comparison for κ*; the s = 1 model as
  a solvable test case.

## Row 211 — [P] the PD density of an S-symmetric witness is its boundary value on the unit circle
- **C227 (spectral density law).** Let h be even and S-symmetric (h(1/x) = |x|h(x)), with h(x) = F(x²) on
  [−1,1] and F(ζ) = Σ c_k ζ^k.
  - The log profile is P(v) = Σ c_k e^{−(2k+½)|v|}.
  - The spectrum is Σ c_k·2ν_k/(ν_k²+τ²), with ν_k = 2k+½.
  - Equivalently, spectrum·cosh(πτ) = 2∫_0^π cosh(τθ)K(θ)dθ, where
    K(θ) = Σ c_k cos(ν_kθ) = Re[e^{iθ/2}F(e^{2iθ})] = Re[e^{iθ/2}h(e^{iθ})].
  - The PD density is the rotated boundary value of the continued witness on the unit circle, so PD ⟸ K ≥ 0.
  - Proof: ∫_0^π cosh(τθ)cos(ν_kθ)dθ = ν_k cosh(πτ)/(ν_k²+τ²), since cos(ν_kπ) = 0 and sin(ν_kπ) = 1. Lean target.
- **Arc case.** Arc vectors are 2√sinα Σ P_{2k}(cos α)x^{2k} (Legendre generating function). Their K is the
  Mehler–Dirichlet–Murphy kernel (4/π)√sinα·1_{θ<α}/√(2(cosθ−cosα)), i.e. the Abel transform 𝒜κ.
  - Arc-supported h: K ≡ 0 on (2π/3, π]. This follows from analyticity across the gap arc plus S-symmetry, which
    makes e^{iθ/2}h(e^{iθ}) purely imaginary there and real on [0, π/3).
  - Hierarchy: TAMP (κ* ≥ 0) ⟹ K* = 𝒜κ* ≥ 0 ⟹ Λ ≥ 0 ⟺ (N1) in the BRS class.
- **Γ-factor law (given the row-210 BRS link).** V₁ = C·Ξ²·|Γ(¾+iτ/2)|²·Λ_{κ*}(τ), with
  Λ_{κ*}(τ) = ∫_{−2π/3}^{2π/3} cosh(τθ)K*(θ)dθ.
  - The poles of 1/cosh(πτ) at ±i(2k+3/2) cancel automatically, because arc functions are even-analytic at 0.
  - So V₁/Ξ² = R* is entire of exponential type π/6, and |Γ(¾+iτ/2)|^{−2}R* is a Laplace transform supported in
    [−2π/3, 2π/3].
- **Transfer formula on A.** Blindness gives Σ_n h*(w+n) = A cos 2πw on the scalloped domain Ω = ∪_n D(n,1) ∪ mirror.
  - The inner boundary value on A continues analytically: h*₋(w) = A cos 2πw − Σ_{n≠0} h*(w+n), with
    h*(w+n) = ±(w+n)^{−1}h*(1/(w+n)) at interior points.
  - Outer and inner boundary values are related by e^{iα/2}h₊ = ±conj(e^{iα/2}h₋).
  - The main term 2Re[e^{iθ/2}A cos(2πe^{iθ})] changes sign on A (≈ +189A at i, ≈ −100A at the corner), so K* on A is a
    near-cancellation between it and the n = ±1 transfer terms.
- **Variation diminishing.** cosh(τθ) is a power series in (τθ)² with positive coefficients. If K* has exactly one sign
  change (− then + toward 2π/3, where the corner law makes it positive), then (N1)-BRS ⟺ Λ(0) = ∫K* ≥ 0.
- **Correction.** The "smoothness law" (blindness ⟹ h even-smooth at 0) is automatic for arc superpositions and is
  not a constraint. It is a constraint only for the θ-generators k_θ(|x|) (s=1 half-line Cauchy kernels at
  e^{i(π−θ)}), whose spectrum is cosh(τθ)/cosh(πτ).
- **[L] row 211.** `RHTower/SelfReciprocalBoundaryDensity` (standard axioms, `lake --old` clean, wired).
  - `integral_cos_mul_selfRecProfile`: Lorentzian form Σc_k·2ν_k/(ν_k²+τ²).
  - `integral_cosh_mul_cos_selfRecExponent`: ∫_0^π cosh(τθ)cos(ν_kθ) = ν_k cosh(πτ)/(ν_k²+τ²).
  - `integral_cos_mul_selfRecProfile_eq_density`: the spectral density law.
  - `integral_cos_mul_selfRecProfile_pos`: K ≥ 0 and K ≢ 0 ⟹ strictly PD.
  - `exp_half_mul_selfRecLine`, `selfRecLine_inv`, `selfRecLine_neg`: the h ↔ profile dictionary and S-symmetry.
  - `selfRecDensity_eq_re`: K(θ) = Re(e^{iθ/2}F(e^{2iθ})).
  - Hypothesis: Σ|c_k| < ∞.

## Row 212 — [P→L] the corner coefficient of the unique witness is positive (high-frequency PD)
- **Decay class at s = ½ means "annihilate the mode-0 space".** ker𝔐² ∩ even = span{√sin α, √sin α·log sin α}, which on A
  are exactly the traces of the two mode-0 eigenfunctions √y and √y log y.
  - At s = 1 this fails: the second kernel element is (α−π/2)cos α, which is not a trace of 1. So the s=1 "model" is
    degenerate (a real zero at τ = 0) and should not be used as a test case.
- **Clean characterization.** σ* = ∂_nV*, where V* is the unique eigenfunction in D with
  - V* = 0 on A;
  - V* − √y I₀(2πy)cos 2πx → 0 at the cusp: no mode-0 part at all, no √y and no √y log y;
  - the minimal corner singularity β r^{−3/2}sin(3θ'/2).
  Equivalently V* = V₁ + (β/π)S*, with the reciprocity s₀* = πp₀ (the √y-coefficient of S* equals π times the corner
  coefficient of V₀).
- **Theorem (paper, rigorous modulo standard elliptic facts).** β > 0 in the normalization where ĥ*(1) > 0.
  - β = u₀(φ₁)/p₀ with p₀ > 0 (Hopf), where u₀(φ₁) = ∫_A I₀(2πy)cos(2πx) dω and ω is the cusp harmonic measure of div(y∇·).
  - **Cosine rearrangement lemma.** ω ≥ 0 and ∫_A K₀(2πy)cos(2πx)dω = 0, because a decaying mode has zero cusp
    average. Put λ = I₀/K₀ evaluated at y_A(¼). Then (I₀ − λK₀)(2πy_A(x))·cos(2πx) ≥ 0 pointwise on A, since both
    factors change sign exactly at |x| = ¼ (y_A decreases in |x|, I₀/K₀ increases). Integrating gives u₀(φ₁) > 0.
- **Consequences.**
  - The large-τ spectrum Λ_{σ*}(τ) ~ (3β/π)Γ(−3/2)(2π)^{−1/2}τ e^{2πτ/3} > 0, so h* is PD at all high frequencies.
  - κ* ≈ (8β/(3π)) r^{3/2} > 0 near the corners, and K* > 0 near θ = 2π/3.
  - The large-τ sign is consistent with the sign of ĥ*(1) (same normalization), so there is no obstruction.
- **TAMP reduction.** TAMP ⟸ (C230) ∂_nV* > 0 on the open arc, i.e. the negative nodal domain of V* (which descends
  from the cusp around x = ½) does not reach A, together with positivity of the clamped Green function of (∂²+V)²
  on [π/3, 2π/3] (2V·L² ≈ 1.2, far below the buckling value 4π² ≈ 39).
- **[L] row 212.** `RHTower/ModularArcGrowingModePositivity` (standard axioms, `lake --old` clean, wired).
  - `integral_mul_cos_pos_of_ratio`: the cosine rearrangement inequality on the arc, for general (F, G) with F/G
    radially decreasing.
  - `integral_growingWhittakerCos_pos`: a nonzero finite arc measure blind to √yK₀(2πmy)cos(2πmu), m = 1, 2, satisfies
    ∫√y I₀(2πy)cos(2πu)dν > 0.
  - `exists_arcWitness_growingWhittakerCos_pos`: the corpus cusp-harmonic arc witness is positive on the growing first
    mode.
  - Helper facts: `kMoment_pos_of_pos`, `strictAntiOn_kMoment_zero`, and `measure_abs_ne_quarter_ne_zero` (blindness to
    mode 2 excludes concentration on |u| = ¼).
  - This is the sign input of β > 0, i.e. high-frequency PD of the unique witness.

## Row 213 — [P] V* is an eigenfunction on a cone surface of angle 4π/3; the corner is the obstruction from q = 3 being odd
- **S-oddness.** V* = 0 on A and is even in x. Odd Schwarz reflection across A uses R(z) = 1/z̄ = σ∘S, so V*∘S = −V*
  while V*∘T = V*.
- **Not a character.** (S,T) ↦ (−1,+1) is not a character of PSL₂(ℤ) or of any SL₂(ℤ) multiplier system, because
  χ(ST)³ = −1 ≠ 1.
  - Hence every S-odd, T-even eigenfunction is double-valued around the orbit of ρ, with monodromy −1 and local
    exponents r^{3(2k+1)/2}.
  - V₀ and V₁ take the bounded branch r^{3/2}. V* takes the minimal singular branch r^{−3/2}.
  - So V* lives on the branched double cover of ℍ/Γ at ρ, which is a hyperbolic cone surface with cone angle 4π/3. It is
    not a Fuchsian quotient, so there is no Poincaré-series construction.
- **Contrast with even q.** For the Hecke groups G_q with q even (e.g. q = 6, λ = √3), χ(S) = −1, χ(T_λ) = 1 is a genuine
  character (χ(ST_λ)^q = 1). The analogous V*_q is then a genuine automorphic eigenfunction with character, with no
  corner singularity.
  - The c_{3/2} functional, the r^{3/2} law of κ*, and the 2π/3 corner of D are all exactly the odd-q obstruction at q = 3.
- **Next.** C230 (∂_nV* > 0 on A) via comparison functions on the cone surface. The even-q analog as a solvable model.
- **Interface check (Lean).** The corpus (N1) object is `XiDivisibleBlindTest F` (`RHTower/WeilConeXiDivisibleBlindTest`):
  ExpDecayTest F, crossCorr F F (log n) = 0 for n ≥ 2, and F̂ = Ξ·g on |Im| ≤ ½ with g zero-free on ℝ. Given it,
  `riemannHypothesis_iff_primeBlindPositive_of_exists_xiDivisibleBlindTest` gives RH ⟺ PBAP.
  - Bridge from the ζ-free witness: ν = |F̂|² = Ξ²R, with R* = C|Γ(¾+iτ/2)|²Λ_{κ*} positive on ℝ.
  - Factor R* = g·g^♯ by Hadamard zero-splitting. R* is even, real, order 1 and positive on ℝ, so g is zero-free on ℝ
    with zeros in ℍ. Krein's log-integral fails (R* ~ e^{π|τ|/6}), but the Hadamard split does not need it.
  - Blindness transfers by `logNode_blind_iff_certKernel_vanishes` (d ↔ μ⋆μ).
  - Missing Lean pieces: (a) R* > 0 (the core), (b) the Hadamard spectral factorization, (c) the regularity hypotheses of
    `integral_xi_sq_mul_cpow_eq_tsum`.

## Row 214 — [P] the arc A is not the whole producer cone: full-semicircle generators, non-uniqueness, and the Lean class
- **Every point of the unit semicircle is an S-symmetric PD generator**, not just A.
  - The corpus lemma `integral_cos_mul_symCoshKernel_pos` holds for all |c| < 1.
  - Its mechanism: symCoshKernel(c,v) = Σ_j 2binom(−½,2j)c^{2j}(cosh v)^{−½−2j} has positive coefficients.
  - Hence PD of any arc superposition follows already from positivity of the weighted even moments
    μ_j = ∫u^{2j}(1−u²)^{1/4}dκ(u), which is weaker than κ ≥ 0. In the variable ζ = sech²v = 4x²/(1+x²)²,
    H = √(2/(1+x²))·G(ζ) with G(ζ) = Σμ_jζ^j, analytic off [4,∞). The corner ρ maps to ζ = 4 and i maps to ζ = ∞.
    PD ⟸ G absolutely monotone.
- **The side arcs L₂ carry their own annihilators.** In the cylinder the semicircle is A ∪ L₂, where L₂ = ∂S(D)'s side arcs
  = S(vertical sides of D), a loop through ρ and the ideal point 0.
  - The region U₂ = D ∪ S(D) has ∂U₂ = L₂. The fluxes ν₀'', ν₁'' and the corner functional c''_{3/4} (U₂ has angle 4π/3
    at ρ) of eigenfunctions vanishing on L₂ annihilate every Φ_{≥2}-trace. Green on U₂: the cusp ∞ term vanishes, the
    cusp 0 term vanishes (exponential decay between two Dirichlet arcs), and the smooth corner term vanishes.
  - Together with ν₀, ν₁, c on A this gives ≥ 6 annihilators. After the two decay-class conditions, the space of blind
    decay-class distributions on the semicircle has dimension ≥ 4. Among them is the U₂-analog σ_L* of σ*.
- **Consistency with BRS.** The L₂ witnesses have mass accumulating at α → 0, so their spectra decay only
  subexponentially (~e^{−2√(c|τ|)}). Hence they must lie outside the BRS uniqueness class: BRS needs exponential decay,
  while ν* = Ξ²R* decays like e^{−π|τ|/3}. Compact sub-arcs [ε, π−ε] add nothing: slit tips carry no annihilators because
  of the ideal-boundary pairing.
- **The Lean (N1) class is far larger than the BRS class.**
  - `ExpDecayTest` = C² with decay rate ½+δ in u.
  - The ζ-free blind space W (even, S-symmetric, ĥ(m) = 0 for m ∉ {±1}, decay class) is infinite-dimensional: it already
    contains compactly supported smooth elements, because {cos 2πmx} is not complete on intervals longer than 1.
  - So the frontier phrase "(N1) fails only through the sign of the BRS V₁" holds only inside the BRS-regular class.
    In the Lean class, (N1) ⟺ PD ∩ W ≠ ∅ (plus factorization and regularity), and V₁ ≥ 0 is sufficient but not necessary.
  - Known constraint (frontier, CosDilation rigidity): compact PD cores cannot be blind. So a PD element of W must be
    noncompact, e.g. carry mass near the real axis, which matches the C191 hint.
- **Dual heuristic.** A certificate against PD ∩ W is a real Dirichlet series D = Σ_{m≥2} a_m m^{−s} with
  Re[e^{−2iϑ(τ)}D(½+iτ)] > 0 for all τ, where e^{−2iϑ} = Γ_ℝ(s)/Γ_ℝ(1−s) is unimodular on the line.
  - For finitely many frequencies the phase 2ϑ ~ τ log τ outruns arg D (at most linear growth), so no finite certificate
    exists. This matches Theorem B′ (all finite levels).
  - Any obstruction must be an infinite Dirichlet series whose argument tracks 2ϑ(τ): an approximate-functional-equation
    object.
- **C232 (open).** TAMP_full: a positive κ on the open semicircle, with fast vanishing at α → 0, π, whose twisted moments
  annihilate all m ≥ 2. It is weaker than TAMP and gives a non-BRS (N1) line witness.
- **[L] row 214.** `HTGeometry/SymmetricCoshMomentPositivity` (standard axioms, `lake --old` clean, wired into
  HTGeometry).
  - `integral_cos_mul_coshPowerSeries_pos`: Σ_j b_j(cosh v)^{−½−2j} with b_j ≥ 0, summable and b_0 > 0 is strictly PD.
  - `integral_density_mul_symCoshKernel_eq_tsum`: the moment expansion of ∫k(c)𝒦_c dc for any integrable signed density
    on [−c₀, c₀], c₀ < 1.
  - `integral_cos_mul_momentPositive_symCoshKernel_pos`: nonnegative even moments and positive mass ⟹ strictly PD.
    The PD cone of arc superpositions is now the moment-positive cone (signed densities allowed), not just positive
    measures.
  - Consequence (paper): PD of the unique arc witness ⟸ μ_j(κ*) ≥ 0 for all j. All high μ_j are positive by β > 0
    (row 212, corner dominance), so the open core is finitely many moment inequalities.
- **Dual structure (paper).** For S-symmetric even h, ĥ(m) = (1/(2π√m))∫S_h(τ)cos(θ(τ)+τ log m)dτ, where
  e^{iθ} = ζ(½+iτ)/ζ(½−iτ) (the functional-equation phase).
  - A Farkas certificate against PD ∩ W is a Dirichlet series D (supported on m ≥ 2) with
    Q = Re[ζ(½+iτ)·conj E(½+iτ)] ≥ 0, where E = D∗μ has zero constant term.
  - Necessary for any certificate: at every zero γ on the line, E(½+iγ) must have the prescribed phase
    arg = −ϑ(γ) ± π/2. Otherwise Q changes sign at γ.
  - The family E = ζ·(positive-real-part series) is excluded by the mean-value argument (zero constant term ⟹ zero mean
    of Re E). E = ζ − 1 fails at every zero.

## Row 215 — [L] Theorem C upgraded: signed, moment-positive twisted arc measures suffice
- **[L]** `RHTower/TwistedArcMomentN1Reduction` (standard axioms, `lake --old` clean, wired). Main theorem
  `exists_decayClass_fullLineWitness_of_momentPositive`.
  - Input: a finite measure ν on the arc and a bounded measurable signed density g.
  - Hypotheses: g·ν annihilates every twisted integer moment; m_j = ∫g√(y/2)u^{2j}dν ≥ 0 for all j; m_0 > 0.
  - Conclusion: the full decay-class (N1) line witness, as in Theorem C. TAMP (g ≥ 0) is the special case.
  - Also proved: `hasSum_integral_cos_mul_symCoshKernel` (Ŝ_c = Σ 2C(−½,2j)c^{2j}C_j) and
    `integral_cos_mul_twWitnessWProfile_eq` (spectrum = (¼+τ²)²Σ_j 2C(−½,2j)C_j(τ)m_j).
- **[P] The open core is now finitely many moment signs.** Twisted-blind signed arc measures are exactly ℝκ*, since the
  adjoint of 𝔐² is injective on distributions of the closed arc. Hence:
  - moment-TAMP ⟺ μ_j(κ*) ≥ 0 for all j;
  - the high-j moments are positive (row 212, β > 0 and corner dominance);
  - μ_j = Σ_k c_{jk}λ_k with Legendre moments λ_k = c_k(H*)/4, and c_k(h*) = (2k(2k+1))²c_k(H*);
  - μ_0 ∝ H*(0) = (Mh*)'(0) = ½∫_0^∞ ĥ*(ξ)dξ/ξ, where h*'s Mellin transform has simple zeros at s = 0, 1;
  - sanity identity: Σ_k (4k+1)c_k(H*) = 0, from κ* vanishing at u = ±1.
- **[P] Coefficient transfer system.** h* = F*(x²) and blindness give
  c_k(2k)! = A(−1)^k(2π)^{2k} − 2h*^{(2k)}(1) − 2Σ_m c_m (2m+2k)!/(2m)!·(ζ(2m+2k+1) − 1).
  This is the Mayer transfer at s = ½ in the Taylor basis, so the moments are its solution functionals.

## Row 216 — [L] one sign change + positive mass suffices for (N1)
- **[L]** `RHTower/TwistedArcSingleSignChangeN1` (standard axioms, `lake --old` clean, wired).
  - `moment_ge_of_singleSignChange`: if g ≤ 0 on |u| < u₀ and g ≥ 0 on |u| ≥ u₀, then
    ∫g√(y/2)u^{2j}dν ≥ u₀^{2j}∫g√(y/2)dν. Reason: (u^{2j} − u₀^{2j})g ≥ 0 pointwise.
  - `exists_decayClass_fullLineWitness_of_singleSignChange`: a twisted-blind signed arc density with one sign change
    (− in the centre, + toward the corners) and positive weighted mass gives the decay-class (N1) line witness.
- **Open core now.** For the unique κ*:
  - (A) κ* changes sign at most once on [0,½], from − to + (κ* > 0 near the corners is proved via β > 0);
  - (B) μ_0 = ∫√(y/2)κ* > 0.
- **[P] Formulas for (B).**
  - μ_0 ∝ H*(0) = −Σ_{k≥1}(4k+1)c_k(H*), with c_k(H*) = c_k(h*)/(2k(2k+1))². Every arc vector has x²-coefficient
    2√sinα·P₂(cos α) < 0 on A, so the dominant term is −5c_1(H*), with c_1(H*) = 2∫√sinα P₂(cosα)κ*.
  - Blindness gives Σ_k c_k*ζ(2k+1) = A/2 at x = 0, the x = ½ identity Σ_k c_k*[4^{−k} + (2^{2k+1}−1)ζ(2k+1) − 2^{2k+1}] = −A/2,
    and h*''(0) = −4π²A − 2Σ_{n≥1}h*''(n).
  - μ_0 ∝ −∫log|t|h*(t)dt = c·ĥ*(1) − ∫log|πt/sin πt|·h*(t)dt, where log|πt/sin πt| ≥ 0.

## Row 217 — [L] finite moment certificate; [P] structure of the remaining core
- **[L]** `RHTower/TwistedArcFiniteMomentCertificateN1` (standard axioms, `lake --old` clean, wired).
  - `moment_ge_corner_sub`: if g ≥ 0 on |u| ≥ u₁, then μ_j ≥ u₂^{2j}P − u₁^{2j}Bν(arc), where P is the corner mass on |u| ≥ u₂.
  - `exists_decayClass_fullLineWitness_of_cornerPositive_finiteMoments`: the (N1) line witness follows from
    - corner positivity,
    - positive mass,
    - an explicit J with u₁^{2J}Bν(arc) ≤ u₂^{2J}P,
    - finitely many μ_j ≥ 0 (1 ≤ j < J).
  - The producer core is now a finite certificate for κ*. Corner positivity of κ* is proved (row 212, β > 0).
- **[P] μ_0 via the multiplicative periodization.** Let Θ(x) = Σ_{n≥1} h*(nx). Then:
  - M[Θ](s) = ζ(s)Mh*(s), so (Mh*)'(0) = −2∫_0^∞ Θ(x) log x dx/x;
  - Θ(1/k) = 0 for k ≥ 2, and Θ(1) = A/2;
  - Θ(x) = Σ_k c_k*ζ(2k+1)x^{−2k−1} on [1,∞);
  - Θ(x) = x^{−1}Σ_{m≥1} ĥ*(m/x) on (0,1).
- **[P] Deformation heuristic (caveat).** Corner positivity holds uniformly in any family of arcs on which the
  rearrangement lemma applies (y_A decreasing in |x|).
  - So along a continuous deformation from a positive base case, TAMP can fail only through an interior double zero.
  - The dual (certificates concentrating to δ at the touching point) does not forbid this, because traces are
    almost dense.
  - The naive flat (horocycle) base case is degenerate: the curvature term in √y log y forces corner functionals with
    diverging coefficients as the corner angle → π.
  - Still open: a family with a non-degenerate positive base case and a no-touching mechanism.

## Row 218 — [P] compactness duality for (N1) and a χ-phase rigidity bound (one wrong turn, corrected)
- **Compactness duality (rigorous framework).** Let K = {P even, PD, P(0) = 1, |P| ≤ C₀e^{−a|v|}, |P'| ≤ C₁e^{−a|v|}}.
  K is compact in the weighted uniform topology (Arzelà–Ascoli), and the blindness functionals L_m (and ∫h, together
  with its derivative at s = 1) are continuous on it.
  - By finite intersection, a witness exists in K ⟺ no finite certificate ℓ = Σ a_m L_m is strictly positive on K.
  - Mellin–Parseval: ℓ(P) = c∫S_P(τ)Q(τ)dτ with Q = Re[χ(½+iτ)B(½−iτ)], where B = Σ b_m m^{−s} with b_m ∝ a_m√m is a
    real Dirichlet polynomial supported on m ≥ 2, and χ(½+iτ) = e^{iθ(τ)} = ζ(½+iτ)/ζ(½−iτ).
  - Tail bound: PD and |P'| ≤ C₁ give ∫_{|τ|>T} S_P ≤ 8πC₁/T.
- **Wrong turn, corrected.** I first argued that a chirp-approximating B with Q ≥ c on [−T,T] and Σ|b_m| = O(√T) exists for
  every T. That would kill every finite-envelope witness, including the corpus's positive cusp-harmonic witness h₀
  (`exists_arcWitness`: PD, blind at all m ≠ 0, finite envelope with a = ½). Since h₀ exists, the claim is false.
- **Rigorous consequence (χ-phase rigidity).** Apply the duality to h₀. For every real Dirichlet polynomial B on m ≥ 2 and
  every T: if Re[χ(½+iτ)B(½−iτ)] ≥ c > 0 on |τ| ≤ T, then the bound M of |Q| satisfies M/c ≥ T/(4C₁(h₀)) − 1.
  - Keeping the χ-rotated Dirichlet polynomial positive on long intervals costs linearly growing ℓ¹ mass.
  - This quantifies why finite certificates fail (C214) and why the limit step C191 is delicate. Uniform-envelope
    finite-level witnesses exist ⟺ no certificate with bounded M/c exists.
- **Status.** All regular (compact-envelope) constructions lead to h*. The producer core stays the finite moment
  certificate of rows 215–217.

## Row 219 — [L] (N1) from a Ξ-divisible strip function; [P] bridge plan from the arc witness
- **[L]** `RHTower/StripFactorXiDivisibleBlindTest` (standard axioms, `lake --old` clean, wired into RHTower).
  - Setting: `StripDecay Φ b ε C` means Φ holomorphic on |Im z| ≤ b with ‖Φ(z)‖ ≤ Ce^{−ε|Re z|}; Φ(−r) = conj Φ(r).
    The test is `stripTest Φ x = Re (1/2π)∫Φ(r)e^{−irx}dr`.
  - `expDecayTest_stripTest`: for b > ½ it is C² with |F|, |F'| ≤ Ke^{−b|x|}. Proof: horizontal contour shift to
    Im z = ∓b; F' is the transform of −izΦ, which is again StripDecay with ε/2; C² via `Real.contDiff_fourier`.
  - `paperFT_stripTest`: F̂ = Φ on the open strip |Im z| < b. Proof: Fourier inversion on ℝ, strip analyticity of F̂
    (`differentiableAt_paperFT_of_expDecay`), identity theorem.
  - `crossCorr_stripTest`: (F ⋆ F̃)(y) = (1/2π)∫|Φ(r)|²cos(ry)dr (Fubini).
  - `xiDivisibleBlindTest_stripTest` and `riemannHypothesis_iff_primeBlindPositive_of_stripFactor`: if Φ = Ξ·g on
    |Im z| ≤ ½ with g zero-free on ℝ and ∫|Φ|²cos(r log n) = 0 for n ≥ 2, then `XiDivisibleBlindTest (stripTest Φ)`
    and RH ⟺ PBAP.
  - So (N1) is now, in Lean, the existence of a Ξ-divisible strip function of exponential decay whose spectral square
    has vanishing cosine moments at every log n.
- **[P] From the arc witness to a strip function (the "Hadamard split").**
  - With R = Mh/(G(s)G(1−s)) one has R(½+iz) = c₀Γ(¾+iz/2)Γ(¾−iz/2)·L(z), c₀ = 4π^{−3/2}, where
    L(z) = ∫cosh(zθ)K(θ)dθ and K is the Abel density of the arc measure, supported in [0, 2π/3].
  - If K ≥ 0 then Re L(r+iy) = ∫cosh(rθ)cos(yθ)K > 0 for |y| < 3/4. So g = √c₀Γ(¾+iz/2)·exp(½log L) is holomorphic on
    |Im z| < 3/4 with |g|² = R on ℝ, and Φ = Ξg decays like e^{−π|r|/6}.
  - The factorization is therefore explicit (a principal square root) for every Abel-positive arc density. The
    restriction θ ≤ 2π/3 (the corner angle) is exactly what puts the strip beyond ½.
- **[P] Weaker route: families.** By the corpus moment expansion,
  R(r) = Σ_j w_j|Q_j(r)|² with Q_j(z) = Π_{k<j}(k+¼+iz/2) = Γ(j+¼+iz/2)/Γ(¼+iz/2) and w_j ∝ C(−½,2j)2^{2j}m_j/Γ(½+2j).
  - Each F̂_j = Ξ·Q_j is a polynomial multiple of Ξ: a fixed universal family (derivatives of Riemann's Φ-kernel).
  - Moment positivity m_j ≥ 0 gives a nonnegative family whose combined autocorrelation is the arc witness.
  - A family version of the XiDivisible rigidity would therefore give (N1) from moment positivity alone, which is
    weaker than Abel positivity.
  - (N1)_family is the linear-conic problem: find w ≥ 0 with Σ_j w_j(F_j ⋆ F̃_j)(log n) = 0 for every n ≥ 2. The arc
    generators lie inside this cone, so the cone is strictly larger than the arc cone.
- **Remaining formal gaps for arc ⟹ (N1).**
  - (M3) The divisor transfer at an abscissa c ∈ (1,2); the corpus has it at 3, where Mh has a pole.
  - (M4) certKernel_c R = κ·Ch via the shift c → ½, `soninMellinEvaluation_fourier`, and Mellin inversion.
  - Either the Abel representation (route a) or the family rigidity theorem (route c).

## Row 220 — [L] divisor transfer at any c > 1, kernel = Fourier transform, and the family (N1) rigidity
- **[L]** `RHTower/DivisorTransferAbscissa` (standard axioms, `lake --old` clean, wired).
  - `integral_xi_sq_mul_cpow_eq_tsum_at`: for R holomorphic on ½ ≤ Re s ≤ c (c > 1) with C/(1+t²) bounds,
    ∫ξ(½+it)²R n^{−½−it} = 2πΣ_m d(m)Ψ_{R,c}(mn), where Ψ_{R,c} = 𝓜^{−1}_c[G²R].
  - Summability uses only `LSeriesSummable` of d = 1⋆1 at c. The corpus version had c = 3, which crosses the pole of
    𝓜h at s = 3 for every decay-class arc profile.
  - `logNode_blind_of_certKernelAt_vanishes`: if Ψ_{R,c} vanishes on ℕ_{≥2}, the test with density Ξ²R is blind.
- **[L]** `RHTower/DivisorKernelFourierIdentification` (standard axioms, `lake --old` clean, wired).
  - `mellin_fourier_of_re_eq_half`: 𝓜[𝓕h](s) = (Γ_ℝ(s)/Γ_ℝ(1−s))𝓜h(1−s) on Re s = ½.
  - `mellinInv_eq_fourier_of_strip`: if G is holomorphic on ½ ≤ Re s ≤ c with 1/(1+t²) decay and equals that ratio on
    the line, then 𝓜^{−1}_c[G] = 𝓕h. Proof: shift to ½, then Mellin inversion.
  - `logNode_blind_of_fourier_vanishes`: G²R = γ·𝓜h(1−·) on the line and 𝓕h(n) = 0 for n ≥ 2 ⟹ ∫Ξ²R n^{−it} = 0.
  - So the corpus line witnesses' blindness (𝓕h(m) = 0) is now formally the (N1) blindness of Ξ²R.
- **[L]** `RHTower/WeilConeXiDivisibleBlindFamily` (600 lines, standard axioms, `lake --old` clean, wired).
  - Hypotheses:
    - F_j is C² with |F_j|, |F_j'| ≤ C_je^{−(½+δ)|x|}, and Σw_jC_j² < ∞ with w_j ≥ 0;
    - every F̂_j vanishes at all zeros;
    - Σ_j w_j(F_j⋆F̃_j)(log n) = 0 for every n ≥ 2;
    - one member with w_{j₀} > 0 has no real zeros off the critical ordinates.
  - Conclusion: `eq_vonMangoldt_of_xiDivisibleBlindFamily` and
    `riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily`.
  - Proof: per-member truncation identity; uniform C_j² bounds on the zeta side (tail majorant) and prime side
    (summation by parts); dominated convergence in j; the Abel prime pairings cancel after exchanging Σ_j and Σ_n;
    Fatou in L and in j (counting measure).
- **Consequence (frontier).** (N1) no longer needs a spectral factorization. Any nonnegative combination
  Σ_j w_j|Ξg_j|² of Ξ-divisible decay tests with blind total autocorrelation suffices.
  - For the arc witness, g_j = Q_j = Γ(j+¼+iz/2)/Γ(¼+iz/2) with w_j ∝ C(−½,2j)4^j m_j/Γ(½+2j).
  - The open core is now exactly the moment positivity m_j(κ*) ≥ 0, plus routine instantiation: the decay constants of
    ΞQ_j and the strip bounds of R = Σw_jQ_j(z)Q_j(−z), using |R(σ+it)| ≤ Π_k(1+1/(4(k+¼)²))·R(½+it).
- **[P] Dictionary freedom.** The family theorem accepts any dictionary of Ξ-divisible tests.
  - With a Gaussian dictionary g_b(z) = e^{−(z−b)²/2}, (N1) reduces to a positive measure ν on ℝ annihilating
    k_n(b) = ∫Ξ²e^{−(r−b)²}cos(r log n)dr.
  - The dual certificate is a mean-zero Dirichlet cosine polynomial T with Gaussian-smoothed Ξ²T > 0 everywhere.
  - Open problem C235: a dictionary in which the annihilation problem is compact and a minimum principle holds.

## Row 221 — [L] the shifted-Gamma dictionary: (N1) as a conic linear problem
- **[L]** `RHTower/XiShiftedGammaFamily` (standard axioms, `lake --old` clean, wired).
  - Q_j(z) = ∏_{k<j}(k+¼+iz/2) and Φ_j = Ξ·Q_j = (s(s−1)/2)π^{−s/2}Γ(s/2+j)ζ(s): the completed zeta with its Gamma
    factor shifted by j.
  - `norm_shiftedGammaPoly_le_factorial`: ‖Q_j(z)‖ ≤ 3·j!(3/2)^j 3^{|Re z|/2} on |Im z| ≤ 3/2. Proof: integer ceiling
    of |Re z|/2, then j!C(j+m,j), then C(j+m,j) ≤ (3/2)^j3^m from (2/3+1/3)^{j+m} = 1.
  - `exists_stripDecay_xiShiftedGamma`: one constant for all j, decay rate 3/4 − (log 3)/2 > 0 on |Im z| ≤ 3/4, via the
    corpus horizontal decay of Ξ.
  - `decayBound_stripTest`: explicit, linear decay constants for strip tests.
  - `exists_decayBound_xiShiftedGammaTest`: |F_j|, |F_j'| ≤ C·j!(3/2)^j e^{−(3/4)|x|}.
  - `paperFT_xiShiftedGammaTest_gammaOf`: F̂_j vanishes at every nontrivial zero.
    `riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero`: F̂_0 = Ξ has only critical real zeros.
  - `crossCorr_xiShiftedGammaTest`: (F_j⋆F̃_j)(y) = (1/2π)∫|ΞQ_j|²cos(ry).
  - **`riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights`**: suppose w_j ≥ 0, w_0 > 0,
    Σ_j w_j(j!)²(9/4)^j < ∞, and Σ_j w_j A_{n,j} = 0 for every n ≥ 2, where A_{n,j} = ∫|Ξ(r)Q_j(r)|²cos(r log n)dr.
    Then RH ⟺ PBAP.
- **(N1)_Q is now a conic LP in Lean.** The arc witness with nonnegative moments gives w_j ∝ 4^j m_j/(2j)!, which
  satisfies the growth bound since |m_j| ≤ 4^{−j}m_0.
- **[P] Structure of the LP.**
  - By the kernel identification per j: A_{n,j} = 2π n^{½}Σ_m d(m)Ψ_j(mn), with
    Ψ_j = (θ(θ−1))²∏_{k<j}(k+½−θ/2)[4π^jx^jK_j(2πx)] and θ = −x∂_x, using π^{−s}Γ(s/2)Γ(s/2+j) = 𝓜[4π^jx^jK_j(2πx)].
  - After Möbius inversion: Σ_j w_jΨ_j(N) = 0 for every N ≥ 2.
  - Ψ_0(x) = 4[(t⁴+9t²)K_0(t) − 6t³K_1(t)] with t = 2πx.
  - Sign pattern: Ψ_j(N) ~ (−1)^j·(positive)·e^{−2πN} for N ≫ j; positive for j ≫ N (concentration at x = ±1).
- **[P] Dual certificates.** Positive combinations of the |Q_j|² are even and increasing in |r|.
  - A certificate is a Dirichlet polynomial D (N ≥ 2) with ∫|archXi|²|Q_j|²Re[e^{iθ}D] > 0 for every j, including the
    limit j = ∞, whose functional is ∫(¼+r²)²Re[e^{iθ}D].
  - Such a certificate refutes (N1)_Q and moment positivity together. Whether one exists is open (C236).

## Row 222 — [L] second derivatives and Fourier decay of the twisted witness; [P] the shifted-Gamma LP has one candidate per class
- **[L]** `RHTower/TwistedArcWitnessFourierDecay` (standard axioms, `lake --old` clean, wired).
  - `monoDeriv`/`abs_monoDeriv_le`: monomials α x^iQ^{−½−j} with i+1 ≤ 2j are closed under d/dx, with
    |·| ≤ 2298240(1+x²)⁻¹ when |α| ≤ 945 and i, j ≤ 5.
  - `twPointDeriv2`, `abs_twPointDeriv2_le`, `abs_twArcDeriv2_le`: g_u″ = O(1/(1+x²)) uniformly on the arc.
  - `hasDerivAt_twWitnessWDeriv`: the weighted witness h is C², with h″ = ∫g·g_u″ dν.
  - `norm_fourier_twWitnessW_le`: (1+ξ²)|𝓕h(ξ)| ≤ ∫|h| + ∫|h″|/4π², since 𝓕(h″) = (2πiξ)²𝓕h.
    `integrable_fourier_twWitnessW` follows.
  - These are the regularity inputs of the kernel identification (`DivisorKernelFourierIdentification`) for arc
    witnesses.
- **[P] The base-profile picture of the shifted-Gamma LP.**
  - Nonnegative w ⟺ base log-profile sech^{½}(v)G(sech²v) with G absolutely monotone, G(σ) = Σw'_jσ^j.
  - The twisted profile is P = (¼−∂²)²[sech^{½}G(sech²)] = sech^{½}·Σ_j w'_jσ^j(α_j − β_jσ + γ_jσ²), where
    α_j = 4j²(2j+1)², β_j = s(s+1)(8j²+12j+6), γ_j = s(s+1)(s+2)(s+3), s = ½+2j.
  - P_0 = −(9/2)sech^{5/2} + (105/16)sech^{9/2}.
  - Arc points give G_u(σ) = 2Σ_j C(−½,2j)u^{2j}σ^j, with radius 1/u².
  - The Lean growth bound Σw_j(j!)²(9/4)^j < ∞ allows radius > 9/4, i.e. arc points up to |u| < 2/3: beyond the corners
    u = ±½. Within the analytic (BRS) class the blind witness is unique, so there the LP has the single candidate
    h* and (N1)_Q ⟺ m_j(κ*) ≥ 0. Extended arcs (½ < |u| < 2/3) leave the BRS class and add blind directions
    (conjecture C237: TAMP on an extended arc [−u₀, u₀] with u₀ < 2/3).
- **[P] Bessel form.** Ψ_j = c_j∏_{k<j}[(k+½−θ/2)(k+θ/2)]Ψ_0, θ = −x∂_x, Ψ_0 ∝ (θ²−θ)²K_0(2πx) = (t⁴+9t²)K_0 − 6t³K_1 (t = 2πx).
  Rough Bessel values suggest Ψ_0 < 0 on x ∈ (~0.19, ~0.76) and Ψ_0 > 0 at every integer.

## Row 223 — [L] the exact spectral identity and the explicit arc weights
- **[L]** `RHTower/ShiftedGammaSpectralIdentity` (standard axioms, `lake --old` clean, wired).
  - `integral_cos_mul_cosh_rpow_neg_eq`: ∫cos(τv)cosh(v)^{−s} = 2^{s−1}|Γ((s+iτ)/2)|²/Γ(s) (closed form, extracted).
  - `Gamma_add_nat_eq_mul_prod`, `norm_Gamma_shift_eq`: |Γ(¼+j+iτ/2)| = |Γ(¼+iτ/2)|·|Q_j(τ)|.
  - `norm_archXi_criticalLine_sq`: |G(½+iτ)|² = ((¼+τ²)²/4)π^{−½}|Γ(¼+iτ/2)|².
  - **`norm_archXi_sq_mul_norm_shiftedGammaPoly_sq`**: |G(½+iτ)|²|Q_j(τ)|² = λ_j(¼+τ²)²C_j(τ), where
    λ_j = π^{−½}Γ(½+2j)/(4·2^{2j−½}).
  - `ringChoose_neg_half_eq`: C(−½,n) = (−1)^nΓ(n+½)/(√π n!).
  - `arcGammaWeight m j = 4√2·4^j m/(2j)!`, with `arcGammaWeight_mul_lambda`: w_jλ_j = 2C(−½,2j)m_j.
  - `summable_arcGammaWeight`: 0 ≤ m_j ≤ M4^{−j} ⟹ Σw_j(j!)²(9/4)^j < ∞, via (j!)²4^j ≤ (2j+1)(2j)!.
- **Consequence.** For a moment-positive twisted arc density, the weights w_j = 4√2·4^jm_j/(2j)! satisfy the growth
  hypothesis of `riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights`. They reproduce the arc spectrum
  exactly: Σw_j|G|²|Q_j|² = Ŝ_h (by the corpus moment expansion).
- **Remaining for the formal chain** (module B2b):
  - holomorphy and strip bounds of R(s) = Σw_jQ_j(z)Q_j(−z);
  - the critical-line identity G²R = γ·𝓜h(1−·), from the identity above and the corpus moment expansion;
  - the Fourier/Mellin step applied with h = twWitnessW (regularity from B1);
  - 𝓕h(n) = 0 from twisted blindness (Fubini);
  - final assembly.

## Row 224 — [L] TAMP ⟹ (RH ⟺ PBAP), formal chain closed
- **[L]** `RHTower/ArcGammaMultiplier` (standard axioms, `lake --old` clean, wired).
  - R(s) = Σ_j w_jQ_j(z)Q_j(−z) with z = −i(s−½). It is holomorphic on |Re s−½| < 3/2, with ‖R‖ ≤ 9S·3^{|Im s|}.
  - ξ²R = Σw_jΦ_j(z)Φ_j(−z).
  - ‖ξ²R‖ ≤ C/(1+t²) and ‖G²R‖ ≤ C'/(1+t²) on ½ ≤ Re s ≤ 5/4. The G-bound comes from the Stirling-type
    |Γ(s/2)| ≤ K(1+|t|)^N e^{−π|t|/4} and polynomial·e^{−at} ≤ k!/a^k.
  - R(½+iτ) = Σw_j|Q_j(τ)|².
- **[L]** `RHTower/TwistedArcMomentPositiveRH` (standard axioms, `lake --old` clean, wired).
  - `mellin_twWitnessW_criticalLine`: 𝓜h(½−iτ) = ∫cos(τv)e^{v/2}h(e^v)dv.
  - `fourier_ofReal_eq_cos_of_even`: 𝓕 of an even real L¹ function is its cosine transform.
  - `fourier_twWitnessW_natCast_eq_zero`: 𝓕h(N) = ∫g·M_{N−2}dν = 0 for N ≥ 2 (Fubini).
  - `archXi_sq_mul_arcGammaMultiplier_criticalLine`: G(s)²R(s) = (Γ_ℝ(s)/Γ_ℝ(1−s))𝓜h(1−s) on Re s = ½, with
    w_j = 4√2·4^jm_j/(2j)!.
    - G(s) = (Γ_ℝ(s)/Γ_ℝ(1−s))·conj G(s) on the line, so G² = ratio·|G|².
    - Then |G|²Σw_j|Q_j|² = (¼+τ²)²Σ2C(−½,2j)C_j m_j is the moment expansion of the witness profile.
  - `integrableOn_norm_mul_rpow_neg_half`: the t^{−½}-weighted integrability from an O((1+t²)⁻¹) bound.
  - **`riemannHypothesis_iff_primeBlindPositive_of_twistedArc_momentPositive`**: suppose g is bounded and measurable,
    ∫g·M_n dν = 0 for every n, m_j ≥ 0 for every j, and m_0 > 0. Then RH ⟺ PBAP.
- **Meaning.** The earlier corpus statement was "TAMP ⟹ line witness with positive profile", which still needed a
  spectral factorisation. The whole chain is now unconditional in Lean:
  TAMP (a positive-moment blind arc density) ⟹ (N1) in the shifted-Gamma dictionary ⟹ RH ⟺ PBAP.
- **Open inputs on this route (exactly two).**
  1. Existence of a moment-positive blind arc density. On the analytic class this is m_j(κ*) ≥ 0 for the unique
     blind density; C237 is the extended-arc variant with |u| < 2/3.
  2. PBAP.
- **Row 224 addendum [L].**
  - `shiftedGammaPoly_ofReal_ne_zero`: Q_j has no real zeros. So every j₀ with w_{j₀} > 0 is zero-faithful
    (`riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights_of_pos`).
  - The arc theorem now needs only some m_{j₀} > 0, which admits zero-mass (two-arc type) densities.
  - `riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple`: TMP ⟹ (RH ⟺ PBAP).
- **[P] Twisted moments as tangential operators.**
  - Notation: arc z = e^{iφ}; W_m = √y K₀(2πmy)cos(2πmu) with ΔW_m = ¼W_m; E = r∂_r the dilation generator.
  - Then (E²−¼)W = L W on |z| = 1, where L = −∂_φ² − ¼ − 1/(4sin²φ) is tangential and commutes with E.
  - Hence **M_n = 4·L²w_{n+2}**, with w_m = W_m|_{|z|=1}.
  - Annihilators of the traces of decaying solutions (modes ≥ 2) are fluxes ∂_nΨ of solutions vanishing on the arc:
    - Ψ_0: the cusp log mode, giving the harmonic measure ω;
    - Ψ_1: the m = 1 growing mode;
    - Ψ_c: the corner singularity r^{−3/2} at the glued corner (interior angle 2π/3). It is symmetric, so it survives
      in the even sector.
  - The r³ mode is antisymmetric, so its compatibility condition is void for even data.
  - So the even twisted annihilator is {κ : κ∘L² ∈ span(ω, χ_1, c_1)}, modulo the 2-dimensional even kernel of L².
    It is 1-dimensional, which explains the unique κ*.

## Row 225 — [P] bottom-arc rigidity; Mehler admissibility of the whole semicircle (C238 setup)
- **[P] Rigidity.** On the bottom arc A the even twisted annihilator satisfies κ∘L² ∈ span(ω, χ_1, c_1), and it must
  vanish on ker L² = span(√y, √y log y)|_A.
  - Green's identity on F gives ω(√y) = 1 and χ_1(√y) = c_1(√y) = 0. Hence the ω-coefficient is 0.
  - So κ*∘L² = β_c χ_1 − β_1 c_1, built from the m = 1 growing mode and the r^{−3/2} corner singularity only.
  - κ* ~ r^{3/2} at the corners, with no point masses. For large j, sign(m_j) = the sign of κ* at the corners.
  - A smooth clamped twisted-blind density on A must vanish (σ = L²κ would be an untwisted blind measure ⊥ √y, √y log y).
- **[P] Mehler admissibility (C238a).**
  - Mehler: P_{−½+iτ}(cos α) = (√2/π)∫_0^α cosh(τφ)(cos φ − cos α)^{−½}dφ, a positive combination of
    cosh(τφ) = Σ_k τ^{2k}φ^{2k}/(2k)!.
  - The arc multiplier of the point c = cos α is R_c ∝ |Γ(¾+iτ/2)|²(P_{−½+iτ}(c) + P_{−½+iτ}(−c)).
  - So R_c = Σ_k w_k|z^kΓ(¾+iz/2)|² with w_k ≥ 0.
  - The family Φ_k(z) = z^kΓ(¾+iz/2) has |ΞΦ_k| ≲ |t|^k e^{−π|t|/2}, so C_k ~ k!/(π/2−ε)^k.
  - Σw_kC_k² < ∞ ⟺ max(α, π−α) < π.
  - Hence every compactly supported positive measure on the open semicircle is (N1)-admissible, extending the range from
    |c| ≤ ½ (current Lean) or 2/3 (the Q_j bound) to |c| < 1.
- **C238b (open).** The twisted side-arc minimum principle: a positive measure on a compact part of the side arcs (or of the
  semicircle) annihilating every M_n. The untwisted version is in the corpus (`whittakerSideArc_coeff_eq_zero`).
  Near the horn E²(E+1)²(log y) = 0, so the leading cusp terms of a twisted combination vanish.

## Row 226 — C237 FALSE (support rigidity); the arc producer reduces to a single Mehler–Fock positivity
- **[P] 3D lift.** With W = √y·Ṽ, the equation ΔW = ¼W becomes div(y∇Ṽ) = 0. This is the axisymmetric Laplace equation in ℝ³:
  axis = u-axis, cylindrical radius = y.
  - Decaying periodic Whittaker sums are periodic axisymmetric harmonic functions outside the chain ∪_k B(k e_u, 1).
  - The bottom arc A is the spherical zone |u| ≤ ½ of the unit sphere.
  - E = r∂_r is the 3D radial generator. On traces E(E+1) = −Δ_{S²} (solid harmonics r^ℓ and r^{−ℓ−1}), so the
    twisted moment is ∫Δ_{S²}²Ṽ dκ.
  - The corner is the intersection circle of adjacent spheres (dihedral angle 2π/3). The Kelvin transform is the modular
    reflection.
- **[P] Support rigidity (kills C237).** Let κ (or ℓ = L²κ in the twisted case) annihilate the traces of every periodic
  decaying solution with modes ≥ 2.
  - Its single-layer potential U below the support equals the m = 0 and m = 1 terms only, so it is smooth there.
  - On a compact extension E of A (c₀ < 1) the pieces E are slits inside one connected component of the complement.
    So the jump of ∂_nU across E vanishes, hence κ|_E = 0 (twisted: L²κ = 0 on E with free-end conditions, hence κ|_E = 0).
  - Conclusion: every blind or twisted-blind signed measure on a compact sub-arc of the open semicircle lives on A, and is
    zero unless the sub-arc contains A.
  - Side-arc blind measures (corpus) must reach the cusps, where every Lean family (Q_j or Mehler) degenerates.
  - **C237 (extended-arc TAMP): FALSE as a source of new directions.**
- **Positive survivor (exact).** The arc producer is one function κ* (the 1-dimensional even twisted annihilator on A).
  - **(CORE)** P̂*(τ) := ℓ*(Θ_{iτ}) = (¼+τ²)²∫_A √(sinφ)P_{−½+iτ}(cos φ)dκ*(φ) ≥ 0 for all real τ.
  - Θ_{iτ} = √(sinφ)P_{−½+iτ}(cosφ) are the eigenfunctions of L (eigenvalue −(¼+τ²)).
  - CORE is necessary for (N1) through any arc family, and sufficient given a Lean sum-of-squares factorisation of R.
  - It is strictly weaker than each of m_j(κ*) ≥ 0 (Q_j cone), positivity of the Abel transform of κ* (Mehler cone),
    and κ* ≥ 0 (TMP).
- **[P] Large-τ sign.** Θ_{iτ} peaks at the corners (~e^{2πτ/3}), so ℓ*(Θ_{iτ}) ~ (−β_1)·Γ(−3/2)·τ^{3/2}e^{2πτ/3}·(sign of
  the corner flux), with Γ(−3/2) = 4√π/3 > 0. The large-τ sign of CORE is fixed by sign(β_1), the √y-coefficient of the m = 1
  growing mode corrected to vanish on A.
- **Status.** Paper sketches. Next: decide sign(β_1) structurally, and the τ = 0 sign; formalise whichever piece closes.

## Row 227 — [P] sign(β_1) < 0; κ* normalisation; why the explicit ζ-weighted tests fail (Voronoi wall)
- **[P] β_1 < 0.** Let Ṽ_0 = log ρ + β_0 + Σa_mK_0(2πmρ)cos 2πmu be the cusp Green function: it vanishes on the zone,
  is positive in Ω, and is axisymmetric-harmonic in the 3D lift.
  - Moving planes (reflect in u = t, 0 < t ≤ ½; the reflected chain stays inside the obstacle on the relevant range,
    since (1−2t+u)² ≥ u² for u ≥ t−½) give: Ṽ_0(·,ρ) is nondecreasing in u on [0,½].
  - Hence ∫Ṽ_0 cos 2πu du = ∫_0^{¼}(f(u) − f(½−u))cos 2πu du ≤ 0, so a_1 < 0 (strong maximum principle).
  - Green's identity with H = I_0(2πρ)cos 2πu gives ω_∞(H) = −a_1/2 > 0.
  - β_1 = −ω_∞(H) = a_1/2 < 0.
- **Normalisation.** Take Ψ_c > 0 near the corner. Then β_c > 0 (Harnack), and ℓ* = β_cχ_1 + |β_1|c_1 with both coefficients
  positive.
  - c_1 is a positive density away from the corner, with finite-part (Hadamard) renormalisation at the corner.
  - χ_1 is positive in the middle of A and negative near the corners.
  - κ* ~ +r^{3/2} at the corners, and CORE holds for large τ, because f.p.∫e^{−τr}r^{−5/2}dr = Γ(−3/2)τ^{3/2} > 0.
  - CORE can only fail at moderate τ, if κ* is too negative in the middle of A (τ = 0 weights the middle most).
- **[P] Voronoi wall for explicit tests.**
  - P̂ = |ζ|²(¼+τ²)²|φ̂|² gives 𝓕h(N) = Σ_m d(m)·ŵ(log(N/m))·(…), not log(mN). Earlier sign error corrected: the
    ratios N/m hit every rational, so this is never zero.
  - The variant P̂ = |ζA|²ν with A a short Dirichlet polynomial fails the same way: the d(m)-sum produces ratios lN/(mk)
    equal to 1.
  - Any positive P̂ meets γ(1−s) = ζ(s)/ζ(1−s), so blindness is always a Voronoi d(m)-interpolation. This matches the
    memory n1-voronoi-maass-interpolation; no shortcut.
- **[P] Bandlimited witnesses fail.** ĥ supported in [−2,2] is blind automatically. But self-reciprocity h(1/x) = |x|h(x)
  with smooth ĥ forces h ≡ 0. A non-smooth ĥ needs 𝓜ĥ(1−s)/𝓜ĥ(s) = γ(1−s)², a self-dual functional equation.
- **[P] The canonical potential Ψ*.** ℓ* is the flux of Ψ* := β_cΨ_1 + |β_1|Ψ_c. Since β_cβ_1 + |β_1|β_c = 0, Ψ* is the
  unique (up to scale) solution in F with these properties:
  - it vanishes on A;
  - its cusp expansion is the pure m = 1 growing mode √y I_0(2πy)cos 2πu plus decaying terms, with no √y and no √y log y;
  - it has a positive r^{−3/2} singularity at the glued corner.
  - So κ* is the unique twisted "dual" of a single explicit boundary-value problem: κ*∘L² = ∂_nΨ*|_A.
- **C240 (conjecture).** Q(μ) := κ*(Θ_λ) (μ = λ²) is entire of order ½ in μ and has only zeros μ > 0 (real λ),
  with Q(0) > 0.
  - Then Hadamard gives Q(−τ²) = Q(0)Π(1 + τ²/λ_k²) > 0, which is CORE.
  - The large-τ positivity is consistent with this; a mechanism would be a self-adjoint (secular-equation) realisation of
    λ² ↦ ∂_nΨ*-pairing.
  - [OPEN CORE]: find the self-adjoint structure. Green identities on the dilation sector fail because Ψ* grows like e^{2πy}.

## Row 228 — C241: the continuous Gamma-exponent family escapes rigidity
- **Family.** Φ_a(z) = Γ(a+iz/2)/Γ(¼+iz/2), a > 3/8.
  - Poles at Im z = 2(a+k) > ¾, so Φ_a is analytic on the strip. |Φ_a| ~ |z/2|^{a−¼}, so ΞΦ_a decays like e^{−π|t|/4}.
  - Reality: Φ_a(−τ) = conj Φ_a(τ).
  - Witness: h_a = 𝒟²ψ_a with ψ_a(x) = |x|^{−½}sech^{2a}(log|x|) = 2^{2a}|x|^{2a−½}(1+x²)^{−2a}.
  - a = ¼ + j recovers the Q_j / B_j basis (entire R, rigid). Non-integer a − ¼ gives a meromorphic R, so the
    generator has no compact support on the semicircle, and support rigidity does not apply.
- **Twisted moments.** M_n(a) = ĥ_a(n+2).
  - For non-integer a: M_n(a) ≈ C(a)(2a+½)²(2a−½)²(n+2)^{−2a−½} + O(e^{−2πn}), with
    sign C(a) = −sign(sin(π(2a−½)/2)). So the tail is negative on (3/8, 5/4) and positive on (5/4, 9/4).
  - For a ≫ n²: M_n(a) ≈ (2πn)⁴·(positive bump), so positive.
- **C241 (conjecture).** For some compact [a₀, a₁] ⊂ (3/8, ∞) crossing a = 5/4 (and/or reaching large a), a probability
  measure on [a₀, a₁] annihilates every M_n, n ≥ 0 (Gordan: no Σc_nM_n(a) > 0 on [a₀, a₁]).
  - Through a measure-indexed family theorem this gives (N1), and so RH ⟺ PBAP.
- **Immediate kill.** For [a₀, a₁] ⊂ (3/8, 5/4], −M_n is a certificate for large n, so the interval must cross 5/4.
- **Phase 4 on C241.**
  - At a = ¼ + j: M_n(a) = (−1)^j E_j(n+2) with E_j(m) ~ m^{2j−½}e^{−2πm}.
  - On (¼+j, ¼+j+1) the power tail has sign (−1)^{j+1}, from 1/Γ(¼−a).
  - So on any compact [a₀, a₁] only finitely many alternations occur. A Dirichlet polynomial D with zeros at the odd
    integers s = 2a_j + ½ in range (exponential-sum Descartes rule) plausibly certifies Σc_nM_n > 0.
  - **Verdict: C241 (compact) likely FALSE** (not proven).
- **C241′ (survivor, CM cone).** Write sech^{2a} = e^{−2a·log cosh v}. Positive combinations of the generators are exactly the
  base profiles B(v) = L(log cosh v) with L completely monotone (Bernstein): L(t) = ∫e^{−2at}dν(a), ν ≥ 0 on (3/8, ∞), with
  admissibility ∫Γ(2a)²(2/π)^{4a}dν < ∞.
  - The Q_j cone is ν atomic at a = ¼+j; arc points are CM because (e^t ∓ c)^{−½} expand with positive coefficients.
  - Conjecture: a CM L ≠ 0 exists whose twisted witness is blind at every integer ≥ 2.
  - Certificates would need a fixed-sign Laplace transform T_D(a) = ∫e^{−2at}F̃_D(t)dt on all of (3/8, ∞), against infinitely
    many alternations (integer points up to a ~ N, power tails). This is the same borderline counting as C236.
  - **Verdict: SURVIVES PRELIMINARY ATTACK.**

## Row 229 — [P] TMP ⟸ (C242 nodal positivity of Ψ*) + (P3 clamped Green positivity)
- **Construction.**
  - Let f = ∂_nΨ*|_A. Its corner behaviour is C_f r^{−5/2} with C_f > 0, and Green gives f.p.∫_A w f = 0 for every trace w of
    a decaying periodic solution with modes ≥ 2.
  - Let k := ∫G(φ,φ')f(φ')dφ', with G the clamped (k = k' = 0 at both corners) Green's function of L² on A. It converges
    absolutely, since G = O(r'²) and r'^{2−5/2} is integrable.
  - Integrate by parts: the (Lw)'k and (Lw)k' terms vanish because k is clamped. The w(a), w'(a) point terms match the
    finite part of ℓ* exactly because ℓ* ⊥ ker L² = span(√y, √y log y), which holds by the zero √y coefficient of Ψ*.
  - Hence κ* = k dφ is twisted-blind: ∫M_n dκ* = 4f.p.∫w_{n+2} f = 0.
  - **This direction needs only Green's identity and the existence of Ψ*, not the trace-closure rigidity.**
- **Sufficient conditions for TMP (κ* ≥ 0):**
  - **(P3)** the clamped Green's function of L² = (−∂² − V)², V = ¼ + 1/(4sin²φ) ∈ [½, 7/12], on an interval of length π/3,
    is ≥ 0. For V = 0 this is the classical positive 1D clamped beam kernel, and V ≪ λ_1(−∂²) = 9.
  - **(C242)** f ≥ 0 on A, i.e. Ψ* > 0 in a neighbourhood of A (Hopf).
- **[P] Representation.** Let 𝒫(g) be the solution with data g that decays at the cusp; it exists for every g, with the
  ω-defect absorbed by the corner Martin kernel K_P (normalised K_P/√y → 1).
  - Then Ψ*/β_c = Ψ̂ = I-mode − 𝒫(I-mode|_A) = Ψ_1 + |β_1|K_P.
  - So f is the Cauchy-data mismatch N_I − Λ_𝒫(D_I) of the m = 1 growing mode.
  - Equivalently, Ψ̂(z) ∝ the m = 1 cusp Fourier coefficient of the decaying Green function G_𝒫(z,·).
- **Nodal picture.** Ψ̂ → +∞ at the corner P and ≈ √yI_0(2πy)cos 2πu at the cusp, so it is negative near u = ±½ high up.
  The negative region N must be bounded below by a nodal curve through (½, y*), y* > √3/2.
  - C242 says this curve, from the cusp at u ≈ ¼ to the cusp at u ≈ ¾, never touches A.
  - The danger zone is ¼ < |u| < 0.45 on A.
- **Status.** C242 and P3 are open; this is the new [OPEN CORE]. P3 looks provable (perturbation of the clamped beam).
  C242 is a quantitative potential-theory statement; the planned attack is explicit max-principle barriers on the corner
  regions plus the middle region.
- **[P] Corner weight is positive.** Write 𝒫(g) = D_g − ω(g)K_P. Then Ψ̂ = Ψ_1 + ω(g)K_P with ω(g) = −β_1 = |β_1| > 0, the
  ω-average of the m = 1 mode data g = I_0(2πy_A)cos 2πu on A.
  - Green between K̃_P and the cusp Green function gives the exact normalisation C̃_P = 2/(√3π c_0), where ω ≈ (3√3/4)c_0 r^{½}dr
    near each corner.
- **[P] Nodal-domain lemma.** div(y∇) has no zeroth-order term, so every negative nodal domain of Ṽ = Ψ̂/√y must reach the
  cusp. Hence the only negative domain is N_∞, the one around u = ½ at the cusp. C242 ⟺ N_∞ does not touch A.
- **Heuristic magnitudes** (decision guidance only, not proof).
  - The corner term |β_1|∂_nK_P ~ 45C_P d^{−5/2} (d = arc distance to the corner) dominates the m = 1 flux near the corners
    and in the middle.
  - The margin is thinnest at |u| ≈ 0.27–0.33 (estimated ratio 1.4–1.7). So C242 is plausible but not robust.
- **C243 (weaker, preferred).** m_j(κ*) ≥ 0 for every j (TAMP for the canonical κ*).
  - It is robust to a small negative dip of κ* in the danger zone, because κ* ~ +r^{3/2} carries corner-dominated mass
    (u² ≈ ¼) and that mass controls every m_j.
  - The Lean chain already accepts TAMP (`…_of_twistedArc_momentPositive`).
- **Proof programme** (all unconditional classical analysis):
  - (T1) existence of Ψ_1 and K_P on F (Perron, with cusp and corner asymptotics);
  - (T2) quantitative flux bounds via explicit barriers;
  - (T3) Green identity with the corner finite part ⟹ κ* = G_clamped f is twisted-blind;
  - (T4) P3, clamped Green positivity;
  - (T5) M_n = 4L²w_{n+2}, connecting to Lean's `twArcMoment`.
- **Corpus check (after the fact).**
  - (P3) is already formal: `HTGeometry/ClampedBeamPositivity.nonneg_of_coshSq_clampedBeam`. It is an elementary convexity
    argument, needs no smallness, and is stated in s = log tan(α/2), where 𝔐 = Δ_{S²} = cosh²s·∂_s².
  - The twisted operator in the Ṽ-picture is exactly 𝔐²: Lw = −√y·Δ_Sṽ and L²w = √y·Δ_S²ṽ.
  - β_1 < 0 is already formal: `ModularArcGrowingModePositivity.exists_arcWitness_growingWhittakerCos_pos` (cosine
    rearrangement: (I₀ − λK₀)(2πy)cos 2πu ≥ 0 on the arc). My moving-plane proof was a REDISCOVERY.
  - Lesson: run `research` on every sub-claim before deriving it.
- **Refined [OPEN CORE] (C242), in corpus coordinates.**
  - Ṽ* = Z − D_Z + ω(Z)K̃_P for any λ, with Z = (I₀ − λK₀)(2πy)cos 2πu ≥ 0 on A (corpus) and D_Z the bounded extension.
  - The load is σ* = y∂_nṼ*|_A = y∂_n(Z − D_Z) + ω(Z)·y∂_nK̃_P.
  - TMP ⟸ σ* ≥ 0 on the open arc: the clamped 𝔐²-solution with load σ*/cosh² is then ≥ 0 by the corpus lemma (extended to
    the r^{−5/2} endpoint load by truncation).
  - With λ the corpus value (Z vanishes on |u| = ¼ and y = y_{¼} = √15/4), Z − D_Z ≤ 0 on the corner pieces below y_{¼}.
    The competition is localised to |u| ∈ (¼, ½).
- **Link to the frontier.** The frontier map says "(N1)/C-PIN fails only through zero-faithfulness (the sign of the BRS V₁)".
  - In the ξ-divisible (shifted-Gamma / arc) framework, zero-faithfulness is automatic (Q_j has no real zeros, now in Lean),
    and the residual difficulty is a single sign: the sign of κ*.
  - Row 229 gives a new geometric form of that sign: **C242, the nodal curve of the canonical arc potential
    Ṽ* = Z − D_Z + ω(Z)K̃_P avoids the bottom arc**. Together with the corpus clamped-beam lemma, this would make TMP, and with
    it RH ⟺ PBAP, unconditional.
- **Next.** A quantitative barrier proof of C242:
  - (E1) an upper bound for the negative m = 1 flux on ¼ < |u| < 0.4;
  - (E2) a lower bound for the corner Martin flux with cusp normalisation (C̃_P = 2/(√3πc_0) needs an upper bound on the
    ω corner coefficient c_0);
  - (E3) a quantitative lower bound for ω(Z).
  - Candidate tools: explicit axisymmetric 3D harmonics (solid Legendre and Kelvin images in the unit sphere) and the corpus
    cosine rearrangement.

## Row 230 — [P] THE TWISTED MINIMUM PRINCIPLE HOLDS (paper proof; (N1) for HF modulo classical PDE inputs)
**Theorem (TMP).** There is a nonzero finite positive measure on the bottom arc annihilating every twisted moment M_n,
n ≥ 0. Hence `TwistedArcMinimumPrinciple` holds and, by
`riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple` [L], RH ⟺ PBAP.

**Notation.**
- Ṽ-picture: div(y∇Ṽ) = 0 (the axisymmetric 3D Laplace equation).
- Arc z = e^{iα}, α ∈ [π/3, 2π/3]; s = log tan(α/2) ∈ [−S, S]; Δ_S = cosh²s·∂_s²; surface measure sin α dα = sech²s ds.
- ṽ_m = K₀(2πm sin α)cos(2πm cos α), the traces of the decaying modes.
- P is the glued corner, with interior angle 2π/3 in the cylinder.

**Steps.**
1. **Bridge.** 𝓕(𝒟f) = −θ(θ+1)𝓕f, with θ = ξ∂_ξ the Euler operator E = r∂_r on (u,y) by homogeneity. On y-harmonic functions
   E(E+1) = −Δ_S (the 3D Laplacian in spherical coordinates). Hence M_n(u) = 4√y·(Δ_S²ṽ_{n+2})(α_u).
2. **Potentials** (classical Dirichlet and Martin theory on the cusped domain F).
   - D_g is the bounded solution with data g = I₀(2πy)cos 2πu on A; its cusp limit is ω(g).
   - β := ω(g) > 0. This is corpus cosine rearrangement, valid for the cusp harmonic measure, which annihilates the
     K-modes.
   - Ψ̃₁ := I₀(2πy)cos 2πu − D_g: it vanishes on A, is regular at P, and has cusp expansion I-mode − β + K-modes.
   - K̃_P is the corner Martin kernel: positive, zero on A∖P, cusp limit 1, singular term C̃r^{−3/2}sin(3θ/2) at P.
   - Ṽ* := Ψ̃₁ + βK̃_P: it vanishes on A, its cusp expansion is the I-mode plus K-modes with no constant and no log term,
     and its corner coefficient is βC̃ > 0.
3. **Load and deflection.** σ* := sech²s·EṼ*|_A, the flux density in ds; σ* ~ +r^{−5/2} at P.
   - κ̃* is the clamped solution of (cosh²κ̃'')'' = σ*, even, with κ̃ = κ̃' = 0 at ±S.
   - M := cosh²κ̃'' satisfies M'' = σ* and M ~ +r^{−½} at the ends. The clamping fixes M(0) through ∫M sech² = 0.
4. **Blindness.** For an even smooth trace ṽ:
   ∫(Δ_S²ṽ)κ̃* sin α dα = lim_{s→S}[∫_0^s ṽσ* + ṽ'M − ṽM'] (four integrations by parts; clamping kills the other terms).
   - 2D Green on F with the excised corner gives the same regularised pairing minus the cusp terms.
   - The two regularisations differ by a linear functional of the 1-jet of ṽ at P (both are exact for jets O(r²)).
   - That functional vanishes on Ṽ ≡ 1 and Ṽ = log y: there Δ_S²ṽ = 0, and the cusp terms vanish because Ṽ* has no constant
     and no log mode. The two jets are independent, so the functional is identically zero.
   - For ṽ_m with m ≥ 2 the cusp terms are 0 for every height (mode orthogonality), so ∫(Δ_S²ṽ_m)κ̃* = 0.
5. **Positivity.** M'(s) = Φ(s) := ∫_0^s σ* = ∫_0^s flux(Ψ̃₁) + β∫_0^s flux(K̃_P).
   - flux(K̃_P) > 0 on the open arc (Hopf).
   - Ψ̃₁ is regular at P. **Nodal lemma:** div(y∇) has no zeroth-order term, so no nodal domain of Ψ̃₁ is bounded. At the
     cusp the nodal set has exactly two ends (u = ±¼), so Ψ̃₁ has exactly two nodal domains.
   - Therefore no nodal arc joins A to A (it would enclose a bounded domain), and flux(Ψ̃₁) changes sign at exactly ±u₁,
     positive on the central arc (an X-crossing would create a bounded domain).
   - Green with the constant 1 gives total flux(Ψ̃₁) = 0, so the cumulative flux from the centre is ≥ 0.
   - Hence Φ > 0, M is nondecreasing on [0, S), M(0) < 0 (otherwise κ̃* would be convex and clamped, hence 0), and M → +∞.
     So κ̃*'' has sign pattern (+, −, +), and the corpus lemma `nonneg_of_clamped_of_signPattern` (extended to continuous
     κ̃*' at singular ends) gives κ̃* ≥ 0, κ̃* ≢ 0.
6. **Conclusion.** dκ* := κ̃* sin α dα / √y is positive, nonzero, and annihilates every M_n, so TMP holds.

**Why the earlier attempts failed.**
- The load positivity C242 (pointwise σ* ≥ 0) is not needed: the cumulative load suffices.
- The ω-defect of the m = 1 mode is paid exactly by the corner Martin kernel with positive weight β.
- The single sign change comes from nodal topology, not from estimates.
- No numerics are used anywhere.

**Classical inputs to justify or formalise:**
- (i) Dirichlet problem on F (cusp and glued corner);
- (ii) the Martin kernel at the corner with its r^{−3/2} asymptotics;
- (iii) corner regularity (Ψ̃₁ = O(r^{3/2}));
- (iv) analyticity of nodal sets up to smooth boundary points;
- (v) the bridge identity.
- **Row 230 [L] addendum.** New module `HTGeometry/ClampedBeamCumulativeLoad`: standard axioms, `lake --old` clean, wired.
  - `nonneg_of_clamped_of_signPattern_Ioo`: the corpus sign-pattern lemma with regularity only on (a,b) and u, u' continuous
    on [a,b]. This admits the r^{−5/2} corner load.
  - `exists_signPattern_of_ordConnected` and `ordConnected_neg_of_antitone_monotone`.
  - **`nonneg_of_coshSq_clampedBeam_of_cumulativeLoad`**: if the shear M' = Φ is ≤ 0 on (a,c] and ≥ 0 on [c,b), the clamped
    𝔐²-deflection is ≥ 0. This is exactly Step 5's 1D conclusion: cumulative flux ≥ 0 ⟹ κ̃* ≥ 0.
- **Remaining for a formal TMP:**
  - (i) the bridge M_n = 4√y·Δ_S²ṽ_{n+2};
  - (ii) the potentials Ψ̃₁ and K̃_P on F with cusp and corner asymptotics (Dirichlet problem and corner Martin kernel; not in
    mathlib);
  - (iii) the 1D/2D Green identity with corner jet matching;
  - (iv) the nodal two-domain lemma for Ψ̃₁.
  - No search in the corpus finds a refutation of TMP.
- **Row 230 [L] M1.** `RHTower/TwistedArcLegendreBridge`: standard axioms, `lake --old` clean, wired.
  - `legendreOp f c = (1−c²)f''(c) − 2c f'(c)` (the spherical Laplacian in c = cos α); `poissonRoot x c = Q_c(x)^{−1/2}`.
  - `hasDerivAt_poissonRoot`: s' = x s³. `arcQuadTerm_eq_poissonRoot_pow`: Q^{−1/2−k} = s^{2k+1}.
  - **`twPointVec_eq_legendreOp_sq`**: τ_c(x) = ℒ²[Q_c(x)^{−1/2}](c). The twisted point generator is the spherical
    bi-Laplacian of the Poisson root in the arc parameter; this is the pointwise form of the bridge, with no relation
    needed.

## Row 231 — [P] explicit dual of TMP: three cases closed, one provably needs the corner potential
- **Certificate:** T = ℒ²ṽ > 0 on the arc, where ṽ is the trace of V = Σ_{m≥2}a_mK₀(2πmy)cos 2πmu and ℒ = ∂_u(1−u²)∂_u.
- **Step 1 (1D).** The even part of ker ℒ² is span(1, log(1−u²)), the traces of the periodic solutions 1 and log y.
  - h = c₀ + c₁log y matches ṽ's 1-jet at the corner P, with c₁ = −(3/2)ṽ'(½).
  - The clamped beam (corpus) gives ṽ − h ≥ 0 on the arc, vanishing to second order at P.
- **Step 2.** U := V − c₀ − c₁log y is a periodic solution with U ≥ 0 on the arc and ∇U(P) = 0 (tangential contact plus
  symmetry in u = ½).
- **Step 3 (the cases).**
  - **(a) c₁ < 0.** U → +∞ at the cusp, so the minimum principle gives U ≥ 0 in F. **Corner Hopf:** a nonnegative
    (super)solution in a sector of angle 2π/3 > π/2 vanishing to second order at the vertex is ≡ 0 near it (comparison with
    r^{3/2}sin(3θ/2)). Hence U ≡ 0, so V = c₀ + c₁log y, so V ≡ 0. Contradiction.
  - **(b) c₁ = 0, c₀ ≤ 0.** The same argument works, since the cusp limit is −c₀ ≥ 0.
  - **(c) c₁ = 0, c₀ > 0.** V ≥ c₀ > 0 on the arc contradicts the corpus untwisted principle (`whittakerArc_coeff_eq_zero`).
  - **(d) c₁ > 0** (ṽ increasing inward from P). Not closable explicitly:
    - Adding an explicit m ≥ 1 comparison function h₁ = −C (C a twisted certificate, ℒ²C ≥ 0) would close (d) whenever
      C'_t(P) < 0.
    - But the primal objects show the corner-slope functional C ↦ C'_t(P) is represented by the positive clamped measure
      (ℒ²)^{−T}[δ'_P + (a/β_c)c₁]: its bending moment is convex and tends to +∞ at the ends, so by the corpus lemma the
      measure is ≥ 0.
    - Hence every m ≥ 1 twisted certificate increases inward from P, and **case (d) needs the corner Martin potential**.
- **Consequence for Lean.**
  - Cases (a)–(c) are formalisable now (clamped beam, minimum principle, corner Hopf, Legendre bridge).
  - The full TMP needs the potential-theory library: Dirichlet problem on F, the corner Martin kernel, fluxes, and the
    nodal two-domain lemma.
  - The rigidity theory says no explicit shortcut exists.

## Row 232 — [L] stream-function Neumann minimum principle (replaces the nodal two-domain lemma); [P] elementary corner modes; [P] archimedean-family audit of the HF chain
- **[P] Stream-function form of TMP Step 5.**
  - For v with div(y∇v) = 0, the stream function χ (χ_u = y v_y, χ_y = −y v_u) solves L*χ := χ_uu + χ_yy − χ_y/y = 0.
  - v = 0 on the arc ⟹ the radial derivative of χ vanishes on the arc (Neumann).
  - Evenness plus periodicity plus no log term ⟹ χ = 0 on u = 0 and u = ½.
  - The cumulative flux Φ(s) through the arc, counted from u = 0, equals χ at the arc point.
  - So Φ ≥ 0 ⟸ χ ≥ 0 on F₊, which is a mixed Dirichlet–Neumann minimum principle:
    - barrier w = −(u² + y²), with L*w = −2 and radial derivative −2 on the arc;
    - no interior minimum (second-derivative test), no arc minimum (one-sided radial derivative), sides and top excluded.
  - The cusp input is χ* ~ yI₁(2πy) sin 2πu > 0. The corner input is χ* ~ C̃β r^{−3/2}cos(3θ/2) ≥ 0 on the π/3 sector,
    and the corrections are odd about u = ½.
  - This removes (C4) (nodal analyticity) and the planar-topology (Jordan) argument from TMP.
- **[L] `HTGeometry/ModularArcStreamMinimumPrinciple`** (standard axioms, `lake --old` clean, wired):
  `nonneg_of_neumann_on_modularHalfArc`, `nonneg_of_isLocalMinOn_Ici` (one-sided Fermat), `halfArcRegion`,
  `isCompact_halfArcRegion`. All hypotheses are local:
  - interior equation above height b;
  - Neumann on the open arc;
  - sign on the sides, near the corner (y ≤ b, minus P), and at the cusp (liminf).
- **[P] The corner modes are elementary.** In hyperbolic polar coordinates (R, θ) at P, both arcs are geodesic rays
  (θ = 0 and θ = 2π/3), and (Δ_hyp + ¼)g = 0 separates.
  - Symmetric Dirichlet modes are sin(μθ), μ = 3(k+½).
  - With g = (sinh R)^{−½} b(R): b'' = n(n+1) b/sinh²R, n = μ − ½ = 3k+1.
  - Hence b ∈ span{P_n(coth R), Q_n(coth R)} (Legendre's equation in x = coth R).
  - For μ = 3/2: b_sing = coth R (~ R^{−1}, so g ~ R^{−3/2}); b_reg = R coth R − 1 (~ R²/3, so g ~ R^{3/2}/3).
  - So (C2) and (C3) (corner Martin asymptotics, corner regularity) reduce to Fourier sine series in θ plus explicit
    elementary radial functions. No Kondratiev theory is needed.
  - The sector expansion is valid for R < d(P, ρ) = log 3; together with the Kelvin-extended cusp expansion (y > √3/2) it
    covers F.
  - What remains classical is global existence (C1) only.
- **[P] Archimedean-family audit (Phase 4 consistency of the HF chain).**
  - PBAP(γ, q) depends only on the archimedean data, and the Weil cone W(γ, q) is common to every Dirichlet series in
    the family F(γ, q).
  - If an (N1) witness existed for a Davenport–Heilbronn member L′ of a family that also contains a GRH member L, then
    GRH(L) ⟹ PBAP ⟹ W ≠ ∅ ⟹ Λ_{L′} ∈ W ⟹ RH(L′), which is false.
  - The blindness mechanism (`logNode_blind_of_fourier_vanishes`) is coefficient-blind: Σ_m c(m)Ψ(mn) with Ψ = 0 on
    integers ≥ 2. So the arithmetic must enter through the witness geometry.
  - Check: the level-q arc {|z| = q^{−½}} meets u = ±½ above the real axis only for q ≤ 3 (corner angle and cusp
    structure as at level 1). For q ≥ 4 the region reaches the real axis (new cusps), and the corner Martin kernel and
    stream-function argument break.
  - Families with DH members and GRH members first occur at q = 7 (odd: (·/7), χ₆, χ̄₆), where the geometry has already
    broken.
  - **Verdict: no inconsistency.** TMP is level-1 specific, matching Hamburger uniqueness.
  - Function-field analogue: W(g, q) contains Λ_C for every curve of genus g over F_q, so it is not a singleton and no
    (N1) rigidity exists. The HF route's RH ⟺ PBAP is the number-field-only statement "the archimedean data (Γ_ℝ, 1)
    admit any positive Weil functional".
- **Next.**
  - TMP formalisation:
    - (i) explicit corner modes in Lean (polar ODE identities);
    - (ii) global existence (C1): choose Perron in the 3D lift, or Schwarz alternating between the corner sector
      (elementary modes) and the cusp strip (Fourier–Bessel), or a Fredholm matching argument;
    - (iii) the Green identity with jet matching.
  - PBAP: still no producer idea that passes walls 5 and 8.

## Row 233 — TMP is in Lean (other agent, dual route); correction to row 231; [L] node criticality of PBAP
- **Corpus state.** `RHTower/TwistedArcMinimumPrincipleProof.twistedArcMinimumPrinciple_holds` has standard axioms
  (checked). So `riemannHypothesis_iff_primeBlindPositive_unconditional` and the unconditional Weil-cone uniqueness
  `WeilConeUniquenessUnconditional.eq_vonMangoldt_of_weilPositiveFull` hold. The HF route is now exactly: RH ⟺ PBAP.
- **Correction to row 231.** The claim "case (d) provably needs the corner potential" was FALSE.
  - The dual proof closes (d) with the certificate's own stream function ψ = Σa_i yK₁(k_iy)sin(k_ix).
  - Z = ψ − 2G(½)x has a negative ray derivative on the arc, so the minimum principle gives Z ≥ −G(½).
  - Then ∂_y∂_xψ(ρ) ≤ 0, while the certificate forces √3(G′(½) − 2G(½)) > 0.
  - Lesson: a positive representation of a linear functional does not exclude sign arguments on an auxiliary explicit
    function. "Provably needs X" claims need a proof.
- My potential-theory programme (row 232: M3a/M3b) is obsolete. The Neumann stream principle
  (`ModularArcStreamMinimumPrinciple`) stays as a general lemma.
- **[L] `RHTower/PrimeBlindNodeCriticality`** (new):
  - `PrimeBlindPositiveOn S`: PBAP with blindness required only at the nodes n ∈ S.
  - `exists_weilPositiveFull_of_primeBlindPositiveOn`: S-restricted Hahn–Banach, using the log vectors restricted to S and
    the pair tests.
  - **`primeBlindPositiveOn_iff`**: PBAP_S ⟺ RH ∧ (every prime power lies in S). Unconditional.
  - `riemannHypothesis_iff_primeBlindPositiveOn_primePowers`: blindness at the prime powers alone characterises RH.
  - **`not_primeBlindPositiveOn_of_primePower_not_mem`** and **`exists_negative_arch_of_primePower_node_deleted`**:
    for every prime power m, some nonnegative combination of autocorrelations, blind at every log n with n ≠ m, has
    negative pole+archimedean part. Unconditional.
- **Meaning (new wall for PBAP attacks).**
  - Archimedean positivity on the blind cone is node-critical: the nodes log p^k are exactly the active constraints,
    with shadow price Λ(p^k) under RH, and the composite non-prime-power nodes (6, 10, 12, …) are redundant.
  - Any argument that would survive deleting one prime-power node cannot prove PBAP. Examples: Nyquist/sampling
    density, Beurling–Malliavin completeness, generic uncertainty principles, dilation-free support counting.
  - Such arguments prove at most PBAP_{ℕ∖{m}}, which is false.
  - A PBAP proof must see the multiplicative structure: why log 4 matters and log 6 does not.
- **[L] Positive survivor (same module): unique repair.**
  - `RepairedBlindPositive S w`: the Weil functional with weights w at the nodes off S, and 0 on S, is ≥ 0 on the
    S-blind cone.
  - **`repairedBlindPositive_iff`**: this holds ⟺ RH ∧ w(n) = Λ(n) at every deleted node n ≥ 2.
  - The archimedean place therefore determines the von Mangoldt weight of every node it is asked to repair, and the
    only admissible repair weight is exact.
  - Helper lemmas: `linearCombination_extendOn`, `linearCombination_coeff_add`, `offNodes`.
- **[P] Tiling reformulation of the PBAP domain.**
  - G(k log p) = 0 for all k ≥ 1 ⟺ the 2π/log p-periodisation of Ĝ ≥ 0 is constant (Poisson summation).
  - So PBAP reads: "every nonnegative Paley–Wiener Ĝ that tiles ℝ at every prime period 2π/log p has
    pole + ∫ĜΩ ≥ 0".
  - Node criticality: dropping one Fourier mode of one periodisation breaks it.
  - Blindness kills the p-Euler terms because each is a 2π/log p-periodic, mean-zero function, namely log p·(Poisson
    kernel − 1).
  - Wall reading: proving PBAP means finding why Ω (digamma density) dominates on functions tiling at all
    incommensurable periods 2π/log p. A density or single-period argument cannot work (wall 11).

## Row 234 — [L] the von Mangoldt function as an archimedean unit-node energy (C251 proved)
- **Definition.** E_m := {A(c) : c ≥ 0, L_n(c) = 0 for all n ≥ 2 with n ≠ m, L_m(c) = 1} (`unitNodeEnergies`): the archimedean
  energies of combinations that are blind everywhere except at the single node log m, where they carry unit mass.
- **[L] `RHTower/ArchimedeanUnitNodeEnergy`** (standard axioms, `lake --old` clean, wired):
  - `isGLB_unitNodeEnergies`: RH ⟹ inf E_m = Λ(m) for every m ≥ 2. This is log p at m = p^k and 0 at every other m.
  - `not_bddBelow_unitNodeEnergies`: ¬RH ⟹ E_m is unbounded below, for every m.
  - `riemannHypothesis_iff_bddBelow_unitNodeEnergies`: RH ⟺ E_m is bounded below, for any single m (e.g. m = 2).
  - Proof: the lower bound is W_Λ ≥ 0; sharpness comes from unique repair; unboundedness comes from ¬PBAP plus a
    normalized pair test.
- **Meaning.** Under RH, the archimedean place computes the primes: Λ(m) is the least archimedean energy that puts unit
  mass at the single node log m. RH is one inequality, inf E_2 > −∞.
- **[P] Attainment (not formalised).**
  - Take an arc measure annihilating the twisted moments M_n for n ≥ 1 but not M_0. The stream-function dual proof
    covers combinations with a₀ = 0, so such a measure exists if the annihilator of modes ≥ 3 is not that of modes ≥ 2.
  - Its Ξ-divisible test is blind off log 2, and W_Λ = 0 unconditionally, so A = log 2·L_2: an unconditional element
    of E_2 with energy exactly log 2.
  - So RH ⟺ this explicit modular witness minimises E_2. Same tightness as PBAP. The open core is the lower bound.
- **Status of the RH core.** Every reformulation this session (node criticality, unique repair, unit-node energy) is
  an exact equivalence with the twisted-arc witnesses as extremisers. No producer for the lower bound yet: walls 5, 8,
  11. The modular transfer only reaches Ξ-divisible tests (R = Ĝ/Ξ² holomorphic), and on those A is attained.

## Row 235 — direct attacks on inf E_2 > −∞ (PBAP): four mechanisms, all reduce to known walls
- **C252 (Farey–Möbius face of blindness) [P].**
  - Put g(y) = G(log|y|) and take its additive Fourier transform ĝ. Poisson summation for g(·m), plus Möbius inversion
    over denominators, gives: G is blind at every log n (n ≥ 2) ⟺ Σ_{a∈ℤ, (a,q)=1} ĝ(a/q) = 2G(0)μ(q) for every q ≥ 1.
  - So PBAP reads: A(G) ≥ 0 for PD G whose primitive Farey sums are exactly 2G(0)μ.
  - This bridges HF to the Farey/Franel–Landau and Möbius (MC) lanes. Verdict: BRIDGE, a re-encoding of μ with no
    positivity mechanism.
- **C253 (product closure) [P].**
  - The blind cone is an ideal under pointwise products with PD functions (Schur).
  - The Lévy jump energy satisfies the Leibniz bound ℰ(G₁G₂) ≤ G₁(0)ℰ(G₂) + G₂(0)ℰ(G₁).
  - Powers G^k of a hypothetical negative certificate become positive by high-frequency growth; no contradiction.
  - Verdict: FALSE as a producer (only upper bounds on A of new tests).
- **Krein local extension.**
  - RH ⟺ W_a ≠ ∅ at every aperture a. A local lemma W_a ≠ ∅ ⟹ W_{a+δ} ≠ ∅ would need the PD extension on
    (2a, 2a+2δ) to have the form "A minus atoms at log n".
  - This is route RW, with known saturation at small apertures.
  - Quantitative reading: a quadruple at depth δ is compensated by on-line neighbours only if δ ≪ zero spacing
    (~2π/log γ). The classical zero-free region is borderline, which is wall 1 and the WL lag threshold.
  - Verdict: REDISCOVERED (RW/WL).
- **Modular transfer of general tests.**
  - The divisor transfer reaches only Ξ-divisible tests (R = Ĝ/Ξ² holomorphic), and A is attained (= 0, or
    = Λ(m)L_m) exactly on those.
  - For general tests R has poles at zeros, and the transfer returns the zero sum.
  - Verdict: CIRCULAR.
- **State.** The RH core in the HF route is the single inequality inf E_2 > −∞ (equivalently PBAP or Weil positivity).
  Walls 1, 5, 8 and 11 apply. Next: a positivity mechanism that distinguishes prime powers (wall 11) and is not a
  density/Nyquist count.

## Row 236 — infinite divisibility (wall 6, rediscovered) and the tangent cone at the witness
- **C254 (Lévy–Khintchine route).**
  - For σ > 1, ζ(σ+it)/ζ(σ) is an infinitely divisible characteristic function, with Lévy measure on log p^k and masses
    p^{−kσ}/k. This sees exactly the prime powers, so it would pass wall 11.
  - For σ > ½ the Steinhaus/Bohr–Jessen model reproduces only the value distribution, not exact positivity.
  - At σ = ½ positive-definiteness is lost.
  - The corpus has this: `CriticalPrimeTailEulerLogPositiveDefinite` (safe passivity, off the line) and
    `EulerActivationLevelCascade` (the critical line is the level-two boundary).
  - Verdict: REDISCOVERED (walls 6/7).
  - Interrogation: the archimedean part is itself Lévy–Khintchine:
    - Ω(t) − Ω(0) = ∫(1 − cos tu)ω(u)du, so on blind PD φ with φ(0) = 1,
      A = Ω(0) + 2∫ω(1−φ) + pole(φ).
    - The jump part is ≥ 0, Ω(0) = −|A(0)| < 0, and pole(φ) = 2π(m(i/2) + m(−i/2)) is the spectral density at
      complex points. That pole term is the only sign-indefinite part.
    - So PBAP ⟺ jump energy + pole term ≥ |A(0)| on blind PD φ. This is the PD uncertainty form already in memory
      (≈5.3 relaxed versus 5.372).
- **C255 (tangent cone at the witness) [P].**
  - The twisted-arc witness φ* has spectral density m* = |Ξ|²R*, which vanishes exactly at the real zeros, and
    A(φ*) = 0.
  - Since A is linear, PBAP ⟺ A ≥ 0 on the closed tangent cone of K at φ*.
  - That cone consists of blind ψ of any sign whose density is ≥ 0 at the real Ξ-zeros, plus decay and closure
    conditions.
  - So the continuum constraint m ≥ 0 on ℝ is replaced by the discrete constraint m_ψ(γ) ≥ 0 at real zeros. Off-line
    zeros are invisible to the tangent cone, which is where the RH content sits.
  - The closure (uniform ε near infinitely many zeros, tail decay) is technical.
  - Verdict: equivalent reformulation, content RH (CIRCULAR as a producer).
- **State.** Unchanged: the core is inf E_2 > −∞. Candidate mechanisms must pass walls 2 (|ζ|² versus zero sums), 6/7
  (absolute convergence or statistics) and 11 (prime-power sensitivity) simultaneously.

## Row 237 — Hecke positivity on the modular side: rediscovered; the resonance-width reading
- **Corpus.** `EisensteinHeckeResonantMoment` and `EisensteinHeckeSecondMoment` [L].
  - The truncated resonant state Λ^Y E_u at a zeta zero ρ = 1 + 2u has exact Hecke data: mean p^u + p^{ū} and variance
    2(1 − p^{2 Re u}) = 2(1 − p^{β−1}).
- **Reading.**
  - Resonance width η = (1 − β)/2. RH ⟺ every modular resonance has width ¼ (Pavlov–Faddeev).
  - For an off-line pair (β, 1 − β), the mean Hecke variance is 2 − p^{−½}(p^δ + p^{−δ}) = 2(1 − p^{−½}) − 2p^{−½}(cosh(δ log p) − 1),
    with δ = β − ½. So off-line pairs carry strictly less Hecke variance than on-line ones.
- **C256.** A sum rule "average Hecke variance over resonant states ≥ 2(1 − p^{−½})" would give RH.
  - Attack: the only sum rules over resonances are Hecke-twisted Selberg trace formulas. Their spectral side is the
    explicit formula twisted at p, with the off-line deficit 2p^{−½}(cosh(δ log p) − 1).
  - That deficit is Weil's cosh term, so the inequality is Weil positivity restricted to the p-twisted tests.
  - Bhatia–Davis and the operator-norm bounds (‖T_p‖ on the complement of constants, Kim–Sarnak 7/64) hold for every
    β ∈ (0, 1). They carry no information.
  - Verdict: CIRCULAR (walls 8/5). The Hecke structure supplies prime-power sensitivity (wall 11) but its positivity
    is again the explicit formula.
- **Session state after rows 233–237.**
  - The HF route is exactly RH ⟺ PBAP ⟺ inf E_2 > −∞, all in Lean.
  - Attacks tried, each killed with a recorded reason: Farey–Möbius, product closure, Krein extension, modular
    transfer, infinite divisibility, tangent cone, Hecke variance.
  - The missing mechanism must produce a sum-rule inequality over zeros or resonances from a source outside the
    explicit formula: a geometric Hodge index (wall 5) or an exact identity at σ = ½ that is not a |ζ|² moment
    (wall 2).

## Row 238 — searching for a modular transfer of general blind tests: constant terms versus Fourier coefficients
- **Constant-term route (Maass–Selberg).**
  - ‖Λ^Y E(·,½+it)‖² ≥ 0 gives positivity of 2 log Y − φ′/φ(½+it), with φ(s) = ξ(2s−1)/ξ(2s). That is a statement
    about ξ′/ξ on Re s = 1.
  - This is the edge of absolute convergence (Sarnak's nonvanishing on Re s = 1; wall 6).
  - Reaching Re ξ = ½ this way needs Eisenstein parameters at Re s = ¼, which are non-unitary: no norm, no positivity.
  - Verdict: wall 6. The Langlands–Shahidi-type edge is structural.
- **Fourier-coefficient route (Hecke).**
  - E(z,½) ≡ 0 for SL₂(ℤ). Its s-derivative F₀ has coefficients d(n)·√y K₀(2πny), and its Hecke L-function is ζ(w)²,
    whose critical line is the unitary point.
  - **This is why TMP could reach critical-line statements:** the twisted arc moments are the K₀ modes of F₀, and
    the divisor transfer is its Hecke L-function.
  - The reach is limited to tests whose spectrum carries the factor ξ² (Mellin of F₀). For a general blind test,
    Ĝ/ξ² has poles at the zeros, and the transfer returns the zero sum.
- **[P] Structural statement (new reading).**
  - Modular positivity reaches the critical line only through Hecke L-functions of unitary Eisenstein data (ζ² at
    s = ½). The resulting tests are Ξ²-divisible, which is exactly the null face of PBAP.
  - So modular maximum principles produce the extremisers, not the lower bound.
  - A lower bound would need a modular object whose Hecke L-function is a positive multiple of ζ²·(1/ζ²-type
    corrections) on the line. Equivalently, a PD kernel whose Mellin transform divides out ξ². That is the
    zero-faithfulness wall.
- **Next.** Either (i) a positivity source that is not modular, or (ii) a second-order modular object: variations of
  the witness family (s-derivatives beyond F₀, i.e. ∂_s²E at s = ½, whose Hecke data involve d(n) log n) and whether
  log n weights can carry Λ = μ ∗ log.

## Row 239 — C257: the second s-derivative of E at s = ½ carries the first Laguerre expression (route LA)
- **[P] Identification.**
  - The Hecke L-function of E(z,s) is ζ(w+s−½)ζ(w−s+½).
  - Its first s-derivative at s = ½ vanishes identically; that object is F₀, the source of TMP (d(n)K₀ modes).
  - Its second s-derivative is 2(ζζ″ − ζ′²)(w) = 2ζ²(log ζ)″. Λ enters through (log ζ)″ = Σ Λ(n) log n·n^{−w}.
  - After completion, ξξ″ − ξ′² on the critical line is exactly the first Laguerre expression
    c₂(t) = Ξ′² − ΞΞ″ = Ξ²Σ_ρ(t − γ_ρ)^{−2} (corpus `xiSliceCoeff_two_eq_laguerre`).
  - So the second-order modular object is to route LA what F₀ is to route HF.
- **Status of the target in the corpus.**
  - First Laguerre for all t is weaker than RH (`H:FirstLaguerreNotRealRooted`).
  - It fails on |t − γ| ≤ δ/2 around any isolated off-line pair (`laguerre_re_neg_near_offLine_pair`). So
    "first Laguerre for all t" would exclude every isolated near-line off-line pair: a strong partial RH.
  - The corpus also has `XiRealCriticalPointSignLaw`: RH ⟺ ξ′ ≠ 0 on Re s > ½ ∧ ΞΞ″ < 0 at real critical points.
- **Attack.**
  - TMP-type modular arguments produce existence statements (a positive annihilating measure), dual to "no positive
    certificate".
  - First Laguerre is a pointwise sign of an explicit function. c₂ = ∫L(w)e^{itw}dw with Laguerre kernel
    L(w) = ½∫(2u − w)²Φ(u)Φ(w − u)du ≥ 0, so c₂ is positive definite in t, which does not give pointwise positivity.
  - There is no cone duality to transfer the max-principle mechanism.
  - The frontier map already excludes generic first-Laguerre/finite-moment positivity as a producer.
  - Verdict: REDISCOVERED (route LA). The modular identification is new but gives no mechanism.
- **Lesson.** The modular arc machinery proves cone or existence statements (the positive annihilator, TMP). The RH
  core in every route is a cone-positivity of the opposite type: a nonempty dual cone (PBAP) or a pointwise sign
  (LA). Max-principle arguments give the former; nothing in the corpus gives the latter.
- **Correction and sharpening of the lesson (wall 12, forced dual measure).**
  - PBAP does have a TMP-like "no certificate" form: no PD blind G with A(G) < 0.
  - Its Gordan dual is a positive measure on the spectral line representing A modulo the blind constraints.
  - By uniqueness (Weil cone = {Λ}) and the corpus boundary-measure atomicity (`WeilConeNullAtomicSpectrum`), that
    measure is forced to be the critical-zero counting measure.
  - In TMP the dual positive object κ lived on a geometric arc and could be built from potential theory. In PBAP it is
    pinned to the zeros themselves.
  - So any PBAP producer is a construction of the zero-counting measure as a positive measure: a spectral realisation
    (Hilbert–Pólya type).
  - This is why every route of rows 233–239 terminated at the explicit formula.

## Row 240 — wall 12 against the corpus operator machinery: Krein/Pontryagin reading
- **Corpus.** Spectral realisations exist only as RH-equivalences (receivers), for example:
  - `XiHedenmalmReciprocalOperator.xiReciprocalOperator_isSelfAdjoint_iff_rh`;
  - `SuzukiHilbertPolya`;
  - the de Branges gauge modules (`DeBrangesExplicitGammaGauge`, `DeBrangesHTGaugeSaturation`);
  - the FZZ Krein operators (formally self-adjoint, with no definiteness).
  - None produces definiteness.
- **C258 (Pontryagin bound from the witnesses).**
  - Unconditionally W_Λ is a Krein form whose negative index κ counts the off-line zeros.
  - In a Pontryagin space Π_κ every neutral subspace has dimension ≤ κ, so a large neutral family would bound κ.
  - Attack: the Ξ-divisible witnesses satisfy W_Λ(F, H) = Σ_ρ F̂(γ_ρ)·(…) = 0 for every H. They lie in the radical,
    not in a neutral subspace, and the bound does not apply.
  - Blind subspaces have infinite codimension, so the restriction bound κ(W|_B) ≥ κ − codim is empty.
  - Verdict: FALSE as a producer.
- **Survivor (receiver only, not pursued).**
  - The aperture negative index κ(A) (negative squares of W_Λ on tests supported in [−A, A]) is nondecreasing.
  - RH ⟺ κ(A) = 0 for all A, and κ(A) = 0 for small A (RW).
  - Bounds κ(A) ≤ C e^{cA} from zero density would be receivers.
- **State.** Wall 12 stands. A producer needs an operator or geometry whose definiteness is proved independently of the
  explicit formula. The corpus contains none, and all its spectral realisations are equivalences.

## Row 241 — the general-test modular dictionary exists (Mayer at s = ½); wall 13: Bochner cone versus pointwise cone
- **Corpus.** `BlindCoreMayerTransferHalf`: for compact dilation cores, integer blindness ⟺ the inhomogeneous Mayer
  transfer equation (1 + σ)L_{½}Q_{A_f} = a + b cos 2πx of the Gauss map at the centre of the critical strip.
  - So general blind tests do have a modular-dynamical dictionary: the boundary dynamics of the modular surface, whose
    Fredholm determinant is the Selberg zeta function, with resonances at ρ/2.
- **C259 (Perron–Frobenius route).**
  - L_s has a positive kernel, so Ruelle–Perron–Frobenius positivity and the minimum principle of TMP act on
    pointwise-positive cones.
  - Attack: PBAP's cone is the Bochner cone (Ĝ ≥ 0). Under the arc and Mehler–Fock dictionary it becomes
    Mehler–Fock-positive distributions, i.e. Bochner–Godement positive-definite zonal functions.
  - Those are not pointwise-positive arc measures.
  - The two cones meet exactly in the nonnegative-core sector (f ≥ 0). There the corpus already reduces PBAP to the
    one-window inequality (`PrimeBlindNonnegativeConeReduction`), which is non-RH, numerically true and still a Prop.
  - Verdict: positivity methods on pointwise cones reach only the nonnegative-core sector.
- **Wall 13 (cone mismatch).**
  - TMP succeeded because (N1) is a pointwise-cone statement: a positive measure on the arc annihilating moments.
  - PBAP is a Bochner-cone statement. Maximum principles, transfer-operator positivity and Perron–Frobenius preserve
    pointwise cones only.
  - A PBAP producer needs a positivity-transfer from the Bochner cone to a pointwise cone that commutes with
    blindness. That amounts to the spectral realisation of wall 12.
  - The only sector where both cones coincide (nonnegative cores) is non-RH.
- **Concrete non-RH Lean target identified (lower priority).** Prove `WindowPositive` (the Weil energy inequality
  for nonnegative h on (0, log 2), margin ≈ 0.15) without computation. That would make PBAP unconditional on the
  nonnegative-core sector. Wall 11 suggests this sector carries no RH content.

## Row 242 — wall 13 bridge attempts; WindowPositive feasibility (paper)
- **Bochner→pointwise maps that commute with blindness.**
  - G ↦ G² (Schur) keeps PD and blindness and is pointwise ≥ 0. But A(G²) is not controlled by A(G): a negative
    certificate does not transport. KILLED.
  - G ↦ G(0) ± G is pointwise ≥ 0 but breaks blindness by a constant at every node. KILLED.
  - Modulations G·cos(s·) keep PD and blindness but push A to +∞. Useless.
  - No linear transfer commutes with blindness and carries A, consistent with wall 13.
- **[P] WindowPositive analysis (non-RH sector, for the record).** Constants:
  - A(0) = ψ(¼) − log π = −γ − π/2 − 3 log 2 − log π ≈ −5.3721;
  - ω(x) = Σ_k e^{−(2k+½)x};
  - for h ≥ 0 on (0, L), L = log 2: RHS = 2∫_L^∞ω + 2∫_0^L[ω(1−c) + 2c cosh(x/2)], where c is the normalised
    autocorrelation.
  - **Pointwise relaxation** (c ∈ [0,1], ignoring that c is an autocorrelation):
    - minimum = 2Σ_k 2^{−(2k+½)}/(2k+½) + 2∫_0^L min(ω, 2cosh(x/2)) ≈ 2.994 + 2.222 = 5.216 < 5.372;
    - the crossover is at ω = 2cosh(x/2), x* ≈ 0.28.
  - So the PD/autocorrelation structure must supply about 0.16 (3%). This matches "relaxations fall short".
  - **Feasible proof route:**
    - the corpus pole-vanishing ground energy at aperture ½log 2 is ≥ 1/10
      (`PoleVanishingWeilPositivityHalfLogTwo`, computer-free enclosure certificate);
    - add the explicit 2-dimensional pole complement span(e^{±x/2}·1_{(0,L)}) and use ℓ₊(h)ℓ₋(h) > 0 for h ≥ 0;
    - this gives a 3×3 positivity with explicit integrals of exponentials against ω.
  - Value: makes PBAP unconditional on the nonnegative-core sector, a non-RH sector (walls 11, 13).
  - Status: recorded target, not started. Its value for the RH core is low.

## Row 243 — semigroup, trace-formula and pseudo-Laplacian attempts at wall 12
- **Semigroup structure of the nodes.**
  - log ℕ_{≥2} is closed under addition, so blind G has translates τ_{log m}G that vanish on all of log ℕ_{≥1}.
  - Translates are not PD. Even symmetrisation G(·+log m) + G(·−log m) meets uncontrolled values at log(n/m).
  - The blind cone is a multiplicative ideal (Schur), but A is not monotone under products.
  - Verdict: no positivity mechanism.
- **Selberg trace formula for SL₂(ℤ).**
  - The spectral side is positive unconditionally: Maass r_j are real at level 1, and −φ′/φ(½+ir) is a sum of
    positive Poisson kernels over the resonances ρ/2, all with Re < ½ regardless of RH.
  - So trace-formula positivity holds for every zero configuration and carries no RH information.
  - The ζ zeros enter only as resonances: non-unitary, off the spectral axis.
  - Verdict: wall 6/12.
- **Pseudo-Laplacian / Lax–Phillips.**
  - Pseudo-Laplacian eigenvalues solve φ(½+ir) = −a^{2ir}: unitary, but they are not the zeros.
  - The Lax–Phillips generator has the resonances as spectrum, but it is not self-adjoint. RH ⟺ that spectrum lies on
    one line.
  - Verdict: no realisation with forced definiteness. The modular surface realises the ζ zeros only as resonances.
- **Structural conclusion.**
  - The unitary objects attached to SL₂(ℤ) (Maass spectrum, Eisenstein continuous spectrum, Hecke Ramanujan edge)
    are definite but blind to the zeros.
  - The objects that see the zeros (resonances, scattering poles, truncated resonant states) are non-unitary.
  - TMP used the one bridge, the F₀ Hecke L-function ζ², which reaches only the null face.
  - Wall 12 at level 1 is therefore "resonance versus eigenvalue".

## Row 244 — corpus definiteness sources outside level-1 unitary spectrum: Deninger and CCM/prolate
- **Deninger Calderón–Koszul** (`DeningerArithmeticPositiveCalderonKoszul`): finite-dimensional linear algebra in which
  a positive Dirichlet-to-Neumann operator is assumed. No arithmetic source of positivity. Verdict: receiver
  infrastructure (wall 5).
- **CCM / prolate.**
  - The prolate operator is self-adjoint for free (it commutes with time-band limiting).
  - Small-aperture restricted Weil positivity comes from certificates (`PoleVanishingWeilPositivityHalfLogTwo`).
  - Killed-routes ledger: no-go-100 (prolate parameters cannot share the required unitary transport), CANNOT-03 /
    HARD LOCK P (positivity alone supplies no upper bound), DG-PRIME-CD0 (cutoff-prime curvature unbounded below).
  - Matching prolate eigenvalues to the zeros is a spectral identification. It is not supplied by self-adjointness,
    and the corpus has it only asymptotically or numerically.
  - Verdict: REDISCOVERED; walls 12 and 13 stand.
- **Saturation statement.**
  - Every corpus source of definiteness is one of four kinds:
    - assumed (Deninger packets);
    - certified at small aperture only (RW/CCM);
    - unitary but blind to the zeros (SL₂(ℤ) spectrum, the Selberg trace formula);
    - a pointwise cone (TMP, Mayer, Perron–Frobenius).
  - None meets CANNOT-535 to 537 together. A PBAP producer needs a definiteness source of a new kind.

## Row 245 — candidate new definiteness kinds: local Euler factors, Schoenberg total positivity, and the WindowPositive margin
- **Local Euler factors are Bochner-positive and prime-power supported.**
  - |1 − p^{−½−it}|^{−2} is a Poisson kernel; its Fourier measure is Σ_k p^{−k/2}δ_{±k log p} + δ₀ ≥ 0.
  - So each local factor is PD in t and sits exactly on the p-power nodes. This would pass walls 11 and 13 locally.
  - Finite products are |Σ_{P-smooth} n^{−½−it}|², with positive Fourier measure on log(m/n).
  - Pairing with blind Ĝ ≥ 0: the integer-ratio terms vanish, and the remaining terms at non-integer ratios are
    uncontrolled. The infinite product diverges on the line (wall 6), and ζ(½+it) is not infinitely divisible
    (Lévy mass Σ_p p^{−½} = ∞).
  - Verdict: local definiteness exists, but the global product is lost at σ = ½.
- **Schoenberg / total positivity (TP_∞).**
  - RH ⟺ Ξ ∈ LP ⟺ the reciprocal is the bilateral Laplace transform of a Pólya frequency function: a TP kernel of
    every order. This is a definiteness kind beyond Bochner.
  - The archimedean factor is PF (Γ(s) = ∫e^{sx}e^{−e^x}dx is log-concave, and 1/Γ ∈ LP).
  - The arithmetic factor 1/ζ = Σμ(n)n^{−s} is the transform of a signed measure, so it is not PF. TP of the convolution
    would itself be the RH content.
  - The corpus LA route excludes Laguerre–Pólya preimages under polynomial symbols (`XiRealRootedPolynomialPreimage`)
    and multiplier sequences (`RiemannKernelMomentsNotMultiplier`).
  - Verdict: equivalent reformulation, no mechanism.
- **WindowPositive margin, quantified further.**
  - The PD doubling inequality 1 − C(2x) ≤ 4(1 − C(x)) forces 1 − C(x) ≥ (x/2L)².
  - That recovers only ≈ 0.007 of the 0.156 gap. The true margin needs the full Bochner structure of C, which is
    where the corpus's √2 trace certificate does its work.
  - A Lean proof would need certified enclosures (norm_num). Recorded, not started.

## Row 246 — [L] interpolating RH criteria, including a single-prime Weil criterion
- **[L] Added to `RHTower/PrimeBlindNodeCriticality`** (standard axioms; `lake --old` clean for this module and for the
  dependent `ArchimedeanUnitNodeEnergy`):
  - `riemannHypothesis_iff_repairedBlindPositive_vonMangoldt S`: for every node set S, RH ⟺ the Weil functional with
    weights Λ off S is ≥ 0 on the S-blind cone. S = ∅ is Weil's criterion; S = ℕ is PBAP.
  - `riemannHypothesis_iff_singlePrimeWeilPositive p`: RH ⟺ the archimedean part plus the Euler factor at one prime p
    (weights Λ(p^k)) is ≥ 0 on combinations blind at every node that is not a power of p.
- **Reading (globalised local Euler positivity).**
  - The single local factor at p is Bochner-positive with spectrum on the lattice log p·ℤ.
  - The single-prime criterion says RH is "archimedean + one local factor" positivity on tests tiling at every
    other prime period 2π/log q.
  - The remaining infinitely many constraints are the tiling conditions, not Euler factors.
  - Open: whether tiling at all q ≠ p plus the explicit τ_p-periodic weight log p·(P_p − 1) admits a direct positivity
    proof. Pointwise, Ω − log 2·(P_2 − 1) ≈ −8.7 at t = 0, so the tiling conditions must carry the argument.

## Row 247 — single-prime criterion at p = 2: averaging and lattice decomposition (both circular)
- **Averaging that preserves tiling.**
  - The operators that preserve blindness at every node and the PD cone are exactly Schur multiplication by a PD φ.
    On the spectral side this is convolution Ĝ ↦ Ĝ ∗ ν with ν a probability measure.
  - A reduction "W₂(G) ≥ W₂(Gφ) ≥ 0" needs W₂ − W₂∘M_φ ≥ 0 on the same cone: a positivity statement of the same type.
  - The difference splits into an Ω-smoothing term (Jensen: favourable where Ω is concave, unfavourable near t = 0
    where Ω is convex), a pole difference, and Σ_k c_k G(k log 2)(1 − φ(k log 2)). All are sign-indefinite.
  - Verdict: CIRCULAR.
- **Dyadic lattice decomposition.**
  - G = G_lat + G_blind, where G_lat interpolates the lattice values G(k log 2) with a fixed PD bump vanishing at the
    other nodes.
  - Then W₂(G) = W₂(G_lat) + A(G_blind) + cross terms. A(G_blind) ≥ 0 is PBAP itself.
  - Verdict: CIRCULAR.
- **State.** Cycles 235–247 have exhausted the corpus mechanisms and the natural new ones (Farey, Euler-local,
  Schoenberg TP, Hecke, Mayer, trace formula, Pontryagin, averaging). Each has a recorded kill. The RH core stands as
  in STATUS MUST-1437–1440 and CANNOT-535–537.

## Row 248 — single-test form via Boas–Kac: self-orthogonality and Steinhaus mimicry
- **[P] Reduction.**
  - In dimension 1, every compactly supported PD function is a single autocorrelation g ⋆ g̃ with supp g in half the
    support (Boas–Kac / Krein).
  - So PBAP is equivalent to: ⟨f, A f⟩ ≥ 0 for every single f with ⟨f, f(· + log n)⟩ = 0 for all n ≥ 2.
  - This is positivity of a quadratic form on an intersection of quadrics: f is self-orthogonal under every log-integer
    translation.
  - Regularity caveat: the factor g is in L², not C², so the corpus decay-class extension would be needed to close it.
- **Steinhaus reading.**
  - The normalised spectral measure μ = |f̂|²dt/‖f‖² integrates every Dirichlet polynomial to its constant term,
    exactly as the Steinhaus (Haar) measure on the infinite torus does.
  - So PBAP reads: "every Steinhaus-mimicking spectral measure of compact type has ∫Ω dμ + pole ≥ 0".
  - The heuristic "mimicry forces spread, and spread forces ∫Ω ≫ 0" is a density argument, killed by wall 11. Deleting
    one node destroys mimicry at a single character, yet negativity appears.
- **Verdict.** REFORMULATION. The Boas–Kac formalisation (Krein–Akhiezer factorisation of nonnegative exponential-type
  functions) would only give PBAP ⟺ single-test PBAP. Not pursued.

## Row 249 — frontier-wide scan of "Needs" lines for a non-RH-hard producer gap
- I scanned the "Needs" line of every live route and candidate in the frontier map.
- Almost every route's missing step is recorded as the Weil-positivity receiver, explicit-formula balance or
  zero-side vanishing ("Core (rows 564/707/714)"). That is wall 12 seen from each route.
- The only quantitative non-RH milestone is TG's "Gaussian central-gap bound, first milestone < 1/4".
  - By `GaussianCentralGapRatePowerSaving`, rate e^{sε}√ε ⟺ every zero has b + b²/8 ≤ s (b = Re ρ − ½).
  - So s < 1/4 is a zero-free strip Re s < ¾ + O(s²): a quasi-Riemann hypothesis, beyond the Vinogradov–Korobov exponent
    1/4 that the corpus already owns.
  - No zero-free strip of any positive width is known. Verdict: quasi-RH hard, not a tractable sub-producer.
- **Conclusion.** The corpus frontier sits at RH or quasi-RH hardness in every route. In the HF route the TMP
  formalisation removed the last non-RH gap ((N1)). What remains anywhere is a genuine new positivity mechanism,
  constrained by walls 11–13.

## Row 250 — C260: continuity method in the archimedean shift (new framing; dies at the integrality wall)
- **Setup.**
  - Deform only the Gamma factor: Γ_ℝ(s) → Γ_ℝ(s+a), so A_a has spectral density Re ψ(¼ + a/2 + it/2) − log π.
  - Keep the pole terms and the blindness set log ℕ fixed. PBAP(a) is the deformed statement; RH ⟺ PBAP(0).
- **Continuity scheme.** Let a₀ := inf{a ≥ 0 : PBAP holds on [a, ∞)}.
  - (1) PBAP(a) for all a ≥ a* (plausible, non-RH). Blindness at the dense nodes log n kills the large-|x| pole mass,
    and Ω_a ≈ log(a/2) dominates.
  - (2) Openness: strict PBAP at a ⇒ PBAP near a, since |A_a − A_{a−δ}|(G) ≤ Cδ·G(0). Non-RH.
  - (3) Closedness: pointwise limits.
  - Hence a₀ > 0 forces PBAP(a₀) to hold tightly: inf over normalised blind G of A_{a₀}(G) = 0.
  - Under RH: a₀ = 0. The witness G* is tight at a = 0, D_a(G*) > 0 for small a, and compactness makes PBAP(a) strict
    on (0, ε).
  - Note: Re ψ(x+iy) decreases in x near x = ¼ at large y (Re ψ′ ≈ −1/(4y²)), so A_a is not spectrally monotone in a.
    This is why a₀ is defined via [a, ∞).
- **Crux (step 4): no tight threshold at a₀ > 0.**
  - At a tight point a minimiser (pole-budget compactness, corpus) is a null blind test. Every cone point's boundary
    measure is then atomic on its real zero set (corpus `WeilConeNullAtomicSpectrum`).
  - So λ ∈ W(a₀) gives a Herglotz Dirichlet series: L := exp(Σλ_n n^{−s}/log n) is holomorphic and zero-free on
    Re s > ½, with archimedean data Γ_ℝ(s+a₀).
  - The hoped-for contradiction was a Hamburger/Hecke converse theorem: no L-function with FE for Γ_ℝ(s+a₀), a₀ ∉ {0, 1}.
  - **Attack:** threshold objects need not be L-functions.
    - Herglotz Dirichlet series exist for every a with W(a) ≠ ∅ (fat cones at large a, e.g. λ = 0). They carry no FE.
    - Their boundary atoms are integers only if L continues meromorphically across the line. That is the corpus
      integrality gap ("integrality of the atoms of μ_λ on {F̂=0}"; memory archimedean-integrality-obstructions).
- **Verdict.** FALSE as a producer: step 4 has no mechanism and reduces to the archimedean integrality wall.
  Positive survivors (non-RH, recorded as possible Lean targets):
  - (1) large-a PBAP;
  - (2) openness of strict PBAP in a;
  - the reformulation RH ⟺ [no tight point of the shifted-Gamma blind problem in (0, ∞)] ∧ (1).

## Row 251 — integrality of atoms at the C260 threshold: the corpus's closed integrality-anchor route
- **Corpus.** The integrality-anchor law (ULF-INT-001, closed after a nine-candidate loop; CANNOT-186/187, MUST-122) and
  the archimedean-integrality obstructions manuscript.
  - Remaining honest directions recorded there: "an F₁ object without characteristic polynomial (test-function-side
    integrality), or a genuinely new one-signed datum".
- **Attempt.** Test-function-side integrality: the blind nodes are logarithms of integers, so does blindness force the
  boundary atoms w_γ of a tight minimiser to be integers?
  - L := exp(−∫D), with D the Dirichlet series of λ ∈ W(a₀).
  - The pole term fixes the residue at s = 1 to be 1, so L ~ (s−1)^{−1} there (normalisation c = 1).
  - At the atoms, L ~ (s−ρ)^{w_γ}. Integrality ⟺ L is single-valued across the critical line.
  - That needs analytic continuation of L past Re s = ½ (an FE or equivalent). Blindness constrains G's values at
    log n, not the continuation of L.
  - Real-coefficient Dirichlet series with meromorphic continuation can carry arbitrary real residues on the line
    (c·ζ′/ζ-type, c ∉ ℤ), and nothing at the threshold fixes c at the zeros separately from s = 1.
- **Verdict.** REDISCOVERED (integrality-anchor wall). C260's step 4 stays closed.
- **Session-level conclusion (rows 233–251).**
  - All PBAP attacks end at one of three known walls:
    - the explicit formula / forced dual measure (12);
    - the cone mismatch (13);
    - archimedean integrality (F₁).
  - Node criticality (11) constrains every remaining candidate.

## Row 252 — C260 step 1 (PBAP(a) for large a) analysed: not elementary, needs off-line zero control
- **Lévy form.** With x = ¼ + a/2:
  - Ω_a(t) = ψ(x) − log π + ∫_0^∞ ω_a(v)(1 − cos tv)dv, where ω_a(v) = 2e^{−(½+a)v}/(1 − e^{−2v});
  - A_a(G) = (ψ(x) − log π)G(0) + ∫ω_a(G(0) − G) + pole(G).
  - The first term is ≈ log(a/2)·G(0), the jump term is ≥ 0, and the pole term is sign-indefinite.
- **Narrow-bump family.**
  - f = φ(·−R) − φ(·+R) is blind if the width is ≲ e^{−2R}.
  - Then pole/G(0) ≈ −w e^R ≳ −e^{−R}: bounded.
- **Bandwidth heuristic.**
  - PD Lipschitz control gives |G| ≲ √B·e^{−x} beyond x ≈ ½ log B (B = spectral second moment).
  - But on [0, ½ log B] only |G| ≤ G(0) is available, so |pole| ≲ B^{1/4}G(0), against a jump gain of only ~log B.
  - So no elementary bound. Under RH the pole is bounded below by −|Ω_0(0)|G(0), because A_0 ≥ 0 on blind tests. The
    B^{1/4} scenario is not realised, but proving that unconditionally means controlling the off-line zero sum on
    blind tests.
  - Equivalently, PBAP(a) for large a ⟸ Σ_{off-line} Ĝ(γ_ρ) ≥ −K·G(0) − (jump) on blind tests. This is a
    zero-density-type estimate combined with narrowness from blindness.
  - Non-RH, but a substantial analytic theorem.
- **Verdict.** C260's survivors are not cheap. With step 4 dead (row 251), C260 is closed.

## Row 253 — WindowPositive: exact value at the flat profile (paper evaluation)
- **Flat profile.** h = 1_{(0,L)}, L = log 2, c(x) = 1 − x/L.
- **Terms of F(h) = 2∫_L^∞ω + 2∫_0^L[ω(1−c) + 2c cosh(x/2)]:**
  - 2∫_L^∞ω = 2Σ_k 2^{−(2k+½)}/(2k+½) ≈ 2.9937.
  - ∫_0^L ω·x/L = (1/L)Σ_k [1 − e^{−β_kL}(1+β_kL)]/β_k², with β_k = 2k+½. This is ≈ 0.4027/L ≈ 0.5810.
  - 2∫_0^L(1 − x/L)cosh(x/2) = 2[2 sinh(L/2) − (2L sinh(L/2) − 4cosh(L/2) + 4)/L] ≈ 0.7001.
  - Total F(flat) ≈ 2.9937 + 2(0.5810 + 0.7001) ≈ 5.556 > |A(0)| ≈ 5.3721, a margin of 0.184.
- **Bracketing.**
  - The flat profile gives 5.556. The pointwise relaxation gives a lower bound of 5.216.
  - The true minimum lies in between; the corpus records margin ≈ 0.15, so the minimum is ≈ 5.52.
  - An analytic proof must certify a lower bound ≥ 5.3721 over all autocorrelation profiles of nonnegative functions.
    This is a copositive variational problem with a 3% gap.
- **Status.** The target stays recorded. A hand-designed certificate is not feasible without computation, and the
  sector carries no RH content (CANNOT-535).

## Row 254 — |ζ|²-weighted positivity on blind tests versus the zero sum (wall 2, rediscovered)
- **Input.** Corpus identity (HF, `CosDilationKernelPositivityRigidity`): blind cores satisfy
  ∫|ζ(½+it)𝓜f(½+it)|²dt = 2πΨ_f(1) ≥ 0. This is an exact |ζ|²-positivity on the blind cone.
- **Attempt.** Link it to A(G) = Σ_ρ Ĝ(γ_ρ) through log-concavity:
  - Jensen: ∫ log|ζ|² dμ ≤ log ∫ |ζ|² dμ;
  - Poisson–Jensen: zero sums are ∫∫ log|ξ|·ΔH.
- **Kill.** Mean-square (|ζ|²) control bounds log|ζ| averages from above. Jensen's formula then turns this into upper
  bounds on zero counts (density estimates N(σ,T)), never a count of exactly zero. Excluding all off-line zeros needs
  equality in Jensen, which no moment method gives.
- **Verdict.** REDISCOVERED, wall 2 (|ζ|²-positivity versus log|ζ|; Jensen gap).

## Row 255 — minimum principle on the spectral side and θ zero-freeness (walls LA and 6)
- **Spectral minimum principle.**
  - u = Re(ξ′/ξ) is harmonic on Re s > ½ minus the off-line zeros.
  - Its boundary measure on the line is π Σ δ_γ ≥ 0, and u → +∞ as Re s → ∞. If u were harmonic there, the minimum
    principle would give u ≥ 0, i.e. RH.
  - But the poles are the off-line zeros themselves. Circular (corpus LA: RH ⟺ Re(ξ′/ξ) ≥ 0 on Re s > ½).
- **θ zero-freeness on ℍ.**
  - log θ is holomorphic on ℍ by the Jacobi triple product.
  - Its Mellin transform involves ζ(s)ζ(s+1)Γ(s) with divisor-sum coefficients.
  - Zero-freeness of θ is a product-convergence fact (|q| < 1), wall 6. It carries no critical-line information.
  - Ray-rotated Mellin transforms of θ give the same Λ(s) with rotated archimedean factors (e^{iφ})^{−s/2}: no new
    positivity.
- **Verdict.** Both REDISCOVERED.

## Row 256 — "magic function" / frame certificate for Weil positivity (Cohn–Elkies analogy): killed by spectral singularity
- **Analogy.**
  - The TMP witness G* is the primal optimiser of PBAP, playing the role of E8.
  - The dual certificate is W_Λ ⪰ 0, playing the role of the magic function.
  - Attempt: certify W_Λ ⪰ 0 as a positive superposition W_Λ(f) = ∫|⟨f, g_u⟩|²dν(u), with explicit modular vectors g_u
    (twisted arc vectors) and ν ≥ 0 proved by a minimum principle. A mixture weighted by a pointwise-positive measure
    would bridge wall 13.
- **Kill (translation averaging).**
  - W_Λ depends only on f ⋆ f̃, so it is translation invariant.
  - Averaging the superposition over translations of f gives W_Λ(f) = ∫|f̂(t)|²(∫|ĝ_u(t)|²dν(u))dt. The spectral
    density is absolutely continuous whenever g_u ∈ L².
  - Under RH the spectral measure of W_Λ is purely atomic (the zeros; corpus `WeilConeNullAtomicSpectrum`).
  - So no superposition of L² rank-one forms certifies Weil positivity. A certificate must be spectrally singular,
    which is wall 12 in sharpened form.
- **Verdict.** FALSE. Unlike sphere packing, where the magic function is a regular Schwartz function, the RH
  certificate is forced to be singular.

## Row 257 — singular certificates: Fourier quasicrystals and Lee–Yang (Kurasov–Sarnak) — corpus-explored
- **Motivation.** Row 256 forces a singular certificate: an atomic positive measure μ with
  μ̂ = archimedean density − Σ Λ(n)n^{−½}δ_{±log n}.
- **Known singular positive mechanism.** Kurasov–Sarnak / Olevskii–Ulanovskii: positive Fourier quasicrystals are the
  zero sets of Lee–Yang-stable exponential polynomials P(e^{iλ₁t}, …), real-rooted by stability on the polydisc.
- **Attempt.** Use the Bohr lift 1/ζ = Π_p(1 − z_p p^{−s}). Each factor is stable on the polydisc for σ > 0, and a
  stable, self-reciprocal lift would give real zeros.
- **Kill.**
  - The lift converges only for σ > ½ (wall 6).
  - ξ is not a finite exponential polynomial, and its Fourier side carries a continuous archimedean part, so it is not
    a quasicrystal.
  - Corpus: Lee–Yang fake zetas killed (an a.c. density −½ log N appears), multi-prime Putnam/Lee–Yang formalised
    (`ZetaZerosLeeYangPutnam`), Lee–Yang all graphs (`lee-yang-asano-lean`).
- **Verdict.** REDISCOVERED (walls 6 and 12). Singular positive certificates that are known to exist (stable
  polynomials) need a finite toric presentation, which ζ lacks at σ = ½.

## Row 258 — singular certificate via a Sturm–Liouville problem on the arc: killed by the Weyl law
- **Attempt (towards a spectral realisation).**
  - The Legendre operator 𝔐 = ∂_u(1−u²)∂_u on the arc u ∈ [−½, ½] is regular, since 1 − u² ≥ ¾.
  - With self-adjoint boundary conditions at the corners it has real eigenvalues ¼ + τ_j². The secular equation is a
    combination of P_{−½+iτ}(±½), Q_{−½+iτ}(±½) and their derivatives.
  - If that secular function were Ξ(τ) times a non-vanishing factor, self-adjointness would give RH. This is the
    conical-function realisation suggested by row 227 (C240).
- **Kill (counting).**
  - A regular SL problem on a compact interval has τ_j ~ πj/ℓ, so N(T) ~ cT.
  - Zeta zeros have N(T) ~ (T/2π) log T.
  - Any self-adjoint realisation therefore needs a singular end or infinite volume supplying the log T. At level 1
    this is the cusp, whose zeta-resonances are non-unitary (row 243), or the adelic class space (wall 5).
- **Verdict.** FALSE. The compact arc carries the null-face witnesses (TMP) but cannot carry the zeros spectrally.

## Row 259 — infinite-volume version: the TMP half-cylinder F with Dirichlet on the arc — non-arithmetic scattering
- **Attempt.** Add the cusp to the arc: Δ + ¼ on F (half-cylinder above the arc) with Dirichlet on A.
  - The cusp supplies continuous spectrum and the log T counting.
  - Define E_F(z,s) (Dirichlet on A, y^s + φ_F(s)y^{1−s} + decaying) and ask whether the poles of φ_F are the ζ zeros.
- **Kill.**
  - Neumann on A gives σ-even functions: exactly the even modular objects (E(z,s), with φ = ξ(2s−1)/ξ(2s), so ζ zeros
    appear only as non-unitary resonances).
  - Dirichlet on A gives σ-odd functions. Together with T-periodicity and evenness this character is inconsistent at
    the 2π/3 corner (rows 230/232), so F with Dirichlet on A is not a quotient of ℍ.
  - φ_F is then a ratio of arc harmonic measures of (1−u²)^{s/2} and (1−u²)^{(1−s)/2}, with no Hecke or Euler
    structure. Its poles are not tied to ζ.
- **Verdict.** FALSE. The arithmetic (Neumann) version sees ζ only through resonances; the Dirichlet version that TMP
  uses is non-arithmetic. Same resonance-versus-eigenvalue dichotomy as row 243.

## Row 260 — convolving a negative certificate with the witness
- **Identity [P, unconditional].** For any PD test G and the TMP witness G*, whose spectrum Ĝ* contains |Ξ|²:
  - Ĝ·Ĝ* vanishes at every zero, so W_Λ(G ⋆ G*) = 0;
  - hence A(G ⋆ G*) = Σ_n Λ(n) ℓ_n(G ⋆ G*).
  - This is an exact archimedean–prime balance for every convolution with the witness.
- **Attack on PBAP.**
  - G ⋆ G* is not blind: (G ⋆ G*)(log n) = ∫G(y)G*(log n − y)dy.
  - A(G ⋆ G*) carries no sign information about A(G).
  - The Schur product G·G* is blind and PD, but A(G·G*) is not controlled by A(G) (row 235).
- **Verdict.** No transfer. The identity just restates W_Λ ≡ 0 on the Ξ-divisible ideal, for every λ ∈ W.

## Row 261 — summing node energies against the PNT (circular)
- **Attempt.** Under RH, Σ_{m≤x} inf E_m = ψ(x) ~ x. Can the unconditional PNT force inf E_m > −∞?
- **Kill.** E_m is either bounded below at every m (RH) or unbounded at every m (¬RH), by
  `isGLB_unitNodeEnergies` and `not_bddBelow_unitNodeEnergies`. The sum is ψ(x) or −∞, and the PNT carries no
  information on which.
- **Finite-aperture variant.**
  - Λ_A(m) := inf E_m^{(A)}, over tests supported in [−A, A], equals max{λ_m : λ ∈ W_A}.
  - Under RH this decreases to Λ(m). Nonemptiness of W_A at every A is the RW route (Krein induction).
- **Verdict.** CIRCULAR.

## Row 262 — regularised Lévy–Khintchine form of the full Weil kernel (tautological on blind tests); lint check
- **Attempt.**
  - The full Weil kernel is "constant·δ₀ + 2cosh(x/2) − N", where N = ω(|x|)dx + Σ_n Λ(n)n^{−½}δ_{±log n} is the total
    Lévy measure of ξ at σ = ½.
  - On PD tests G(0) − G ≥ 0, so a Lévy–Khintchine split would give positivity, but N has infinite mass because
    Σ Λ(n)n^{−½} = ∞ (wall 6).
  - Regularise at N₀: A(G) = ℰ_{N₀}(G) + (Ω(0) − 2ψ_½(N₀))G(0) + pole(G), with ℰ_{N₀} ≥ 0 and ψ_½(N₀) ~ 2√N₀.
- **Kill.** On blind tests the prime part of ℰ_{N₀} is exactly 2ψ_½(N₀)G(0), which cancels the regularising constant.
  The identity is tautological.
- **Maintenance.** `scripts/formal_tools.py lint`: no errors in `PrimeBlindNodeCriticality`,
  `ArchimedeanUnitNodeEnergy` or `ModularArcStreamMinimumPrinciple`. The two remaining errors belong to other agents'
  unwired modules.

## Row 263 — Bohr-lift / F. and M. Riesz reading of blindness (corpus Helson lane)
- **Reading.**
  - Push the spectral measure μ = Ĝ dt forward to the infinite torus via t ↦ (p^{it})_p.
  - Its Fourier coefficient at the character of r ∈ ℚ_{>0} is G(log r).
  - Blindness kills the coefficients on the positive orthant ℕ^∞ ∖ 0, and by symmetry on the negative orthant.
    Mixed-sign indices (non-integer ratios) are free.
- **Attempt.** Use an F. and M. Riesz / Helson–Lowdenslager / Bochner-cone theorem (spectrum in a cone forces absolute
  continuity) to force structure on blind μ.
- **Kill.**
  - Those theorems need the spectrum inside a half-space or a line-free cone.
  - The free set of blind μ (all mixed-sign indices) contains lines, e.g. the direction of log(2/3), so no absolute
    continuity follows.
  - Full rational blindness (a half-space) would force G ≡ 0 (known).
  - Corpus: Helson lane (`helson-stratum-borel`, `helson-haar-null-closed`, `helson-divisor-card-closed`).
- **Verdict.** REDISCOVERED or insufficient. The orthant structure of ℕ is too weak for Riesz-type rigidity.

## Row 264 — saddle-point (Lagrangian) certificate (circular)
- L(G, λ) = A(G) − Σ_n λ_n ℓ_n(G) on PD tests.
- The witness G* (blind, A(G*) = 0) gives L(G*, λ) = 0 for every λ. Λ maximises L(G*, ·) trivially.
- (G*, Λ) is a saddle ⟺ G* minimises L(·, Λ) ⟺ W_Λ ⪰ 0 ⟺ RH.
- The only nontrivial half of the saddle certificate is RH itself; the duality gap is 0 iff RH.
- Verdict: CIRCULAR.

## Row 265 — WindowPositive: spectral form and an analytic proof strategy (non-RH sector; paper)
- **Spectral form.** For h ≥ 0 on (0, L), normalised spectral density p = |ĥ|²/∫|ĥ|²:
  - F(h) = 2∫_L^∞ ω + 2∫ p(t)Φ(t)dt, where Φ(t) := ∫_0^L ω(x)(1 − cos xt)dx + 2∫_0^L cosh(x/2)cos(xt)dx.
  - WindowPositive ⟺ ∫pΦ ≥ (5.3721 − 2.9937)/2 = 1.1892 for every admissible p.
- **Values.**
  - Φ(0) = 4 sinh(L/2) ≈ 1.414.
  - Φ dips to ≈ 0.9 near t ≈ π/L ≈ 4.5: the jump part ≈ ½(log(tL) + γ − Ci(tL)) ≈ 0.88 and the cosh part ≈ 0.01.
  - Φ → ∞ logarithmically.
  - So inf_t Φ < 1.19 and the signed problem fails, as expected.
- **What nonnegativity adds.**
  - ĥ is the characteristic function of a positive measure, hence PD: p(t) ≤ p(0).
  - With the support centred, |ĥ(t)|/ĥ(0) ≥ 1 − t²L²/8 for |t| ≤ √8/L ≈ 4.08.
  - Example: h = bump·(1 + cos 4.5x) puts weights ⅔ at 0 and ⅓ at ±4.5, so ∫pΦ ≈ 0.94 + 0.30 = 1.24 > 1.19, a thin
    margin.
- **Strategy (two regimes).**
  - (a) Flat h, with ‖h‖² ≤ K(∫h)²/L: the guaranteed low-frequency mass from the characteristic-function lower bound
    sits where Φ ≈ 1.41.
  - (b) Spiky h: the spectral mass spreads to high t where Φ ≳ ½ log t.
  - Choose K to balance the regimes. This needs explicit enclosures of Φ on a grid (integrals of e^{−βx}cos(xt)
    against ω = Σ e^{−(2k+½)x}, all closed-form).
  - Lean would use the corpus `MidpointRadiusTrigEnclosures` toolkit.
- **Status.** Recorded plan. Non-RH (CANNOT-535); it would close the frontier map's "numeric" window gap in HF.

## Row 266 — WindowPositive certificate shape (copositive = pointwise-nonnegative + PSD); why it is not hand-tunable
- **Form.** Q(h) := F(h) − |A(0)|‖h‖² = Lévy(h) + 2∫∫h(x)h(y)cosh((x−y)/2) − 5.3721‖h‖², where
  Lévy(h) = ∫_0^∞ ω(z)‖h − h(·+z)‖² is a PSD Dirichlet form.
- **Certificate shape (Diananda-type).** Q = Q_PSD + Q_K, with Q_K(h) = ∫∫h h K and K ≥ 0 pointwise on (−L, L).
  Then Q ≥ 0 on h ≥ 0.
  - Natural split: K = 2cosh(z/2) − β ≥ 0 for β ≤ 2, and Q_PSD = Lévy + β(∫h)² − 5.3721‖h‖².
  - This requires Q_PSD ⪰ 0 on all signed h, which fails at low frequency: for ∫h = 0 and smooth h, Lévy ≈ 2·0.9‖h‖²
    is far below 5.37‖h‖².
  - So K must also carry non-constant, z-dependent mass that couples with the low modes. Tuning that split is a
    semidefinite/LP design problem, which is computation.
- **Status.** The certificate shape is identified, but it cannot be produced by hand within the no-computation rule.
  WindowPositive stays a recorded non-RH target.

## Row 267 — multiplicative-Toeplitz Gram matrices of integer translates (corpus-owned)
- **Attempt.** Positivity of W_Λ on spans of the translates f(· − log n) gives, for narrow f, the matrix
  [K_arch(log(m/n)) − Λ-atoms at m/n ∈ ℕ^{±1}]_{m,n ≤ N} ⪰ 0.
  - This is a GCD/Redheffer-type multiplicative Toeplitz positivity; compare Redheffer det = M(N).
- **Kill.**
  - The corpus owns this: `WeilPositivityMultiplicativeToeplitzBound` (imported by the one-sided criterion). The
    Toeplitz-index candidates were closed in the integrality-anchor loop.
  - Positivity for all N is Weil positivity restricted to translate spans, which is wall 8.
- **Verdict.** REDISCOVERED.

## Row 268 — Hodge index for Hecke correspondences on X × X (wall 5)
- **Attempt.** A function-field-style positivity: Hecke correspondences T_n ⊂ X₀(N) × X₀(N) as divisors, with the Hodge
  index theorem applied to Σ a_n T_n.
- **Kill.**
  - Via Eichler–Shimura (T_p ≡ Frob + Ver mod p), this gives the Ramanujan bound for weight-2 cusp forms: the
    Weil/Deligne mechanism over finite fields.
  - For ζ the relevant Hecke eigenvalues are Eisenstein (σ₁(n), giving ζ(s)ζ(s−1)). Their positivity is on the
    1-line, and X(1) has genus 0.
  - There is no geometric Frobenius whose Hodge index sees the zeros of ζ: wall 5 (no F₁ / geometric Frobenius).
- **Verdict.** REDISCOVERED (wall 5).

## Row 269 — number-field and extra-node variants (no gain)
- **PBAP_K for an imaginary quadratic K** (Γ_ℂ, blind at the ideal norms):
  - GRH(ζ_K) ⟹ RH(ζ), and the blind set is sparser, so the cone is larger and the statement stronger.
  - With a TMP-type uniqueness it would be equivalent to GRH(ζ_K). Harder, not easier.
- **PBAP with extra nodes E ⊃ log ℕ** (for example log(ℕ/2)):
  - The cone is smaller, so the statement is weaker.
  - The TMP witness is not blind at E, so uniqueness fails and the cone W_E is fat; PBAP_E is non-RH.
  - Recovering RH as E → ∅ needs uniform control, which is RH again.
- **Verdict.** No gain in either direction. Node criticality pins the node set exactly to log(prime powers).

## Row 270 — C270 (recorded direction): extend the HF chain to small conductors (q = 3, 4)
- **Idea.** The TMP geometry is the bottom arc of SL₂(ℤ) with a corner at the elliptic point.
  - Row 232: at level q the arc |z| = q^{−½} meets u = ±½ above the real axis exactly for q ≤ 3. q = 4 touches the
    cusp at ½.
  - A level-q twisted minimum principle (χ-twisted K-Bessel modes for the odd characters χ₋₃ and χ₋₄; for Γ_ℝ(s+1)²,
    K₁-type modes) would give an (N1) witness for L(s, χ₋q).
  - With that witness, cone uniqueness gives GRH(L(s,χ₋q)) ⟺ PBAP(Γ_ℝ(s+1), q).
- **Consistency.** The families F(Γ_ℝ(s+1), 3) and F(Γ_ℝ(s+1), 4) have a single member (one odd character each), so
  Hamburger-type uniqueness is not contradicted (row 232 audit).
- **Value.** It extends the corpus RH ⟺ PBAP to GRH for χ₋₃ and χ₋₄. It is a structural extension, not progress on
  any PBAP core.
- **Effort.** Large: twisted moments with χ, a new arc geometry, stream-function minimum principle at the new corner,
  and a divisor transfer for L(s,χ)².
- **Status.** Recorded as a backlog direction, not started.

## Row 271 — [L] integer blindness is a Möbius law for primitive Farey sums (C252 formalised)
- **[L] `RHTower/BlindIntegerFareyMoebius`** (standard axioms, `lake --old` clean, wired):
  - `primitiveFareySum f q` := Σ_{a≥1, gcd(a,q)=1} f̂(a/q);
  - `tsum_fareyDilate_eq_sum_divisors`: grouping by gcd gives Σ_{k≥1} f̂(k/m) = Σ_{q∣m} primitiveFareySum f q;
  - `fareyDilateSum_of_blind`: dilated Poisson summation for an integer-blind function;
  - **`primitiveFareySum_eq_moebius_mul`**: for even Schwartz f with f(0) = 0 and f(n) = 0 for all n ≥ 2,
    primitiveFareySum f q = μ(q)·f(1) for every q ≥ 2.
- **Meaning.** For a Weil test, g(y) = G(log|y|) is even and vanishes near 0. Prime blindness of G is exactly
  g(n) = 0 for n ≥ 2, i.e. the primitive Farey sums of ĝ are the Möbius function times g(1). This is an exact bridge
  from the HF/PBAP domain to the Farey/Möbius (MC) lane.
- **Status.** A bridge, not a producer (row 235 verdict). It is new Lean content linking the two lanes.
- **Row 271 addendum [L]: converse.**
  - `blind_iff_primitiveFareySum`: for compactly supported even Schwartz f, f(0) = 0 ∧ f(n) = 0 for all n ≥ 2 ⟺
    the Möbius law for every q ≥ 2.
  - Mechanism:
    - the Möbius law makes V(m) = P(1) − f(1), so Poisson summation reads f(0) + 2Σf(mn) = C/m;
    - comparing m = N+2 and 2N+4 gives C = 0 and f(0) = 0;
    - downward induction over multiples (`eq_zero_of_multiple_sums`) finishes.
  - Standard axioms, `lake --old` clean.
- **Row 271 addendum 2 [L]:** `sum_primitiveFareySum_eq_mertens`.
  - For an integer-blind f: Σ_{q≤Q+1} P_f(q) = P_f(1) + f(1)·(M(Q+1) − 1).
  - Blind tests carry the Mertens function exactly in their cumulative Farey sums.
  - Attack recorded: bounding the left side independently (e.g. O(Q^{½+ε})) would give RH. But the Farey Riemann sums
    of a fixed smooth ĝ with ∫ĝ = 0 have error governed by M itself (Franel–Landau duality), so this is circular
    (wall 1/MC).

## Row 272 — C272 blind Riemann–Roch transfer (Weil's hard half on blind tests)
- **Conjecture.** Weil's curve proof is (easy half) "effective ⇒ positive against ample" plus (hard half) Riemann–Roch,
  which turns D² > 0 into effectivity. Dictionary on blind tests:
  - effective ↔ h = g⋆g̃ with g ≥ 0;
  - ample ↔ the pole functionals ∫h e^{±x/2}.
  - C272: every blind PD test with Q_arch(h) < 0 forces a blind effective test with Q_arch < 0.
- **Easy half.** On blind tests it holds modulo `WindowPositive`. `weilArchRe_nonneg_of_primeBlind` (hW) is exactly
  "effective ⇒ positive". Without blindness the easy half is already RH-equivalent (old loop row 468, shift-pair
  criterion). Blindness therefore splits Weil's proof cleanly: easy half = a local numeric inequality; hard half = RH.
- **Kill (CIRCULAR).**
  - Blind effectivity is window-confined: g ≥ 0 with g⋆g̃(log n) = 0 for all n ≥ 2 has |supp g| ≤ log 2
    (`DilationFreeSetMeasure`, quantile transport).
  - A test of support ≤ log 2 cannot resolve an off-line zero. For ĥ of exponential type log 2, the off-line quadruple
    term is bounded by a fixed multiple of ‖h‖₁, while the on-line density log T dominates at height T.
  - So under ¬RH the effective sector stays positive (given WindowPositive) while the PD sector goes to −∞. A transfer
    map would itself decide RH. There is no h⁰(nD)-growth: multiples do not enlarge support.
- **Lesson.** Over ℚ, blind effectivity is local (length log 2). The RR step would have to manufacture large-support
  positive objects from Bochner data; no such object exists in the blind world. This is the arithmetic form of
  "no surface Spec ℤ ×_{F₁} Spec ℤ".

## Row 273 — C273 null-face plus window decomposition of the blind PD cone
- **Conjecture.** Every blind PD h = h₁ + h₂ with ĥ₁ = Ξ²φ (φ ≥ 0, blind; Q_arch(h₁) = Σ_ρ ĥ₁(γ_ρ) = 0
  unconditionally) and h₂ a window core (Q_arch ≥ 0 by WindowPositive). This would give PBAP.
- **Kill (FALSE).**
  - ĥ₂ would have to interpolate ĥ and ĥ′ at every zero.
  - ĥ₂ is of exponential type ≤ log 2, so it samples at density ≤ log 2/π, while the zeros have density
    (1/2π) log(T/2π) → ∞.
  - Ξ has infinite exponential type, so Ξ²-divisible parts are never compactly supported.
- **Lesson.** Any positive decomposition of the blind cone needs pieces of infinite spectral type. Finite-aperture
  sectors are spectrally too thin.

## Row 274 — C274 PBAP on the doubly-positive blind cone D = {h ≥ 0, ĥ ≥ 0, h(log n) = 0}
- **Kernel form.** For even h:
  Q_arch(h) = A(0)h(0) + 2∫_0^∞ ω(x)(h(0) − h(x))dx + 4∫_0^∞ h(x)cosh(x/2)dx.
  - The far kernel 4cosh(x/2) − 2ω(x) > 0 for x > x* ≈ 0.28.
  - Hence Q_arch(h) ≥ Q_arch(h·1_{[−log 2, log 2]}) for every h ≥ 0: nonnegative mass beyond log 2 only adds energy.
  - Narrow far bumps forced by node gaps (width e^{−L} at distance L) add ≈ L e^{L} of arch energy, against an
    off-line term ≈ e^{δL} with δ < ½.
  - Smooth chirp profiles a(x)sin²(πe^{|x|}) need compensating spectral mass ≈ e^{L/2} at frequency e^{L}. The
    "chirp tax" L·e^{L/2} beats e^{δL} exactly because δ < ½.
- **Reduction.** D-PBAP reduces to the local problem on [0, log 2]:
  −2.378 h(0) + 2∫_0^{ℓ} ω(h(0) − h) + 4∫_0^{ℓ} h cosh ≥ 0.
  - The pointwise relaxation (0 ≤ h ≤ h(0), PD dropped) gives min 1.124 + 1.099 = 2.223, a shortfall of 0.156.
    This is the same 5.216 vs 5.372 gap as WindowPositive.
  - PD is needed near 0: h(c) = h(0) forces c-periodicity, and ω ~ 1/(2x) penalises the drop.
- **Verdict.** NON-RH (wall 13, now with mechanism). Pole reserve and chirp tax dominate any off-line contribution on
  D. RH content is carried only by blind PD tests that change sign beyond log 2.

## Row 275 — C275 blind moment calculus (Dirichlet series against blind spectral densities)
- **Identity [P].** Let Φ be a blind spectral density: entire, Φ̂(log n) = 0 for n ≥ 2, decaying in horizontal strips.
  Let D = Σ a_n n^{−s} converge absolutely on Re s > 1 and continue meromorphically.
  - On Re z = 2 every n ≥ 2 term dies after shifting y → y + 3i/2.
  - The rectangle then gives
    ∫ D(½+it)Φ(t)dt = a₁Φ̂(0) − 2π Σ_{poles z₀, Re z₀ > ½} Res_{z₀}[D(z)Φ((z−½)/i)],
    with principal values for singularities on the line.
- **Instances.**
  - D = ζ: ∫ζ(½+it)Φ(t)dt = Φ̂(0) − 2πΦ(−i/2), unconditional and exact.
  - D = ζM for a Dirichlet polynomial M: ∫ζMΦ = Φ̂(0) − 2πM(1)Φ(−i/2). Blind measures mollify exactly at first order.
  - D = ζ′/ζ: the explicit formula.
  - D = 1/ζ: RH ⟺ σ ↦ ∫(1/ζ)(σ+it)Φ(t − i(σ−½))dt is constant on (½, 2] for every blind Φ.
  - D = log ζ (cuts): the blind Jensen formula
    ∫log|ζ(½+it)|Φ = −2π∫_0^{½}Φ(−iu)du + 2πΣ_{β>½} Re∫_0^{β−½}Φ(γ−iu)du.
- **Attack.**
  - |ζ|² = χ(1−s)ζ² carries the χ factor, so on the far line the n ≥ 2 terms become Voronoi transforms that blindness
    does not kill. The only exact |ζ|² identity is the corpus cos-dilation law (Fourier-side blindness, (N1) type), not
    PBAP blindness.
  - Second moments keep the diagonal ν̂(0)Σ|c_n|²/n, so the mollified mean-square floor survives blindness
    (mollifier lane, `mollified-mean-square-floor`).
  - Jensen with the first-moment identity only bounds off-line horizontal integrals by the pole reserve. That is
    density-method strength, not RH.
- **Verdict.** BRIDGE (Mellin–Perron shift). Positive survivor: PBAP-blindness annihilates every Dirichlet series
  exactly at first order, so all first moments of ζ-type series against blind spectra are pole data. |ζ|²-positivity
  needs the χ factor and hence Fourier-side blindness.

## Row 276 — C276 doubly-blind Jensen squeeze
- **Setting.** g = f ⋆_× f̃ blind on both sides (g(n) = ĝ(n) = 0 for n ≥ 2). The corpus law
  ∫|ζ𝓜f|² = 2πΨ_f(1) combines with the blind Jensen formula (Φ = |𝓜f|², PBAP-blind) via Jensen,
  E log|ζ|² ≤ log E|ζ|². This gives
  Σ_{β>½} Re∫_0^{β−½}Φ(γ−iu)du ≤ ∫_0^{½}Φ(−iu)du + (1/4π) log(Ψ_f(1)/‖f‖²)·∫Φ.
- **Reading.** Under RH every doubly-blind core satisfies Ψ_f(1) ≥ ‖f‖² exp(−4π∫_0^{½}Φ(−iu)du / ∫Φ).
  An unconditional doubly-blind core violating this would refute RH.
- **Verdict.** RECEIVER/FALSIFIER, not a producer. The off-line terms Re∫Φ(γ−iu)du have no sign. Recorded as a test
  for any future doubly-blind construction.

## Row 277 — blind decay and the Carlson edge (rediscovery check)
- **Observation.** A Lagrange-interpolation bound at nodes of spacing e^{−u} gives
  |h(u)| ≤ inf_k (M_k/k!)(k e^{−u})^k. Hence:
  - a blind PD test whose spectrum decays like e^{−a|t|} decays like exp(−(a/e)e^{u});
  - a band-limited blind test vanishes (Jensen: e^{r} zeros against exponential type);
  - Blaschke in the strip |Im| < a forces a < π/2, i.e. spectra cannot decay faster than e^{−(π/2)|t|};
  - Ξ² decays exactly at that rate.
- **Corpus check.** Already owned, sharper and in Lean: `PrimeBlindCarlsonThreshold` (rate π/2, polynomial and √|t|
  room, Ξ²·h blind ⟹ h not tempered), `IntegerBlindLogarithmicCarlsonThreshold` / `...Critical` (exact constant
  K = π/2 under log room), `StripFactorXiDivisibleBlindTest`.
- **Verdict.** REDISCOVERED. Positive reading for PBAP: under RH the normalised infimum of Q_arch over blind PD tests is
  approached only by spectra at the Carlson edge (tail ≍ e^{−π|t|/2} times non-tempered multipliers). Low-frequency
  concentration is forbidden by Carlson, so every PBAP minimising sequence lives at the edge where the NULL face sits.

## Row 278 — Euler–Maclaurin form of PBAP; exact far-kernel threshold
- **Change of variables.** In w = e^x:
  Q_arch(h) = A(0)g(1) + 2∫_1^∞ [√w (g(1) − g(w))/(w² − 1) + (w^{−½} + w^{−3/2}) g(w)] dw, with g(w) = h(log w),
  g(1/w) = g(w), g′(1) = 0.
- **Trapezoid split.** Euler–Maclaurin on the integers gives
  - Q_arch = κ·g(1) − 2·(trapezoid error of Φ), with κ = A(0) + 2 + 2Σ_{k≥0}(ζ(3/2 + 2k) − 1) ≈ 0.1723 > 0;
  - the sampled Weil coefficient at n ≥ 2 is 2n^{−½}(1 − Λ(n) − 1/(n³ − n)), a pole-regularised von Mangoldt
    (compare DR);
  - for blind g only the n = 1 sample survives.
- **Exact threshold.** The far kernel 4cosh(x/2) − 2ω(x) vanishes exactly at e^x = ρ_plastic (w³ = w + 1), so
  x* = log ρ_plastic ≈ 0.2812 (row 274).
- **Abel–Plana.** Abel–Plana would turn Q_arch into a vertical-line integral of g against the Planck weight
  1/(e^{2πy} − 1), with sin(πw) and Planck combining to e^{−πy}. It needs analyticity on Re w ≥ 1, i.e. Carlson-edge
  tests only.
- **Verdict.** BRIDGE (a rewriting; the trapezoid error has no sign).

## Row 279 — [L] blindness at log ℕ forces exponential decay (MUST-1444)
- **Conjecture.** The converse of the Carlson threshold: blindness plus k spectral moments forces physical decay at
  rate k.
- **Proof.** The nodes log n, …, log(n+k) near x span at most 2k e^{−x}. The Rolle cascade then gives
  |f| ≤ sup|f^{(k)}|·(2k)^k e^{−kx}.
- **[L] `RHTower/BlindLogNodeDecay`** (standard axioms, `lake --old` clean, wired):
  - `abs_le_of_zeros_of_iteratedDeriv_le` (Rolle cascade);
  - `abs_le_of_logNat_zero`;
  - `norm_charFun_le_of_logNat_blind`: ‖φ_μ(x)‖ ≤ 2(∫|t|^k dμ)(2k)^k e^{−k|x|};
  - `integrable_norm_charFun_mul_exp_of_logNat_blind`: weight e^{a|x|}, any a < k.
- **Meaning for PBAP.**
  - The Weil decay class needs no hypothesis for blind tests with one spectral moment.
  - Blind spectral measures with all moments have characteristic functions decaying faster than every exponential,
    so their densities are entire.
  - With Carlson (`PrimeBlindCarlsonThreshold`), blind spectra are squeezed between "entire" and "decay no faster than
    e^{−π|t|/2}".
- **Verdict.** BRIDGE/STRUCTURE (new to the corpus, not a producer).
- **Next.** The sharp Lagrange factor 1/k! would give doubly exponential decay exp(−c·e^{2|x|}) for Gaussian spectral
  tails, the Riemann–Pólya rate. Mathlib has no Lagrange interpolation error formula; deferred.
- **Side note (other agent, CANNOT-539).** For conductor q ≥ 9.3 (odd) the archimedean symbol is nonnegative, so
  PBAP_χ is vacuous. C270 (row 270) is viable only for q = 3, 4, consistent with row 232.

## Row 280 — the blind cone is invariant under integer dilations
- **Observation.** For k ∈ ℕ, D_k h(x) = h(kx) satisfies D_k h(log n) = h(log nᵏ) = 0. So D_k preserves
  integer-blindness, prime-power-blindness (p^j ↦ p^{jk}) and PD. The blind PD cone is also closed under Schur
  products and modulation h·cos(τx).
- **Energy under dilation.** Q_arch(D_k h) = (1/k)Σ_ρ ĥ(γ_ρ/k) ≈ A(0)h(0) + h(0)(log k + c_h) → +∞, while the pole
  part → 0. Schur powers h^m → h(0)^m·(narrow bump) also have Q_arch → +∞.
- **Real dilations.** For real u, Z_h(u) = (1/u)Σ_ρ ĥ(γ_ρ/u) = a_h(u) − P_h(u). The prime part
  P_h(u) = 2ΣΛ(n)n^{−½}h(u log n) vanishes at every integer u. RH ⟹ a_h(u) ≥ P_h(u) for all u > 0. The Mellin
  transform in u gives the Cramér–Guinand pair Σγ^{s−1} ↔ ΣΛ(n)n^{−½}(log n)^{−s} (rediscovered).
- **Verdict.** STRUCTURE. PBAP violations are infrared: dilation and Schur powers push every blind test to positive
  energy. A violation must live in wide tests, where the off-line depth δ survives, and no semigroup flow reaches
  them from the positive sector.

## Row 281 — Poisson split of an off-line contribution
- **Setting.** For a PD test with spectral density ψ, analytic in the strip |Im| < b, an off-line zero at γ − iδ
  (0 < δ < b) contributes 2Re ψ(γ − iδ).
- **Split.** The strip Poisson representation separates it into:
  - a positive average of ψ ≥ 0 over the real line near γ (harmonic measure 1 − δ/b);
  - a leakage term from the line Im = −b with harmonic weight δ/b, bounded by ∫|h|e^{b|x|}.
- **Bound on the leakage.** By MUST-1444, ∫|h|e^{b|x|} ≤ C_b(h(0) + M_k) for blind tests with k > b. Violations
  therefore need leakage, i.e. tests with spatial extent ≳ 1/δ.
- **Verdict.** RECEIVER (zero-density-type control); no sign for the sum over off-line zeros.

## Row 282 — [L] sharp interpolation and doubly exponential decay of blind tests (MUST-1444 add.)
- **[L] `RHTower/BlindLogNodeDecay`** (561 lines, standard axioms, `lake --old` clean):
  - `exists_iteratedDeriv_eq_zero` (generalised Rolle);
  - `abs_le_div_factorial_mul_prod` (Lagrange bound);
  - `abs_le_of_logNat_zero_sharp`;
  - `norm_charFun_le_of_logNat_blind_sharp`;
  - `norm_charFun_le_doubleExp_of_logNat_blind`.
- **Structure of the blind cone.** In w = e^{|x|}, blind PD tests behave like sin(πw)·e^{−cw}. The PW_π cardinal
  candidate h(0)[sinc(y−1) + sinc(y+1)] is blind and in the Weil class, but its log-spectrum oscillates in sign
  (Γ(it)(2π)^{−it} phase), so it is not PD. Consistent with Carlson, PD forces non-band-limited structure.
- **Verdict.** STRUCTURE, not a producer.

## Row 283 — C283 low-frequency pole balance: the bad band
- **Pole reserve on the real line.** With ψ = ĥ, Q_arch = (1/2π)∫ψA + 2ψ(i/2).
  - Representing ψ(i/2) by harmonic measure in the strip {0 < Im < b} splits it into a real-line part
    ∫Π₀^{(b)}ψ (Π₀ > 0) plus leakage from Im = b with weight 1/(2b).
  - The real-line reserve is at most the half-plane Poisson kernel, 2P_{1/2}(t) = 1/(π(t² + ¼)).
- **Bad band.** The effective symbol A(t) + 2/(t² + ¼) is positive at t = 0 (−5.37 + 8 = 2.63) but negative on
  roughly 1 ≲ |t| ≲ 6.3 (A(2) ≈ −1.16 against +0.47). No real-line accounting of the pole closes PBAP. This matches the
  0.156 window shortfall (rows 266, 274).
- **Blindness against the bad band.** The prime-2 marginal is Haar on the circle t·log 2 mod 2π. The band
  ±[1, 6.3] maps into an arc that misses (−0.69, 0.69), so at least 1.386/2π ≈ 22% of the spectral mass must lie in
  t ∈ (−1, 1) + (2π/log 2)ℤ. Each prime adds such an exclusion.
- **Verdict.** STRUCTURE. By node criticality no finite set of primes can make the relaxed linear program
  nonnegative (PBAP restricted to S = {2^j} is false unconditionally). The proof must use all primes' marginals
  jointly; that joint law is the producer target in these terms.

## Row 284 — C284 conductor dominance via a quadratic field
- **Conjecture.** For imaginary quadratic K of large discriminant, arch_K(t) = A(t) + A_χ(t) + log d ≥ 0 pointwise
  (log d > 7.6). The only negative source is then the ζ pole. Prove PBAP_K (blind at S_K = {p^k : χ(p^k) ≠ −1}) by
  pole-versus-chirp-tax (row 274: tax L·e^{L} beats pole e^{L}), and conclude GRH(ζ_K) ⟹ RH.
- **Attack.**
  - PBAP_K ⟹ GRH(ζ_K) needs Weil-cone uniqueness for ζ_K. TMP gives it only for the conductor-1 data Γ_ℝ(s).
  - With arch_K ≥ 0, fake weights are not excluded: CANNOT-539, where the cone is not a point once the symbol is
    nonnegative. With a pole, w = 0 still fails (odd two-bump tests make the pole −2e^{L} with bounded arch energy),
    but small fake perturbations of Λ_K are not ruled out.
  - Chirp-tax domination is heuristic for generic profiles only; near-null-face tests evade it (row 274).
- **Verdict.** CIRCULAR/BLOCKED: requires a K-version of TMP uniqueness, which large conductor makes false.
  Lesson: the RH content of PBAP is exactly the conductor-1 deficit (A(0) = −5.37) balanced by the pole. Any route
  that buys positivity with conductor loses uniqueness.

## Row 285 — first-Gamma-pole absorption: Q_arch with constant A(0) + 4
- **Identity [P, exact].** Split ω = e^{−x/2} + ω₁ with ω₁(x) = e^{−5x/2}/(1 − e^{−2x}) (Gamma poles λ_k = 2k + ½,
  k ≥ 1). The λ₀ = ½ term cancels the e^{−x/2} half of the pole term, giving
  Q_arch(h) = (A(0) + 4)·h(0) + 2∫_0^∞ ω₁(x)(h(0) − h(x))dx + 2∫_0^∞ h(x)e^{x/2}dx, with A(0) + 4 ≈ −1.372.
  This is the ξ normalisation s(s−1)/2 (Γ pole at s = 0 against ζ pole at s = 1).
- **Spectral form.** A(t) = A(0) + Σ_k 2t²/(λ_k(λ_k² + t²)): a Stieltjes function of t², so Ã(P) is A(0) plus an
  operator-monotone function of P².
- **Window problem in this form.**
  - The pointwise crossover e^{x/2} = ω₁(x) is again w³ = w + 1 (plastic number, x* = 0.2812, as in row 278).
  - Relaxation: 0.6038 + 0.4464 = 1.0502 against the needed 1.372 − 0.1656 = 1.2066, the same 0.156 shortfall.
- **Verdict.** BRIDGE (normal form). The constant −1.372 is the true conductor-1 deficit once the trivial
  Γ-pole/ζ-pole cancellation is removed.

## Row 286 — chirp tax in the normal form (heuristic threshold)
- **Estimate.** A blind test with nonpositive far part (−b·sin²(πe^x) bumps of width w at distance L) loses
  (bw/2)e^{L/2} through the pole term. PD forces compensating spectral mass ≈ (bw/2)e^{L/2} near frequency e^L,
  which gains about L per unit of ω₁-Lévy energy and costs 1.372 through h(0). Net ≈ (bw/2)e^{L/2}(L − 2.37).
- **Reading.** Generic sign-changing blind tests satisfy PBAP once the far part sits beyond L ≈ 2.4. Violations
  under ¬RH must be fine-tuned near-null-face tests (Carlson edge, row 277), not generic chirps.
- **Verdict.** HEURISTIC (cannot be made rigorous for near-null tests, which is where RH lives).

## Row 287 — positivity-source census against the walls
- Already dead in the corpus or in this log:
  - Hodge index, Riemann–Roch, F₁ (wall 5, rows 272, 468);
  - spectral realisation (wall 12);
  - maximum principle and transfer operators (wall 13);
  - Lee–Yang and stability preservers (W1C);
  - total positivity (row 245);
  - Herglotz/Bochner (circular duality);
  - Gibbs/KMS entropy (wall 6);
  - Néron–Tate heights (needs an arithmetic surface, wall 5);
  - automorphic L² norms (these see ζ only on the 1-line; Rankin–Selberg gives |ζ|² mean squares, wall 2);
  - sieve squares (Selberg routes capped);
  - prime-torus joint laws (JAS, owned: Kakutani threshold ½);
  - Mehler–Fock arc kernels (owned: TwistedCoshKernel, SymmetricCosh*).
- Not yet tried, with obstructions noted:
  - (a) Löwner/operator monotonicity: only the archimedean symbol is operator monotone; the pole is rank 2, and
    there is no arithmetic operator-monotone object.
  - (b) Strong subadditivity / operator convexity of entropy: needs a quantum state family whose relative entropy
    Hessian is the Weil form. Bost–Connes gives this only for β > 1 (wall 6).
- **Verdict.** No untried positivity source passes the walls. Consistent with the old-loop row 510 conclusion: the
  open frontier is a new positivity object.

## Row 288 — [L] prime-circle periodization and the null-test / fake-producer dichotomy (MUST-1447)
- **[L] `RHTower/PrimeCirclePeriodization`** (standard axioms, `lake --old` clean, wired):
  - `map_phase_eq_of_blind` / `blind_of_map_phase_eq`: blind at every p^j ⟺ the spectral measure pushes forward to
    Haar on the p-circle;
  - `integral_periodic_eq_of_blind`;
  - `integral_nonneg_of_periodization`: pointwise certificates S ≥ ΣP_i(t log p_i) with zero-mean continuous P_i;
  - `ae_eq_of_periodization_of_integral_eq_zero`: null blind measures saturate every certificate.
- **C288 (pole-free data, conductor 3).** For odd χ₋₃ the symbol S₃(t) = Re ψ(¾ + it/2) − log(π/3) is negative only
  on |t| < 2.14 (S₃(0) = −1.132), and L(s, χ₋₃) has no pole.
  - Hand estimate: the 2-circle alone allows uniform-on-one-period measures with ∫S₃ ≈ −0.017 (barely negative).
  - Adding P₅ = −c·cos on the 5-circle lifts the mean of the 2-circle minimum to ≈ +0.007 at c ≈ 0.2. A certificate
    with primes {2, 5} (or a few more) looks feasible.
  - If so: a Weil-positive weight on finitely many prime powers, so the Weil cone of χ₋₃ is not a point and PBAP_χ₋₃
    holds without GRH. That would extend CANNOT-539 from q ≥ 9.3 down to q = 3, i.e. every odd χ.
  - The exact certificate needs numerically designed P_p (blocked by the no-computation rule). Status: [P-heuristic].
- **Dichotomy [L-abstract].** For pole-free data, a blind null test with full-support spectrum and a certificate with
  slack cannot coexist. So level-q TMP (C270) succeeds ⟺ no finite-prime fake producer. Margins are thin at q = 3.
- **For ζ.** Periodization certificates are exactly the real-line dual of blindness. The pole ψ(i/2) is evaluation off
  the line; its strip-Poisson split leaves the symbol A/2π + 1/cosh(πt), still negative on about [0.6, 6.3]. No
  periodization certificate can close ζ's PBAP, consistent with MUST-1445 (arch-only cone empty).
- **Verdict.** STRUCTURE plus a falsifiable conjecture (C288). The RH producer is untouched: ζ's PBAP lives in the
  pole, which no real-line certificate reaches.

## Row 289 — C289 pole through the shifted line (strip Poisson + complex periodization)
- **Attempt.** For an even blind PD h with spectral density ψ, analytic and bounded on 0 ≤ Im ≤ 1:
  - the strip Poisson kernel at the centre gives ψ(i/2) = ∫Π(t)[ψ(t) + ψ(t + i)]dt, with Π(t) = 1/(2cosh πt);
  - on Im = 1, ψ(·+i) is the transform of h(x)e^{−x}, which is still blind, so its complex spectral measure is
    equidistributed on every prime circle (MUST-1447 applies to complex measures through Fourier coefficients);
  - hence Π may be replaced by Π − ΣP_p(t log p) for zero-mean P_p without changing the second integral.
- **Kill.**
  - The leakage term is then bounded by ‖Π − ΣP_p∘phase‖_∞·∫|ψ(·+i)|. Π → 0 at infinity, while a mean-zero
    almost-periodic D recurs, so inf_D ‖Π − D‖_∞ ≥ ‖Π‖_∞ − o(1). Point evaluation off the line cannot be
    approximated by real-line periodization.
  - Weighted versions run into ∫|ψ(·+i)| ≤ 2π∫|f|²cosh(2x), the e^{|x|} growth that blindness does not control.
- **Verdict.** FAILS (structural). The pole is an off-line point evaluation; blindness constrains only Fourier
  coefficients at log n on every horizontal line. Precisely: blindness fixes the circle marginals on every line
  Im = y, never a point value.

## Row 290 — pole-weight rigidity at the true weights (observation)
- **Fact (unconditional, [P]).** At λ = Λ, Ξ²-divisible tests are null: W_Λ(k) = Σ_ρ k̂(γ_ρ) = 0.
  - Even null test k̂ = Ξ²: pole = 2Ξ(i/2)² = ½ > 0.
  - Odd null test k̂ = t²Ξ² (F̂ = itΞ, F real and odd): pole = 2F̂(i/2)F̂(−i/2) = 2·(−¼)(¼) = −1/8 < 0.
  - So W^β_Λ ≥ 0 forces β = 1 from both sides.
- **The all-λ version.** It needs null tests that are blind:
  - β < 1 is done (MUST-1445, via twisted-arc joint blindness);
  - β > 1 needs a blind odd-type null family (pole < 0). The even TMP family cannot give it, since its pole sum is
    w₀/2 > 0 and κ is rigid. An odd twisted-arc minimum principle (Γ(¾ + it/2) twist) is the natural candidate.
- **Verdict.** RECEIVER-side rigidity (open item flagged in MUST-1445; another agent's lane). Not pursued further
  here.

## Row 291 — C291 real-line pole absorption: the symbols θ′ + 1 − Re ζ and θ′ + 2sin²θ
- **Setting.** Additive form g(y) = ∫u(xy)u(x)dx with Mellin density |𝓜u(½+it)|² (PD); θ is the Riemann–Siegel
  theta, so A = 2θ′, χ(½+it) = e^{−2iθ(t)} and Z = e^{iθ}ζ(½+it).
- **Pole via Poisson [P, checked twice].**
  - pole = 𝓜g(0) + 𝓜g(1) = ĝ(0), and Poisson with g(0) = 0 gives
    pole = 2g(1) − 2ĝ(1) + 2Σ_{n≥2}g(n) − 2Σ_{k≥2}ĝ(k).
  - g(1) = (1/2π)∫|𝓜u|².
  - ĝ(1) = (1/2π)∫|𝓜u|²χ(½+it)dt (Mellin–Parseval, since 𝓜[2cos 2πy](½−it) = χ(½+it)), so
    ĝ(1) = (1/2π)∫|𝓜u|²cos 2θ.
- **(i) Prime-blind tests.** Combined with the blind first-moment identity (row 275):
  Q_arch = (1/π)∫|𝓜u(½+it)|²·[θ′(t) + 1 − Re ζ(½+it)]dt. The pole becomes the real-line function
  1 − Re ζ(½+it); S(0) = −2.686 + 1 + 1.460 = −0.226 < 0.
- **(ii) Doubly blind tests (g(n) = ĝ(n) = 0 for n ≥ 2).** Q_arch = (1/π)∫|𝓜u(½+it)|²·Θ(t)dt with
  Θ = θ′ + 2sin²θ = θ′ + 1 − cos 2θ, a purely archimedean symbol (no ζ). The pole equals
  ‖u − JCu‖²-type = (2/π)∫|𝓜u|²sin²θ ≥ 0.
  - Rough values: Θ(0) = −2.686, Θ(0.25) ≈ −1.58, Θ(0.5) ≈ −0.04, Θ(1) ≈ +0.94, Θ(2.5) < 0, Θ(3.5) ≈ −0.29,
    Θ(5) ≈ +0.08.
  - So Θ < 0 on about [0, 0.52) ∪ [2, 4.8], where θ ≈ −π and sin²θ is small.
- **(iii) Consistency.** The corpus law ∫|ζ𝓜u|² = 2πΨ_u(1) for Fourier-blind cores reads, in these normalisations,
  ∫|𝓜u|²|ζ(½+it)|² = ∫|𝓜u|²cos 2θ.
- **Open.**
  - Is PBAP restricted to doubly blind tests RH-equivalent? If yes: RH ⟺ ∫Θ dμ ≥ 0 for all doubly blind spectral
    measures, a pole-free and ζ-free real-line form (the most archimedean statement of RH in the corpus).
  - Obstacle: the cone-uniqueness proof (`eq_vonMangoldt_of_weilPositiveFull`) uses the twisted-arc null family,
    which is prime-blind but not known to be Fourier-blind. The doubly blind dual cone has extra Fourier-side weights
    b_k (symbols k^{−½}cos(2θ − t log k)); uniqueness needs a doubly blind Ξ-divisible null family.
  - Existence of nonzero doubly blind PD tests is itself open. They are not T₂/Voronoi (N1) objects: those are
    Γ_ℝ²/ζ².
- **Verdict.** BRIDGE plus an open conjecture C291: doubly blind PBAP ⟺ RH. A Θ-form certificate would still be
  singular (wall 12) if uniqueness holds. The real-line Θ removes the pole obstruction of rows 283 and 289, not the
  spectral-realisation wall.

## Row 292 — C291 reduced to a Fourier-repair lemma (R291); [L] Poisson pole lemmas
- **[L] `RHTower/BlindIntegerFareyMoebius`** (added; standard axioms, `lake --old` clean):
  - `fourier_zero_eq_poisson`: F(0) = 2f(1) − 2F(1) + 2Σ_{n≥2}f(n) − 2Σ_{k≥2}F(k) for even Schwartz f with f(0) = 0;
  - `fourier_zero_eq_of_blind`;
  - `fourier_zero_eq_of_doublyBlind`: F(0) = 2f(1) − 2F(1).
  These are the formal Poisson step of the pole absorption (row 291).
- **Reduction.** C291 (doubly blind PBAP ⟺ RH) follows from:
  - R291 (Fourier repair): for every prime-blind PD test u there is a prime-blind Ξ²-divisible PD null test v with
    ĝ_v(k) = −ĝ_u(k) for all k ≥ 2.
  - Proof: w = u + v is doubly blind and PD, and Q_arch(v) = Σ_ρ v̂(γ_ρ) = 0 unconditionally (Ξ²-divisible). So
    Q_arch(u) = Q_arch(w) ≥ 0, giving PBAP and hence RH (corpus).
  - The same "repair by null tests" pattern as unique repair (`repairedBlindPositive_iff`).
- **What R291 asks.** The Fourier values of a Ξ²-divisible test with multiplier φ are Voronoi sums:
  ĝ_v(k) = (1/2π)∫¼(t² + ¼)²|Γ_ℝ(½+it)|²ζ(½+it)²φ(t)k^{−½+it}dt = Σ_m d(m)m^{−½}V_φ(m/k)k^{−½}.
  - This is because e^{−2iθ}Ξ² = ¼(t² + ¼)²|Γ_ℝ|²ζ(½+it)².
  - R291 is therefore a positive-cone Voronoi interpolation problem at the integers, the (N1)/T₂ lane
    (memory n1-voronoi: "no linear relations among integer values", D = 0, which suggests the integer values are
    free).
  - Constraint: the multiplier φ must be non-tempered (PrimeBlindCarlsonThreshold), and the null cone must reach
    both signs.
- **Verdict.** REDUCED. C291 ⟸ R291. R291 is open and sits in the (N1) Voronoi lane. Payoff if true: RH ⟺ the
  Gamma-only symbol θ′ + 2sin²θ integrates nonnegatively against doubly blind spectra. That is still a receiver
  (wall 12 for certificates), but pole-free.

## Row 293 — R291 as pointedness of the null Fourier image; link to the (N1) witness cone
- **Duality form of C291.** A doubly blind certificate (a, b) gives the symbol
  S_{a,b} = Θ − Σa_n n^{−½}cos(t log n) − Σb_k k^{−½}cos(2θ − t log k).
  - Tested on prime-blind Ξ²-divisible null tests v (Q(v) = 0 unconditionally):
    ∫μ_v S_{a,b} ∝ Σ_k (2 − b_k)ĝ_v(k).
  - If the null Fourier image N̂ = {(ĝ_v(k))_{k≥2}} is not pointed (no nonzero c with Σc_kĝ_v(k) ≥ 0 on N̂), every
    certificate has b ≡ 2. Then a = Λ − 1 by corpus cone uniqueness, and doubly blind PBAP ⟹ RH.
  - So C291 ⟸ (N̂ not pointed), the density form of R291.
- **Heuristic for non-pointedness.** If N were all prime-blind |Ξ|²φ (φ ≥ 0), a functional nonneg on N̂ needs a
  twisted polynomial D_c plus an almost-periodic A_a with D_c + A_a ≥ 0 a.e. Both have Cesàro mean 0 (chirps
  2θ − t log k; Bohr mean of A_a), which forces D_c + A_a ≡ 0 and hence c = 0, given independence of chirps and
  almost-periodic functions.
- **Caveat.** N may be small.
  - TMP rigidity makes arc-generated null families essentially unique.
  - But the corpus also has the a-twisted family (a ∈ [0, ¼), `TwistedArcFamilyN1Reduction`) and the two-arc witness
    h₊ (Fourier-blind at m ≥ 1).
  - Via the (N1) ⟺ Ξ-divisible-blind correspondence (`WeilConeXiDivisibleBlindTest`), N is at least
    multi-dimensional.
  - R291 is a statement about the size of the (N1) witness cone: do its null tests' Fourier values fill
    sequence space?
- **Verdict.** OPEN, reduced to the (N1) lane. C291 ⟺? non-pointedness of N̂; only ⟸ is shown. Next: compute the
  Fourier values of the corpus a-family null tests and test for a common sign functional.

## Row 294 — [L] doubly blind cores: pole = ‖f − JCf‖², mean-zero doubly blind cores vanish
- **[L] `RHTower/DoublyBlindCorePoleDistance`** (standard axioms, `lake --old` clean, wired):
  - `cosDilationKernel_zero_eq_integral_sq_sub_inverted`: Ψ_f(0) = ∫_0^∞ (f − JCf)²;
  - `cosDilationKernel_zero_nonneg_of_doublyBlind`;
  - `eq_zero_of_doublyBlind_of_cosDilationKernel_zero` and `eq_zero_of_doublyBlind_of_integral_eq_zero`;
  - supporting lemmas: half-line Plancherel `integral_Ioi_halfLineCosTransform_sq`, inversion unitarity
    `integral_Ioi_invertedCosTransform_sq`, periodization at the origin
    `two_mul_dilationAutocorr_one_eq_of_doublyBlind`.
- **Meaning.**
  - JC is the Mellin multiplier e^{−2iθ(t)} on L²(0, ∞) (corrected in row 295; it is unitary but not an
    involution).
  - For doubly blind tests the pole term is exactly the squared distance from that self-dual subspace, the formal
    compact-core form of "pole = (2/π)∫|𝓜u|²sin²θ" (row 291).
  - The corpus result (`CosDilationKernelPositivityRigidity`) needs Ψ_f(n) = 0 for all n ≥ 1. Here PBAP-blindness
    replaces the n = 1 condition and the conclusion is sharper: the pole cannot vanish.
- **Consequence for C291.** Doubly blind PBAP has no pole-vanishing sector; its energy is arch(f) + ‖f − JCf‖².
  RH content would sit in how close doubly blind tests can come to JC-self-duality while keeping arch(f) < 0.
- **Verdict.** STRUCTURE (new rigidity theorem, formal). Producer status unchanged; C291 / R291 still open.

## Row 295 — JC is the Riemann–Siegel phase operator; correction and reading
- **Computation.**
  - 𝓜[JCf](s) = 𝓜[Cf](1 − s) = (Γ_ℝ(1−s)/Γ_ℝ(s))𝓜f(s), i.e. JC = multiplication by e^{−2iθ(t)} on the critical line
    (corpus local FE `Gammaℝ_mul_mellin_halfLineCosTransform`).
  - So JC is linear and unitary, with (JC)² = e^{−4iθ} ≠ I.
  - Hence ‖f − JCf‖² = (1/2π)∫|𝓜f|²|1 − e^{−2iθ}|² = (2/π)∫|𝓜f|²sin²θ, matching row 291 by a second route.
  - JCf = f ⟹ f = 0 for every L² f (e^{−2iθ} ≠ 1 a.e.). The Lean rigidity of row 294 is the compact-core shadow
    of this, proved there without Mellin calculus.
- **Correction.** The ± decomposition f = f₊ + f₋ that I sketched is void, since JC is not an involution. Row 294's
  "involution" wording has been fixed.
- **Reading.** With U = e^{−2iθ(D)}, the doubly blind energy symbol is Θ = θ′ + (1 − Re U):
  - θ′ is the Gamma part of the Wigner time delay of the scattering phase 2θ;
  - 1 − Re U is the phase defect.
  - C291 is a constrained positivity of "time delay + phase defect". The Levinson/trace-formula reading of the
    explicit formula is wall 12 (spectral realisation).
- **Verdict.** BRIDGE plus correction. C291 / R291 unchanged.

## Row 296 — commutative multiplier picture; Fourier blindness as virtual nodes at log(e^{−A(0)}k)
- **Multiplier picture.** On the critical line every operator in play is a multiplier in the Mellin frequency t:
  - dilations D_n ↦ n^{−it};
  - JC = U = e^{−2iθ(t)};
  - the archimedean symbol 2θ′.
  So PBAP and its doubly blind form are linear programs over positive spectral densities ψ. The only
  non-multiplier, the pole (an off-line point evaluation), is converted by Poisson into ∫ψ(1 − Re U) plus twisted
  moments ∫ψUk^{it}. No non-commutative structure is available to produce positivity; the dual remains the zero
  measure (wall 12).
- **Virtual nodes.** Near t = 0, 2θ(t) ≈ A(0)t with A(0) = ψ(¼) − log π = −5.3722, so
  U k^{it} ≈ (e^{−A(0)}k)^{it} = (215.3·k)^{it}.
  - At low frequency, Fourier blindness at k acts like prime-blindness at the virtual nodes log(215.3k).
  - The constant e^{−A(0)} = 215.3 is exactly the even-character conductor threshold of CANNOT-539
    (A(0) + log q ≥ 0 ⟺ q ≥ 215.3).
  - So the second blindness family is the first family dilated by the critical conductor. Doubly blind PBAP is
    PBAP with an extra node set log ℕ + 5.372 at low frequency.
- **Verdict.** BRIDGE/numerology with content. It explains why the deficit −5.372 and the conductor 215.3 are
  the same number on both sides of the Poisson duality. No producer.

## Row 297 — heuristic verdict on C291: probably not RH-equivalent
- **Argument by analogy with row 269.** Adding blindness at nodes outside log(prime powers) shrinks the test cone
  and fattens the dual cone.
  - Row 269: PBAP with extra nodes E ⊃ log ℕ is non-RH because the TMP null family is not blind at E, so cone
    uniqueness fails.
  - By row 296, doubly blind PBAP is PBAP with extra virtual nodes log(215.3k) at low frequency (exact form: twisted
    characters U·k^{it}).
  - The twisted-arc null family is not Fourier-blind (no corpus statement says so; the (N1) witnesses are
    Fourier-blind but mean-zero, and the Ξ-divisible family is prime-blind).
  - So the uniqueness step of C291 has no null family to run on. The Fourier-side weights b_k of a doubly blind
    certificate are unconstrained by the available null tests.
- **What would settle it.**
  - A finite twisted-plus-plain certificate Θ − Σa_n n^{−½}cos(t log n) − Σb_k k^{−½}cos(2θ − t log k) ≥ 0 would make
    doubly blind PBAP unconditional (C291 false). Hand check: a single low-k twisted term lifting Θ(0) = −2.69
    overshoots near t ≈ 0.58, so plain terms must rebalance; this is a linear program (numerics).
  - Conversely, a doubly blind Ξ²-divisible null family would make C291 true (row 293).
- **Verdict.** C291 PROBABLY FALSE (heuristic). The pole-free Θ-form is then a weaker, non-RH statement. Its value
  is as a structural law (rows 291, 294–296), not as a route.

## Row 298 — [L] single-node Weil-positive weights for odd conductor q ≥ 7 (C288, partly settled)
- **[L] `RHTower/OddDirichletSingleNodeFakeProducer`** (standard axioms, `lake --old` clean, wired):
  - `re_digamma_add_mul_I_sub_ge`: first-Gauss-term growth of Re ψ on vertical lines;
  - `oddDirichletSingleNodeSymbol_nonneg_of_bounds`;
  - `oddDirichletSingleNodeSymbol_nonneg_two` (q ≥ 7, node 2);
  - `oddDirichletSingleNodeSymbol_nonneg_eight_three` (q = 8, node 3);
  - `integral_oddDirichletSingleNode_nonneg`.
- **Content.** For odd data with conductor q ≥ 7, a single cosine at log 2 with coefficient c_q ≤ ½ lifts the
  archimedean symbol to pointwise nonnegativity.
  - The odd Weil cone therefore contains a weight supported on {2}, far from Λχ, so PBAP_χ is unconditional and
    vacuous.
  - This is C288's dichotomy settled on the fake-producer side for q ≥ 7, with no numerics: it is an analytic
    certificate whose constants are checked by `linarith`.
- **Boundary.**
  - q = 3 (c = 1.132) and q = 4 (c = 0.844) are beyond the first-term method, since 16τ²/(27 + 12τ²) < 4/3 < 2c.
  - q = 5 needs the second Gauss term.
  - Whether the cone at q = 3, 4 is a point (a level-3/4 analogue of TMP) remains open (C270).
- **Lesson for RH.** Single-node certificates exist exactly while the deficit is small and there is no pole.
  - ζ's deficit 5.37 is about 7× beyond the single-node regime, and its pole makes the cone rigid.
  - The HF uniqueness is a large-deficit phenomenon. Conductors 3 and 4 are the interesting intermediate cases.
- **Verdict.** CANNOT (new, formal); structure for the HF route, not a producer.

## Row 299 — C299 deforming the data from the fat side (KILLED)
- **Conjecture.** Deform the archimedean data D(q, m) (conductor q, pole mass m) from a fat cone (q ≥ 216, zero weight
  admissible) to ζ = D(1, 1), keeping bounded certificates. The weak limit would lie in the ζ cone ⊆ {Λ}, giving RH.
- **Kill.** Λ ∈ cone(q, 1) ⟺ RH for every q ≥ 1.
  - Adding log q·‖u‖² is a bounded perturbation, while an off-line zero gives tests with Z(u)/‖u‖² → −∞ (cosh
    multipliers of type λ, growth e^{2λδ}).
  - Fake certificates in cone(q, 1) for q > 1 carry no information about Λ.
  - Continuation therefore needs unbounded weights, which defeats compactness. Verdict: CIRCULAR.
- **Correction found on the way.** The pole energy is P(h) = ⟨h, e^{x/2}⟩·⟨h, e^{−x/2}⟩ (Lévy–pole form,
  `RHTower.NonnegativeCone.poleEnergy`): a product of two functionals, with signature (1,1).
  - It is not positive semidefinite, so cones are not monotone in the pole mass m.
  - The earlier picture "the pole only helps" holds only on the nonnegative cone (both factors > 0).

## Row 300 — where an off-line zero must show up on blind tests [P]
- **Arch floor.** For every test, arch(u) ≥ A(0)‖u‖² = −5.37‖u‖², since the symbol is minimal at t = 0.
  - So a prime-blind test with F(u) = Z(u) ≪ −‖u‖² must have pole P(u) ≪ 0.
  - Detecting an off-line zero of depth δ with type-λ multipliers needs P ≈ −e^{2λδ}‖u‖².
- **Positive statement [P].** PBAP fails only through exponentially negative pole energy:
  P(u) = ab with a = 𝓜u(1) and b = 𝓜u(0) of opposite signs and both large. That needs mass at both ends ±L of the
  support with opposite signs.
- **Tradeoff [heuristic].** Blindness of the cross-correlation at the dense nodes log n ≈ 2L (spacing e^{−2L}) forces
  either:
  - smooth end pieces with ∫c₊₋ ≈ 0, which kills ab; or
  - frequency ≳ e^{2L} in the end pieces, which costs arch ≈ 2L per unit mass and shrinks |∫h e^{±x/2}|.
  - For bump pairs the pole/arch ratio is ≈ e^{−X}/X → 0.
  - PBAP is exactly the statement that this tradeoff never loses. Its quantitative weakening "P ≥ −C e^{θL}(arch + c)"
    is a zero-free strip Re ρ < ½ + θ/2 (quasi-RH-hard; consistent with CANNOT-517).
- **Doubly blind tests.** Their pole is ‖f − JCf‖² ≥ 0 (MUST-1449), hence F ≥ −5.37‖u‖².
  - They cannot carry the exponential signal; an off-line zero is visible to them only with bounded strength.
  - This does not refute C291 (a bounded negative value suffices), but it locates C291's content in "mild"
    detection only.

## Row 301 — blind spectral measures are spread [P]
- **Not band-limited.** A prime-blind finite measure μ is atomless: its pushforward to each prime circle is Haar
  (MUST-1447). It is also not band-limited: if μ had compact support, μ̂ would be entire of exponential type with
  ≫ e^R/R zeros in [0, R], so μ̂ ≡ 0.
- **One-prime arch floor.** Blindness at the powers of 2 alone gives ∫A dμ ≥ μ(ℝ)·(1/T₂)∫_{−T₂/2}^{T₂/2}A.
  - Here T₂ = 2π/log 2, using the coset minimum and the evenness and monotonicity of A in |t|.
  - The value is about −1.5 per unit mass, against −5.37 pointwise.
  - The window indicator of length log 2 has arch ≈ −1.15 per unit mass [estimate]. So the arch alone stays negative on
    blind tests, and the pole is indispensable even on windows (Yoshida-type positivity uses it).
- **Verdict.** Structure only; the constants are estimates and were not formalized (no numerics).

## Row 302 — the conductor-bound reading of window positivity [P]
- **Reading.** For pole-free data (parity ε, conductor q), every window test (log-support < log 2) is blind at every
  n ≥ 2. Hence nonempty cone ⟹ arch_{ε,q} ≥ 0 on windows. That is exactly the explicit-formula (Odlyzko–Mestre)
  lower bound for the conductor.
- **Estimates** (indicator window, odd data). arch_{odd,1} ≈ −1.04 per unit mass < log 3 = 1.099.
  - So χ₋₃ sits just above the odd window threshold, and is the minimal-conductor case.
  - Even pole-free conductor-1 data has negative window energy (≈ −1.15). ζ's window positivity exists only through
    the pole.
- **Picture for HF.**
  - Large conductors: fat cones (CANNOT-539/540).
  - Near the window threshold: thin cones (conductor 3: no single node, row 303).
  - ζ: the pole carries window positivity and makes the cone a point.
- **Conjecture C302 (open).** The odd conductor-3 cone (χ₋₃) contains no finitely supported weight.
  - True ⟹ χ₋₃ is the first pole-free candidate for an HF-type rigidity, needing a Γ₀(3)-analogue of TMP.
  - False ⟹ a finite fake exists.

## Row 303 — [L] single-node threshold for odd data lies in (3, 5] (CANNOT-541, MUST-1451)
- **[L] `RHTower/OddDirichletSingleNodeConductorThreshold`** (standard axioms, `lake --old` exit 0, wired):
  - `hasSum_re_digamma_vertical_sub`: the exact vertical Gauss expansion;
  - `sum_range_le_re_digamma_vertical_sub`: finite lower bounds;
  - `re_digamma_vertical_sub_le`: three terms plus a telescoped tail;
  - `oddDirichletSingleNodeSymbol_nonneg_two_of_five_le`: q ≥ 5, node 2;
  - `not_forall_oddConductorThree_singleNodeSymbol_nonneg`: q = 3, no single node at any m ≥ 2 with any weight;
  - constants `eulerMascheroniConstant_lt_harmonic_sixteen`, `log_five_ge`, `oddDeficit_three_ge`.
- **Content.** Single-node fakes exist for every odd conductor ≥ 5 and for no odd data at conductor 3.
  - Conductor 4 (c₄ ≈ 0.844) is undecided by these bounds. Expected feasible at node 2: margin ≈ 0.04 at y ≈ 2 with
    4–8 Gauss terms and the sixth-order cosine bound.
- **Link to row 302.** Conductor 3 is the minimal odd conductor and sits just above the odd window threshold. Its
  cone is the thinnest among actual odd characters.
  - The next question is C302: does the χ₋₃ cone contain any finite weight?
  - Two-node trials {2,3} and {2,4} fail on paper (row 302 estimates). A general finite-node obstruction would need a
    blind measure with negative S₃-energy beyond windows.
- **Verdict.** MUST/CANNOT (new, formal). Structure for the HF route (which conductors can carry an HF-type
  rigidity); not an RH producer.

## Row 304 — corpus audit of rows 299–302 (rediscoveries noted)
- **Already in the corpus**, so rows 299–302 overlap and nothing more is claimed for them:
  - the pole hyperbolic plane (PBAP ⟺ Arch + 2(∫f cosh)² ≥ 2(∫f sinh)², ULF lane);
  - "Weil-cone rigidity is a pole phenomenon" (MUST-1442 addendum);
  - the pole-weight family β (MUST-1445/1446, C190);
  - blind spectra at the Carlson edge, stronger than my row-301 "not band-limited"
    (`PrimeBlindCarlsonThreshold`, `IntegerBlindLogarithmicCarlsonCritical`, critical K = π/2);
  - "finite level is free, rigidity is compactness at infinity".
- **Also rediscovered: finite-level compactness.** Let C_L be the set of weights on nodes ≤ e^L that make the Weil
  form PSD on tests of support ≤ L. Then RH ⟺ C_L ≠ ∅ for every L. Proof: compact nested projections give a
  consistent weight in the full cone, hence Λ by uniqueness. This is exact but constructs nothing (Nyquist wall).
- **Lesson.** Grep the memory hubs (pole-weight-rigidity-srp, relaxed-producer-abscissa) before any pole/cone
  cycle.

## Row 305 — C193 (shifted TMP) in potential language; one-dimensional maximum-principle reduction [P]
- **Dictionary.** Write f(u) = 4Σ a_i K₀(k_i√(1−u²))cos(k_i u), the arc trace of the axisymmetric harmonic function
  Φ(x,y) = Σ a_i K₀(k_i y)cos(k_i x) in ℝ³ (axis = x-axis, y = distance to the axis). Then:
  - twisted moments: F/√y = 𝔐²f with 𝔐 the spherical Legendre operator;
  - on harmonic Φ, 𝔐 = −E(E+1) with E = r∂_r, and E(E+1) + λ₀ = (E+½−α)(E+½+α), α = √(¼ − λ₀);
  - so C193 is the TMP for Φ' = −(E+½−α)(E+½+α)E²(E+1)²Φ.
- **Where the proof breaks.** E is the dilation about 0. The wall x = ½ is the mirror exchanging the arcs |z| = 1 and
  |z−1| = 1. The stream function of the shifted data equals −yψ_xy(½,y) on that wall (computed from ψ = ψ_y =
  ψ_xx = 0 there), not 0. This matches the recorded obstruction.
- **Reduction [P].** Suppose (𝔐 − λ₀)F ≥ δ > 0 on [0,½], with F even and λ₀ > 0.
  - An interior maximum u* of F has 𝔐F(u*) ≤ 0, so F(u*) ≤ −δ/λ₀ < 0. Then −F > 0 on the whole arc,
    contradicting the TMP (applied to −F).
  - Hence F attains its maximum on [0,½] only at u = ½, with F(½) ≥ 0 and F′(½⁻) ≥ 0.
  - So C193 ⟺ excluding the corner configuration "strict maximum of F at the corner ρ". This agrees with and
    sharpens the recorded corner-local bad case.
  - Not formalized: `twArcMoment` has no u-derivatives in Lean yet.
- **Odd sector [P].** All s = ½ point vectors |x − z|⁻¹ with |z| = 1 are self-reciprocal. Odd-sector vectors arise
  only from mirror pairs v_z − |z|⁻¹v_{1/z̄} off the arc. At the arc they become radial dipoles, whose moments are
  E Φ on the arc, i.e. odd polynomials in (E + ½), since E + ½ anticommutes with the Kelvin inversion. The operator
  trick (𝔐 − λ₀), even in (E+½), mixes the sectors: (τ² + α²)H = |τQ|² + α²|Q|².
- **Verdict.** C193 remains open; the reduction is exact. This is a route decision (SRP), not a producer.

## Row 306 — WindowPositive by pointwise relaxation fails [P]
- **Setting.** For h ≥ 0 on a window of length ℓ = log 2, with c = h⋆h̃:
  E ≥ c(0)(A(0) + 2Ω(ℓ)) + 2∫₀^ℓ[ω(c(0) − c) + 2c cosh(x/2)].
- **Pointwise (box) minimisation over c(x) ∈ [0, c(0)].** The minimiser is c = c(0)·1_{[0,x₀]} with x₀ = log(plastic
  number), and the bound is c(0)(A(0) + 2Ω(x₀) + 8 sinh(x₀/2)) ≈ c(0)(−5.37 + 4.09 + 1.13) = −0.15·c(0).
- **Subadditivity.** D(x) = ‖h − h_x‖ is subadditive, which forces c(x) ≤ (1 − ⌈ℓ/x⌉⁻²)c(0). This recovers only
  ≈ 0.003.
- **Conclusion.** The positive-definiteness structure (not just pointwise bounds) carries the 0.15 margin, so
  WindowPositive needs a spectral certificate (numeric-design type; blocked under the no-computation rule).
- **Verdict.** FAILED analytic route; recorded.

## Row 307 — [L] Fourier-integer-blind cores have support ratio ≥ 3/2 (MUST-1454)
- **[L] `RHTower/CosDilationBlindSesquiSupportVanishing`.** Theorem
  `eq_zero_of_cosDilationKernel_blind_of_lt_three_halves_mul`: Ψ_f(n) = 0 for all n ≥ 2 and β < 3α/2 ⟹ f = 0. The
  corpus short-core theorem needed Ψ_f(0) = 0, i.e. mean zero; this removes that hypothesis below ratio 3/2.
- **Mechanism.** The Poisson periodization of A_f is a trigonometric polynomial of degree 1. Below ratio 3/2 it has a
  gap interval (R−1, 2−R) around ½ where every translate |x+k| leaves supp A_f, which forces Ψ_f(0) = Ψ_f(1) = 0.
- **For C291.** Doubly blind compact cores, if any exist, have support ratio ≥ 3/2.
- **Open conjecture C307.** None exist below ratio 2.
  - Degrees-of-freedom heuristic: constraints ≈ Bβ vs freedom ≈ 2B(β−α), so the problem is overdetermined for β < 2α.
  - With Ψ_f(0) free the two periodization nodes x = 0 and x = ½ give Ψ_f(0) = A_f(1) + A_f(3/2) ≥ (7/12)A_f(1). This
    is consistent, not contradictory, so C307 needs the full Mayer-type functional equation on [1/R, 1].
- **Insight [P].** Compactly supported even G with Ĝ(n) = 0 for every |n| ≥ 2 are exactly G = K⋆m.
  - Here K = 2cos²(πx)·1_{[−½,½]} is the Hann window and m is an even distribution supported in |x| ≤ R − ½.
  - Reason: Ĝ = [sinc(ξ)/(1−ξ²)]·m̂ by Paley–Wiener–Schwartz, and sinc/(1−ξ²) is the transform of the Hann window,
    which tiles to 1 + cos 2πx.
  - For doubly blind cores, the pole Ψ_f(0) equals the mass of m and Ψ_f(1) = ½ m̂(1).
- **Verdict.** MUST (new, small); structure for the C291 lane, not a producer.

## Row 308 — C307 up to the golden ratio [P]: Fourier-integer-blind cores of ratio R < φ = (1+√5)/2 vanish
- **Farey transfer form.** For R = β/α < 2, B := A_f|_{[½,1]} (zero below 1/R) satisfies on (½, 1)
  B(u) + B(φ₁u)/(2−u) + B(φ₂u)/(1+u) = c(u) := Ψ_f(0) + 2Ψ_f(1)cos 2πu, with φ₁u = 1/(2−u) and φ₂u = 1/(1+u).
  These are the inverse branches of a Farey-type map with a parabolic fixed point at 1; the weights are |φ_j′|^{1/2}
  (a transfer operator at s = ½).
- **Region II** (u > R−1, which holds on (1/R, 1) iff R < φ, since R/(R+1) < 1/R). The φ₂-term vanishes. In
  v = 1/(1−u) the map φ₁ is v ↦ v+1, and B(t) = v·F(v), where F(w) := Σ_{i≥0}(−1)^i g(w+i) and
  g(x) = c(1 − 1/x)/x. This uses B continuous at 1.
- **Region I** (u ∈ (R−1, 1/R), nonempty iff R < φ). B(u) = 0 and the φ₂-term is 0, so B(φ₁u) = (2−u)c(u).
  Comparing with Region II on φ₁((R−1, 1/R)) gives, via F(w) + F(w+1) = g(w):
  F(w) = 0 for all w ∈ (1/(2−R), R/(R−1)), which is a nonempty interval inside [2, ∞) when 3/2 ≤ R < φ.
- **Conclusion.**
  - F extends analytically to Re w > 0, so F ≡ 0.
  - Euler–Boole summation gives F(w) = ½g(w) − ¼g′(w) + … with g(x) = (Ψ₀ + 2Ψ₁)/x − 4π²Ψ₁/x³ + …. Hence
    Ψ₀ + 2Ψ₁ = 0.
  - Then g(x) = −4Ψ₁ sin²(π/x)/x, with positive decreasing terms for x ≥ 2, so the alternating sum is nonzero
    unless Ψ₁ = 0.
  - So Ψ_f(0) = Ψ_f(1) = 0, and the short-core theorem gives f = 0.
- **Status.** [P] for 3/2 ≤ R < φ, which together with the formal R < 3/2 case gives the range R < φ. Not formalized:
  the analytic-continuation step and the asymptotics are heavy. A finite alternative is a Wronskian or monotonicity
  bound for σ/β, where β(w) = Σ(−1)^i/(w+i) = ∫₀¹x^{w−1}/(1+x)dx and σ(w) = Σ(−1)^i sin²(π/(w+i))/(w+i).
- **Beyond φ.** φ₂ enters Region II. The Farey picture suggests the method extends by induction along the
  Stern–Brocot/Farey tree up to R = 2, which is the degrees-of-freedom threshold.
- **Verdict.** Structure (C291 lane). The golden ratio threshold is new; the transfer-operator form links doubly
  blind cores to the Farey map at s = ½.

## Row 309 — [L] the golden-ratio threshold is formal (MUST-1455)
- **[L] `RHTower/CosDilationBlindGoldenSupportVanishing`** (611 lines; standard axioms; `lake --old` exit 0;
  wired). Row 308's paper proof is now a Lean theorem, `eq_zero_of_cosDilationKernel_blind_of_golden`.
  - It uses no asymptotics: after the identity theorem, the recursion at v = 2 and v = 4 gives Ψ_f(0) = 0
    directly.
- **Reusable pieces.**
  - `dilationAutocorr_farey_recursion` (the transfer recursion);
  - `altHarmonicR_add_one`, `altCosDefectR_add_one` (functional equations);
  - `norm_cos_sub_one_le` (complex cosine bound on |x| ≤ 4π);
  - holomorphy of the two alternating series on Re z > ½.
- **Next.**
  - Beyond φ the second Farey branch enters Region II; the Stern–Brocot induction toward ratio 2 is C307.
  - Existence of doubly blind cores at ratio ≥ 2 decides whether C291 means anything on compact tests.
- **Verdict.** MUST (new, formal). It belongs to the HF/C291 structure lane, not to a producer.

## Row 310 — the next Farey level: blind cores vanish below ratio 5/3 [P]; structure of C307
- **Two-branch equation [P].** For R < 2 and every v ≥ 2 (periodization at x = 1 − 1/v; the translates
  k = 0, −2, 1 survive):
  H(v) + H(v+1) + H(τv)/(v−1) = g(v), with τv = 2 + 1/(v−1) and g(v) = (Ψ₀ + 2Ψ₁cos(2π/v))/v.
  - τ is the Gauss branch; its fixed point is φ² = (3+√5)/2. H = 0 on [2, w₂] with w₂ = R/(R−1).
  - The branch term vanishes for v ≥ v* := 1/(2−R), so H = F (the explicit decaying series) on [v*, ∞).
- **Level two (φ ≤ R < 5/3) [P].**
  - Since v* ≤ 3, for v ∈ [2, w₂] the equation gives H(τv) = (v−1)F(v).
  - Where τv ≥ v* (a nondegenerate interval since R < 5/3), this yields the Lewis-type identity
    (v−1)F(v) = F(2 + 1/(v−1)). Both sides are holomorphic on Re v > 1, so the identity holds for all v > 1.
  - Letting v → ∞ (vP(v) → ½, vE(v) → 0) gives F(2) = a/2. At v = 2 it gives F(2) = F(3), and with
    F(2) + F(3) = g(2) this yields b = −a/2.
  - Then F = a·Σ(−1)^i k(v+i) with k(x) = (3 − cos(2π/x))/(2x), which is positive and decreasing on [2, ∞), so F
    has the sign of a. At the fixed point φ² the identity forces F(φ²) = 0, hence a = b = 0 and f = 0.
- **Structure of C307.**
  - Each further level of the Stern–Brocot/Farey tree adds one Lewis-type identity of the three-term period
    equation H + T₁H + T₂H = g.
  - C307 (ratio 2) amounts to showing that a bounded decaying solution vanishing on [2, w₂] must coincide with the
    one-branch solution. That is a uniqueness statement for Lewis–Zagier-type period functions at s = ½.
- **Corpus relevance.** The TMP (N1) witness is itself an integer-Fourier-blind (Ψ-blind) PD kernel of decay class,
  i.e. a noncompact blind core. The compact case is rigid below ratio 5/3 (and conjecturally below 2), which is
  consistent with the (N1) producer being necessarily noncompact.
- **Status.** [P] for ratio 5/3, not formalized (incremental over row 309). C307 remains open.
- **Verdict.** Structure; not producer-relevant beyond the (N1) noncompactness picture.

## Row 311 — [L] the 5/3 Farey level is formal (MUST-1456); correction to row 310
- **[L] `RHTower/CosDilationBlindFiveThirdsSupportVanishing`.** Row 310's paper proof is now in Lean.
  - The golden module was refactored to expose the decaying-series solution, uniqueness of decaying solutions, the
    profile identification and the identity-theorem-on-a-real-interval lemma.
- **Correction to row 310.** The TMP witness h is Fourier-side blind only: 𝓕h(N) = 0, inversion law, PD log profile.
  It is not known to vanish at the integers, so it is not known to be doubly blind.
  - The claim that C291 is non-vacuous via (N1) is withdrawn; the card was corrected.
  - Precise mechanism (corpus `TwistedArcMomentPositiveRH`): the archimedean shadow h, with 𝓜h ↔ |G|²R, is
    Fourier-blind exactly when the null kernel ξ²R is integer-blind. Fourier-side blindness of ξ²R is the separate
    ζ²/Voronoi condition R291.
- **Verdict.** MUST (new, formal). Blind-core structure; still not a producer.

## Row 312 — Wall 13 test on arc vectors (KILLED quickly); the Gauss–Farey equation is Lewis's equation for E(z, ½) [P]
- **C312 (Wall 13 via arc energies).** Hoped: E(g_u) ≥ 0 for every arc vector, so superpositions would inherit a
  sign.
  - Kill: arc superpositions h = ∫g_u dμ are Fourier-blind archimedean shadows. The prime-blind objects they produce
    are the null kernels ξ²R, which have E = 0 because K̂ carries the factor ζ(½+it)².
  - Any kernel whose spectrum carries a ζ factor is null. A kernel that detects zeros cannot come from this mechanism.
    This is Wall 12 in concrete form.
  - Variant with |L(½+it,χ)|² in place of |ζ|²: the kernel is null for L(χ), but its ζ-energy is Σ over ζ-zeros,
    with no unconditional sign. Verdict: CIRCULAR.
- **Insight [P].** The homogeneous Gauss–Farey equation h(v) + h(v+1) + h(2 + 1/(v−1))/(v−1) = 0 (rows 309–311) is
  the Lewis–Zagier three-term period equation at s = ½, written in Farey coordinates.
  - At λ = ¼ there are no cusp forms for SL₂(ℤ) (λ₁ ≈ 91.1). The candidate solutions come from the Eisenstein series
    E(z, ½) = 2√y + c√y Σ_n d(n)K₀(2πny)cos 2πnx.
  - Its nonconstant modes are exactly the twisted arc Whittaker modes of the TMP.
  - So existence or non-existence of compact Fourier-blind cores above ratio 2 (C307 and its converse) is governed by
    the period function of E(z, ½), whose coefficients are the divisor function d(n), i.e. ζ².
  - This ties the blind-core lane, the TMP arc and R291 (the ζ²/Voronoi condition) to one object.
- **Verdict.** Structure. Next possible target: the period function of E(z, ½) as the obstruction or generator of
  compact Fourier-blind cores at ratio ≥ 2.

## Row 313 — C313 (no compact Fourier-blind cores at any ratio): linearization and the Heisenberg-uniqueness view [P]
- **Linearization.** The rigidity proofs of rows 307–311 use the core f only at the very last step (A(1) = ‖f‖²).
  - Everything before that is linear in G := A_f(|x|): continuity, support in [1/R, R], the inversion law
    G(1/x) = |x|G(x), and Fourier-blindness Ĝ(n) = 0 for |n| ≥ 2.
  - Linear C313: is there a nonzero continuous inversion-symmetric G, compactly supported away from 0, with Ĝ(n) = 0
    for all |n| ≥ 2? For R < φ the Farey argument gives no (with g = 0 the regions [2, w₂] and [v*, ∞) cover
    [2, ∞)); PD is not needed.
  - Degree-of-freedom count for the linear problem: free data G|_{[1/R,1]} against periodization constraints on
    [0, ½], so it is overdetermined below R = 2 and underdetermined above.
- **Heisenberg-uniqueness view.** By inversion, ∫G(x)e^{2πinx}dx = ∫G(t)e^{2πin/t}dt/|t|. So the condition is the
  lattice-cross annihilation problem on the hyperbola (Hedenmalm–Montes-Rodríguez), with weights 1 and 1/|t| tied
  by the symmetry, parameters αβ = 4 > 1 (non-uniqueness regime), exceptions n = 0, ±1, and compact support.
  - The relevant transfer operator is the Gauss-type map at s = ½, consistent with row 312 (Lewis equation for
    E(z, ½)).
- **RH relevance (recorded, not new).** Zeros of ζ(2s) are eigenvalue-±1 points of Mayer's L_s (Z(s) = det(1 − L_s²)),
  so RH ⟺ no such points with ¼ < Re s < ½ off the Maass spectrum. This is a complex-s spectral statement where
  transfer-operator positivity (real s) does not reach: Wall 13 again.
- **Status.** C313 open: linear existence above ratio 2 is likely; PD existence unknown.
- **Verdict.** Structure. No producer.

## Row 314 — C313 in spectral form: chirp blindness, and an envelope heuristic for existence [P]
- **Spectral form.** With U(t) = 𝓜f(½+it), the core is Fourier-integer-blind iff
  ∫|U(t)|² e^{i(2θ(t) − t log k)} dt = 0 for all k ≥ 2 (the row-291 chirp symbols). Here θ is the Riemann–Siegel
  theta and |U|² is entire of exponential type log R.
- **Linear existence above ratio 2 (sketch).** Write G = h + Jh with Jh(x) = h(1/x)/x and h supported in [1, R].
  - The periodization becomes, for x ∈ (0, ½]: u(1+x) + u(2−x) + u(1/(1−x))/(1−x) = r(x), with u = h|_{[1,2]} and r
    fixed by the free data h|_{[2,R]}.
  - That is one equation on an interval of length ½ for an unknown on an interval of length 1, so it is
    underdetermined. Choosing u on (1, 3/2] freely, the rest can be solved Farey-recursively.
  - So the linear form of C313 is very likely false for R ≥ 2. Continuity at the joins was not checked.
- **Positive-definite existence (heuristic).**
  - The chirp at k is stationary at t = 2πk with window ≍ √k. Blindness forces the smooth envelope of |U|² to vanish
    to leading order at every t = 2πk.
  - The choice f(e^v)e^{v/2} = φ(v + ½) − φ(v − ½) gives |U|² = 4 sin²(t/2)|φ̂|², a double zero at every 2πk. It kills
    all leading stationary-phase terms at once, with ratio R ≈ e·(support of φ).
  - Exact blindness needs corrections at every order in k^{−1/2}. Plausible for large R but not proved.
- **Status.** C313 is probably false at large ratios: compact blind cores likely exist and are built from
  e-dilation differences. Both directions are open in the PD setting.
- **Meaning for C291.** If such cores exist, compact doubly blind tests exist once A(n) = 0 is also imposed for
  2 ≤ n ≤ R (finitely many more conditions).
- **Verdict.** Structure; open.

## Row 315 — [L] linear Heisenberg-type rigidity below the golden ratio (MUST-1457)
- **[L] `RHTower/InversionSymmetricFourierBlindRigidity`.** Theorem
  `eq_zero_of_inversionSymmetric_fourierBlind_of_golden`: continuous, even, inversion-symmetric (G(1/x) = xG(x)),
  zero on [0, c) with c² + c > 1, and Ĝ(n) = 0 for |n| ≥ 2 ⟹ G = 0.
  - Also: the general Poisson periodization lemma `tsum_add_eq_of_fourierBlind` for even, compactly supported,
    Fourier-blind functions.
- **Linear threshold.** The linear form of C313 now has a formal lower bound φ, with existence above 2 sketched
  (row 314). The true linear threshold lies in [φ, 2]. The second Farey level (row 311) lifts the lower bound to 5/3
  for autocorrelations; the same argument should work linearly.
- **Verdict.** MUST (new, formal). Uniqueness-pair structure; not a producer.

## Row 316 — survey of candidate "Needs" (all RH-equivalent); Farey-tree structure of the linear threshold problem [P]
- **Candidate survey.** Re-checked every candidate route's "Needs" (APF, BAG, BSH, CDC, CTF, DR, EGC, EWJ, FEL, GTA,
  HCF, HJ, IRK, JAS, MSC, PBM, PCS, PTR, RFHM, SC, SEC, W1C, WBF). Each core is stated as RH-equivalent (rows 564,
  707, 714 of the corpus ledger). No candidate has a non-RH handoff that a structural lemma could close.
- **Producer sources reconsidered.**
  - Jensen/outerness of (s−1)ζ(s) on Re s > ½ is a one-sided log|ζ| bound. Moments overshoot by Jensen's inequality:
    Wall 2.
  - Mollifier/Selberg positivity gives proportions: typical-height lane, saturated.
  - Λ(n) ≥ 0 only reaches σ > 1: Wall 6.
  - Transfer-operator (Mayer) positivity is real-s only: Wall 13.
  - No new source found.
- **Linear threshold problem, φ < R < 2 [P].**
  - Regions: Z = [2, w₂) where H = 0, E = [v*, ∞) where H = F, and U = (w₂, v*) unknown.
  - The Gauss branch τ maps U into itself (τ(w₂) = R + 1 < v* iff R > φ) and contracts to φ²; the shift v ↦ v+1
    exits U into E in finitely many steps.
  - With k(u) = H(τu)/(u−1) supported on [2, v*): (u−1)k(u) = F(τu) − Σ_i (−1)^i k(τu + i) on [2, v*), and
    F(v) = Σ_j (−1)^j k(v + j) on Z.
  - Rigidity ⟺ this system forces a = b = 0. Level 2 (R < 5/3) is the case where it closes in one step (row 311).
    Deeper levels are period-function identities for the explicit series F.
- **Status.**
  - Linear threshold R* ∈ [φ, ≈3]: φ is formal (row 315); 5/3 is formal for autocorrelations and likely transfers to
    the linear case; the upper bound ≈3 is from the existence sketch.
  - Conjecture R* = 2.
- **Verdict.** Structure; no producer.

## Row 317 — C317: linear 5/3 threshold (MUST-1459) [L]
- **Statement.** Inversion-symmetric Fourier-blind G (|n| ≥ 2) with support ratio 1/c < 5/3 vanishes. Linear form of MUST-1456; no positive definiteness.
- **Mechanism.**
  - Gauss–Farey equation for G, then the Lewis identity on (2, q), then a₀ = a₁ = 0.
  - New step: τ maps the window [1/(1−c), c/(2c−1)] into itself, so H = −H∘τ/(v−1) is a contraction (factor (1−c)/c < 1). H = 0.
- **Refactor.** `eq_zero_of_fareySeriesR_lewis_identity` is shared between the dilation module and the linear module.
- **Status.** Linear threshold R* ∈ [5/3, ≈3]. Conjecture: R* = 2.
- **Verdict.** Structure; no producer. It is a positivity-free uniqueness statement, which is the direction the user asked for next.

## Row 318 — C318: census of producer mechanisms that do not need positivity
- **Trigger.** The user asked for routes that do not need positivity. Row 316 had claimed positivity was the only producer route; that claim is withdrawn as unexamined.
- **Census of the frontier map** (non-positivity routes, with each missing step):

| Route | Missing step | Reduces to |
|---|---|---|
| DR, PBM | convergence of Σ(Λ(n)−1)n^{−s}/log n, or Σ(1_P(n) − 1/log n)n^{−s}, at real s > ½ | (a) √x cancellation |
| MC | Möbius sum ≪ x^{½+ε} | (a) |
| CTF | bounded-row approximation, or the dual sampling inequality | (a) — the rows are forced to μ |
| Báez-Duarte, Farey D₁/D₂ | rate bounds | (a) |
| BAG | deterministic returns | (b) Wall 7; the Bohr support theorem puts returns in a null set |
| IRK, HJ, CDC, PCS, SC, RFHM, BSH, GTA, EWJ, APF | arithmetic landing | (c) the zero set restated |
| Speiser | ζ′ has no zeros in 0 < σ < ½ | (c), moved to ζ′ |

  - New candidate MTR (Mayer transfer resonances): the double zeta Ψ_s(x) = Σ_{m,n≥1}(mx+n)^{−2s} satisfies Ψ_s(x) − Ψ_s(x+1) − (x+1)^{−2s}Ψ_s(x/(x+1)) = ζ(2s)(x+1)^{−2s}. So ζ zeros give homogeneous Lewis solutions at s = ρ/2 without the boundary term (1 + x^{−2s}). This is class (c): Lewis–Zagier ties these solutions to E*(z, ρ/2), whose constant term has a single power.
- **Mechanisms that prove RH-type theorems elsewhere without positivity:**
  - (i) Symmetry plus exact count, with a dominance parameter: Rankin–Swinnerton-Dyer, period polynomials, Lagarias–Suzuki a_y for y ≥ 1. For ζ no dominance parameter exists, because dominance and convergence to Ξ are opposed (Wall 4). The a_y family is all on-line for y ≥ 1, and the ξ-zeros appear only in the limit y → 0, at (ρ+1)/2.
  - (ii) Stepanov counting: needs a Frobenius (Wall 5).
  - (iii) Lee–Yang/Asano contraction: needs an arithmetic ferromagnet (W1C).
- **Extremality.** Ξ is extremal in every known cone: Weil cone = {Λ}, Λ_dBN = 0, LP-maximal, Carlson edge. So inequality producers have zero slack, and a producer must be an exact identity or a rigidity statement.
- **Verdict.**
  - Census survives.
  - No non-positivity route has a producer step that is not (a), (b) or (c).
  - (a) is quasi-RH-hard. The classical zero-free-region mechanism near σ = 1 itself uses positivity (3+4cos+cos2, Λ ≥ 0). Turán power sums are positivity-free but local (Wall 3).
- **Next.** Attack (a) through a positivity-free mechanism, or build a dominance parameter for (i).

## Row 319 — C319–C322: positivity-free mechanisms, attacked one by one
- **C319 (Riemann's theta split satisfies Hermite–Biehler dominance).**
  - Write ξ = B + B^# with B(s) = ¼ + (s(s−1)/2)∫₁^∞ ω(x)x^{−(s+1)/2}dx, and B^#(s) = B(1−s).
  - B and B^# are entire with B ≈ ¼ + cs (c = Σe^{−πn²}), so B has only finitely many zeros. Asymptotically |B| > |B^#| on Re s > ½.
  - **FALSE**, by the exact identity |B|² − |B^#|² = Re((B − B^#)·conj ξ).
    - ξ decays like e^{−π|t|/4} while B ± B^# grow linearly. So dominance ⟺ Re((B − B^#)/ξ) > 0, i.e. B − B^# ≈ 2ict must follow the phase of ξ(σ+it).
    - That phase winds once per nearby zero, so the sign changes.
  - **Positive survivor.**
    - Any dominance split of ξ with a polynomially bounded odd part must wind with ξ, i.e. the odd part knows N(T).
    - The Rankin–Swinnerton-Dyer mechanism needs a noise-reduction parameter: the terms n^{−½}, n ≥ 2, must be small against the main term.
    - The heat time t is such a parameter, but only above height exp(C/t) (Polymath-type dominance). As t → 0 the dominance region escapes to infinity.
- **C320 (Lee–Yang in Bohr variables).**
  - Setup: w_p = p^{−s}. The functional equation is the inversion w_p ↦ 1/(p·conj w_p) through the torus |w_p| = p^{−½}. The critical line is that torus. Lee–Yang would follow from nonvanishing on the polydisc |w_p| < p^{−½}.
  - **Kill.** Regularize: ζ = G(w)·exp(L(w)), where G = Π(1−w_p)^{−1}e^{−w_p} is holomorphic and nonvanishing on the ℓ²-polydisc, and L = Σ_p w_p. The diagonal lies in the ℓ²-polydisc for Re s > ½, but L is unbounded on ℓ². On the diagonal L is the prime zeta P(s), whose continuation to Re s > ½ is equivalent to RH. So Lee–Yang reduces to core (a).
- **C321 (relative power gain from Dirichlet-convolution identities, e.g. Σ_d a_d M(x/d) = small).**
  - The target shape is the corpus "producer target shape": error ≤ n^{−δ}·error + O(√n).
  - **Kill.** A contraction at exponent θ needs Σ_{d≥2}|a_d|d^{−θ} < |a_1|. Then A(s) = Σa_d d^{−s} is zero-free on Re s ≥ θ. But smallness of the left side needs A/ζ to be analytic there, which is circular.
  - Lesson: relative gains cannot come from multiplicative convolution. They need additive (lattice) structure. This is the Beurling wall (`regular_integers_do_not_constrain_zeros` [L]).
- **C322 (relative gain from large-moduli variance, Barban–Davenport–Halberstam / Montgomery–Hooley).**
  - **Kill.** The q = 1 term is one summand. Transfer caps at the Bombieri–Vinogradov range and gives PNT strength only.
- **Big-picture insight (new formulation): RH is the degenerate-point problem of every family.**
  - Every unconditional square-root phenomenon holds for generic or averaged members: large moduli, short intervals, twists n^{−it} with t large, Bohr phases θ ≠ 1 almost surely, heat time t > 0 above height e^{C/t}, cosine level h ≥ ½.
  - ζ sits at the degenerate point: q = 1, t = 0 twist, θ = (1, 1, …), t = 0 heat time, h = 0.
  - The corpus states the same thing for Bohr: strong recurrence ⟺ continuity at θ = 1 ⟺ RH.
  - So a producer must be a rigidity that transfers generic behaviour to the degenerate point (continuity or analyticity in the family parameter at that point), or a symmetry that moves the degenerate point to generic ones. For ζ the only natural symmetry orbit is the vertical translates, a measure-zero curve in the Bohr torus.
- **Verdict.**
  - C319–C322 are killed.
  - Positive survivor: the degenerate-point principle. It tells the next cycle what a positivity-free producer must look like, namely a transfer to the degenerate point.

## Row 320 — C323 killed; C324: the Gauss transfer series reaches 1 + 1/√2 (MUST-1461) [L]
- **C323 (weak recurrence (WR) heights are closed, so WR at off-line zeros follows from density).**
  - The closedness half is true. If t_k → t and WR holds at t_k on enlarged compacts, then WR holds at t: Cauchy estimates on the return functions, which are bounded on the enlarged compact.
  - **Killed:** the set of zero-free heights for a fixed disc has interior gaps around every off-line zero height, so density cannot reach those heights. This is the degenerate-point principle again.
- **C324 (positivity-free transfer in the blind-core model).**
  - Statement: inversion-symmetric Fourier-blind G vanish when (1 − c)² < 2c − 1 (1/c < 1 + 1/√2).
  - Mechanism:
    - The holomorphic Gauss transfer series S solves S + (S∘τ)/(z−1) = F on Re z > 2, by geometric convergence after two Gauss steps.
    - On the τ-invariant window [1/(1−c), c/(2c−1)], the equation is two-term exactly when v* < w₂ + 1, i.e. (1 − c)² < 2c − 1. So H = S there, by uniqueness of bounded solutions.
    - The left edge gives H(τv) = (v−1)F(v) on an interval. The identity theorem gives S(τz) = (z−1)F(z) on Re z > 1, and then S ≡ 0 and F ≡ 0.
  - Corollary: Ψ-blind cores need β/α ≥ 1 + 1/√2.
  - The proof is simpler than the 5/3 one (no limit v → ∞, no fixed-point evaluation).
- **Reading.** This is the first instance in the corpus of the transfer the degenerate-point principle (row 319) asks for. The holomorphic fixed point of a transfer operator carries an identity from a real interval to the whole half-plane, including the degenerate end. It works because the Gauss branch is a strict holomorphic contraction (Denjoy–Wolff type, factor 4/5 after two steps).
- **Open.**
  - Below c = 2 − √2 the window equation has three unknown terms. The analogous object is the alternating Mayer-type operator Σ_n (−1)^n H(τ(v+n))/(v+n−1), which is not a sup-norm contraction.
  - Conjecture C325: the true linear threshold is R* = 1 + 1/√2, with a nonzero solution for c < 2 − √2. Alternatively, a weighted-norm contraction may push the threshold to 2.
- **Verdict.** Structure plus a new positivity-free transfer technique [L]. Not a producer.

## Row 321 — C326: a holomorphic contraction at ζ's degenerate point? Killed by the cusp principle
- **Conjecture.** The row-320 template (a holomorphic fixed point of a contracting transfer operator carries an interval identity to the degenerate end) has an arithmetic instance for ζ. Candidate: the Mayer/Lewis operator at s = ρ/2. Here ζ(2s) = 0 makes the double zeta Ψ_s(x) = Σ_{m,n≥1}(mx+n)^{−2s} a homogeneous Lewis solution, since Ψ_s − Ψ_s(·+1) − (x+1)^{−2s}Ψ_s(x/(x+1)) = ζ(2s)(x+1)^{−2s}.
- **Kill (the cusp principle).**
  1. In the blind-core model, the contraction worked only because compact support removed the parabolic branch v ↦ v+1: one parabolic step leaves the window. The threshold (1−c)² < 2c−1 is exactly where two parabolic steps fit inside it.
  2. In every transfer operator attached to ζ (Gauss/Mayer L_s, Farey map, Lewis equation), the parabolic branch is the cusp of PSL(2,ℤ). It carries the pole and the lattice density 1 that Beurling's wall says a producer must use. Its derivative is 1, so it never contracts.
     - L_σ has leading eigenvalue ≥ 1 for σ ≤ 1. The ζ-relevant s = ρ/2 (Re s < ½) lie in the continued region, where no domination by L_σ holds.
  3. Closing the cusp (truncation, or a character with χ(T) ≠ 1) restores self-adjoint control: the twisted Laplacian has pure point spectrum, so its zeta zeros sit on Re s = ½ or on the real axis. But it removes ζ, because ζ zeros are exactly the scattering poles of an open cusp.
- **Positive survivor (dichotomy).**
  - Closed cusp: automatic location (self-adjointness), no ζ.
  - Open cusp: ζ present, resonances on the non-unitary line Re s = ¼ (on RH), no self-adjoint control.
  - So the RH line for the modular surface is not its unitary axis. A positivity-free producer would need a contraction mechanism that survives an open cusp. None is known: the alternating structure (η, the "+" parabolic sign in the blind-core recursion) gives conditional convergence, not contraction.
- **Verdict.** C326 killed. Degenerate point = cusp = pole = lattice (consistent with rows 316, 319 and the Beurling wall).
- **Next.** C325, sharpness of 1 + 1/√2 in the blind-core lane.
  - For c < 2 − √2, the alternating parabolic sum gives H = F − MH with (MH)(v) = Σ_{0≤n<v*−v}(−1)^n H(τ(v+n))/(v+n−1) on the core (w₂, 3], plus the constraint MH = F on [2, w₂].
  - The term count ⌈v* − v⌉ is piecewise constant, so analyticity breaks at v = v* − n. That piecewise freedom is where a counterexample would live.
- **C325 (row 321 addendum, paper): 1 + 1/√2 is not sharp.**
  - The method extends to c > 7/12 (1/c < 12/7 ≈ 1.714).
  - Setup: for 3 < v* < 3.5, the interval [v*−1, q] with q = 1 + 1/(v*−3) is τ-invariant (τ(q) = v*−1, and τ(v*−1) ≤ q ⟺ v*² − 5v* + 5 ≤ 0). The two-term equation holds there because v+1 ≥ v*. So H = S on [v*−1, q].
  - For v ∈ [2, min(w₂, 1/(v*−3))], both v+1 and τv lie in [v*−1, q]. So S(z+1) + S(τz)/(z−1) = F(z) + F(z+1) on an interval, hence on Re z > 1, hence S(z+1) − S(z) = F(z+1).
  - Then a = 0 from the asymptotics: vF(v) = (v/(v−1))S(τv) − S(τ(v+1)) → 0, while (v−1)F(v) → a/2.
  - Then b = 0 from telescoping S(u) = −bΣ_j e(u+1+2j) with e(w) = (cos(2π/w) − 1)/w < 0. Evaluating at u = 2, 2.5, 3 gives b(P(2) + P(2.5)/2) = 0 with P < 0.
  - The remaining homogeneous window is a contraction (on J₀ the map v ↦ τ(v+1) has factor 1/v < 1).
  - Hard limit of this method: v* = φ² + 1 (c ≈ 0.5802, 1/c ≈ 1.7236), where the τ-invariant good interval disappears. Below that the full Lewis three-term structure is needed.
  - Not formalized: small gain, structural lane.

## Row 322 — C327, C328: regularized Mayer secular equation and the η twist (both killed)
- **C327 (regularize the cusp out of the Mayer operator).**
  - Write L_s = L_s^{reg} + P_s, with P_s f = f(0)·ζ(2s, z+1) the rank-one cusp part. L^{reg} converges for Re s > 0.
  - If ‖L_s^{reg}‖ < 1 on ¼ < Re s < ½, then det(1 − L_s) = 0 reduces to an explicit secular equation, 1 = ⟨δ₀, (1 − L^{reg})^{−1} ζ(2s, ·+1)⟩, built from a convergent transfer series.
  - **Kill:** this is a restatement. The secular function's zeros in the strip are exactly ρ/2, so locating them is RH again. Removing the cusp from the operator moves it into the rank-one datum ζ(2s, z+1).
- **C328 (η = (1 − 2^{1−s})ζ is entire; its theta θ₄ has a closed cusp at 0).**
  - **Kill:** the cusp at ∞ stays open (constant term 1, the s = 0 pole). ζ zeros survive in any modular object with an open cusp, and the parabolic branch at ∞ still has derivative 1.
- **Toy check of the cusp principle (paper).** The odd blind-core variant (G odd) has the parabolic step H(v) − H(v+1), a non-alternating sum. It still has golden-type uniqueness, because the weight 1/v in H(v) = G(1−1/v)/v pins the cusp value H(∞) = 0. So the sign of the parabolic step is not the whole story. The weight 1/v already supplies a cusp anchor in the compact-support model, and ζ has no such anchor.
- **State of the producer search (this session).**
  - Positivity routes end at the walls (2, 6, 11–13).
  - Non-positivity routes end at the three cores (√x cancellation, Wall 7, zero-set restatement).
  - The transfer mechanisms all fail at the open cusp.
  - No producer exists in the corpus or in this session's attempts.

## Row 323 — C329: Hecke–Maass–Selberg at the open cusp (killed); C330: cusp-edge principle; C331: R* = 2 via the Farey operator
- **C329.**
  - Setup: truncated resonant states u = Λ^T E*(·, ρ/2) and u' = Λ^T E*(·, (1−ρ̄)/2). Do Gram positivity or Hecke self-adjointness on them see β?
  - Maass–Selberg in the limit gives:
    - ‖u‖² = |ξ(ρ−1)|²T^{1−β}/(1−β);
    - ‖u'‖² = |ξ(1+ρ)|²T^{β}/β;
    - ⟨u, u'⟩ = 2ξ(ρ−1)ξ(1+ρ)T^{½}.
  - **Kill:** Cauchy–Schwarz becomes 4β(1−β) ≤ 1, i.e. (2β−1)² ≥ 0, which always holds. Hecke self-adjointness on Λ^T-states only produces explicit boundary identities, which hold for any zero.
  - **Positive survivor (receiver):** the Gram determinant equals |ξ(ρ−1)ξ(1+ρ)|²·T·(2β−1)²/(β(1−β)). This is a one-signed off-line detector that vanishes iff β = ½. It is one-signed only because it uses ρ's own resonant state (MUST-132 conflict).
- **C330 (refined cusp principle; structural).**
  - Clean reformulation of the blind-core problem for c > ½. With u = G on [½, 1],
    `(1 + T)u = a₀ + 2a₁cos 2πy` on [½, 1], u = 0 on [½, c),
    where Tu(y) = u(f₁y)·f₁(y) + u(f₂y)·f₂(y), f₁(y) = 1/(2−y) and f₂(y) = 1/(1+y). This follows from `inversionSymmetric_three_term_periodization` plus inversion.
  - Under z = 1/(1+t), f₁ and f₂ become the two inverse branches of the Farey map, with weights |f'|^{1/2}. So T is the Farey transfer operator at q = ½ (parabolic fixed point y = 1).
  - So blind cores are the **eigenvalue −1 problem** for the Farey operator at the cusp. Along the parabolic orbit, the solution of (1+T)u = h is an alternating sum Σ(−1)^n W_n h(f₁^n y) with W_n ~ 1/n, which converges. These are the alternating series (altHarmonic, altCosDefect) in `fareySeriesR`. The alternation tames the cusp.
  - For ζ, the Lewis/Mayer equation at s = ρ/2 is the **eigenvalue +1 problem**, Σ h(f₁^n y)/n. It diverges logarithmically; that divergence is the pole of ζ. Eisenstein period functions solve it for every s, and ζ(2s) = 0 is one extra linear condition.
  - Reading: ζ's zeros are threshold eigenvalues at the edge λ = 1 of the cusp's continuous spectrum. The tamed analogue (λ = −1, away from the edge) is where the positivity-free transfer methods work (MUST-1455/1456/1459/1461).
- **C331 (conjecture, structural).** R* = 2 exactly.
  - Length count in the (1+T) form: the unknown u lives on [c, 1] (length 1 − c), the equations on [½, 1] (length ½). So the system is overdetermined for c > ½ and underdetermined for c < ½.
  - Route to a proof: a Farey-tree induction that enlarges the set where H equals an explicit analytic expression (as in the √2 and 12/7 arguments) until two expressions meet. Alternatively: invertibility of 1 + T on a Farey–Laplace space, since the cusp's continuous spectrum lies in [0, 1] and −1 is away from it, with no Maass eigenvalue ¼ for SL(2,ℤ).
  - Curiosity: 5/3 = [1;1,2] and 12/7 = [1;1,2,2] are convergents of 1 + 1/√2 = [1;1,2,2,2,…]. The proven thresholds so far are continued-fraction convergents (or limits) of one expansion.
- **Verdict.** C329 killed. C330 is a structural principle that sharpens rows 319/321. C331 is an open conjecture in the structural lane. No producer.

## Row 324 — C332: blind cores are the χ-twisted Mayer problem at s = ½ (closed cusp); R* ≥ 2 reduces to a spectral statement
- **Exact reduction (paper, derived from proven lemmas).**
  - Setup: H(v) = G(1−1/v)/v. H = 0 on [2, w₂], H = F on [v*, ∞), and E(v): H(v) + H(v+1) + H(τv)/(v−1) = F(v) + F(v+1).
  - Alternate E over v, v+1, v+2, … (H(v+N) → 0, and F = Σ(−1)^n g(·+n)). This gives, for every v ≥ 2,
    `H(v) = F(v) − Σ_{n≥0} (−1)^n H(τ(v+n))/(v+n−1)`,
    and every τ(v+n) lies in (2, 3].
  - With ϑ(r) := H(2+r), r ∈ (0, 1], the whole system becomes
    `(1 + M)ϑ = F(2+·)` on (0, 1], ϑ = 0 on (0, w₂−2],
    where `(Mϑ)(r) = Σ_{m≥1} (−1)^{m−1} ϑ(1/(r+m))/(r+m)`.
  - M is the Mayer transfer operator of the Gauss map at s = ½, twisted by ε_m = (−1)^{m−1} = χ(S′T^m), with χ(T) = −1 and S′ the reflection [[0,1],[1,0]]. **M does not depend on c**; c enters only through the support condition.
- **Consequence.** R* ≥ 2 (uniqueness for every c > ½) follows from two facts:
  - (i) −1 is not an eigenvalue of M on a holomorphic space. After pairing m, m+1, M is nuclear there, so by the Fredholm alternative 1 + M is invertible and ϑ_F = (1+M)^{−1}F is real-analytic.
  - (ii) Continuous solutions vanishing near 0 coincide with ϑ_F. The sums are finite for such ϑ.
  - Then ϑ = 0 on (0, w₂−2] forces ϑ_F ≡ 0, hence F ≡ 0, hence a = b = 0 and H ≡ 0.
  - Fact (i) is, via the twisted Mayer–Lewis–Zagier dictionary, the absence of λ = ¼ Maass forms for PGL(2,ℤ) with the cusp-closing character χ (a level-2 congruence situation, where the spectral gap is expected). The proven thresholds (φ, 5/3, 1 + 1/√2, 12/7 on paper) are partial inversions of 1 + M on subintervals.
- **Reading (sharp form of the cusp principle).**
  - Blind cores: χ(T) = −1. The cusp is closed, there is no Eisenstein series, the spectrum is discrete, and positivity-free uniqueness holds; this is the "+" alternation of the Farey series.
  - RH: χ trivial at s = ρ/2. The cusp is open, Eisenstein and ζ(2s) appear, and the eigenvalue +1 sits at the edge of the continuous spectrum.
  - The positivity-free transfer methods are exactly the closed-cusp methods. Every RH producer must work in the open-cusp sector.
- **Verdict.** Structural. C331 is reduced to a closed-cusp spectral statement (open, deep). It is not formalizable now; it needs twisted Mayer nuclearity and Lewis–Zagier. No producer.

## Row 325 — C333: the unitary scattering phase at the open cusp (killed)
- **Conjecture.** The cusp scattering coefficient φ(s) = ξ(2s−1)/ξ(2s) is unitary on Re s = ½. Its phase −2 arg ξ(1+2it) is computable from the Euler product on the 1-line. It might give a one-signed off-line quantity that does not use ρ's own frequency.
- **Computation.**
  - φ is inner on Re s > ½: it is bounded there, |φ| = 1 on the line, and its zeros are at (1+ρ)/2.
  - So −d/dt arg φ(½+it) = Σ_ρ β/((β/2)² + (t−γ/2)²) + const. This is the Hadamard identity Re ξ'/ξ(1+it) = Σ_ρ (1−β)/|1+it−ρ|², read at σ = 1.
- **Kill.**
  - Every zero contributes with positive weight 1 − β, whatever β is, because the unitary axis lies at distance ½ from ζ's critical line. So the phase is one-signed but β-blind.
  - Pairing ρ with 1−ρ̄ gives f(β) + f(1−β) with f(x) = x/(x² + u²). This is below 2f(½) for u > 1/√3 (concave far field) and above it for small u. Since ∫P_x = π for every x, the far-field deficit is exactly compensated by the near-field surplus.
  - Detecting β therefore needs test functions varying at scale 1, which is the Weil explicit formula and its positivity again.
- **Positive survivor (principle).** A one-signed quantity without frequency information comes only from lines at positive distance from all zeros, and every such line is β-blind by mass conservation of Poisson kernels. This sharpens MUST-132.
- **Verdict.** Killed.

## Row 326 — [L] MUST-1462: the twisted Mayer reduction is formal
- `RHTower/InversionSymmetricFourierBlindTwistedMayer`:
  - `eq_sub_sum_of_gauss_farey_steps`: abstract alternating telescoping.
  - `inversionSymmetric_alternating_parabolic_sum`.
  - `twistedMayerHalf` and `inversionSymmetric_twistedMayerHalf`.
- This formalizes the reduction of row 324: blind cores ⟺ (1 + M)ϑ = F with the support condition, M the closed-cusp twisted Mayer operator at s = ½, independent of c.
- Next steps toward R* = 2:
  - (a) Nuclearity of the paired operator on a disc around [0, 1] (the pairs m, m+1 give O(1/m²)).
  - (b) −1 ∉ spec. This is a twisted Lewis–Zagier statement, deep.
  - (c) Continuous solutions vanishing near 0 are holomorphic.
- Verdict: structural [L]. No producer.

## Row 327 — C334: threshold tools (killed); C335: Bessel form of the cusp principle (Fermi vs Bose)
- **C334.** Mourre estimates, virial identities and Carleman unique continuation at the edge of ζ's cusp continuous spectrum.
  - **Kill:** each of these is a commutator or weight positivity. The dilation-commutator form on the Weil test space is a restricted Weil/PBAP positivity (walls 12/13).
  - The resonances ρ/2 have Im λ = γ(1−β)/2, which grows with height, so they are not near-real thresholds. A Mourre resonance-free strip in the s-plane is a zero-free region near Re 2s = 1.
- **C335 (structural, paper; standard ingredients checked).**
  - Mayer's Laplace representation f = 𝓛φ, together with (z+m)^{−1}e^{−t/(z+m)} = ∫₀^∞ e^{−(z+m)u}J₀(2√(ut))du, turns the twisted operator of MUST-1462 into
    `M𝓛φ = 𝓛(w·𝓗φ)`, `w(u) = Σ_{m≥1}(−1)^{m−1}e^{−mu} = 1/(e^u+1)`, `𝓗φ(u) = ∫₀^∞J₀(2√(ut))φ(t)dt`.
  - 𝓗 is unitary on L²(ℝ₊): its Mellin multiplier is Γ(s)/Γ(1−s), of modulus 1 on Re s = ½. So **‖M‖ ≤ sup w = ½ on H²(Re z > 0)**. The closed-cusp operator is a ½-contraction, and −1 ∉ spec on H².
  - Untwisted (ζ): w(u) = 1/(e^u − 1) = 1/u − β(u). The Bose singular part 1/u is ζ's pole. The remainder β(u) = 1/u − 1/(e^u−1) ∈ (0, ½] is again bounded by ½. This β is the corpus's CTF "chronological Bose" kernel.
  - So ζ's transfer operator = (Mellin-diagonal pole part with weight 1/u) − (½-bounded part); the blind-core operator is the ½-bounded part alone. **The pole is the only non-contracting piece.**
  - Distinction from the corpus Fermi Nyman–Beurling lane (PM, closed):
    - That lane alternates over the integers (η = (1 − 2^{1−s})ζ). The cusp stays open and ζ's zeros remain.
    - The twist here alternates over the Gauss branches (χ(T) = −1). The cusp closes and ζ disappears.
- **C331 status (R* = 2).**
  - Now reduced to: (1 + M) is injective on the solutions that arise, which are continuous on [0, 1] and analytic near 0.
  - The H² and holomorphic-disc theory gives a unique analytic solution ϑ_F. Then ϑ = ϑ_F, ϑ = 0 near 0, the identity theorem gives F = 0, and so G = 0.
  - The gap is uniqueness among merely continuous solutions. The C¹ route fails because the m=1 branch has weight 1 and derivative 1 at r = 0.
  - Lean is not feasible yet: Mathlib has no Bessel J₀, no Hankel–Plancherel, and no Fredholm alternative for compact operators.
- **Verdict.** C334 killed. C335 is a structural principle: **the pole of ζ is the only non-contracting piece of its transfer operator.** No producer.

## Row 328 — C336: Rouché-type perturbation around ζ's pole part (killed); C331 continuity gap sharpened
- **Conjecture C336.**
  - Split ζ's Mayer operator at s (Bessel form, w = 1/(e^u−1) = 1/u − β(u)) as L_s = A_s − B_s:
    - A_s is the pole part with weight 1/u: Mellin-diagonal after the J_{2s−1} Hankel step, multiplier Γ(w)/Γ(2s−w);
    - B_s has weight β ≤ ½.
  - Claim: ‖(1 − A_s)^{−1}B_s‖ < 1 for ¼ < Re s < ½. That would make 1 − L_s invertible there, so ζ(2s) ≠ 0 off Re s = ¼.
- **Kill (three independent reasons).**
  1. **Symmetry.** The zero set {ρ/2} is symmetric under s ↦ ½ − s̄. That symmetry is ζ's own functional equation; it is not a symmetry of the modular-surface operator, whose symmetry is s ↦ 1 − s. So the split cannot single out the line Re s = ¼; it can at most give zero-free regions.
  2. **Zero slack.** On-line zeros accumulate on Re s = ¼ at every height. So any norm bound must reach 1 there, while Rouché needs uniform slack. At best this gives Re s > ¼ + δ(t).
  3. **Height growth.** The Mellin multipliers Γ(w)/Γ(2s−w) and the weight u^{2σ−1} are not uniformly bounded in t = Im s. So δ(t) ~ 1/log t at best, a classical de la Vallée Poussin-type region, not quasi-RH.
- **C331 gap sharpened (R* = 2 for continuous G).**
  - The H² ½-contraction controls analytic solutions.
  - For merely continuous ϑ (which vanishes on [0, δ], δ = w₂ − 2), the head of the sum, m < 1/δ, has sup-norm size about log(1/δ). That exceeds 1 as c ↓ ½, and there is no cancellation, because the alternation only helps in the tail.
  - So uniqueness among continuous G near ratio 2 is genuinely open.
  - New possibility (C337): **R*(continuous) < R*(H²-regular) = 2.** Non-analytic continuous solutions may exist close to ratio 2, invisible to the H² theory. That would be a regularity-dependent threshold, worth testing.
- **Verdict.** C336 killed. C331 split into an analytic part (reduces to the H² contraction plus continuation) and a continuous part (open; the threshold may be lower).

## Row 329 — [L] MUST-1464: blind-core threshold 12/7
- The paper argument of row 321 (C325) is now formal. It is simpler than planned: the shift identity gives S(v) = −S(2+1/v)/v, so sup|S| halves on (2, 5/2], with no asymptotics or sums.
- Proven thresholds in Lean:
  - golden φ ≈ 1.618 (MUST-1457);
  - 5/3 (MUST-1459);
  - 1 + 1/√2 ≈ 1.707 (MUST-1461);
  - 12/7 ≈ 1.714 (MUST-1464).
- Conjecture C331: the true threshold is 2. The analytic part reduces to the twisted Mayer ½-contraction (row 327). The continuous part is open, and the threshold may be lower for merely continuous G (C337).
- Verdict: structural [L]. No producer.

## Row 330 — C337/C338: exact data at the pole; cusp-closing deformation (both killed)
- **C337 (exact identity at the pole).**
  - The only exact data at ζ's pole are its Laurent/Taylor jets. Under z = 1 − 1/s the critical line becomes |z| = 1 and the pole goes to z = 0. The jet of log ξ at s = 1 determines ξ.
  - RH ⟺ Li positivity λ_n ≥ 0 for all n (corpus LI route). Equivalently, a Herglotz/Carathéodory property of the jet's generating function on the disc.
  - **Kill.**
    - The transfer from the pole to the zeros is exact (analytic continuation of the jet), but the needed property is positivity of the jet.
    - Arithmetically, λ_n = (archimedean part) + (prime sum with Laguerre kernels). Bounding the prime sum from below at the (n/2)log n scale is Wall 1.
    - An off-line zero shows up only as |1 − 1/ρ|^n growth at n ≳ γ²/(½−β), i.e. it is read at its own frequency (MUST-132).
  - Positive survivor: Li is the degenerate-point principle in pure form. The degenerate point *is* the pole, and RH is positivity of its jet.
- **C338 (resonances as limits of closed-cusp problems).**
  - Characters χ_θ(T) = e^{iθ} give twisted Mayer weights w_θ(u) = 1/(e^{u−iθ} − 1), with sup|w_θ| = 1/(2 sin(θ/2)).
  - For θ ≠ 0 the cusp is closed and the twisted Laplacian is self-adjoint with real spectrum. At θ = 0 the cusp opens and ζ's resonances ρ/2 appear. So the family interpolates Fermi (θ = π) to Bose (θ → 0).
  - Conjecture: the reality of the spectrum for θ ≠ 0 passes to a constraint on the resonances at θ = 0.
  - **Kill.** As θ → 0 the real eigenvalues λ_j(θ) accumulate into the continuous spectrum [¼, ∞). The resolvents R_θ converge to R_0 only on the physical sheet. The second-sheet poles (resonances, Im λ = γ(1−β)/2, not small) are not limits of the θ ≠ 0 poles. Fermi's golden rule gives Im λ ~ θ², which applies only to dissolving embedded eigenvalues, not to ζ-resonances.
  - Positive survivor: the family θ ↦ M_θ is the exact interpolation between the provable (closed-cusp) regime and RH (open cusp). The norm blows up like 1/(2 sin(θ/2)), which is the quantitative cusp principle.
- **Verdict.** Both killed. Every exact transfer to the pole or cusp ends in a positivity statement at that point, with zero slack.
- **Correction to row 323 (C329).** The "Gram-determinant off-line detector" is a REDISCOVERY. The corpus has it in Lean as the partner angle law, `RHTower/EisensteinResonantPartnerAngle`: cos² of the angle between the truncated resonant states E*(·, ρ/2) and E*(·, ρ'/2) equals 4Re ρ(1 − Re ρ), and the sine is |2Re ρ − 1|. The lesson, already in memory and not followed here: run the corpus search before every cycle, not after.
- **Next experiment (C339, structural test of the cusp principle).**
  - Fourier blindness at shifted integers, Ĝ(n + α) = 0, twists the periodization Σ_k e^{2πikα}G(x+k).
  - The relative sign between the k = 0 and k = −2 translates sets the parabolic step. α = ¼ gives H(v) − H(v+1), the open-cusp sign: the Farey series becomes non-alternating and the coefficient a carries a pole-like divergence.
  - Question: does the boundedness anchor H(v) = G(1−1/v)/v → 0 still force uniqueness at small support ratio? If yes, the cusp principle must be refined to "open cusp without an anchor". ζ has no compact-support anchor; its anchor is the pole itself, with weight pinned to 1 (MUST-1458).

## Row 331 — C339: the obstruction is the pole coefficient at an open cusp, not the open cusp (paper)
- **Odd toy (open cusp).** Take G odd, G(1/x) = xG(x), Fourier-blind at |n| ≥ 2. Then Σ_k G(x+k) = b·sin 2πx (Ĝ(0) = 0), and the recursion is
  `H(v) − H(v+1) + H(τv)/(v−1) = −b sin(2π/v)/v` (open-cusp parabolic sign).
  - The anchor H(v) = G(1−1/v)/v → 0 gives the profile F_odd(v) = −bΣ_{k≥0} sin(2π/(v+k))/(v+k). It is holomorphic on Re v > 0 and ~ −2πb/v, and there is no a-term.
  - On the window, H + KH = F_odd with the same Gauss operator K. So the golden, 5/3, √2 and 12/7 arguments carry over verbatim: the odd toy is rigid without positivity.
- **Refined cusp principle.**
  - Positivity-free transfer works when, at the cusp, either the parabolic sum alternates (closed cusp; the a/v pole term is tamed), or the pole coefficient vanishes and a compact-support anchor pins H(∞) = 0.
  - An anchor is incompatible with an open cusp carrying a nonzero pole term, because Σ a/(v+k) diverges.
  - ζ has exactly that configuration. The pole coefficient is the residue 1, pinned (MUST-1458). It is the constant term of θ, i.e. the zero lattice vector n = 0.
  - Every modular realization of ζ carries such a constant term at some open cusp: θ at ∞; θ₂ and θ₄ at the other cusp, giving (2^s−1)ζ(s) and η.
- **Big-picture reading.** Degenerate point = cusp = pole = constant term = zero lattice vector. RH is a statement about how the arithmetic of the nonzero lattice vectors (primes, via the Euler product) balances the zero vector's contribution. All positivity-free rigidity in the corpus lives where that contribution is absent or alternated away.
- **Verdict.** Structural principle, sharper than rows 321–327. Formalizing the odd toy is optional (~250 lines, mirrors MUST-1457). No producer.

## Row 332 — C340–C342: window certificates, Krein reflection, pole-free blind positivity (paper; all killed or rediscovered)
- **C340 (window certificates, non-positivity attempt).**
  - Let C_L be the set of real weights a on {log n : n ≤ e^L} for which the Weil form (pole + archimedean − Σ a_n n^{−½} h(±log n)) is PSD on tests supported in [−L, L].
  - C_L uses only Γ_ℝ, the pole and log ℕ. Each C_L is closed, and bounded coordinatewise for L > log n + ε (two-bump tests at ±log n/2).
  - König compactness plus cone ⊆ {Λ} gives RH ⟺ C_L ≠ ∅ for every L.
  - Kill (REDISCOVERED): by SDP/Krein duality, C_L ≠ ∅ ⟺ PBAP on window L with all-integer nodes. This is the dual form of the corpus's RH ⟺ PBAP. Elements of C_L are forced towards Λ as L grows, so constructing a certificate is RH at scale L.
  - On a window, a Dirichlet polynomial certificate D must cancel the pole's e^{u/2} to √X precision (Σ_{n≤X} a_n n^{−½−it} ≈ ∫_1^X x^{−½−it}dx), and its fluctuation must be PD. A model weight such as a ≡ 1 fails because Re ζ(½+it) exceeds the archimedean density log t/2π at some heights.
- **C341 (relentless step: edge freedom / Krein continuation).**
  - Grow the window L → L + η, adjusting only the edge weights. PD on (−L, L) extends iff the continuous Krein/Schur reflection coefficient stays in the unit disc.
  - Kill (REDISCOVERED): this is the Suzuki screw / canonical-system lane (corpus `SuzukiScrewWeilIdentity`, `SuzukiScrewCompactHullParityLaw`, `SuzukiFriedrichsExtension`). The sub-unit condition |γ(u)| < 1 at each u is again window positivity.
- **C342 (pole-free blind positivity).**
  - For a primitive χ mod q, the archimedean Weil density (1/2π)(log(q/π) + Re ψ((a+½)/2 + it/2)) satisfies Re ψ(x+iy) ≥ ψ(x), from the series for ψ. So it is everywhere positive once q > πe^{−ψ(¼)} = 8πe^{γ+π/2} ≈ 215.3 (even χ) or q > 8πe^{γ−π/2} ≈ 9.3 (odd χ). These are Serre's constants.
  - Hence χ-PBAP (positivity on prime-blind PD tests) holds unconditionally for such χ. A proof of "GRH_χ ⟺ χ-PBAP" would prove GRH_χ, so no such equivalence can come from general principles.
  - RH ⟺ PBAP therefore rests on ζ-specific structure: the pole and the conductor-1 Poisson summation (Hamburger uniqueness; the T₂-self-dual (N1) witness).
  - For ζ, PBAP is non-trivial because the density is negative on |t| < t₀ ≈ 6.29 (θ'(t₀) = 0) and because the pole terms 2M₊M₋ (M± = ∫g e^{±u/2}) can be negative.
  - Rough paper estimate: the Fejér test of support ±log 2 (trivially blind) has archimedean part ≈ −1.2 and pole part ≈ +1.4. So the pole is needed even on the trivial window ("pole criticality", the analogue of Wall 11 for the pole). This is not rigorous; no numerics were run.
- **Correction to row 331.** The big-picture reading "RH = balance of nonzero lattice vectors against the zero vector" overreached.
  - GRH_χ for χ ≠ χ₀ has no pole: θ_χ has no constant term (χ(0) = 0). It is equally open.
  - So the cusp principle describes the blind-core transfer mechanism (null face), not where the RH difficulty lies.
- **Census check (user directive: routes without positivity).** These candidate non-positivity mechanisms were re-examined:
  - Sturm/Chebyshev orthogonality: Hardy's method; quantitative versions need mollified moments.
  - Integrality plus continuity (collision counting): WD/TG.
  - Cohn/Schur–Cohn derivative criterion: Speiser.
  - Interlacing families / Borcea–Brändén: LP/TT/LA lanes.
  - Temperedness: RH ⟺ the zero distribution Z = Φ − Σ Λ(n)n^{−½}δ_{±log n} is tempered. Bochner–Schwartz gives temperedness for free from PD, and the non-PD route needs √x cancellation.
  - Landau/Pringsheim one-sided positivity: every nonnegative arithmetic Dirichlet series has its pole at the abscissa, which masks the zeros. Unmasking needs a one-sided √x bound (Wall 1). Deligne's tensor-power trick works over function fields because H⁰/H² are divided out exactly, which is Wall 5.
  - No mechanism outside the classes (a)–(c) of row 318 was found.
- **Verdict.** C340/C341 REDISCOVERED; C342 a structural survivor [P] (pole and conductor-1 dependence of RH ⟺ PBAP). No producer.

## Row 333 — [L] MUST-1465: the open-cusp odd toy is rigid by a sign argument (formalizes row 331)
- `RHTower/InversionSymmetricOddFourierBlindRigidity`:
  - `fourier_neg_of_odd`;
  - `tsum_add_eq_of_odd_fourierBlind`: Σ_k G(x+k) = −2 Im Ĝ(1) sin 2πx;
  - `eq_zero_of_inversionSymmetric_odd_of_zero_on_Ico`;
  - `inversionSymmetric_odd_four_term_periodization`;
  - `inversionSymmetric_odd_parabolic_recursion`: H(v) − H(v+1) = 2 Im Ĝ(1) sin(2π/v)/v for v ≥ max(2, c/(2c−1));
  - **`eq_zero_of_inversionSymmetric_odd_fourierBlind_of_golden`** (c² + c > 1 ⟹ G = 0).
- Proof mechanism: at the open cusp the parabolic sum telescopes without alternation. The pole coefficient vanishes (Ĝ(0) = 0). For v > 2 every profile term sin(2π/(v+k))/(v+k) is positive.
  - From v₀ ∈ (v*, w₂), where H(v₀) = 0: |H(v₀+N)| ≥ |β| sin(2π/v₀)/v₀, while H(v₀+N) → 0. So β = 0, H is 1-periodic near the cusp, and H = 0.
  - No identity theorem is used, unlike the even, closed-cusp case.
- Structural comparison:
  - closed cusp (χ(T) = −1): alternating profile, needs analytic continuation;
  - open cusp without pole: one-signed profile, elementary;
  - open cusp with pole: incompatible with a compact-support anchor, since Σ a/(v+k) diverges.
- Standard axioms; `lake --old` clean; wired into `RHTower.lean`.
- Verdict: positive survivor of row 331 formalized. Null-face structure; no producer.

## Row 334 — C343–C346 (paper kills) and C337 resolved: [L] CANNOT-551, a continuous Fourier-blind core of ratio 9/5
- **Corpus check first** (`--mode deep`, Poisson/Voronoi blind positivity). `exists_weilPositiveFull_iff_primeBlindPositive` already contains the SDP duality of C340. The uniqueness uses a Ξ-divisible blind (N1) test (`WeilConeXiDivisibleBlindTest`), so blind cores are exactly the uniqueness witnesses.
- **C343 (k-PBAP).** Schur multiples h·k of a fixed null core are always blind, and their PBAP reads Σ_ρ k̂(t − γ_ρ) ≥ 0. Killed: k̂ = Ξ²|g|² decays exponentially, so the on-line zero density near γ₀ swamps any off-line term. Strictly weaker than RH (insufficient detection).
- **C344 (second moment).** For blind h, ∫ĥ|ζ(σ+it)|² = ζ(2σ)Σ_{(a,b)=1}(ab)^{−σ}h(log(a/b)). The continuation to σ = ½ crosses the pole: pole terms ĥ(±i(1−σ))ζ(2σ−1), and ζ(2σ) has a pole at ½. No inequality survives. Killed (Wall 2).
- **C345 (antichain Gram tests).** These are blind only at narrow widths, so they detect nothing. INSIGNIFICANT.
- **C346 (theta pointwise positivity).** Killed (Wall 13).
- **C337 resolved (TRUE): R*(continuous) < 2.** [L] `RHTower/InversionSymmetricFourierBlindContinuousCore`.
  - `exists_blindCoreMayer_eigen`: the twisted Mayer operator at s = ½ (three branches) has a continuous eigenfunction with eigenvalue −1, supported in [¼, 4/5].
  - Mechanism: the lift S u(1/(r+m)) = (−1)^{m−1}u(r)/W(r) with W = Σ_{m≤3}1/(r+m) ≥ 13/12 on [0,1]. So MS = id on [0,1] and ‖S‖ ≤ 12/13. Then f = Σ(−1)^k S^k u₀ with M u₀ = 0 satisfies f + Sf = u₀ ≠ 0.
  - Splitting each value among three Gauss branches is a contraction that only continuous functions can exploit.
  - `exists_inversionSymmetric_fourierBlind_nine_fifths`: there is a nonzero continuous even G with G(1/x) = xG(x), vanishing on [0, 5/9), with Ĝ(n) = 0 for **every** integer n, supported in 5/9 ≤ |x| ≤ 9/5.
  - G is built as G(x) = Γ(|x|) + Γ(1/|x|)/|x| with Γ = −M f((2x−1)/(1−x))/(1−x) on [½,1). The eigen-equation at (1−x)/x gives G(x) + G(1+x) + G(2−x) = 0. The periodization then vanishes, and `Real.fourierCoeff_tsum_comp_add` gives Ĝ(n) = 0.
  - Also proved: `fourier_eq_zero_of_tsum_add_int_eq_zero` (periodization ≡ 0 ⟹ Ĝ(ℤ) = 0).
  - Standard axioms; `lake --old` clean; wired.
- **Consequences.**
  - The continuous threshold satisfies R*_cont ∈ [12/7, 9/5] ≈ [1.714, 1.8].
  - C331 (R* = 2) is FALSE for continuous G. It can hold at most for regular (H²/analytic, maybe C¹) G, where the analytic Mayer theory applies.
  - The positivity-free rigidity chain (φ → 5/3 → 1+1/√2 → 12/7) is a continuous-function result, and it is now known to be near-sharp.
  - This parallels the essential spectrum: on C^α the bounded-digit Mayer operator has essential radius ≥ 1 for small α, and −1 is an actual eigenvalue on continuous functions.
- **Verdict.** C343–C346 killed. C337 settled with an explicit continuous counterexample (CANNOT-551). Null face, no producer. RH not proved.
