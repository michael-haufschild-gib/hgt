# APT contribution loop (goal: 100 field-native contributions)

- **ID:** apt-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md (read-only)
- **Statement:** Develop Arithmetic Positivity Theory by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field (factorial sources,
  critical kernels, Weil/Markov/pole channels, collar arithmetic, sampling forms).

## Goal
100 significant contributions. Each must use the field's objects and mechanisms, extend what
the field explains or solves (README §1, §5), and be proved unconditionally in Lean.

## Rules in force
No hgtl7 skill. No numerical experiments. No added axioms or hypotheses in capstones. One
foreground Lean process at a time (`lake env lean`; oleans only via
`lake --old env lean -j 1 -o ...`). No full or umbrella builds. Wire new modules into
`GaloisForLFunctions/ArithmeticPositivityTheory.lean`. README is read-only.

## Conjecture queue
1. **Critical kernel sign (README §5, frontier 1).** The continuous real kernel `R` is
   strictly negative on `[0,1]`; hence `P∞(S,b) ≤ -κ Σ b_j²` for every finite real pattern.
   Route: Poisson for the band-limited weight (`Σ_z γ(t+z) = π²/6`) turns each harmonic tail
   `S_m(t) = ½Σ_{j≥m}(γ(j+t)+γ(j+1-t))` into `π²/12 - ½W_m(t)` with a finite window
   `W_m(t) = Σ_{z=-m}^{m-1} γ(t+z)`; the triangle representation
   `γ(u) = ∫_0^{π/6}(π/6-ξ)cos(ξu)dξ` and the Dirichlet telescoping
   `Σ_z cos(ξ(t+z)) sin(ξ/2) = cos(ξ(t-½)) sin(ξm)` give
   `S_m(t) - J_m/m = -½∫(a-ξ) g(ξ,t-½) sin(ξm) dξ`, `|g| ≤ ξ/5.6`. With the proved mean
   `Σ A(m)J_m/m⁴ ≤ -log2/390` and `Σ|A(m)|/m³ ≤ 0.71` this leaves a negative margin.
2. Complete critical form: archimedean term at β = 1/2 plus prime and polar channels.
3. Affine model constant `N∫v⁻²|Φ_N-Ψ_N|² → 7ζ(3)/(256π²)`.
4. Odd-sector capacity ratio `S(g)²/(2M_N(g))` under aperture growth.

## Log
- 2026-10-19 — loop started; README read in full; frontier cards read; queue seeded.

## Contribution ledger (append-only)
- **C1 · Critical prime kernel is uniformly negative; limiting critical prime form is negative
  definite** — `CriticalBandWeightPoissonWindow`, `FactorialCriticalPrimeKernelNegativeDefinite`.
  Closes README §5 frontier 1 (the critical kernel sign).
  `tsum_criticalBandWeight`: Poisson identity `Σ_{z∈ℤ} γ(t+z) = π²/6` for the even band-limited
  weight `γ = (π²/72)sinc²(π·/12)` (triangle spectrum vanishes at nonzero integers).
  `factorialCriticalPrimeHarmonicTail_add_reflect`: reflected harmonic tails close on a finite
  window, `T_m(t)+T_m(1-t) = π²/6 - W_m(t)`. `factorialCriticalHarmonicDefect_eq_band`:
  `J_m = m(π²/12 - ∫₀^m γ)`. `abs_criticalBandWindowDeviation_le_cube/_quartic`: via the triangle
  representation and Dirichlet telescoping, `|W_m(t) - 2∫₀^mγ| ≤ min((π/6)³/35, m(π/6)⁴/70)`,
  uniformly in `m`, `t` (curvature `|cos(ξs)/sin(ξ/2) - 2/ξ| ≤ 6ξ/35`).
  `factorialCriticalPrimeCellKernel_eq_tsum_tail` (summation by parts) +
  `factorialCriticalPrimeContinuousRealKernel_eq`: exact formula
  `R(t) = Σ A(m)J_m/m⁴ - ½Σ (A(m)/m³)(W_m(t) - 2∫₀^mγ)`.
  `factorialCriticalPrimeContinuousRealKernel_le`: `R ≤ -1/7000` on `[0,1]`.
  `factorialCriticalTranslatedPrimeLimit_le_neg_energy`: `P∞(S,b) ≤ -(4/(7000π⁴))Σ b_j²` for
  every finite real pattern; `_neg`: strict for nonzero patterns. New insight: at the critical
  scale the reflected kernel is a near-constant (its mean, the singleton limit, dominates a
  curvature correction that Poisson makes uniform in the harmonic index), so the sign of the
  whole translated prime form is decided by the singleton — the prime channel contributes a
  uniformly positive-definite amount to the complete critical Weil form. Standard axioms;
  lint: no new errors (two pre-existing unreachable modules owned by other loops).
- **C2 · Sharp affine collar constant `7ζ(3)/(256π²)`** — `FactorialAffineCollarSharpConstant`.
  Proves the README §5 "affine model" conjecture.
  `tendsto_factorialAffinePhaseCombination_singleton_sharp`:
  `N ∫_{v>1} v⁻²|Φ_N - Ψ_N|² → 7ζ(3)/(256π²)` (ζ(3) as `Σ' k, 1/k³`).
  Mechanism: `factorialAffineCollarHead_energy` — for `K ≤ N+1` the Bernoulli layers' frequency
  intervals `[2πkλ_N, 2πk(N+1/12)]` are separated, the cosine-shell Gram
  `∫ v⁻² L_k L_l = (π/2)|I_k ∩ I_l|` is diagonal, and `∫_{v>0} v⁻² A_K² = π² e_N Σ_{k<K} k w_k²`
  exactly; `abs_factorialAffineCollarTail_le` (tail `≤ 4/K` uniformly);
  `abs_factorialAffineCollarHead_le` (head `≤ 2πe_N(1+log N)v`, harmonic number);
  `abs_dyadicCenteredBernoulliFilter_sub_le` (`P₀` is `9/2`-Lipschitz);
  `tendsto_natCast_mul_factorialAffineDefect` (`N e_N → 1/144` from the collar cubic);
  `tsum_natCast_mul_dyadicHarmonicWeight_sq` (`Σ χ(k)²/k³ = (63/64)ζ(3)`). New insight: across
  harmonics the affine error is *exactly orthogonal* up to `k ≈ 140N²` (not merely Minkowski
  bounded), so the existing comparison constant `(4/π²)(Σ|w_k|√k)²` is not sharp; the sharp
  per-defect constant is `(4/π²)Σ k w_k² = (63/(16π²))ζ(3)`. Standard axioms.
- **C3 · Weil completeness of the factorial tent family** — `FactorialTentPatternWeilCompleteness`.
  README §5 "density of the factorial spans in the form topology" (for the native tent family);
  review A2's "joint regime needed for density".
  `riemannHypothesis_iff_factorialTentPattern_nonneg`: RH ⟺ `Q(f) ≥ 0` for every finite pattern
  of translated factorial tents (complete Gamma, prime and polar channels).
  Mechanism: `gridTentPattern_apply` — on the grid `a + j d_n` every tent carries the same
  global factor `e^{3x/2}`, and `causalTent_div_eq` (hat = difference of two unit ramps) +
  `sum_hat_eq_gridInterpolant` (Abel summation) give *exactly* `f = e^{3x/2}·(PL interpolant of
  the nodal data)`. `sum_unitRamp` (consecutive ramps sum to one clamp) ⟹
  `gridInterpolant_lipschitz` (interpolant keeps the data's Lipschitz constant) and
  `abs_gridInterpolant_sub_le` (`≤ 2Ld`); `expWeight_mul_lipschitz` transports Lipschitz control
  through `e^{3x/2}`; `tendsto_compactFullWeilEnergy_gridTentPattern`: A2 stability yields
  `|Q(f_n) - Q(g)| ≤ C·d_n → 0` with `C` uniform. (⇒) by mollification of tent patterns.
  New insight: single-scale grid tent patterns already suffice — the factorial tent family is a
  complete RH test family (complete and, by A3, detecting), so APT's laboratory now contains a
  native receiver; positivity results on the family are exactly partial RH information.
  Standard axioms.
- **C4 · Scale coupling and isotropy of the critical prime channel** —
  `FactorialCriticalPrimeScaleCoupling`. `factorialCriticalTranslatedPrimeLimit_eq_coupling`: the
  limiting prime form is Toeplitz, `P∞(S,b) = (4/π⁴)Σ_{i,j} b_i b_j R̂_{|i-j|}` (`R̂_k` = cosine
  coefficients of the critical kernel). `factorialCriticalPrimeCoupling_zero`: `R̂₀` is the
  singleton limit `Σ A(m)J_m/m⁴`. `factorialCriticalPrimeCoupling_eq_tsum`: for `k ≥ 1`,
  `R̂_k = Σ_m (A(m)/m³)∫₀^{π/6}(π/6-ξ)ξ sin(mξ)/(4π²k²-ξ²)dξ` (window cosine moments telescope:
  `∫₀¹ W_m(t)cos(2πkt)dt = ∫_{-m}^{m}γ(u)cos(2πku)du`). `abs_factorialCriticalPrimeCoupling_le`:
  `|R̂_k| ≤ (Σ|A(m)|/m³)·(π/6)³/6/(4π²k²-(π/6)²) = O(1/k²)`.
  `abs_factorialCriticalTranslatedPrimeLimit_sub_isotropic_le` (critical isotropy law):
  `|P∞(S,b) - (4/π⁴)R̂₀ Σb_j²| ≤ (4/π⁴)·budget·Σb_j²` — two-sided, uniform in pattern size and
  positions. New insight: translated scales interact in the critical prime channel only through
  a single `1/k²`-decaying coupling whose whole symbol is the charge-weighted sine transform of
  the band `[0,π/6]`; the singleton value is the exact isotropic part. Standard axioms.
- **C5 · Rational dilation law of critical sources** — `FactorialCriticalRationalDilationLaw`.
  `factorialCriticalTranslatedDilationCorrelation_tendsto`: at every real dilation `ρ > 0` the
  complete critical correlation `∫_{v>1} v⁻² F_n(v) F_n(ρv)` of a translated pattern converges to
  the resonance sum over harmonic pairs `k = ρ l` (cosine-product limit with rates `k`, `ρl`;
  the collar slow phase survives exactly on resonance as `J_k(b)`).
  `factorialCriticalDilationLimit_eq_zero_of_irrational`: the limit vanishes at irrational `ρ`.
  `factorialCriticalDilationLimit_rat`: at reduced `p/q`, limit `= (4/π⁴)Σ_t w_{pt}w_{qt}J_{pt}(b)`.
  `criticalFactorialSource_translated_autocorrelation_tendsto(_zero)`: the limiting
  autocorrelation of every translated critical source at shift `x` is
  `e^{-x/2}·Lim(e^x)` and vanishes whenever `e^x` is irrational. New insight: the critical
  limit has a *rational spectrum* — autocorrelation atoms exactly at `log(p/q)`; the Weil prime
  channel sees only the integer atoms `log r`, the non-integer rational atoms (e.g. `log(3/2)`)
  are invisible to every prime and feed only the archimedean/Lévy channel. Extends the integer
  dilation law to all real dilations. Standard axioms.
- **C6 · The complete critical form diverges to +∞ (eventual positivity)** —
  `FactorialCriticalCompleteFormDivergence`. README §5 frontier 2 ("the archimedean term at
  β = 1/2 ... remain to be assembled into a sign statement for the complete form").
  Complete critical energy in Gamma–Lévy form `criticalTranslatedCompleteEnergy` (EReal): Lévy
  jump energy + `Ω(0)ac(0)` + `2·polar` − `2·prime`.
  `abs_criticalFactorialPolarReadout_le`: `|∫_{v>1}v⁻²F| ≤ 24Σ|b_n|/(n+1)` (IBP against the
  bounded lattice primitive); `tendsto_criticalTranslatedPolarProduct`: polar channel → 0.
  `factorialCriticalDilationLimit_one_pos`: limiting mass > 0 for nonzero patterns.
  `ae_irrational_exp` + C5 ⟹ autocorrelation → 0 a.e.; `tendsto_criticalTranslatedLevyEnergy_top`:
  Fatou + `ω(x) ≥ e^{-1/2}/x` ⟹ Lévy energy → ∞. `tendsto_criticalTranslatedArithmeticChannels`:
  arithmetic channels → `Ω(0)μ∞ − 2P∞`, with `−2P∞ ≥ (8/(7000π⁴))Σb_j²`
  (`neg_two_factorialCriticalTranslatedPrimeLimit_ge`).
  `tendsto_criticalTranslatedCompleteEnergy_top`: for every nonzero finite pattern the complete
  critical energy of its translates tends to `+∞`. New insight: at the critical scale every
  non-archimedean channel stays bounded (polar vanishes, prime converges and is favourable),
  while the archimedean channel diverges because the rational spectrum of C5 makes the source
  decorrelate at almost every shift — the critical complete form is archimedean-dominated, so
  its sign question is settled for each fixed pattern; uniformity in patterns is what remains.
  Standard axioms.
- **C7 · Uniform finite-scale negativity of the actual critical prime channel** —
  `FactorialCriticalPrimeFiniteScaleNegativity`. Single-scale sources `criticalScaleSource`,
  cross correlations `criticalScaleCrossCorrelation`; bilinear expansion of translated
  autocorrelations at every shift t ≥ 0 (`criticalFactorialSource_translated_correlation_eq_sum`).
  `factorialCriticalTranslatedPrimeEnergy_eq_matrix`: the actual prime energy is the quadratic
  form of the symmetric finite-scale prime matrix `criticalTranslatedPrimeMatrix n i j`.
  `tendsto_criticalTranslatedPrimeMatrix`: `M_n(i,j) → (4/π⁴)κ(|i−j|)` (Toeplitz limit, by
  polarization of the translated prime limit + C4). `eventually_factorialCriticalTranslatedPrimeEnergy_le`:
  for every finite support S, eventually in n, for ALL b: actual prime energy ≤ −(2/(7000π⁴))Σb².
  New insight: C1's negativity is not only a limit statement — the actual von Mangoldt channel
  on every finite span of critical sources is uniformly negative definite past a support-dependent
  threshold scale, i.e. the prime term of the complete critical form has a definite (favourable)
  sign at finite scale. Standard axioms.
- **C8 · Uniform coercivity / eventual positive definiteness of the complete critical form** —
  `FactorialCriticalCompleteFormUniformCoercivity` (+ quantitative refactor of C6:
  `factorialCriticalDilationLimit_one_ge` mass floor `Σb²/(12π⁴) ≤ μ∞`,
  `lintegral_ofReal_mul_archLevySinhWeight_eq_top`, `abs_criticalTranslatedPolarProduct_le`).
  Symmetric correlation matrix `criticalTranslatedSymmetricCorrelation`; entrywise dilation law
  `tendsto_criticalTranslatedSymmetricCorrelation` (→ e^{−t/2}·polarized dilation limit at e^t);
  mass matrix represents μ∞ (`factorialCriticalDilationLimit_one_eq_polarization`).
  Decorrelation defect `criticalTranslatedDecorrelationDefect` → 0 a.e.; pointwise jump floor
  `ac(0) − ac(x) ≥ (1/(12π⁴) − d_n(x))Σb²`; common Lévy floor `criticalTranslatedLevyFloor`
  with `Lévy_n(b) ≥ Σb²·floor_n` and `floor_n → ∞` (Fatou).
  `eventually_criticalTranslatedCompleteEnergy_coercive`: ∀ S finite, ∀ M, eventually in n,
  ∀ b: complete critical energy ≥ M·Σ_{j∈S} b_j². `eventually_criticalTranslatedCompleteEnergy_pos`.
  New insight: C6's per-pattern divergence is uniform — the smallest eigenvalue of the complete
  critical form on the span of single-scale critical sources at scales n+S tends to +∞. The
  mechanism is a matrix-level decorrelation law (polarized rational dilation law) plus a
  coefficient-free mass floor; the only remaining non-uniformity is in the support S itself
  (threshold scale depends on S). Standard axioms.
- **C9 · Toeplitz symbol law and sharp spectral range of the limiting critical prime form** —
  `FactorialCriticalPrimeToeplitzSymbolRange`. `R(1−t) = R(t)`; sine moments vanish; Fourier
  coefficients of R on the cell are exactly κ(|n|) (`fourierCoeffOn_factorialCriticalPrimeContinuousRealKernel`);
  `summable_abs_factorialCriticalPrimeCoupling` (κ(k) = O(1/k²)); symbol law
  `hasSum_factorialCriticalPrimeCoupling_cos`: R(t) = Σ_{n∈ℤ} κ(|n|)cos(2πnt) on [0,1].
  Toeplitz counting identity `sum_range_sum_range_natAbs`; Cesàro limit
  `tendsto_factorialCriticalTranslatedPrimeLimit_cos_add_sin`: (P∞(cos_L)+P∞(sin_L))/L → (4/π⁴)R(t).
  Mediant sharpness `exists_lt_factorialCriticalTranslatedPrimeLimit` / `exists_factorialCriticalTranslatedPrimeLimit_lt`.
  Capstones `isLUB_factorialCriticalPrimeRayleighSet` = (4/π⁴)·max R and
  `isGLB_factorialCriticalPrimeRayleighSet` = (4/π⁴)·min R: the exact ℓ² spectral range of P∞ over
  all finite patterns is the range of the critical kernel; `sSup_factorialCriticalPrimeContinuousRealKernel_le`
  (max R ≤ −1/7000) so the optimal negativity constant is −(4/π⁴)max R. New insight: the critical
  kernel R is not merely a sufficient certificate (C1) but the exact symbol — sign/size questions
  about the limiting critical prime channel are equivalent to pointwise questions about R, and the
  extremal patterns are long frequency-modulated patterns concentrating at argmax/argmin R.
  Standard axioms.
- **C10 · Logarithmic coercivity of the critical archimedean channel (uniform in the support)** —
  `CriticalSourceMellinLowFrequencyExclusion` + `CriticalArchimedeanLogCoercivity`.
  General-exponent nonstationary bound `norm_integral_Ioi_one_rpow_mul_cexp_phase_le_of_one_lt`
  (‖∫_1^∞ v^{-p}e^{i(ωv−t log v)}‖ ≤ 5/|ω| for p > 1); critical readout
  `paperFT_criticalFactorialSource` (ĝ(t) = ∫_1^∞ v^{-3/2}B_b(v)e^{-it log v}); critical
  low-frequency exclusion `norm_sq_paperFT_criticalFactorialSource_le` (‖ĝ‖² ≤ (2D²/M)Σb² on |t| ≤ πM).
  Spectral autocorrelation `criticalFactorialSource_autocorrelation_eq_spectral`
  (ac(x) = (1/2π)∫‖ĝ‖²cos(tx), via polarized Plancherel + translation rule); Lévy symbol bound
  `ofReal_log_sub_le_lintegral_one_sub_cos_mul_archLevySinhWeight` (W(t) ≥ e^{-1/2}(log|t| − 3));
  Tonelli `criticalLevyEnergy_ge_highBand`; mass floor `integral_criticalFactorialSource_sq_ge`.
  Capstone `ofReal_le_criticalLevyEnergy`: for EVERY finite family on scales n+1 ≥ M ≥ 2 and every
  real b, Lévy(g_b) ≥ e^{-1/2}(A/2)(log M − 3 − log(1/η))Σb². New insight: C6/C8's divergence of
  the critical archimedean channel is not a limit phenomenon of fixed patterns — it is a uniform
  logarithmic law in the minimal scale, exactly as at the canonical envelope (§3.8): the critical
  envelope inherits high-scale archimedean coercivity even though its prime majorant diverges.
  Standard axioms.
- **C11 · Positivity of the complete critical form on growing patterns (effective)** —
  `CriticalCompleteFormGrowingPatterns`. General-support complete energy `criticalCompleteEnergy`
  (Lévy + Ω(0)ac(0) + 2·polar − 2·prime), identified with C6's translated form by `rfl`
  (`criticalTranslatedCompleteEnergy_eq`). Atom bound `abs_criticalPrimeAtom_le` (|atom_r| ≤ KΛ(r)/r²),
  `abs_criticalPrimeEnergy_le`, dyadic admission constant `criticalFactorialPrimeConstant_le_of_dyadic`
  (K ≤ 384B₁² on M ≤ n+1 ≤ 2M), mass `criticalAutocorrelation_zero_le` (≤ 4B₁²), channel bound
  `neg_le_criticalArithmeticChannels` (≥ −C B₁², C = 4|Ω(0)| + 288 + 768ΣΛ/r²).
  `criticalCompleteEnergy_ge`: E_crit ≥ s(log M − c₀)Σb² − C(Σ|b|)² for every pattern on [M,2M].
  `criticalCompleteEnergy_pos`: every nonzero pattern with C|S| < s(log M − c₀) has E_crit > 0.
  `criticalTranslatedCompleteEnergy_pos`: effective threshold for C8 (offsets ≤ n and
  C|S| < s(log(n+1) − c₀)). New insight: the README's "finite-scale error strong enough for
  growing patterns" is supplied — not by sharpening the prime channel (whose finite-scale bound
  only sees ℓ¹ mass) but by the ℓ²-uniform log-growth of the critical archimedean channel; the
  admissible pattern size is logarithmic in the scale, the exact trade-off between the ℓ¹ prime
  budget and the ℓ² Lévy gain. Remaining sharp gap: ℓ²-uniform finite-scale prime bound would
  remove the |S| restriction. Standard axioms.
- **C12 · Dyadic dilation inequality** — `DyadicDilationCorrelationInequality`. For a weight φ
  integrable on (1,∞) with cosine transform |F_φ| ≤ A, |F_φ(f)| ≤ B/f², every dyadic block
  (`DyadicScaleBlock S M`: M ≤ n+1 ≤ 2M) and every integer dilation r ≥ 1:
  `abs_integral_weight_realPhaseCombination_dilate_le` |∫_{v>1} φ B_b(v)B_b(rv)| ≤ (4/π⁴)K(A,B)r^{-1/2}Σb².
  Ingredients: spaced/far sums (`sum_abs_le_of_spaced`, 11/12-spacing `scaleBranch_spacing`),
  resonance localisation `dyadicResonanceBound` (A + O(B/q²) only for k ≍ lr), cross-scale kernel
  `dyadicCrossKernel` + harmonic kernel identity `integral_mul_realHarmonicLayer_mul_dilate`, Schur
  test `abs_bilinear_le_of_row_col`, per-harmonic bound `abs_bilinear_dyadicCrossKernel_le`,
  resonance trade `weight_mul_resonance_le` (1/k² paid against √(lr) ≥ √r). New insight: the
  ℓ¹-obstruction of the critical prime channel is not intrinsic to the dilation structure; with a
  1/f²-decaying weight the cross-scale correlations of phase combinations form an ℓ²-bounded,
  r^{-1/2}-decaying family. The only ℓ¹ source is the 1/f tail of the endpoint jump. Standard axioms.
- **C13 · ℓ²-uniform collared critical prime channel** — `CollaredCriticalPrimeChannelUniformBound`.
  Second-order cosine decay `integral_Ioi_mul_cos_eq_of_flat` (∫φcos(ωv) = −ω⁻²∫φ''cos(ωv) for φ
  flat at the endpoint); smooth collar weight `criticalCollarWeight` ψ(v) = σ(v−1)/v² (C^∞, flat at
  1, = v⁻² on v ≥ 2) with `abs_integral_criticalCollarWeight_mul_cos_le_div_sq`; collared source
  `criticalCollaredSource` g_c = σ(e^{-x}−1)g_b; correlation law
  `integral_criticalCollaredSource_mul_dilate` (r ≥ 2: ∫g_c g_c(·−log r) = r^{-1/2}∫ψB_b(v)B_b(rv));
  capstone `abs_criticalCollaredPrimeEnergy_le`: |Σ_r Λ(r)r^{-1/2}ac_c(log r)| ≤ C_c Σb² on EVERY
  dyadic block, C_c = (4/π⁴)K(‖ψ‖₁,‖ψ''‖₁/4π²)ΣΛ(r)r^{-3/2}. New insight: the uncollared prime
  channel's quadratic-in-Σ|b| bound (C11, 384B₁²) is entirely an endpoint effect; removing the
  endpoint by a collar of fixed width log 2 converts it into an ℓ²-bounded form, so the README's
  growing-pattern gap reduces to (i) collared archimedean log-coercivity and (ii) the endpoint
  layer's cross terms (Hilbert-type, MV route). Standard axioms.
- **C14 · Collared archimedean log-coercivity and positive definiteness of the collared Lévy–prime
  form on high dyadic blocks** — `CollaredCriticalArchimedeanLogCoercivity`. (i) General-source
  Lévy calculus: `AdmissibleSource`, `sourceAutocorrelation_eq_spectral`,
  `sourceLevyEnergy_ge_highBand`, and the abstract law `ofReal_le_sourceLevyEnergy` (mass floor +
  low-band exclusion ⇒ Lévy ≥ e^{-1/2}(A/2)(log M − 3 − log 1/η)E), reusable for any future source.
  (ii) Flat nonstationary phase `norm_integral_Ioi_one_flat_mul_cexp_phase_le` (amplitude vanishing
  at 1: no boundary term, ≤ (2/|ω|)(‖a'‖₁ + ‖a/v²‖₁)); collar amplitude `criticalCollarAmplitude`
  a_c = σ(v−1)v^{-3/2}; collared readout `paperFT_criticalCollaredSource`; collared exclusion
  `norm_sq_paperFT_criticalCollaredSource_le` (‖ĝ_c‖² ≤ 2D_c²/M·E on |t| ≤ πM). (iii) Collared mass
  floor `integral_criticalCollaredSource_sq_ge` (window [2,2+L] beyond the collar).
  (iv) `ofReal_le_criticalCollaredLevyEnergy`: Lévy(g_c) ≥ s_c(log M − c_c)E for every family on
  n+1 ≥ M ≥ 2. Capstones `criticalCollaredLevyPrime_ge` / `criticalCollaredLevyPrime_pos`: on every
  dyadic block, Lévy(g_c) − 2P_c ≥ (s_c(log M − c_c) − 2C_c)E, hence positive definite for all
  M beyond an absolute threshold, with NO restriction on |S| (contrast C11: |S| ≲ log M). New
  insight: once the endpoint is collared the critical Weil-type form splits cleanly into an
  ℓ²-log-growing archimedean part and an ℓ²-bounded prime part — the growing-pattern gap of the
  README is closed for collared sources; the full critical source differs only by the endpoint
  layer (−log 2, 0], whose self-prime interaction vanishes (disjoint supports for r ≥ 2) and whose
  cross terms carry the Hilbert 1/f kernel. Standard axioms.
- **C15 · Positive definiteness of the complete collared critical form on high dyadic blocks** —
  `CollaredCriticalCompleteFormPositivity`. Gamma channel: ℓ² ceiling
  `integral_Ioi_one_rpow_neg_two_mul_norm_sq_le` (∫_1^∞ v⁻²‖B_b‖² ≤ (π²/6)JΣ‖b‖², unit windows with
  j⁻² weights) ⇒ `sourceAutocorrelation_criticalCollaredSource_zero_le`. Polar channels: readout
  `criticalCollaredPolarReadout` = ∫ g_c e^{x/2} (`integral_criticalCollaredSource_mul_exp_half`),
  endpoint `criticalCollaredPolarEndpoint` = improper ∫_1^∞ σ(v−1)B_b(v)/v
  (`tendsto_integral_criticalCollarEndpointWeight_mul`), both ≤ const·Σ|b_n|/(n+1) by IBP against
  the bounded primitive (`abs_criticalCollaredPolarReadout_le`, `abs_criticalCollaredPolarEndpoint_le`),
  product ≤ 144‖ψ'‖₁‖ρ'‖₁Σb² via `sq_sum_abs_div_succ_le`. Complete energy
  `criticalCollaredCompleteEnergy` = Lévy + Ω(0)ac_c(0) + 2R_cE_c − 2P_c;
  `criticalCollaredCompleteEnergy_ge` (≥ (s_c(log M − c_c) − K)Σb² on every dyadic block) and
  capstone `exists_criticalCollaredCompleteEnergy_pos`: ∃ M₀ ∀ M ≥ M₀ ∀ dyadic S at M ∀ b ≠ 0,
  E_c > 0. New insight: every channel of the complete critical form except the archimedean one is
  ℓ²-BOUNDED once the endpoint is collared, while the archimedean channel grows like log M on ℓ²;
  the collared critical form is therefore positive definite on whole high dyadic blocks, the
  ℓ²-uniform version of C11's growing-pattern theorem (which needed |S| ≲ log M). Standard axioms.
- **C16 · The critical prime channel is bounded on ℓ² (Montgomery–Vaughan jump kernel)** —
  `CriticalPrimeChannelUniformBound` (+ refactor of C12: general harmonic reduction
  `abs_integral_weight_realPhaseCombination_dilate_le_of_bilinear`, public `weight_mul_resonance_le`).
  Jump kernel `dyadicJumpKernel` j(f) = −(1/2)∫_{−1}^{1}cos(2πfu) = −sin(2πf)/(2πf); MV bilinear
  bound `abs_bilinear_dyadicJumpKernel_le` (|Σb_nb_{n'}j(x_n − y_{n'})| ≤ (1 + 13/(πD))Σb² for two
  D-separated families, NO cross-separation: sinc = average of exponentials ⇒ Cauchy–Schwarz +
  `HTGeometry.interval_integral_normSq_expSum_le`); dyadic jump cross-kernel bound
  `abs_bilinear_dyadicCrossKernel_jump_le` (MV near resonance, 1/f far). Endpoint weight
  `criticalEndpointWeight` φ_e = (1−σ(v−1))/v² (ψ + φ_e = v⁻²), exact two-IBP split
  `criticalEndpointRemainder_eq` (F_{φ_e} = j + e, |e| ≤ κ_e/f²); endpoint dilation inequality
  `abs_integral_criticalEndpointWeight_dilate_le` (≤ (4/π⁴)K_e r^{-1/2}Σb²); splitting
  `integral_criticalFactorialSource_mul_dilate_eq`; capstone `abs_criticalPrimeEnergy_le_of_dyadic`:
  |Σ_r Λ(r)r^{-1/2}ac(log r)| ≤ C_P Σb² on EVERY dyadic block for the actual critical source. New
  insight: the README's open gap (ℓ²-uniform finite-scale critical prime bound; C11 had only
  (Σ|b|)²) is closed. The endpoint jump produces a Hilbert/sinc kernel whose log-divergent Schur sum
  is cancelled by Montgomery–Vaughan; the prime channel of critical sources is a bounded operator
  on ℓ² of every dyadic block. Standard axioms.
- **C17 · Positive definiteness of the complete critical form on high dyadic blocks** —
  `CriticalCompleteFormHighScalePositivity`. ℓ² Gamma ceiling `criticalAutocorrelation_zero_le_sq`,
  ℓ² channel bound `neg_le_criticalArithmeticChannels_sq` (K = |Ω(0)|U + 1152 + 2C_P),
  `criticalCompleteEnergy_ge_of_dyadic` (E_crit ≥ (s(log M − c₀) − K)Σb²), capstones
  `exists_criticalCompleteEnergy_pos` (∃ M₀ ∀ M ≥ M₀ ∀ dyadic S ∀ b ≠ 0: E_crit(g_b) > 0) and
  `exists_criticalTranslatedCompleteEnergy_pos` (every nonzero pattern with offsets ≤ n translated
  to n ≥ N₀ is positive — C11's |S| ≲ log n restriction removed). New insight: the complete
  critical form (Weil-type Gamma–Lévy form of the critical sources) is uniformly positive definite
  on every high dyadic block — all arithmetic channels are ℓ²-bounded, the archimedean one grows like
  log M. Positivity of the critical form can only fail in the low/mid scales M < M₀ or across
  blocks (multi-scale interaction), which is where the remaining difficulty is concentrated.
  Standard axioms.
- **C18 · Logarithmic window law of the critical prime channel** — `CriticalPrimeChannelScaleWindows`.
  `ScaleWindow S M L` (M ≤ n+1 ≤ LM). Support-agnostic harmonic bounds
  `abs_bilinear_dyadicCrossKernel_le_uniform` (Schur on spaced rows/columns, any finite family) and
  `abs_bilinear_dyadicCrossKernel_jump_le_uniform` (MV on every branch pair); window-far bounds
  `abs_bilinear_dyadicCrossKernel_le_far` (16LB/q²) / `..._jump_le_far` (4L/(πq)) when lr ≥ 8Lk;
  generic reductions `abs_integral_weight_dilate_le_of_uniform` (O(1) for every r) and
  `abs_integral_weight_dilate_le_of_window` (O(√(L/r)) for r ≥ L, near terms pay 1/√k ≤ √(8L/r));
  combined `abs_criticalWindowCorrelation_le` (≤ (4/π⁴)K_W min(1,√(L/r))Σb²); capstone
  `abs_criticalPrimeEnergy_le_of_window`: |P| ≤ C_W(3 + log L)Σb² via min(1,√(L/r)) ≤ (L/r)^ε and
  the corpus Chebyshev series bound `RHTower.tsum_vonMangoldt_div_rpow_le_six` at ε = 1/(2 + log L).
  New insight: across many dyadic blocks the prime channel grows only like the LOGARITHM of the scale
  width — cross-block prime coupling is O(1) per dyadic ring of dilations r ≈ width, summed by
  Mertens; this is the multi-block Gram law asked for in README §5 "Across blocks". Standard axioms.
- **C19 · Positive definiteness of the complete critical form on polynomial scale windows** —
  `CriticalCompleteFormPolynomialWindows`. `neg_le_criticalArithmeticChannels_of_window`,
  `criticalCompleteEnergy_ge_of_window` (E_crit ≥ (s(log M − c₀) − K₀ − 2C_W(3 + log L))Σb²),
  capstone `exists_criticalCompleteEnergy_pos_of_window`: ∃ δ > 0 ∃ M₀ ∀ M ≥ M₀ ∀ L ≤ M^δ ∀ family on
  [M, LM] ∀ b ≠ 0: E_crit(g_b) > 0 (δ = s/(4(C_W+1))). New insight: positivity is not a block-local
  phenomenon — the archimedean gain is log of the smallest scale, the prime cost log of the width,
  so the critical form is positive definite on windows [M, M^{1+δ}] spanning polynomially many
  dyadic blocks. The remaining multi-scale regime is width ≫ M^δ (log L ≍ log M), where the
  constants s, C_W decide. Standard axioms.
- **C20 · Doubly collared (compact) critical sources: block positivity uniform in the truncation** —
  `DoublyCollaredCriticalSourcePositivity`. Upper cutoff `criticalUpperCutoff` χ = 1 − σ(u−1);
  compact source `criticalTruncatedSource` g^V = χ(e^{-x}/V)·g_c (support [−log 2V, 0], continuous);
  far layer `criticalTruncationTail`. Correlation law `integral_criticalTruncatedSource_mul_dilate`
  (r ≥ 2: weight ψ·χ(rv/V), the two cutoffs merge). Uniform transform bounds for truncated weights
  `abs_weightCosineTransform_criticalTruncatedWeight_le` (λσ'(λv−1) vanishes unless λ < 2/v ⇒
  ‖w_λ''‖₁ ≤ ‖ψ''‖₁ + 4sup|σ'|‖ψ'‖₁ + 4sup|σ''|‖ψ‖₁ for ALL λ) ⇒ `abs_criticalTruncatedPrimeEnergy_le`
  (C_T independent of V). Archimedean: tail mass `integral_criticalTruncationTail_sq_le` (≤ (U/V)E via
  the dilated ℓ² ceiling — C15's ceiling generalised to dilations), window floor
  `integral_criticalTruncatedSource_sq_ge`, spectral comparison with the collared low band ⇒
  `ofReal_le_criticalTruncatedLevyEnergy` (V ≥ V₀). Polar: generic flat IBP
  `abs_integral_weight_mul_phase_le`, readout/endpoint bounds uniform in V. Capstones
  `criticalTruncatedCompleteEnergy_ge` and `exists_criticalTruncatedCompleteEnergy_pos`: ∃ M₀ ∀ M ≥ M₀
  ∀ V ≥ V₀ ∀ dyadic block ∀ b ≠ 0: E(g^V) > 0. New insight: block positivity of the critical family
  survives truncation to COMPACT tests with a margin uniform in the aperture log(2V) — the answer
  to README §5 "which compact approximants inherit the block positivity": smooth doubly collared
  truncations, at every length. Standard axioms.
- **C21 · Compact critical sources are Weil-positive for ζ (family → receiver)** —
  `CompactCriticalSourceWeilPositivity`. Lipschitz calculus of the field's objects:
  `abs_dyadicBernoulliFilter_sub_le` (P₀ is 9/2-Lipschitz, from the 1/2-Lipschitz periodic
  quadratic), `abs_factorialPhaseProfile_sub_le`, `realPhaseLipschitz`,
  `abs_realPhaseCombination_sub_le`; closed form `criticalTruncatedSource_eq` (collar kills the
  indicator), continuity, support in [−log 2V, 0], `exists_lipschitz_criticalTruncatedSource`
  (g^V = g^V ∘ proj_{[a,0]}, four bounded Lipschitz factors). Test `criticalTruncatedTest : C_c(ℝ,ℝ)`.
  Receiver identity `compactFullWeilEnergy_criticalTruncatedTest`: Re W_Λ(g^V ⋆ g̃^V) =
  criticalTruncatedCompleteEnergy (prime atoms = Λ(r)r^{-1/2}ac(log r); polar 2cosh integral =
  product of half-exponential moments; Lévy lintegral = Lévy integral). Capstone
  `exists_compactFullWeilEnergy_criticalTruncatedTest_pos`: ∃ M₀ ∀ M ≥ M₀ ∀ V ≥ V₀ ∀ dyadic block
  ∀ b ≠ 0: Re W_Λ(g^V) > 0 — UNCONDITIONAL Weil positivity of ζ on compact tests of ARBITRARILY LONG
  support (log 2V), not via small-support (Yoshida/Bombieri regime) but via the field's
  log-coercivity vs ℓ²-uniform prime channel. Standard axioms.
- **C22 · Cross-block decay law + positivity across lacunary blocks (README §5 "Across blocks")** —
  modules `CriticalPrimeChannelCrossBlockDecay` and `LacunaryCriticalBlockPositivity`.
  (1) Bilinear multi-dilation harmonic reduction `abs_sum_integral_weight_dilate_le_of_bilinear`
  (two patterns, finite dilation family, r-dependent weights). (2) Dilation-sum lemma
  `primeDilationSum_le`: ∑_r (Λ(r)/r)(|F_r(y−rD)|+|F_r(y+rD)|) ≤ 9B/(yD)+6√(D/y)(A+14B/D²), and
  ≤ 5B/D² + [D<y](…) — resonant weight (2D/y)log(2y/D) ≤ 6√(D/y). (3) Cauchy–Schwarz over dilations
  `sum_abs_mul_abs_mul_le_sqrt` with row bound 2(M'+1)β and column bound 12(A+16B)(1+log(1+6kM/M'))²
  (Mertens partial sum `sum_vonMangoldt_div_le`). (4) Per-harmonic bounds for both dilation orders
  (`abs_bilinear_crossBlock_down_le` / `_up_le`), harmonic mass finite (k^{-9/8}, l^{-3/2}).
  Cross-block law `abs_sum_integral_crossBlock_down_le` / `_up_le`:
  |∑_r (Λ(r)/r)∫φ_r B_b(v)B_c(rv)| ≤ K(A,B)·τ(m,n)‖b‖‖c‖, τ(m,n) = (1+log n)√(1/n + m√(m/n)).
  (5) g^V: finite dilation form `criticalTruncatedPrimeEnergy_eq_sum`, block expansion
  `criticalTruncatedPrimeEnergy_biUnion`; lacunary families `IsLacunaryBlockFamily` (M_{i+1} ≥ M_i⁸);
  `crossBlockDecay_le_of_pow_le` (τ ≤ 50 m^{-1/16}n^{-1/16}); `abs_criticalTruncatedPrimeEnergy_le_of_lacunary`
  (|P| ≤ (C_T+100K)∑b², ANY number of blocks). Capstones `exists_criticalTruncatedCompleteEnergy_pos_of_lacunary`
  and `exists_compactFullWeilEnergy_pos_of_lacunary`: ∃M₀ ∀ lacunary families with M_0 ≥ M₀ (any J)
  ∀V ≥ V₀ ∀ b ≠ 0: Re W_Λ(g^V) > 0 — patterns spanning scales M_0 … M_0^{8^{J−1}}. Standard axioms.
  Insight: the multi-scale prime coupling is an ℓ²-sum over dilations (Cauchy–Schwarz over r),
  costing √(D/y) per resonant partner × (number of partners in the smaller block); distinct
  blocks decouple at rate τ(m,n) → 0 once n ≫ m³. Boundary (paper, not formalised): the
  divisibility structure of resonances (k(n+1) ≡ j mod lr) that would give √log-uniform dense
  windows survives only for scale ratios ≲ √scale, because λ_N = N(1+1/(4N))^{1/3} has
  1/12 − δ_N ≈ 1/(144N) (integer and shifted branches resonate arithmetically only while
  lr·η_{n'} ≲ 1). Dense (non-lacunary) windows beyond polynomial remain open.
