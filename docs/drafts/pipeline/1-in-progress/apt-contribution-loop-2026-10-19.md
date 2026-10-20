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
