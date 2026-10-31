# 35 SpacingScaleHarmonicAnalysis — mathematical facts log

## TheSelfEnergyOfAnAtomHasConstantOne (uses AES TheWeilFormAtAtomicResolution)
- archForm f = 2θ'(0)‖f‖² + ∫_0^∞ω(y)‖f − f(·+y)‖²dy, Lévy density ω(y) = e^{−y/2}/(1 − e^{−2y}) ~ 1/(2y).
- Sharp bounds: ω(y) ≥ 1/(2y) on (0,1] (sinh y ≤ y e^{y/2}, cubic Taylor); ω(y) ≤ e^{y/2}/(2y) (y ≤ sinh y); ≤ e^{1/2}/(2y) on (0,1].
- Window integral log(s/w) ≤ 2∫_{(w,s]}ω (0 < w ≤ s ≤ 1). Lévy gain with constant one: shifts in (w,s] move supp f off itself ⇒ levyEnergy ≥ log(s/w)‖f‖².
- Atom in [0,w], w ≤ 1: levyEnergy ≥ log(1/w)‖g‖²; archForm ≥ (2θ'(0) + log(1/w))‖g‖². Corpus constant e^{−1/2} falls short of prime counterterm log N at all w ≥ N^{−e^{1/2}}; constant one reaches the spacing.

## TheArchimedeanCrossKernel
- bumpCorr G(t) = ∫g(v)g(v+t); |G| ≤ ‖g‖²; G = 0 for |t| > w. ∫f(u)f(u+y) = Σ_{m,n}x_mx_nG(y − log(n/m)); ∫(f − f(·+y))² = 2‖f‖² − 2∫f f(·+y).
- Pair window: atoms at log-distance s, |s| ≥ 2w, interact only for |y − s| ≤ w; ∫_{(w,1]}ω·1_window ≤ crossBound = 2e^{1/2}w/|s| if |s| ≤ 2 else 0.
- 1/|log(n/m)| ≤ e²m/|n−m| (|log| ≤ 2); |log n − log m| ≥ δ_N. Row Σ_{n≠m}crossBound ≤ 4e^{5/2}wm(1 + log(N+1)) (harmonic row Σ1/|n−m| ≤ 2(1 + log(N+1))). Symmetric Schur.
- levyEnergy_atomicTest_ge: w ≤ δ_N/2 ⇒ levyEnergy f ≥ ‖g‖²Σ_m x_m²(log(1/w) − 8e^{5/2}wm(1 + log(N+1))). Cross row = relative width w·m × log N; at spacing w = cδ_N it is c(m/N)log N (largest on top dyadic block where prime form has no entries).

## TheSelfEnergyOfAnAtomIsExactlyLogarithmic
- ω(y) ≤ 1/(2y) + e^{1/2}/4 on (0,1]; ω(y) ≤ e^{−y/2}/(1 − e^{−2}) for y ≥ 1. K-Lipschitz g: ‖g − g(·+y)‖² ≤ 2K|y|‖g‖₁.
- Split Lévy integral at w and 1: levyEnergy g ≤ (log(1/w) + C₀)‖g‖² + e^{1/2}Kw‖g‖₁, C₀ = selfEnergyConstant = e^{1/2}/2 + 4e^{−1/2}/(1 − e^{−2}). Dilated profile: last term = e^{1/2}Lip(φ)‖φ‖₁/‖φ‖₂²·‖g‖² (w-independent): levyEnergy = (log(1/w) + O_φ(1))‖g‖². archForm two-sided.

## TheRobinConstantOfAnAtom
- levyRegularPart r(y) = ω(y) − 1/(2y) ∈ [0, e^{1/2}/4] on (0,1]. archRobinConstant 2c_∞ = 2∫_0^1 r + 2∫_1^∞ ω (Γ-factor constant). bumpRobin β(g) = ∫_0^w ‖g − g(·+y)‖²/(2y)dy.
- Exact: levyEnergy g = (log(1/w) + 2c_∞)‖g‖² + β(g) + R, |R| ≤ (e^{1/2}/2)w‖g‖² (abs_levyEnergy_atom_sub_le).
- atomDilate φ(·/w): ‖·‖² = w‖φ‖², β scales by w. profileRobin κ_L(φ) = 2c_∞ + β(φ)/‖φ‖². |levyEnergy(φ_w) − (log(1/w) + κ_L(φ))‖φ_w‖²| ≤ (e^{1/2}/2)w‖φ_w‖²; levyEnergy/mass − log(1/w) → κ_L(φ) as w → 0+.
- Spacing constant κ₀(g) = 2θ'(0) + 2c_∞ + β/‖g‖²; with prime counterterm log N − γ the Markov form on the pole has energy log(1/(wN)) + κ₀ + γ.

## TheArchimedeanPairingOfTwoAtoms
- ω antitone on (0,∞). bumpAutocorr G(z) = ∫g(u)g(u+z), supported [−w,w], ∫G = (∫g)², ∫|G| ≤ (∫|g|)².
- Two atoms at distance s > w: levyMixed(g, g(·−s))(y) = −ω(y)G(y − s) (only forward product survives). Pair energy levyEnergy(g + g(·−s)) = 2levyEnergy g − 2X, X = atomCrossTerm = ∫_0^∞ω(y)G(y−s)dy.
- |X − ω(s)(∫g)²| ≤ (ω(s−w) − ω(s+w))(∫|g|)². With 2ω(s) = e^{s/2}/sinh s: archimedean cross pairing (∫g)²e^{s/2}/sinh s + O(w); with exact self-energy gives archimedean Gram of separated family to O(w).

## TheTiltedPrimeRows (uses RAPT)
- Schur rows with weights n^{−1/2} = A(⌊N/m⌋) + log m; max log N + O(1) attained at every row (top rows carry log N in down tower).
- Tilted Schur test: P_N(x) ≤ Σ_m x_m²Σ_n P(m,n)√(m/n)r(n)/r(m) for r > 0. Chebyshev Σ_{k≤K}Λ(k) ≤ (log4 + 4)K.
- Tilt r(n) = 1 + n/N: up tower costs ≤ log4 + 4; down tower: proper divisor ≤ m/2 ⇒ down row ≤ ((1 + m/2N)/(1 + m/N))log m.
- atomicWeilForm_le_tilted: P_N(x) ≤ Σ x_m²(log N + 2(log4 + 4) − (m/4N)log m). Saving (m/N)log m matches shape of archimedean cross-kernel row at spacing. Power weights n^α cannot produce it; weight separating m from m/2 does.

## TheStabilityLawAtTheSpacingScale
- Constants: spacingRatio c₁ = 1/(32e^{5/2}); spacingConstant C = 2(log4 + 4) + 1; spacingWidthRatio c₀ = c₁e^{−(C + 2|θ'(0)|)}. δ_N ≤ 1/N.
- crossRow_le_saving: at w ≤ c₁/N the cross-kernel row 8e^{5/2}wm(1 + log(N+1)) ≤ (m/4N)log m + 3/4: the down tower of the prime form pays the archimedean cross kernel scale by scale.
- markovEnergy_atomicTest_ge_spacing: 0 < w ≤ c₁δ_N ⇒ M(f) ≥ (2θ'(0) + log(1/w) − log N − C)‖f‖² (= log(1/(wN)) + O(1), Nyquist margin). markovEnergy_atomicTest_nonneg_spacing: M(f) ≥ 0 for w ≤ c₀δ_N, every N ≥ 1 (fixed fraction of spacing: tests see zeros up to height ≍ N).
- Weil: Re W(f) + 2S(f)² ≥ 0 (rank-one pole correction); Re W(f) ≥ 0 on cone |S| ≤ |C| (sinh/cosh half moments), in particular nonnegative weights and bumps.
- Gauge blind: every completely multiplicative sign twin satisfies the same law with the same constants.

## TheDiamagneticInequality
- levyMarkovForm h = 2θ'(0)‖h‖² + levyEnergy h − primeSum h (= Markov form on C² compact). Normal contraction: levyEnergy|f| ≤ levyEnergy f (Dirichlet form). twistedPrimeSum ω f ≤ primeSum|f| for |ω| ≤ 1 (prime place positive kernel).
- diamagnetic_inequality: archForm f − twistedPrimeSum_ω f ≥ levyMarkovForm|f|. Atomic tests below spacing with g ≥ 0: |f_x| = f_{|x|}. ζ = ground state of its gauge orbit: every lower bound M ≥ κ‖f‖² for ζ holds for every twist.
- Consequence: no margin in ζ's favour from arch-minus-prime form on |·|-closed families; margin must come from the pole term (anti-Markovian), signed bumps, or overlapping atoms.

## TheSpacingScaleLawIsUniversal
- Below spacing each prime pairing is exact Hecke pairing ‖g‖²Σ_{m=nk}x_mx_n; twistedPrimeSum ω f_x ≤ ‖g‖²P_N(|x|) for every real twist |ω| ≤ 1 (any, not multiplicative).
- Universal law: archForm f_x − twistedPrimeSum_ω f_x ≥ (2θ'(0) + log(1/w) − log N − C)‖f_x‖² at w ≤ c₁δ_N, ≥ 0 at w ≤ c₀δ_N. Blind to every arithmetic property beyond |a(k)| ≤ Λ(k): no selectivity in separated regime.

## UnboundedOverlapIsTheRiemannHypothesis (uses AOG spline orbit, ACS, HTGeometry inertia)
- Weil Grams translation invariant (common shift). Every finite set of rational Hecke shifts log r moves into logShifts {log n} after one common shift (log of common denominator).
- riemannHypothesis_iff_splineAtomic_negIndex_eq_zero: RH ⇔ for every finite S ⊆ {log n}, prime-side Weil Gram of cubic spline translates B(·−s) is PSD. zeta_splineAtomic_negIndex_law: max negative index = #distinct zeros right of line.
- Every fixed width w > 0 (B_w = U_w^{⋆4}, transform (sin(wz)/(wz))⁴ real-rooted, sees all right zeros): same law. At fixed width overlap wN → ∞. Bracket: ratio ≤ c₀ unconditional positivity; ratio → ∞ is RH; only bounded overlap between.

## TheGaugeEntersThroughNonRatioLags
- Overlap Gram ‖f_x‖² = Σ x_mx_nG(−s_mn). Overlap calculus: primeSum f_x = Σ_kΛ-atom_k·lagForm_k(x), lagForm = Σ x_mx_n(G(−log k − s_mn) + G(log k − s_mn)); twin with ω(k). Ratio lag n = km (or m = kn); non-ratio otherwise; G vanishes unless |log(km/n)| ≤ w.
- Gauge factor ω(k) − ω(m)ω(n) = 0 on ratio lags (completely multiplicative sign gauge) ⇒ twistedPrimeSum_ω f_x − primeSum f_{ωx} = sum over non-ratio lags only (unconditional summability: lags vanish for k > Ne^w).
- Below spacing (w < δ_N) no non-ratio lags (conjugacy of twins). Beyond: N ≥ 3 ⇒ atoms m = j+1, n = 2j+1 with |log 2 − log(n/m)| ≤ 4δ_N, n ≠ 2m. Gauge visible at overlap ratio order one; ζ's margin must use pole or non-ratio lags.

## TheAtomicFamilyIsADirichletPolynomial
- h_{f_x}(z) = h_g(z)D_x(z), D_x(z) = Σ x_ne^{iz log n}; at zero D_x(γ_ρ) = Σx_n n^{ρ−½}. Zero-side summand = m_ρ·h_g(γ_ρ)conj h_g(γ̄_ρ)·D_x(γ_ρ)conj D_x(γ̄_ρ); on line = m_ρ|h_g|²|D_x|² ≥ 0.
- Dictionary: below spacing zeros up to height ≍ 1/w oversample Dirichlet polynomials of length N (Nyquist density log N/2π vs zero density log(T/2π)/2π); at spacing Nyquist rate; beyond undersample.

## OverlapCoordinates (namespace LengthHeight; Mathlib only; #print axioms lines in source)
- height(X,c) = X/c, overlap X/T, bandwidth log X/log T, aperture log X/2 (e^{2·aperture} = X: prime cutoff X). bandwidth = 1 + log(overlap)/log T; bandwidth ≤ 1 ⇔ overlap ≤ 1 ⇔ X ≤ T. bandwidth(T^α) = α, overlap(T^α) = T^{α−1} (fixed excess bandwidth = power-growing overlap; 4/3 ↦ T^{1/3}). log height − log X = −log c. Every fixed overlap c > 0 has limiting bandwidth 1.

## TheNormalizedAtomicTransform (#print axioms lines in source)
- mellinPolynomial Σa_n n^{−s}; D_x(z) = mellinPolynomial(√n x_n)(½ − iz). Unnormalized atom φ(·/w): ĥ = w·h_φ(wz); unit-mass dilate T: h_φ(z/T); both multiply the same Dirichlet polynomial at every complex argument (off-line zeros and poles included). Height = inverse width.
- Compact profile with ∫φ ≠ 0 has nonzero Fourier values at arbitrarily large real heights (entire, vanishing on an interval ⇒ 0): no hard height cutoff.

## TheAtomicApertureRetainsTheProfileWidth (LengthHeight; #print axioms lines)
- Profile supported [a,b], width w: atomic test supported [aw, log N + bw]; centred aperture (log N + (b−a)w)/2 = aperture N + (b−a)w/2; outer cutoff e^{2·aperture} = N e^{(b−a)w} (plateau [0,1]: Ne^w; symmetric [−1,1]: Ne^{2w}). Polynomial length and literal support cutoff are distinct coordinates.

## ProfileNormalizationPreservesTheCompleteForm (LengthHeight; #print axioms lines)
- unitIntervalProfile φ(a + (b−a)u): atom of width w = common translate of normalized atom at width (b−a)w; weilQuad, squared mass, atom mass and normalized complete form preserved (translation invariance). height X((b−a)c) = height X c/(b−a). Symmetric profile at overlap c = unit-interval profile at overlap 2c.

## WeilsFormIsContinuousInTheLevyNorm (part 1)
- weilQuad Q(f) = Re W(f,f) (explicit formula, Λ). Lévy form: Q(f) = 2θ'(0)‖f‖² + levyEnergy f − primeSum f + 2C(f)² − 2S(f)² (C, S = cosh/sinh half moments). Translation invariant.
- Levy energy = square of a seminorm: levyEnergy(tf + d) quadratic in t with mixed term; Cauchy–Schwarz levyEnergy(f+d) ≤ (√E_f + √E_d)².
- Supported in [−R,R]: prime sum finite over k < lagRange R = ⌈e^{2R}⌉ + 1; primeMass P_R = Σ_{k<lagRange}Λ(k)/√k. |primeSum(f+d) − primeSum f| ≤ 2P_R(2‖f‖₂‖d‖₂ + ‖d‖₂²).
- weilQuad_add_le (f, d supported [−R,R]): Q(f+d) − Q(f) ≤ 2|θ'(0)|(2‖f‖‖d‖ + ‖d‖²) + 2√(L_fL_d) + L_d + 2P_R(2‖f‖‖d‖ + ‖d‖²) + 4cosh(R/2)(|C_f| + |S_f|)‖d‖₁ + 4cosh²(R/2)‖d‖₁².
- levyEnergy_le_lipschitz: K-Lipschitz d, 0 < δ ≤ 1: levyEnergy d ≤ e^{1/2}Kδ‖d‖₁ + (2log(1/δ) + C₁)‖d‖₂², C₁ = levyLipConstant = e^{1/2} + 8e^{−1/2}/(1 − e^{−2}). Perturbation of size ε, Lipschitz K moves Q by O(ε√log(K/ε)), not O(K).

## TheLogLatticeSynthesizesWideTests
- cellWeight x_k = ∫_{a_k}^{a_{k+1}}F; cellSum S(r) = Σ x_kψ(r − a_k). Cell lemma: |S(r) − ∫F(t)ψ(r−t)dt| ≤ ‖F‖_∞·h·‖ψ'‖₁ (h max gap; L¹ of ψ', not sup).
- Convolution with probability profile in [−ρ,ρ]: |F*ψ − F| ≤ Lρ‖ψ‖₁ (L-Lipschitz F). Mean value: |f'| ≤ B ⇒ B-Lipschitz.
- logNode a_j = log(n₀ + j) − c, gaps ≤ 1/n₀. dilate φ_k(s) = kφ(ks): same mass and L¹, ‖φ_k'‖₁ = k‖φ'‖₁. Width 1/k bump: error O(k/n₀) ⇒ atoms near height n₀ synthesize a fixed test when k = o(n₀): widths N^{−θ}, θ < 1.

## TheCriticalExponent
- Synthesis bounds: |S − F| ≤ Mh‖ψ'‖₁ + Lρ‖ψ‖₁; Lip(S) ≤ M‖ψ'‖₁ + Mh‖ψ''‖₁. For d with |d| ≤ e on [−R,R]: ‖d‖₁ ≤ 2Re, ‖d‖₂² ≤ e‖d‖₁.
- Log-lattice nodes a_j = log((n₀+j)/n₀) − R cover [−R,R] with cellCount ⌈n₀e^{2R}⌉ cells, block size B = ⌈1 + e^{2R}⌉: atoms n₀ ≤ n ≤ n₀B synthesize F supported in [−R,R]. synthErr e₀ = M(k/n₀)‖φ'‖₁ + L‖φ‖₁/k; synthLip; synthLevy at δ = 1/k: O((k/n₀ + 1/k)²log k).
- exists_atomicTest_weilQuad_le: ∃x: Q(atomic test at level n₀B, dilate k φ) ≤ Q(F) + weilErr(...).
- OverlapGrowth κ: κ_N → ∞ and (κ_N/N)²log κ_N → 0 (overlap ratio N/κ_N beats √log κ_N). Under it synthesis errors → 0.
- riemannHypothesis_iff_atomicFamilies_nonneg_of_growth: C² φ on [−1,1], ∫φ = 1, κ overlap growth ⇒ [RH ⇔ eventually Q ≥ 0 on all atomic tests Σx_nφ_κ(·−log n)]. Widths N^{−θ}, 0 < θ < 1 (critical exponent 1); widths (log N)^α/N, α > ½ (overlap ratio (log N)^{½+ε} already RH).

## TheGaugeBecomesVisibleAtTheCriticalExponent (uses SPTL, RHTower twist obstructions)
- twistCoeff λ(n)/√n; pairing = two Hecke pairings; weilQuadTw Q_λ. Q_λ(f) = Q(f) + Σ_{n<lagRange}(Λ-atom − twistCoeff)·pairing_n(f) (finitely many lags on a window). Translation invariant; continuity: extra lags cost ≤ 4P_R(2‖f‖‖d‖ + ‖d‖²) for |λ| ≤ Λ.
- weilPositive_iff_atomicFamilies_nonneg: |λ| ≤ Λ, overlap growth ⇒ [Q_λ ≥ 0 on all real tests ⇔ eventually ≥ 0 on atomic families]. atomicFamilies_negative_iff: negative infinitely often ⇔ ¬WeilPositiveFull λ.
- Unconditional instances seen: Liouville twin (certified ground eigenvalue < −3/10 at aperture 23/40, SPTL), scalings cΛ (−1 ≤ c < 1), quadratic mixtures Λ(1 − t + tχ) (0 < t ≤ 1, χ real primitive). riemannHypothesis_imp_liouville_separation: under RH, overlap growth separates ζ (eventually ≥ 0) from Liouville (negative i.o.).
- Pole-free complex test with negative atom-symbol energy refutes WeilPositiveFull.

## ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold
- poleMomentNeg m₋ = ∫g e^{−u/2}, poleMomentPos m₊ = ∫g e^{u/2}; markovQuad M(g) = Q(g) − 2m₋m₊. M(u + iv) = M(u) + M(v) ⇒ real negative direction exists (exists_markovQuad_neg; M is not PSD for ζ). M translation invariant; continuity bound adds pole-product motion 2(e^{R/2}(|m₋|+|m₊|)‖d‖₁ + e^R‖d‖₁²).
- markov_atomicFamilies_negative: under overlap growth, for infinitely many N some atomic test has M < 0 — unconditionally, for ζ itself. markovThreshold_bracket: M ≥ 0 at width ≤ c₀δ_N for every N; M < 0 i.o. under overlap growth: threshold not arithmetic.
- riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg: overlap growth ⇒ [RH ⇔ eventually M ≥ 0 on atomic tests with m₋ = 0]. Proof: pole-free negative test synthesized, corrected back into hyperplane by vanishing multiple t of synthesized bump h with m₋(h) > 0 (|t| ≤ corrT → 0).
- Correction rank of stability law: 0 at spacing; ≥ 1 once overlap beats √log N; exactly 1 (the pole) iff RH.

## TheWeightOfOneZero
- Power sums: Σn^a ≤ (N+1)^{a+1}/(a+1); Σn^{−a} ≤ (M+1)^{1−a}/(1−a); product (Σn^a)(Σn^{−a}) ≤ (N+1)²/(1 − a²) (0 ≤ a < 1).
- ‖D_x(z)‖² ≤ ‖x‖²Σ n^{−2Im z}; bump factor ‖h_g(z)‖ ≤ e^{|Im z|r}‖g‖₁ (supp [−r,r]).
- Weight of one zero (σ = Re ρ − ½): ‖term_ρ‖ ≤ m_ρ(e^{|σ|r}‖g‖₁)²‖x‖²(N+1)/√(1 − 4σ²), 1 − 4σ² = 4β(1−β). Dilated φ_k relative to diagonal energy ‖x‖²‖φ_k‖²: ≤ m_ρe^{2|σ|/k}(‖φ‖₁²/‖φ‖₂²)((N+1)/k)/(2√(β(1−β))). (N+1)/k ≈ overlap ratio: at spacing one zero carries a bounded fraction of diagonal energy uniformly in height and N; off-line zero at most 1/(2√(β(1−β))) times on-line bound.

## TheMarkovFormFailsInsideTheSeparatedRegime (part 1)
- Pole vector: P_N(n^{−1/2}) = 2Σ_{n≤N}log n/n (Σ_{d|n}Λ = log n) ≥ log²N − log²3. Σ(n^{−1/2})² = H_N.
- x ≥ 0, g ≥ 0, w < δ_N: levyEnergy f_x ≤ ‖x‖²levyEnergy g (cross correlations only lower it).
- archRobinConstant_eq: 2c_∞ = 2log2 + π/2 (antiderivative ½log((1+e^{−y/2})/(1−e^{−y/2})) + arctan e^{−y/2}).
- Plateau φ_η (1 on [η,1−η], 0 off [0,1], smooth, 2C/η-Lipschitz): ‖φ_η‖² ≥ 1 − 2η; ‖φ − φ(·+y)‖² ≤ 2y + 4η; β(φ_η) ≤ 1 + 2Cη − 4η log η; ∀ε some plateau has β/‖φ‖² ≤ 1 + ε.
- Pole vector bound (φ ≥ 0, w < δ_N): M(f) ≤ ‖g‖²(H_N(2θ'(0) + log(1/w) + κ_L(φ) + e^{1/2}w/2) − (log²N − log²3)).
- 2θ'(0) + γ = −(3log2 + π/2 + log π). Threshold: c ∈ (e^{β/‖φ‖²}/(2π), 1) ⇒ M < 0 on pole vector at width cδ_N for all large N (finite part log(1/c) + β/‖φ‖² − log 2π per log N; γ cancels between H_N and θ'(0)).
- markov_poleVector_negative_inside_separated: every c ∈ (e/(2π), 1) fails (e/(2π) ≈ 0.433 < 1): the pole correction is needed inside the separated regime.

## TheUniversalThresholdIsFinite
- Universal threshold K_univ: largest overlap ratio where Re W_ω + 2S² ≥ 0 for every real twist |ω| ≤ 1 on every atomic family uniformly in N; ≥ c₀.
- weilQuadTw_eq_markov: Re W_ω(f) = archForm f − twistedPrimeSum_ω f + 2C² − 2S² ⇒ Re W_ω + 2S² = M_ω + 2C².
- Wide tests: L-Lipschitz on [0,D]: levyEnergy ≤ 36DL² + 4A(D)‖f‖², A(D) = ∫_D^∞ω → 0; 2θ'(0) < −5 ⇒ archForm < 0 for wide tests.
- Dipole f = g − t g(· − log 2) (N = 2), t = C(g)/C(g(·−log2)) ≤ 1/cosh(log2/2) kills cosh moment; aligned twist ω(k) = sign(pairing_k f) makes twisted prime sum Σ Λ|pairing| ≥ 0 ⇒ Re W_ω + 2S² = M_ω ≤ archForm f < 0 for wide bumps. universalThreshold_bracket: c₀ ≤ K_univ < ∞ (failing family N = 2, ratio W/log(3/2)). Extremal twist = sign of lag correlations; threshold decided on signed families.

## TheRowsAtBoundedOverlap
- ratioLag, nonRatioLag, nonRatioForm NR_w = Σ_kΛ-atom·nonRatioLag_k. lagForm = ‖g‖²ratioLag + nonRatioLag; Σ_kΛ-atom·ratioLag_k = P_N(x). Overlap identity (every width): primeSum f_x = ‖g‖²P_N(x) + NR_w(x); NR_w = 0 below spacing.
- Counting: ≤ 2d naturals ≠ c within d of c; log-window half-width w around c lies within c(e^w − 1). Up window √(m/n) ≤ e^{w/2}/√k; down window ≤ e^{w/2}√k. Reindex by product Σ_{k,n}Λ(k)[Q(kn)] ≤ Σ_{ℓ∈Q}log ℓ.
- Rows: up ≤ 2(log4+4)e^{3w/2}(e^w−1)N (Chebyshev); down ≤ 2e^{w/2}m(e^w−1)(log m + w). |NR_w(x)| ≤ ‖g‖²Σx_m²ρ_w(m) (weighted Schur, weights n^{−1/2}).
- At overlap ratio K (w ≤ K/N ≤ 1): ρ_w(m) ≤ 2(log4+4)e^{5/2}K + 2e^{3/2}K(m/N)(log m + 1). primeSum f_x ≤ ‖g‖²Σx_m²(log N + 2(log4+4) − (m/4N)log m + ρ_w(m)).
- Bounded overlap = competition of three rows of shape (m/N)log N: tilt saving 1/4, archimedean cross kernel ≍ K, non-ratio lags ≍ 2e^{3/2}K. Coefficient-size method closes only while constants allow; beyond, positivity must read signs of non-ratio lags (the gauge).

## TheSecondOrderSynthesis
- Taylor on a cell; trapezoid on a cell: |∫_p^q G − (q−p)(G(p)+G(q))/2| ≤ (q−p)∫|G'| and ≤ (5/4)(q−p)²∫|G''| (endpoint Taylor expansions cancel to first order). trapRule on nodes with gaps ≤ H: errors H∫|G'|, (5/4)H²∫|G''|.
- trapSum S(r) = T(t ↦ F(t)ψ(r−t)): |S − F*ψ| ≤ (5/4)H²(M₂‖ψ‖₁ + 2L‖ψ'‖₁ + M‖ψ''‖₁); |S'| ≤ M‖ψ'‖₁ + H(L‖ψ'‖₁ + M‖ψ''‖₁). Trapezoid weights F(a_j)(a_{j+1} − a_{j−1})/2 on atoms n₀+j: atomic test = translated trapSum.
- synthErrTwo = (5/4)(1/n₀)²(M₂‖φ‖₁ + 2Lk‖φ'‖₁ + Mk²‖φ''‖₁) + L‖φ‖₁/k; Lipschitz O(k); Lévy energy of error O(((k/n₀)² + 1/k)²log k).
- OverlapGrowthTwo: κ → ∞, (κ_N/N)⁴log κ_N → 0 (implied by OverlapGrowth). riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo; widths (log N)^α/N: RH ⇔ eventual positivity for every α > ¼ (riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter). Overlap ratio window narrows to fourth root of log.

## TheEulerMaclaurinSynthesis (uses RHTower DQPT Euler–Maclaurin)
- Weights x_n = F(log n − c)/n turn synthesis into Σ_n s⁻¹H(log s) (H(t) = F(t−c)ψ(r+c−t)) whose integral is F*ψ. logTower T_0 = H, T_{j+1} = T_j' − (j+1)T_j: (d/ds)^j[s⁻¹H(log s)] = s^{−(j+1)}T_j(log s).
- Euler–Maclaurin on log-lattice: H smooth vanishing off [α,β], 0 < α, β < log(1+N): |Σ_{n≤N}(1+n)⁻¹H(log(1+n)) − ∫H| ≤ (|B_p|/p!)e^{−pα}‖T_p‖₁, p = 2m+2 (boundary terms vanish).
- ‖T_p^{(j)}‖₁ ≤ (p+1)!Σ_{i≤p}‖H^{(j+i)}‖₁; Leibniz bound ‖(F(·−c)G(a−·))^{(i)}‖₁ ≤ Σ C(i,l)M_l‖G^{(i−l)}‖₁; ‖(φ_k)^{(q)}‖₁ = k^q‖φ^{(q)}‖₁.
- abs_emSynth_dilate_sub_le: c = log n₀ + R, n₀ ≥ 2: error ≤ emConst·(k/n₀)^{2m+2} for every m (arbitrary order). Lipschitz |S'| ≤ k(M₀‖φ'‖₁ + emConst'(k/n₀)²).
- exists_emSynthesis / exists_atomicTest_weilQuad_le_em: smooth φ, smooth F supported [−R,R]: atomic test = translate of F + D, |D| ≤ emErr = emConst(k/n₀)^{2m+2} + M₁‖φ‖₁/k, Lipschitz emLip; Weil moves by weilErr. (Remaining limit: the convolution error M₁‖φ‖₁/k, first order in 1/k.)

## TheOverlapLawAtEveryRoot
- Mollification g_m = g * φ_m: smooth, supported in [−(R+1), R+1], |g_m − g| ≤ L‖φ‖₁/m, Lipschitz M m‖φ'‖₁; Lévy energy of difference O((log m)/m²) ⇒ exists_smooth_weilQuad_neg: negative C² test ⇒ negative smooth test.
- OverlapGrowthPow q: κ → ∞, (κ_N/N)^q log κ_N → 0 (q = 2: OverlapGrowth, q = 4: OverlapGrowthTwo); monotone in q. EM errors vanish under order 2(2m+2).
- riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow: smooth φ on [−1,1], ∫φ = 1, any q, overlap growth of order q ⇒ [RH ⇔ eventual Q ≥ 0 on atomic families]. riemannHypothesis_iff_atomicFamilies_nonneg_log_pos: widths (log N)^α/N for every α > 0: positivity is RH as soon as overlap ratio is unbounded at any power of log N.

## TheGaugeAtEveryRoot
- StableForm Φ: translation invariant on C² compact tests; a C² perturbation supported in [−R',R'] with |D| ≤ e and Lipschitz L_D moves Φ by ≤ Err(e, synthLevy), Err → 0. Stable: weilQuad, weilQuadTw (|λ| ≤ Λ; extra 4P(2‖F‖‖D‖ + ‖D‖²)), markovQuad (pole-moment cost).
- Transfer: stable form negative on C² test ⇒ negative on smooth test (mollify) ⇒ negative i.o. on atomic families of any order overlap growth; nonneg_iff_atomicFamilies_nonneg_of_stable.
- At every root (any OverlapGrowthPow q, smooth φ): twist seen ⇔ not Weil positive; Liouville, scalings cΛ, quadratic mixtures seen; under RH ζ separates from Liouville at overlap ratio (log N)^ε. Markov form negative i.o. at every root unconditionally.

## ThePoleAtEveryRoot
- Correction: m₋(F) = 0, smooth bump h ≥ 0 on [−2,2] with m₋(h) > 0, small D₁, D₂: some t, |t| ≤ 2e^{R'/2}2R'e₁/m₋(h), puts F + D₁ − t(h + D₂) in pole hyperplane; comb_perturbation bounds; tendsto_comb errors vanish.
- Smooth pole-free negative Markov test from C² one (mollify + correct). frequently_poleHyperplane_markov_neg.
- riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow: any order overlap growth ⇒ [RH ⇔ eventually M ≥ 0 on atomic tests in m₋ = 0]. With Markov failure: at ratio (log N)^ε M has a negative square unconditionally; RH = it has only one (the pole).

## TheGevreyWindow
- |B_{2m+2}|/(2m+2)! ≤ 1 (ζ(2k) ≤ π²/6). Gevrey tower: ‖H^{(j)}‖₁ ≤ C(j!)^sX^j ⇒ ‖T_p^{(j)}‖₁ ≤ C((j+p)!)^sX^jΠ_{i<p}(X + i + 1) (lower-order terms cost X + p + 1, not factorial). Gevrey Leibniz: ‖(F(·−c)G(a−·))^{(i)}‖₁ ≤ MA(i!)^s(b + B')^i.
- abs_gevreySynth_sub_le: |S − F*φ_k| ≤ MA(p^s(b + Bk + p)/n₀)^p, p = 2m+2. gevErr adds Mb‖φ‖₁/k.
- OverlapGrowthGevrey s: κ → ∞, (N/κ_N)/(log log κ_N)^s → ∞. Order p = 2⌈log log k⌉ + 2 growing with level; ratio ρ → 0, quadrature error ≤ MA/(log k)². Mollified tests are Gevrey: |(g*φ_m)^{(l)}| ≤ M_gA(Bm)^l(l!)^s.
- Transfer law in Gevrey window for stable forms; riemannHypothesis_iff_atomicFamilies_nonneg_of_gevrey; widths (log log N)^α/N, α > s: RH ⇔ eventual positivity (riemannHypothesis_iff_atomicFamilies_nonneg_loglog). Gauge seen ⇔ not Weil positive; Markov negative i.o. unconditionally, in Gevrey window.

## TheGevreyProfile
- Glue E(x) = e^{−1/x}: E^{(n)}(x) = P_n(1/x)E(x), P_{n+1} = X²(P_n − P_n'), deg P_n < 2n+1. Weighted coefficient norm W_D(P) = Σ|c_j|j! bounds sup_{t≥0}|P(t)|e^{−t} (t^je^{−t} ≤ j!); W_{D+2}(X²(P − P')) ≤ 2D²W_D(P) ⇒ |E^{(n)}| ≤ 8^n(n!)² (Gevrey class 2).
- gevreyProfile φ_G = cE(1+x)E(1−x): smooth, vanishes off [−1,1], ∫ = 1, |bump^{(q)}| ≤ 16^q(q!)², ‖φ_G^{(q)}‖₁ ≤ 2c16^q(q!)².
- riemannHypothesis_iff_gevreyProfile_nonneg_loglog: every α > 2, RH ⇔ eventual positivity on φ_G atomic families of width (log log N)^α/N. Gauge seen beyond (log log N)² ⇔ not Weil positive.

## TheDenjoyCarlemanProfiles (part 1)
- glueR E_r(x) = E(x^r), r odd: zero on (−∞,0], exp(−(1/x)^r) on (0,∞); E_r^{(n)} = Q_n(1/x)exp(−(1/x)^r), Q_{n+1} = rX^{r+1}Q_n − X²Q_n', deg Q_n < n(r+1)+1; derivatives vanish on (−∞,0] (closure argument).
- Weights (j!)^{1/r}: t^je^{−t^r} ≤ (j!)^{1/r} (r-th power ≤ (t^r)^je^{−t^r} ≤ j!); dcNorm W_D(Q) = Σ|c_j|(j!)^{1/r}; (i+m)! ≤ (i+m)^m i!; one step gains ≤ (r+1)(D+r)^{1+1/r} ⇒ |E_r^{(n)}| ≤ ((r+1)^{2+1/r})^n(n!)^{1+1/r} (Gevrey class 1 + 1/r).
- dcProfile φ_r = cE_r(1+x)E_r(1−x): ‖φ_r^{(q)}‖₁ ≤ 2c(2(r+1)^{2+1/r})^q(q!)^{1+1/r}. riemannHypothesis_iff_dcProfile_nonneg_loglog (α > 1 + 1/r); exists_dcProfile_loglog: every α > 1 has an explicit profile (r = 2⌈1/(α−1)⌉+1) with RH ⇔ eventual positivity at width (log log N)^α/N. Gauge seen ⇔ not Weil positive under Gevrey growth of class 1 + 1/r.

## TheArchimedeanDensityHasQuadraticIncrementControl
- Global inverse-square increment: 0 < a ≤ b ⇒ ω(a) − ω(b) ≤ 19(b − a)/a² (split numerator/denominator variations; a²e^{−2a} ≤ (1 − e^{−2a})²; CHMD ω(a)a² ≤ 34). Pair window: ω(s−w) − ω(s+w) ≤ 38w/(s−w)².

## TheOverlapGramHasBoundedRows (#print axioms line)
- Log-window row: #{n ≤ N: |log n − log m| ≤ w} ≤ 1 + 2m(e^w − 1). ‖f_x‖² ≤ ‖g‖²(1 + 2N(e^w − 1))‖x‖² for any signed x and any compact bump in [0,w]. Fixed overlap c (w = c/N): ‖f_x‖² ≤ ‖g‖²(1 + 2ce^c)‖x‖², uniform in N.

## TheTiltedSplineKeepsAGammaReserveAtEveryOverlap (#print axioms lines; uses BSU cubic spline probe, TMWP Montgomery–Vaughan band, APT Gamma budgets)
- tiltedUnitSpline = boosted cubic spline (splineProbe = tiltedSource of cubic spline) dilated/translated to [0,1]; transform has no real zeros (boost shifts off zero line); ‖·‖² > 0.
- archForm_ge_log_band_sub_mass: archForm f ≥ (log R/2π)∫_R^{101R}|f̂|² − (γ-offset + log2)‖f‖² (gammaBracket ≥ log on band, ≥ −offset elsewhere; Plancherel).
- Fourier floor m > 0 on [c,101c]; Montgomery–Vaughan ∫_N^{101N}|D_x|² ≥ 48N‖x‖² ⇒ high-band mass ≥ 48(c/N)²mN‖x‖².
- exists_tiltedUnitSpline_archForm_reserve: every fixed overlap c > 0: ∃a > 0, b ≥ 0: archForm(atomic test)/(w‖φ‖²) ≥ (a log N − b)‖x‖² for all N and all signed x (Gamma reserve logarithmic in N).

## TheGammaFormLocalizesAtAnOrderedCutoff (#print axioms lines; uses AID touching supports, RAPT Markov finite part)
- Polarization of the spectral Gamma form. Ordered supports (f left of b, g right): archForm(f+g) ≥ archForm f + archForm g − 2π(‖f‖² + ‖g‖²) (no logarithmic loss).
- Separated atoms (w ≤ δ_M/2): archForm(atomic test) ≥ ‖g‖²((2θ'(0) + log(1/w) − 2wM·separatedCrossMassCost)‖x‖² − 32e²wM·poleDefect_M(x)): unit log self-energy at prime-defect cost proportional to overlap.

## EveryProfileWithoutRealFourierZerosKeepsAGammaReserve
- Same reserve for every C² profile on [0,1] with no real Fourier zeros: exists_noRealZero_archForm_reserve (positive floor on compact bands + Montgomery–Vaughan). Used by RAPT/CACT resolution thresholds.
