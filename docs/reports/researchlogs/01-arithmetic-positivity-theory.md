# APT working log (mathematical facts)

Source: concatenation cat/01.txt (57292 lines, 109 files). Progress: lines read up to marker below.

## AdmissibleStencilsAndCellKernelsBeyondDyadic
- Divisor stencil (D, α), 0∉D: P_{D,α}(u)=Σ α(d) C(du) (clamped kernel); phase profile Φ_{D,α,N}(v)=P(λ_N v)−P(N v).
  Cosine expansion: Σ_k w_k cos(2πku) = −(π²/2)·centered filter; w_k = M(k)/(4k²), M(k)=Σ_{d∈D,d|k} α(d)d².
  |w_k| ≤ (Σ|α_d|d²/4)/k². Lipschitz const of P: (Σ|α_d| d)/2.
- Structure `AdmissibleHarmonicWeight w C_w τ`: w0=0, w1=1, |w_k|≤C_w/k², Σ_{k≥2}|w_k|≤τ<1. Gives Σ|w_k|≤1+τ, |B_{w,S,b}|≤4(1+τ)/π²·Σ|b|.
- Four admissible families: dyadic (C=1,τ=3/4); q-adic sign-flip on {1,q,q²} weights (4,−8/q²,4/q⁴), χ_q(k)=1−2[q|k]+[q²|k] (C=1,τ=3/4);
  q-adic drift-free (4,−4(q+1)/q²,4/q³), χ=1−(q+1)[q|k]+q[q²|k], kills linear ramp L and quadratic drift Q; exact Σ|w_k| = (π²/6)(1+(q²−q−1)/q³); τ=24/25 via SOS 5q³−27(q²−q−1)=(q−3)²(5q+3);
  higher-order w_k=c_k/k^p (p≥2, c1=1,|c|≤1), p≥3 ⇒ Σk|w_k|<∞ ⇒ Lipschitz.
- Σ_k [d|k]/k² = (π²/6)/d².
- Window floor for every admissible w: window length L_τ = 8(1+τ²)/(1−τ²)²·K, K=390/π: ∫_a^{a+L_τ}|B|² ≥ (8K/π⁴)Σ b². Proof: first-harmonic dominance lemma `integral_norm_sq_ge_of_first_harmonic` with θ=(1+τ²)/2; harmonic layers have interval bounds (L∓K/k)Σb².
  Dilated upper: ∫_a^{a+ℓ}|B(rv)|² ≤ 4(1+τ)²/π⁴ (ℓ+K) Σ b² (r≥1).
- Collared source g_{w,c}(x)=σ(e^{−x}−1)e^{x/2}B(e^{−x})1_{x≤0} (σ=smoothTransition); doubly collared g^V = cutoff(e^{−x}/V)·g_{w,c}, support [−log 2V,0].
  Mass: A_w Σb² ≤ ∫g² ≤ U_w Σb², A_w=(8K/π⁴)/(2+L_τ)², U_w=(π²/6)·4(1+τ)²(1+K)/π⁴. Via substitution v=e^{−x}: ∫g² = ∫_{v>1} σ²B²/v².
- Low-frequency Mellin exclusion: |ĝ(t)| ≤ 2C_w D_c Σ|b_n|/(n+1) for |t|≤π(n+1); per-harmonic nonstationary bound C/(πk(n+1)), summed over k with |w_k|≤C_w/k². Square: ≤ 2(2C_wD_c)²/M Σb² on scales ≥M (Cauchy–Schwarz + Σ_{n≥M}1/n² ≤ 2/M).
- Lévy coercivity: sourceLevyEnergy(g) ≥ s_w(log M − c_w)Σb², s_w = e^{−1/2}A_w/2 (general lemma `ofReal_le_sourceLevyEnergy`: mass floor + low-band smallness ⇒ log-growth).
- Prime channel: dilation correlation ∫φ(v)B(v)B(rv) reduced harmonic-by-harmonic to dyadicCrossKernel; bound C_w²·(4/π⁴)Σμ.
- Prime channel of collared/truncated sources: atom Λ(r)/√r·∫g g(·−log r) = Λ(r)/r ∫_{v>1} weight·B(v)B(rv); bounded by C_w²·const·Σb² on dyadic blocks uniformly in V via envelopePrimeMajorant 1 (Λ(r)/r^{3/2} summable) and dyadic dilation inequality with factor 1/√r.
- Polar readouts: harmonic primitive G_k (exact sine primitive, |G_k|≤(1/π)Σ|b|/(n+1)) + integration by parts ⇒ |∫φB| ≤ ‖φ'‖₁·2(1+τ)/π³·Σ|b_n|/(n+1). Readout ∫g e^{x/2}, endpoint ∫g e^{−x/2} both O(Σ|b|/(n+1)) ⇒ product ≤ C·T² ≤ C·Σb² (T²≤(2/M)Σb²).
- Truncation tail h^V=g_c−g^V: ∫h² ≤ (U_w/V)Σb² (substitution v→Vu). Threshold V₀(τ)=max(2+L_τ, 8U/A).
- Truncated Lévy coercivity: split low band |t|≤ηM: density(g) ≤ 2dens(g_c)+2dens(h); low band small (≤A/4) ⇒ high-band mass ≥ A/4·E ⇒ Lévy ≥ e^{−1/2}(log R−3)(A/4)E (`sourceLevyEnergy_ge_highBand`).
- Complete energy (Gamma–Lévy form): Lévy + Ω(0)ac(0) + 2·Readout·Endpoint − 2·PrimeEnergy. Equals compactFullWeilEnergy when B Lipschitz (needs Lipschitz for `integrableOn_levy_of_lipschitz` / `re_weilFullFunctional_eq_of_compact_finite_jump`).
- Block positivity: complete energy ≥ (s(log M − c) − K_channels)Σb² ⇒ ∃M₀: positive on every dyadic block above M₀ uniformly in V≥V₀. Also fullZeroForm >0. Mechanism = archimedean log M beats bounded channels.
- Section 3 (cell kernels): charge A_χ(m)=χ(m)Σ_{r|m} rΛ(r)χ(m/r); A_χ(1)=0, A_χ(p)=p log p χ(1)χ(p). |A_χ(m)|≤C²m log m ⇒ Σ|A|/m³ summable.
  Kernel R_χ(t)=Σ_m (A_χ(m)/m³)(T_m(t)+T_m(1−t))/2 (T_m = harmonic tail Σ_j γ(j+m+t)-type); Poisson window decomposition R_χ(t)= Σ A J_m/m⁴ − ½Σ (A/m³)·windowDeviation(m,t); deviation ≤ (π/6)³/35 /m³-type.
  T_2(t) ≥ 1/18 on [0,1] (cos(2πu/12)≤1/2 for u∈[2,3], u^{-2}≥1/9).
- Nonnegative charges (A_χ≥0 all m) ⇒ R_χ(t) ≥ A_χ(2)/144 >0 on [0,1] (positive definite; "prime penalty" regime). Includes all nonnegative multipliers.
- q-adic sign-flip, q≥3: χ_q(2)=1 ⇒ A(2)=+2log2>0 and A(m)=Σ_{r|m} rΛ(r)≥0 for q∤m. So q=2 is the unique sign-flip base with A(2)<0.
- Charge perturbation: (π²/6)Σ|A_χ−A_dyadic|/m³ ≤ 1/7000 − μ ⇒ R_χ ≤ −μ (dyadic kernel R ≤ −1/7000). Perturbed χ_{d,ε}=χ_dyad+ε[d|k], d≥3, ε=min(1/40, (1/14000)/K) gives admissible (τ=4/5) negative-definite kernel ≤ −1/14000 — infinite non-dyadic family with prime subsidy. |ΔA(m)|≤3ε m log m.
## BakerPrimeLogTranscendenceAndCollarSpectrumDisjointness
- Uses RHTower Baker (bakerLinearIndependence_holds, baker_linearForm_transcendental). Nontrivial algebraic linear forms Σc_i log p_i transcendental.
- 4λ_N³ = N²(4N+1): λ_N algebraic (cubic, irrational) ⇒ algebraic combos of collar freqs algebraic; collar width (1/3)log(1+1/(4N)) transcendental.
- Hence Σc_i log p_i ≠ Σα_j λ_{N_j} (spectral disjointness); Bohr mean of relative phase → 0 (qualitative only, no rate).
## CollaredCriticalArchimedeanLogCoercivity (start)
- AdmissibleSource g := complex lift ∈ L¹∩L². sourceAutocorrelation, sourceLevyEnergy = ∫_{x>0}(ac(0)−ac(x))ω(x) in ℝ≥0∞ (ω = archLevySinhWeight = e^{x/2}/sinh x type). ac_g(x) = (1/2π)∫|ĝ|²cos(tx).
- Lévy ≥ e^{−1/2}(log R −3)·(high-band spectral mass beyond R); mass floor A E + low band |ĝ|²≤(2D²/M)E on |t|≤πM ⇒ Lévy ≥ e^{−1/2}(A/2)(log M −3 − log(1/η))E.
- Collared Mellin amplitude a_c(v)=σ(v−1)v^{−3/2} vanishes at v=1 ⇒ IBP without boundary terms: |∫a_c e^{i(ωv − t log v)}| ≤ (2/|ω|)(‖a_c'‖₁+‖a_c/v²‖₁).
- Collared Lévy–prime form: Lévy(g_c) − 2P_c ≥ (s_c(log M−c_c) − 2C_c)Σb² on dyadic blocks; no limit on number of atoms.
- Lévy high-band law proof: spectral jump ac(0)−ac(x)=(1/2π)∫|ĝ|²(1−cos tx); Tonelli swap; per-frequency ∫(1−cos tx)ω(x)dx ≥ e^{−1/2}(log|t|−3) for |t|≥1 (`ofReal_log_sub_le_lintegral_one_sub_cos_mul_archLevySinhWeight`, BiScaleUncertainty).
- Flat-amplitude nonstationary phase lemma (general, reusable): a(1)=0, a→0, a,a',a/v² ∈ L¹(1,∞), |t|≤|ω|/2 ⇒ |∫_{v>1} a e^{i(ωv−t log v)}| ≤ (2/|ω|)(‖a'‖₁+‖a/v²‖₁).
- Dyadic collared constants: mass floor A_c = L/(16π⁴(2+L)²); D_c=3(C_a+1)/π³ (Σ1/k³≤3/2); mass ceiling U=(π²/6)J (J unit-interval upper 49(1+K)/(4π⁴)).
## CollaredCriticalCompleteFormPositivity
- Readout R_c = ∫g_c e^{x/2} = ∫_{v>1}ψ B; endpoint E_c = improper ∫σ(v−1)B/v (defined via primitive regularization −∫ρ'G; proven as limit). Both ≤ ‖·'‖₁·12Σ|b_n|/(n+1) via phase primitive G (|G|≤12Σ|b|/(n+1)).
- (Σ|b_n|/(n+1))² ≤ (2/M)Σb² on scales ≥M.
- Complete collared energy ≥ (s_c(log M−c_c) − K)Σb², K=|Ω(0)|U+288‖ψ'‖‖ρ'‖+2C_c ⇒ ∃M₀ positive definite on every dyadic block ≥M₀ (any number of atoms). Noncompact source (collared, not truncated).
## CollaredCriticalPrimeChannelUniformBound
- Uncollared critical source g_b has endpoint jump at x=0 ⇒ dilation weight v^{−2}1_{v>1} has cosine transform decaying only 1/f (Hilbert tail) ⇒ known bound on dyadic block is quadratic in Σ|b_n| (not ℓ²).
- Collar g_c=σ(e^{−x}−1)g_b removes endpoint on (−log2,0]. For r≥2 correlation = r^{−1/2}∫ψ B(v)B(rv), ψ=σ(v−1)/v² vanishes to 2nd order at v=1 ⇒ two IBPs: |F_ψ(f)| ≤ ‖ψ''‖₁/(4π²f²) (`abs_integral_Ioi_mul_cos_le_of_flat`).
- ⇒ |P_c| ≤ C_c Σb² on every dyadic block (ℓ²-uniform, any # atoms). C_c=(4/π⁴)K(‖ψ‖₁,‖ψ''‖₁/4π²)ΣΛ(r)/r^{3/2}.
- Clock substitution: ∫_{x≤0} e^x H(e^{−x}) = ∫_{v>1} H(v)/v².
## CommonShiftForTheSuzukiDeficit (part 1)
- Suzuki pairing (RHTower/Suzuki): first-variation (autocorr f 0 − SuzukiPairing(f,ω))/ω → Re W_Λ(f⋆f̃) as ω→0⁺.
- Universal envelope suzukiFirstVariationEnvelope A E₀ B ω: source-independent, →0 as ω→0⁺, homogeneous degree 1 in (E₀,B), monotone. Bounds |secant − Re W| for compact C² f with corr cutoff A, ac(0)≤E₀, ac(0)−ac(t)≤Bt. Ingredients: primary Beta density vs tangent 2e^{−5t/2}/(1−e^{−2t}) ≤ Lévy weight; Lévy energy ≤ B·∫tω; constant log π − Re ψ(5/4); shifted coefficients/ω → 2Λ(n).
- Common shift: family f_i with weights w_i, shared (A,E₀,B) and margin γ w_i ≤ Re W(f_i) ⇒ single ω₀ with ω(γ/2)w_i < ac(0) − Suzuki(f_i,ω) for all i.
- criticalTruncatedSource = Σ b_n·(single-mode source); amplitude ≤ 2|S|·‖b‖₂, Lipschitz ≤ (ΣL_n)‖b‖₂ (constants depend on S via |S|, monotone in S).
- Smoothing: |W(smooth_k g) − W(g)| ≤ C_sm(V,S)/(k+1)·Σb² (compactFullWeilEnergy_smoothing_error); mollifiers contract increments (autocorr_smooth_sub_le).
- Common shift dyadic: ∃M₀ ∀M≥M₀ ∀V≥V₀ ∃(k₀,ω₀) uniform over blocks S at M, patterns b, k≥k₀: ω·W(g)/4 < ac(0) − Suzuki(f_{b,k},ω). Ambient set Icc 0 (2M) used for monotone envelopes. Also bounded horizon M∈[M₀,M_max] and lacunary windows with widths L_i ≤ M₀^δ (δ = s/(4(W_p+1))).
- NB: ω₀ depends on V (envelope via A_V ~ 2 log V) and on M (ambient S); not uniform as M→∞.
- Untruncated: |∫g_b g_b(·−log r)| ≤ C(S,b)/r^{3/2} (bounded phase primitive gains one power).
- Small aperture receivers without subsidy: every C² F supported in [−3/10,3/10] has W ≥ (1/5000)∫F² ⇒ common Suzuki deficit margin (1/10000)ac(0); odd F on [−181/500,181/500] (past (log2)/2) has W ≥ (1/1000)∫F².
- Equivalence: small-shift Suzuki deficit slope ≥ μ−δ ∀δ ⇔ μ ≤ Re W(F,F) (zetaZeroConfig); then reflection defect + μ ≤ square mass.
- Graded receiver: odd-test Suzuki deficit floor −(C e^{2σr}ac(0)+δ)ω ⇒ zetaZeroWidth ≤ σ (via zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor, SRT). RH ⇔ no small-shift Suzuki overshoot on all C²_c tests ⇔ odd subexponential-rate floor for every σ>0. (Restatement, no progress.)
## CompactCriticalPolynomialWindowAndTemperednessBridge
- Scale window ScaleWindow S M L (n+1∈[M,LM]). Truncated correlation vs criticalTruncatedWeight(λ) decays like min(1,√(L/r)) uniformly in λ (=r/V): split L≤r (far harmonic bound 16 B L/(lr)) vs L>r (uniform).
- Prime atom ≤ (Λ(r)/r)(4/π⁴)K_TW min(1,√(L/r))Σb²; with ε=1/(2+log L): min ≤ (L/r)^ε, L^ε ≤ e, ΣΛ(r)/r^{1+ε} ≤ 6(1+ε)/ε = 6(3+log L) ⇒ |P| ≤ C_TW(3+log L)Σb² uniformly in V.
- Temperedness gate: ζ(s−a)ζ(s+a) weights Λ(r)(r^a+r^{−a}) ≥ Λ(r)r^{|a|} ⇒ ΣΛ_a(r)/r^{1+ε} diverges for ε≤|a| (reduces to divergence of ΣΛ(r)/r). Window ratio with log L ≥ 1/|a|−2 separates ζ from countermodel.
- Polynomial window positivity: ∃δ=s/(4(W+1)), M₀: ∀M≥M₀, L≤M^δ, V≥V₀ (support [−log 2V,0] arbitrarily long), nonzero b: W(g^V) ≥ (s/4)log M Σb² >0; = fullZeroForm = Re weilFullFunctional. Smooth mollification: reflection defect + (s/8)log M Σb² ≤ square mass (zetaZeroConfig).
## CompactCriticalSourceWeilPositivity
- Dyadic Bernoulli filter P is 9/2-Lipschitz (periodic quadratic 1/2-Lipschitz); phase profile Lipschitz (9/2)(λ_N+N).
- g^V = cutoff·σ·e^{x/2}·B(e^{−x}), Lipschitz via projection onto [−log 2V,0] (4 bounded Lipschitz factors). ⇒ finite jump energy ⇒ compact finite-jump explicit formula (`re_weilFullFunctional_eq_of_compact_finite_jump`).
- Receiver identity: Re W_Λ(g^V) = Lévy + Ω(0)ac(0) + 2R^V E^V − 2P^V (polar ∫2cosh(x/2)ac factors into two half-exponential moments `integral_polar_autocorr_eq_moments`).
- Unconditional: ∃M₀ ∀M≥M₀, V≥V₀, dyadic block, b≠0: Re W_Λ(g^V)>0; supports of unbounded length.
## CompactFullWeilQuantitativeSmoothing
- Identity ac_f(t) − ac_g(t) = ∫(f−g)(x)[f(x+t)+g(x−t)]; increments likewise. ⇒ |ac_f−ac_g| ≤ (M_f+M_g)‖f−g‖₁; Lévy difference ≤ (K_f+K_g)‖f−g‖₁·∫tω; prime+polar pairing ≤ mass(N)(M_f+M_g)‖f−g‖₁.
- compactFullWeilEnergy f := Re weilFullFunctional(Λ)(f,f). |W(f)−W(g)| ≤ ‖f−g‖₁((M_f+M_g)(|Ω(0)|+2mass N)+(K_f+K_g)∫tω). One L¹ accuracy controls all channels.
- Smoothing error: mollifier radius rOut ~ 1/(4(k+1)); |W(smooth_k f) − W(f)| ≤ (R+1)K(M(|Ω(0)|+2 mass N_R)+K∫tω)/(k+1), N_R=⌈e^{2(R+1)+1}⌉.
## CriticalArchimedeanLogCoercivity (uncollared critical source)
- Lévy symbol W(t)=∫_{x>0}(1−cos tx)ω(x) ≥ e^{−1/2}(log|t|−3) for |t|≥1: ω(x) ≥ e^{−1/2}/x on (0,1]; ∫_0^T(1−cos u)/u ≥ log T−3 since |∫_1^T cos u/u| ≤ 3 (one IBP).
- Critical source g_b dominated by 2Σ|b|e^{x/2} on x≤0 ⇒ L¹∩L². Mass floor ∫g² ≥ A Σb² from weighted Riesz lower bound (v^{−4}≤v^{−2}).
- Lévy(g_b) ≥ e^{−1/2}(A/2)(log M −3 − log(1/η))Σb² on scales ≥M (low band ≤ half the mass).
## CriticalBandWeightPoissonWindow
- Kernel weight u^{−2}(1−cos(2πu/12)) = band-limited γ(u)=(π²/72)sinc²(πu/12) (even, spectrum triangle on |ξ|≤π/6). Fourier of sinc²(πu/12) = 12·triangle(12w).
- Poisson: Σ_{z∈ℤ}γ(t+z) = π²/6 for all t (triangle spectrum vanishes at nonzero integers). ∫_{u>0}γ = π²/12.
- γ(u) = ∫_0^{π/6}(π/6−ξ)cos(ξu)dξ. Window W_m(t)=Σ_{n<m}(γ(t+n)+γ(t−n−1)); outside mass = π²/6 − W_m.
- Dirichlet telescoping sin(ξ/2)Σ(cos ξ(t+n)+cos ξ(t−n−1)) = cos(ξ(t−½))sin(ξm). Curvature |cos(ξs)/sin(ξ/2) − 2/ξ| ≤ (6/35)ξ.
- Unit-cell mean ∫_0^1 W_m = 2∫_0^m γ. Harmonic defect J_m = m(π²/12 − ∫_0^m γ).
- Deviation |W_m(t) − 2∫_0^mγ| ≤ (π/6)³/35 (uniform in m) and ≤ m(π/6)⁴/70.
## CriticalCompleteFormGrowingPatterns
- Uncollared critical source: non-arch channels controlled by B₁=Σ|b_n|: mass ≤ 4B₁², polar ≤ 144B₁², prime atom ≤ K Λ(r)/r², K ≤ 384B₁² on dyadic blocks. Channel constant 4|Ω(0)|+288+768ΣΛ/r².
- E_crit ≥ s(log M−c₀)Σb² − C B₁²; B₁² ≤ |S|Σb² ⇒ positive when C|S| < s(log M−c₀): #atoms may grow only logarithmically (endpoint jump ⇒ ℓ¹ not ℓ² control).
- Translated patterns with ≤ s(log(n+1)−c₀)/C atoms positive (effective threshold).
## CriticalCompleteFormHighScalePositivity (uncollared, ℓ²)
- With ℓ²-uniform uncollared prime bound (CriticalPrimeChannelUniformBound): ac(0) ≤ UΣb², |RE| ≤ 576Σb², |P| ≤ C_PΣb² ⇒ E_crit ≥ (s(log M−c₀)−K)Σb²; ∃M₀ positive definite on dyadic blocks ≥M₀, any # atoms; translated patterns of ANY size beyond N₀.
## CriticalCompleteFormPolynomialWindows
- Window [M,LM]: |P| ≤ C_W(3+log L)Σb² ⇒ positive on [M,M^{1+δ}], δ=s/(4(C_W+1)). Arch gain log M vs prime cost log L.
## CriticalPrimeChannelBeyondLinearWindows (part 1)
- Linear window [N,(1+δ)N] (δ small): criticalPrimeEnergy strictly negative definite (−2P is a subsidy).
- Commensurable ratio limit: scales aN, cN, dilation r: cross-correlation → (4/π⁴)Σ_{ak=crl} w_k w_l (J_k+J_{rl}−J_{|k−rl|})/2 (slow-phase polarization). J_m = 1 − ∫_{v>1}v^{−2}cos(2πmv/12).
- Dyadic pair {M−1,2M−1} unit coeffs: r=2 cross term first harmonic +(log2/π⁴)J_2 cancels unique negative harmonic −(log2/π⁴)J_2 ⇒ limit ≥ (1/8)log2/π⁴ > 0. Negativity fails on dyadic blocks, windows L≥2, wide linear δ≥1, polynomial windows, all scales.
- Uncollared cross-block decay (spaced Hilbert Schur, weight transform O(1/|f|)): O(M^{−1/64}M'^{−1/64}‖b‖‖b'‖) for M⁸ ≤ M'; tail ΣΛ(r)/r² over r≥X ≲ X^{−15/8}-type via MVT.
- Lacunary (M_{i+1}≥M_i⁸): Σ M_i^{−1/32} ≤ 5M_0^{−1/32}. Narrow-window lacunary union: P ≤ −(1/(7000π⁴))Σb² for arbitrarily many blocks. Dyadic-block lacunary: P ℓ²-bounded uniformly in J ⇒ uncollared complete energy positive definite for M_0 ≥ M_pos, all J.
- Dyadic pair proof details: limit = Σ_r Λ(r)/r·(2·singleLimit(r) + cross21(r) + cross12(r)); dominated convergence with majorant 1536Λ(r)/r². Cross terms: 1:2 vanishes for even r (4|k ⇒ w_k=0, χ=0 on 4ℕ); 2:1 vanishes for 8|r; |cross| ≤ (11/(5r²))/π⁴ for odd r; r=2 cross ≥ (2/π⁴)J_2; r=4 bounded (11/10)/π⁴. J_3 ≥ 13/10, J_5 ≥ 6/5 (Taylor lower bound). Even r≥6 prime powers 2^k have k≥3 ⇒ both crosses vanish. Tail r≥7 telescoping bound.
- Final dyadic-pair bound: 2·singleLimit ≥ −(log2/π⁴)J_2 + (88/189·13/10 + 128/875·6/5)(log2/π⁴) (keep m=2,3,5; drop m≥6 ≥0, charges A(3)=3log3, A(5)=5log5, A(4)=0). Cross ≥ +(log2/π⁴)J_2 − (11/40+88/675+77/1875+tail)(log2/π⁴). J_2 cancels exactly; margin ≥1/8. Eventually criticalPrimeEnergy(pair) ≥ (1/16)log2/π⁴.
- Prime energy bilinear expansion over disjoint supports: P(S∪S') = P(S)+P(S')+symmetric cross coupling; multi-block expansion over pairwise-disjoint families.
- Uncollared window weight cosine transform: |F| ≤ 1 and ≤ (1+D)/|f| (first-order decay only).
- Tools (BeyondLinearWindows end): first-order spaced sum Σ|F(x₀−y_m)| ≤ A + (4B/s)(1+log N) for |F|≤B/|f|; tail ΣΛ(r)/r² over r≥X ≤ 20X^{−7/8} (log r ≤ 8r^{1/8}); 1+log t ≤ 4t^{1/4} ≤ 16 t^{1/16}.
## CriticalPrimeChannelCrossBlockDecay (part 1)
- Cross coupling of patterns b at M, c at M': |Σ_r(Λ(r)/r)∫φ_r B_b(v)B_c(rv)| ≤ K(A,B) τ(m,n)‖b‖‖c‖, τ=(1+log n)√(1/n + m√(m/n)), m=min, n=max. Steps: harmonic reduction (bilinear kernel dyadicCrossKernel at frequencies k, lr), Cauchy–Schwarz over dilations keeping cancellation between dilations (Schur rows/cols), dilation sums: resonant range y/2<rD<2y has Λ(r)/r ≤ (2D/y)log(2y/D) ≤ 6√(D/y); far ranges see 1/f² tail; harmonic summation √(k√k)√l(1+log 7k) against 1/(k²l²).
- Elementary: Λ(r)/r ≤ 1; Σ_{r≥X}1/r² ≤ 2/X; Σ_{r≤X}Λ(r)/r ≤ (1+log X)² (crude Mertens); spaced family sum ≤ A+(4B/s²)(π²/3).
- dilationSum_le: Σ_r Λ(r)/r(|F(y−rD)|+|F(y+rD)|) ≤ 9B/(yD)+6√(D/y)(A+14B/D²) and ≤ 5B/D² + [D<y](...): three ranges (rD≥2y tail; rD≤y/2 count ≤ y/(2D) at 4B/y²; resonant spaced sum). Schur Cauchy–Schwarz for nonnegative kernel: Σ|x||y|G ≤ √(ρΣx²)√(κΣy²). Rows ≤ 2(M'+1)β, columns ≤ 12(A+16B)(1+log(1+6kM/M'))². Downward order bound 39(A+16B)·harmonicFactor·τ(M',M)·‖b‖‖c‖.
- Cross-block law final: |Σ_r(Λ/r)∫φ_r B_b B_c(r·)| ≤ (4/π⁴)·39(A+16B)·Z·τ(min,max)‖b‖‖c‖, harmonic series √(k√k)(1+log7k)/k² ≤ 15k^{−9/8} summable, dual √l/l². Upward order: dilations overshoot unless k > lM'/(3M); paid by (3kM/(lM'))^{3/2}.
## CriticalPrimeChannelScaleWindows (part 1)
- ScaleWindow S M L := n+1∈[M,LM]. Uniform regime: rows/cols of cross kernel are spaced sums (branch spacing 11/12) ⇒ |ΣbbK_F(p,q)| ≤ 4(A+4B(12/11)²π²/3)Σb² for any support (Schur); jump kernel via Montgomery–Vaughan: ≤ 4(1+13/(π·11/12))Σb².
- Window regime q ≥ 8Lp: arguments ≥ qM/2 ⇒ |ΣbbK_F| ≤ (16LB/q²)Σb² (uses |S|≤LM); jump ≤ (4L/(πq))Σb².
- Window correlation: uncollared weight v^{−2} = collar ψ + endpoint φ_e; both together ≤ (4/π⁴)K_W min(1,√(L/r))Σb²; harmonic trade 1/k² ≤ (1/(k√k))√8·√(L/r) below the far line. ⇒ |P| ≤ C_W(3+log L)Σb² (uncollared, any family on window).
## CriticalPrimeChannelUniformBound
- Uncollared ℓ² bound: v^{−2}=ψ+φ_e, φ_e=(1−σ(v−1))/v² on [1,2] with unit jump at 1. Two IBPs: F_{φ_e} = j + e, jump kernel j(f) = −sin(2πf)/(2πf) = −½∫_{−1}^{1}cos(2πfu), |e| ≤ κ_e/f².
- Jump bilinear form via Montgomery–Vaughan interval inequality on [−1,1]: for D-separated families x,y (no separation between families needed), |Σ b b j(x_n−y_{n'})| ≤ (1+13/(πD))Σb². Branch spacing 11/12 ⇒ near-resonance bound 4(1+13·12/(11π)); off-resonance 16/(π max(p,q)).
- ⇒ |criticalPrimeEnergy| ≤ C_P Σb² on every dyadic block (ℓ²-uniform, uncollared). Endpoint jump's Hilbert 1/f tail is the only ℓ² obstruction; MV removes it.
- Endpoint remainder via two IBPs on [1,2]: e(f) = −(φ_e'(1)cos ω + ∫φ_e''cos(ωv))/ω², ω=2πf (jump φ_e(1)=1 gives exactly j(f), flatness at 2 kills boundary). Endpoint dilation inequality |∫φ_e B B(r·)| ≤ (4/π⁴)K_e r^{−1/2}Σb². C_P = (4/π⁴)(K_c+K_e)ΣΛ(r)/r^{3/2}.
## CriticalSourceMellinLowFrequencyExclusion (start)
- Uncollared critical readout ĝ(t)=∫_1^∞ v^{−3/2}B(v)e^{−it log v}; nonstationary bound |∫_1^∞ v^{−p}e^{i(ωv−t log v)}| ≤ 5/|ω| for p>1, |t|≤|ω|/2 (one IBP against v^{−p}/(ω−t/v)). ⇒ |ĝ(t)| ≤ (15/π³)Σ|b_n|/(n+1) on |t|≤π(n+1).
- Uncollared low band: |ĝ(t)|² ≤ 2D²/M Σb², D=15/π³ (harmonic k contributes 10/π³·k^{−3}·T).
## DenseScaleWindowsAndMultiWindowPositivity (part 1)
- Dilation-ring majorant M_win(L)=Σ_r(Λ(r)/r)min(1,√(L/r)): log L − (log4+4) ≤ M_win ≤ log L + 4log2+9(log4+4); M_win/log L → 1 (Mertens first theorem on r≤L + dyadic blocks with (3/4)^k decay). Removes 6e factor from window prime law (ε-free); Θ(log L) width cost is asymptotically exact for this majorant.
- Spaced-row cross-block: exchanging Σ_{n'} and Σ_r with (11rl/12)-spacing ⇒ row sum scale-free 12(A+16B)(1+log(1+6kM/M'))² ⇒ coupling ≤ 5K(1+log(1+6M/M'))²‖b‖‖c‖ (only depends on ratio; upward order uniformly O(‖b‖‖c‖)). Removes M^{3/4} growth of τ on adjacent blocks.
- Congruence resonance: gap between (k,n),(lr,n') = affine clock diff k(n+1)−lr(n'+1)+(k−lr)/12 + collar defect diff; fixed offset j ⇒ one class mod lr, spacing ≥ lr/gcd(k,lr); dilated defect r e_{n'+1} ∈ [r/(225LM), r/(140M)] ≤ L²/(140M): O(1) only for L ≲ √M (√M collar-drift boundary).
- Lacunary window families (L_iM_i)^8 ≤ M_{i+1}: cross-window couplings ≤ 650K_CB ΣE_i independent of widths, J, V ⇒ positivity on arbitrary-depth lacunary unions of polynomial windows; dense window [M_0,M_0^{1+Δ}] any Δ coupled to higher window.
- "All five form realizations": compactFullWeilEnergy (APT) = fullZeroForm (ACT) = Re weilFullFunctional (RHTower); gridTentPattern (grid tent PL interpolation of G(x)=e^{−3x/2}g^V) and smoothGridTentDetector D (C²_c) with μ/2 ≤ Re W(D,D), zetaZeroConfig reflection defect + μ/2 ≤ square mass. Direct δ = s_T/(4(W_direct+1)), μ = (s_T/8)log M Σb².
- Upward-uniform truncated block coupling ≤ 245K_CB‖b_S‖‖b_S'‖ for M≤M' (log(1+6M/M')≤log7≤6).
- Lacunary window proof: slice each window into dyadic slices; cross-slice couplings ≤ 50K w_k w_k' s s' with w_k=(2^k)^{−1/16} (from (2^k)^8 ≤ 2^{k'} lacunary law); Σ w_k² ≤ 13 (geometric 12/13) ⇒ off-diagonal sum ≤ 650KΣE_i by global Cauchy–Schwarz.
- Lacunary windows complete energy ≥ Σ_i (s(log M_0 − c) − K_0 − 1300K_CB − 2W(log L_i + C_ring))E_i; positivity with margin (s/4)log M_0 when L_i ≤ M_0^δ (all i; note gain is log M_0 only, uses lowest scale).
- Dense two-band [1,LM]: S_low arbitrary in [1,LM] + S_high on window [M,LM] with NO lacunary gap: positive if (s(log M−c)−K−2C(4+log L))E_high − (s(log M−c)ρ + K + 4C(3+log LM)²)E_low ≥ 2μ>0 — i.e. high band must dominate low band by a log² factor; low band itself not certified.
## DoublyCollaredCriticalSourcePositivity (part 1)
- Upper cutoff χ(u)=1−σ(u−1); g^V = χ(e^{−x}/V)·g_c, support [−log 2V,0]. Truncated weight w_λ=ψ·χ(λv), λ=r/V. λσ'(λv−1) vanishes unless λ<2/v ⇒ |λσ'| ≤ 2 sup|σ'|, |λ²σ''| ≤ 4 sup|σ''| on v≥1 ⇒ ‖w_λ''‖₁ uniform in λ ⇒ prime channel ≤ C_TΣb² uniform in V.
- Tail h = (1−χ)g_c mass ≤ (U/V)Σb²; Riesz window [2,2+L] inside truncation ⇒ Lévy(g^V) ≥ s_T(log M − c_T)Σb² for V≥V₀.
- Doubly collared (dyadic version): K_T = |Ω(0)|U + 288 a_R a_E + 2C_T independent of V; ∃M₀ positive on all dyadic blocks ≥M₀ for all V ≥ V₀ = max(2+L, 8U/A_c).
## DyadicBernoulliFilterAndBohrCoercivity
- Bohr mean |(1/L)∫_0^L e^{iωv}| ≤ 2/(|ω|L). kλ_N ≠ mM (irrational shifted freq) ⇒ cross terms vanish in Bohr mean.
- Bohr coercivity const ((2/π²)(1−3/4))²·½ = 1/(8π⁴) (first harmonic beats tail ≤3/4). ⇒ linear independence of factorial correction tails (conditional reduction: needs hcoercive hypothesis as input; the lemma is a trivial "coercive ⇒ zero" reduction).
## DyadicDilationCorrelationInequality (start)
- Dyadic dilation inequality: |∫_{v>1}φB(v)B(rv)| ≤ (4/π⁴)K(A,B)r^{−1/2}Σb² on dyadic blocks (|F_φ|≤A, ≤B/f²). Branches θ∈{λ_{n+1}, n+1} are 11/12-spaced; Schur: A + O(B/(lr)²) near resonance k≈lr, O(B/(lr)²) away; resonance paid by 1/k² weights ⇒ r^{−1/2}.
- Spaced summation lemma: Σ|F(x−y_m)| ≤ A + (4B/s²)(π²/3); DyadicScaleBlock card ≤ M+1; scaleBranch ∈ [n+1, n+1+1/12].
- Dilation inequality details: resonance bound ν(p,q)=A+80B/q²·π²/3 if q/4<p<4q else 32B/q²; Schur test (rows/cols ≤R ⇒ |ΣbbK| ≤ RΣb²); resonance trade 1/k² ≤ (2/(k√k))(1/√r) near resonance; K(A,B)=4(A+(80π²/3+2)B)Z_{3/2}Z_2+68B Z_2². Uniform in M, # and positions of scales.
## EnvelopeCriticalPrimeTransitionAndDilationGain
- Envelope source f_β(x)=e^{βx}B(e^{−x})1_{x≤0}; prime translation log r rescales by r^{−β}; majorant Λ(r)/r^{β+1/2}. Exact: Σ log r/r^{β+1/2} < ∞ ⇔ β>1/2 (comparison with harmonic series at β≤1/2). Canonical β=3/2: ΣΛ(r)/r².
- Physical L² weight v^{−(2β+1)}, ∫_1^∞ = 1/(2β). Polar s=0 weight j^{−(β+1)} summable ⇔ β>0; s=1 polar j^{−β} summable ⇔ β>1. Three regimes: β>1/2 prime majorant ok; β∈(1/2,1] polar s=1 diverges (needs rank-1 pole cancellation); β∈(1,2] both converge.
- Oscillatory dilation gain: |∫_a^b e^{iω(1−r)v}| ≤ 2/(|ω|(r−1)); weighted on (1,∞) same bound; ⇒ Λ(r)/(r^{β+1/2}(r−1)) summable for all β>−1/2 incl. critical β=1/2 where absolute (Cauchy–Schwarz) majorant diverges. (Critical line = failure of absolute bound, not of the prime channel.) Polar bound |2Re(P₀ conj P₁)| ≤ 6JS.
## ExplicitBlockThresholdsOfTheCriticalFamily (start)
- logLinearThreshold s c C = max 2 (⌊exp(c+C/s)⌋+1): beyond it s(log M−c)−C>0. Named thresholds for all positivity laws (critical dyadic, collared, truncated, lacunary, polynomial windows δ=s/(4(W+1)), threshold max 2(⌊exp(2K/s)⌋+1), K=sc+K₀+6W). Effective but constants not numerically evaluated.
## ExplicitCollarThresholdsAndKernelShape (part 1)
- Smooth transition σ (Mathlib smoothTransition from expNegInvGlue): 0 ≤ σ' ≤ 4, |σ''| ≤ 95 (via denominator ≥ e^{−2}, (u^k e^{−u}) max at u=k).
- Mass conservation: ∫|ψ| + ∫|φ_e| = ∫_1^∞v^{−2} = 1; criticalCollarMass + criticalEndpointMass = 2; 1/2 ≤ ‖ψ‖₁ ≤ 1; 1 ≤ endpointMass ≤ 3/2. |ψ'| ≤ 4, |vψ'| ≤ 4, |ψ''| ≤ 113 on v≥1.
- Explicit numerics: ∫|ψ'| ≤ 17/4, ∫|ρ'| ≤ 9/2, ∫|ψ''| ≤ 453/4, collar curvature ≤ 4, φ_e'(1) = −2, |φ_e''| ≤ 119, endpoint curvature ≤ 4. ΣΛ(r)/r^{3/2} ≤ 18, ΣΛ/r² ≤ 12 (from RHTower ΣΛ/r^s ≤ 6s/(s−1)). Σ1/(k√k) ≤ 3, Σ1/k² ≤ 2. K(A,B) ≤ 24A+8000B; collar K ≤ 33000, endpoint ≤ 34000. C_collar ≤ 30000, C_P (uncollared prime) ≤ 61000, |Ω(0)| ≤ 7, U ≤ 40, K_window_base ≤ 1500, complete channel ≤ 125000, collared channel ≤ 66000, window prime slope ≤ 30000. (Archimedean slope s is tiny ⇒ thresholds astronomically large: exp(C/s).)
- Archimedean slopes explicitly tiny: s (uncollared critical) ≥ 10^{−15}; collared ≥ 10^{−8}; window exponent δ ∈ [10^{−21}, 1]. ⇒ thresholds M₀ ~ exp(C/s) ≈ exp(10^{20}): positivity is asymptotic-only in practice.
- Band sine moments μ_m = ∫_0^{π/6}(π/6−ξ)ξ sin(mξ) = (2(1−cos(mπ/6)) − (mπ/6)sin(mπ/6))/m³; μ_m ≥0 for m≤12; |μ_m| ≤ (4+πm/6)/m³. Spectral curvature I₀ = Σ (A(m)/m³)μ_m; Σ|A|/m³·|μ|-moments ≤ 19/1000. Terms: m=2 ∈[−202,−201]·10^{−5}, m=3 ∈[193,195]·10^{−5}, m=5 ∈[124,126]·10^{−5}, m=7 ∈[64,66]·10^{−5}.
- I₀ ∈ [11, 52]·10^{−4}. Spectral perturbation master thm: weight g ≈ C₀(π/6−ξ)ξ sin(mξ) within ε₀(...)|sin| ⇒ charge series ≈ C₀I₀ within ε₀·M_abs.
- Couplings κ(k) (k≥1): |κ(k) − I₀/(4π²k²)| ≤ 14·10^{−5}/(4π²k⁴); κ(k) ∈ [96, 534]·10^{−5}/(4π²k²) >0. κ(1) ∈ [1/50000, 1/6000], κ(2) ∈ [1/200000, 1/24000].
- Kernel shape: R(t₁)−R(t₂) ∈ [7/20000, 56/20000]·((½−t₁)²−(½−t₂)²) on 0≤t₁≤t₂≤½; R strictly decreasing on [0,½], increasing on [½,1]; max R(0)=R(1), unique min R(½). Rayleigh range [(4/π⁴)R(½), (4/π⁴)R(0)].
- R(0)−R(½) ∈ [7,56]/80000; R(0)−κ(0) ∈ [7,56]/120000; κ(0)−R(½) ∈ [7,56]/240000.
## FactorialAffineClockResonance
- Affine defect e_N = N + 1/12 − λ_N; N e_N = δ² + δ³/(3N) (δ = collar shift ∈[1/15,1/12]) ∈ [1/225, 1/140].
- Gap identity λ_N − rλ_M = ((12N+1) − r(12M+1))/12 + r e_M − e_N. Resonant (12N+1 = r(12M+1)): gap ∈ [r/(400M), r/(140M)] >0. Nonresonant (r≤M): |gap| ≥ 1/15. Small gap < 1/15 ⇔ affine relation (for harmonics a≤N, b≤M: |aλ_N − bλ_M| < 1/15 ⇔ a(12N+1) = b(12M+1)).
- Exact collisions aλ_N = bλ_M with affine relation force N=M, a=b (cubic polynomial factor (N−M)·positive).
- Thirteen family: gap(13(m+1)+1, m+1) ∈ [13/(400(m+1)), 13/(140(m+1))] → 0 but >0; physical correlation ∫v^{−2}cos(2π·gap·v) → 1 (full mass) while each Bohr mean = 0. ⇒ uniform cross-scale oscillatory gain is FALSE.
- Dyadic stencil kills mixed integer aliases: k(12N+1) − 12J ≠ 0 when χ(k)≠0 (needs 4|k else) ⇒ |kλ_{n+1} − J| ≥ 1/15 for surviving harmonics k ≤ source scale.
## FactorialAffineCollarSharpConstant (start)
- N∫v^{−2}|Φ_N − Ψ_N|² → (4/π²)(1/144)Σχ(k)²/k³ = 7ζ(3)/(256π²) (Ψ = affine-clock profile at N+1/12; cosine-shell Gram ∫v^{−2}L_kL_l = (π/2)|I_k∩I_l|).
- Dyadic filter P is 9/2-Lipschitz. |Φ_N − Ψ_N|(v) ≤ (9/2)e_N v. N e_N → 1/144 (δ_N → 1/12).
- Cosine-shell Gram law: shells (cos(av)−cos(bv))/v for disjoint intervals [a_i,b_i] are orthogonal in ∫dv; energy π(b−a). Collar layer intervals [2πkλ_N, 2πk(N+1/12)] separated for k ≤ N+1 ⇒ head energy ∫_{v>0}v^{−2}A_K² = π² e_N Σ_{k<K} k w_k² EXACTLY.
- Head pointwise ≤ 2π e_N(1+log N)v; tail beyond K uniformly ≤ 4/K. Limit N∫_{v>1}v^{−2}|Φ_N−Ψ_N|² → (Σk w_k²)/(36π²).
- Σ_k χ(k)²/k³ = (63/64)ζ(3) (only multiples of 4 removed). Sharp affine collar constant: N∫_{v>1}v^{−2}|Φ_N−Ψ_N|² → 7ζ(3)/(256π²). Affine model error is O(1/N) per scale in critical weight.
## FactorialAffineFrequencyIntervals
- For fixed harmonic k, native frequency intervals [2πkλ_{n+1}, 2πk(n+1+1/12)] disjoint across source scales n ⇒ exact diagonal: ∫_ℝ|Σ_n b_n L_{n,k}|²/v² = 2π²k Σ_n e_{n+1}|b_n|². Critical half-line v>1 ≤ half that.
## FactorialCollarIrrationalityAndSpacing
- λ_N = N(1+ε_N), (1+ε_N)³ = (4N+1)/(4N), 4λ_N³ = N²(4N+1). (1+ε_N) and λ_N irrational (b³=4N, a³=b³+1 impossible). kλ_N ≠ any integer frequency.
- Shifted resonance kλ_N = ℓλ_M ⇔ k³N²(4N+1) = ℓ³M²(4M+1) (cubic Diophantine).
- Collar shift δ_N = λ_N − N ∈ [1/15, 1/12]. Dilation separation mλ_N − λ_{mN} ≥ 1/20 (m≥2).
- Four signed branches {±kN, ±kλ_N} pairwise separated by ≥ k/15.
## FactorialCorrectedSampling
- Literal corrected (Müntz-smoothed) source: absolute zero-square mass Σ_ρ m_ρ|ĝ(γ_ρ)|² ≤ C/(n+1), C = 1 + (e²/2)Σ_ρ m_ρ/(1+|γ_ρ|²): single reciprocal mode, boundary coeff² = 1/(4(n+1)); uniform in smoothing k. (Corrected source one log cheaper than tail.)
## FactorialCriticalAffineComparison
- Whole-span affine model: ∫_{v>1}v^{−2}|Φ_S(b) − Ψ_S(b)|² ≤ C_aff Σ_n e_{n+1}|b_n|² ≤ (C_aff/140)Σ|b_n|²/(n+1); C_aff = (4/π²)(Σ|w_{k}|√k)². Tail families n≥m: error ≤ C_aff/(140(m+1))·Σ|b|². Affine model ψ(N+1/12) − ψ(N) keeps both integer and shifted branches.
## FactorialCriticalCompleteFormDivergence
- Upper polar readout ∫_{v>1}v^{−2}F ≤ 24Σ|b_n|/(n+1) via IBP against bounded lattice primitive (|G| ≤ 12Σ|b|/(n+1)).
- Complete energy (Gamma–Lévy form) of translated patterns → +∞: polar O(1/n) → 0; ac(0) → diagonal dilation limit >0; prime channel → P∞ (uniformly negative definite); rational dilation law ⇒ ac(x) → 0 for irrational e^x ⇒ a.e.; Fatou + ω(x) ≥ e^{−1/2}/x ⇒ Lévy energy → ∞.
- Mass floor: diagonal dilation limit D(S,b,1) ≥ Σb_j²/(12π⁴) (first harmonic). ae shift has irrational e^x (countable exception). ω(x)=e^{x/2}/sinh x ≥ e^{−1/2}/x on (0,1] ⇒ ∫c·ω = ∞.
- Polar channel |ĝ(−i/2)ĝ(i/2)| ≤ (24Σ|b|)²/(n+1). Prime limit: −2P∞ ≥ (8/(7000π⁴))Σb². Complete energy (EReal) = Lévy + Γ'-const·ac(0) + 2·polar − 2·prime → +∞ for every nonzero translated pattern.
## FactorialCriticalCompleteFormUniformCoercivity
- ac = quadratic form of symmetric correlation matrix of single-scale sources; entrywise limit e^{−t/2}·polarized dilation limit at e^t; vanishes for irrational e^t.
- Jump floor: ac(0)−ac(x) ≥ (1/(12π⁴) − d_n(x))Σb² with decorrelation defect d_n(x) → 0 a.e. ⇒ common Lévy floor → ∞ (Fatou) uniformly in b.
- THEOREM: for each finite S and each M, eventually (in translation n) complete energy ≥ MΣb² for all b. Eventually positive definite on every finite translated support. Thresholds non-effective (Fatou).
## FactorialCriticalCorrelationLimit (start)
- Cosine decay separates fast arithmetic slopes from slow collar detuning; absolute harmonic summability retains exact dilation resonances.
- Critical weight cosine integral C(a)=∫_{v>1}v^{−2}cos(2πav): C(0)=1, |C|≤1, C(a)→0 (Riemann–Lebesgue). Product of cosines at frequencies aN+s_n, bN+t_n → (a=b)·C(u−v)/2 else 0: fast slopes separate, slow detuning retained.
- Translated shifted freq λ_{n+j+1} − (n+1) → j + 1/12.
- Single-scale profile correlation at integer dilation r: ∫_{v>1}v^{−2}Φ_{n+1}(v)Φ_{n+1}(rv) → (4/π⁴)Σ_l w_{rl}w_l D(rl), with harmonic slow-phase defect D(k) = ∫_{v>1}v^{−2}(1−cos(2πkv/12)) ∈ (0,2], D(k)>0 for k>0. Only exact harmonic coincidences k = r·l survive.
## FactorialCriticalHarmonicFiniteBounds
- D(7),D(13),D(14),D(15),D(17),D(18) ≤ 7/6; D(9),D(10),D(11) ≤ 1 (phase θ=πk/6 IBP bound Dθ² ≤ θ² + θ sinθ + 2(1−cosθ)).
## FactorialCriticalHarmonicOscillationBounds
- |D(m) − 1| ≤ 12/(πm) (two IBPs); D(m) ≤ 1 + sinθ/θ + 2(1−cosθ)/θ² (θ = πm/6); D(m) ≤ 7/6 for m≥19, ≤ 6/5 for m≥20.
## FactorialCriticalHarmonicTaylorBounds
- Kernel weight W(u) = u^{−2}(1−cos(πu/6)), ∫_0^∞ W = π²/12. D(m) = m(π²/12 − ∫_0^m W) (exact head formula). Taylor bounds both sides. D(2) ≥ 10/9 (the unique negative arithmetic harmonic, χ(2)=−1, retains definite mass); D(3), D(5) ≤ 4/3; D(6) ≤ 7/6.
## FactorialCriticalPatternHarmonicMass
- Pattern density ρ_S,b(t) = |Σ b_j e^{2πijt}|² ≥ 0; unit cell ∫_a^{a+1}ρ(mt) = Σb² (m≥1). Twelve-collar identity ∫_{12}^{24}(1−cos(2πmt/12))ρ(mt) = 12Σb².
- Physical harmonic mass J_m(S,b) = ∫_{v>1}v^{−2}(1−cos(2πmv/12))ρ(mv) ∈ [Σb²/48, 4Σb²] for all m≥1, independent of #S and positions. ⇒ J_m = 0 iff b=0.
## FactorialCriticalPhasePrimitive / PolarCutoff
- Phase combination Σb_nΦ_{n+1}(v) has bounded primitive G, |G| ≤ 12Σ|b_n|/(n+1) (lattice primitive /N). Polar endpoint (conditionally convergent ∫_1^T F/v) = −G(1) + ∫_{v>1}G/v², cutoff error ≤ (24/T)Σ|b|/(n+1); |endpoint| ≤ 24Σ|b|/(n+1).
## FactorialCriticalPrimeAdmission
- IBP lemma: F with bounded primitive Q (≤P), |F|≤A, right-derivative |D|≤L ⇒ |∫_{v>1}v^{−2}F(v)F(rv)| ≤ P(4A+L)/r. Phase right-slope ≤ 14N; filter slope ≤ 9/2.
- Fixed finite source: physical correlation at dilation k+1 ≤ C(S,b)/(k+1), C = 12Σ|b|/(n+1)·(8Σ|b| + 14Σ(n+1)|b|): one extra dilation power ⇒ prime atom series absolutely convergent. Constant grows with scale moments (non-uniform in S).
- Critical source = Σ (b_n/amp_n) e^{−x}·corrected Müntz tail_n(x) (literal corrected tails reweighted).
- Log/physical bridge: ∫g(x)g(x−log r)dx = r^{−1/2}∫_{v>1}v^{−2}F(v)F(rv) (critical source g = 1_{x≤0}e^{x/2}F(e^{−x})). Von Mangoldt prime channel Σ Λ(r)/√r·ac(log r) absolutely summable for every fixed finite source (majorant Λ(r)/r²).
## FactorialCriticalPrimeContinuousKernel
- Kernel density on (0,∞): K(u) = Cum(⌊u⌋)·W(u), W(u) = u^{−2}(1−cos(2πu/12)). Periodized cell kernel K_cell(t) = Σ_{k≥1} Cum(k)W(k+t) continuous on [0,1]; R(t) = (K_cell(t)+K_cell(1−t))/2 continuous, R(0)=R(1). Prime limit P∞(S,b) = (4/π⁴)∫_0^1 R(t)ρ_{S,b}(t)dt.
## FactorialCriticalPrimeCumulativeCharge
- Charge A(m) = χ(m)Σ_{r|m} rΛ(r)χ(m/r); odd prime p: A(p) = p log p. |A(m)| ≤ m log m. Cum(N) = Σ_{m≤N}A(m)/m³: Cum(0)=Cum(1)=0, Cum(2)=−log2/4, Cum(3)=Cum(4)=−log2/4+log3/9 <0, Cum(N) > log2/150 for N≥5; only A(2) negative (A(m) ≥ 0 for m≠2) ⇒ Cum monotone from 2; Cum(∞) > log2/150.
- Note: positivity of cumulative charge does NOT determine sign of complete prime form.
## FactorialCriticalPrimeFiniteScaleNegativity (start)
- Translated prime energy = quadratic form of finite-scale prime matrix M_n(i,j) = ΣΛ(r)/√r·sym cross-corr; M_n → Toeplitz (4/π⁴)κ(|i−j|) entrywise; limit negative definite with constant 4/(7000π⁴) ⇒ actual prime energy negative definite with half constant beyond support-dependent threshold, uniform in b.
- Single-scale critical source |g_q(x)| ≤ 2e^{x/2} on x≤0.
- Translated prime matrix M_n(i,j) → (4/π⁴)κ(|i−j|) (Toeplitz) by polarization of singleton/pair limits. Eventually (support-dependent n₀) prime energy ≤ −(2/(7000π⁴))Σb² for all b. Threshold non-effective.
## FactorialCriticalPrimeHarmonicDiagonal
- Single-scale prime limit P∞ = (4/π⁴)Σ_m A(m)D(m)/m⁴ (regroup Σ_r Λ(r)/r·corrLimit(r) by m = r·l; absolutely convergent).
- χ(m)χ(m/r) = χ(r) when 4∤m ⇒ A(m) = Σ_{r|m} rΛ(r)χ(r) (signed divisor sum). Signed charge rΛ(r)χ(r) ≥ 0 except r=2: −2log2.
- SIGN CLASSIFICATION: A(m)<0 ⇔ m=2 (A(2) = −2log2); A(m)=0 ⇔ m=1 or 4|m; A(m)>0 ⇔ m>2, 4∤m (odd prime p|m gives p log p > 2log2).
## FactorialCriticalPrimeHarmonicTruncationAndThreeCellKernel (start)
- Translated limit P∞(S,b) = (4/π⁴)Σ_m A(m)J_m(S,b)/m⁴. Every term m≠2 ≥ 0 ⇒ any finite partial sum containing 2 is a lower bound. {2,3,5} criterion: P∞ ≥ (4/π⁴)(log3/27·J₃ + log5/125·J₅ − log2/8·J₂).
- Physical kernel density: = 0 on (−∞,2); ≥ (log2/150)W(u) on [5,∞); ≥ −(log2/4)W(u) globally. Negative support confined to [2,5).
- Cum(N) ≥ −log2/4 (min at N=2).
## FactorialCriticalPrimeKernelDensity
- J_m(S,b) = m∫_{u>m}W(u)ρ(u)du (common tail; dilation by m). Cum(⌊u⌋) = Σ_{m≤u}A(m)/m³. Physical kernel K(u) = W(u)Cum(⌊u⌋) ∈ L¹(ℝ).
- P∞(S,b) = (4/π⁴)∫_ℝ K ρ_{S,b} = (4/π⁴)∫_0^1 K_per ρ = (4/π⁴)∫_0^1 R ρ (periodize: ρ 1-periodic; symmetrize: ρ(1−t)=ρ(t) for real b).
- No sign asserted by kernel identities.
## FactorialCriticalPrimeKernelMass
- W(u) = (π²/72)sinc²(u/12) (band-limited, Fourier support |ξ| ≤ 1/12·...); ∫sinc²(u/12) = 12; kills nonzero integer frequencies ⇒ ∫_ℝ sinc²(u/12)ρ = 12Σb². ∫_0^∞ W ρ = (π²/12)Σb² (half-line by symmetry). Singleton J_m({j},b) = b_j²D(m).
## FactorialCriticalPrimeKernelNegativeDefinite (KEY)
- Summation by parts: K_cell(t) = Σ_m (A(m)/m³)T_m(t), harmonic tail T_m(t) = Σ_j W(j+m+t). Poisson: T_m(t)+T_m(1−t) = π²/6 − W_m(t) (band window). Reflected pair mean = D(m)/m − dev_m(t)/2.
- EXACT: R(t) = Σ_m A(m)D(m)/m⁴ − ½Σ_m (A(m)/m³)dev_m(t). First sum = singleton prime limit ≤ −log2/390. Correction ≤ ½[(log2/4)(π/6)⁴/35 + (log3/9)·3(π/6)⁴/70 + (π/6)³/35·(2log2+1)/4] (quartic window bounds at m=2,3; |A|≤m log m + integral test beyond).
- THEOREM: R(t) ≤ −1/7000 on [0,1] ⇒ P∞(S,b) ≤ −(4/(7000π⁴))Σb² for every finite real pattern (Parseval ∫_0^1ρ = Σb²). Since Weil form SUBTRACTS prime channel, this is a uniformly positive contribution to the complete form.
## FactorialCriticalPrimeLimit
- Single-scale physical correlation |corr(n,r)| ≤ 264/r uniformly in n. Prime energy (singleton) → P∞ = Σ_r Λ(r)/r·corrLimit(r) by dominated convergence (majorant Λ(r)/r²).
- corrLimit(r) > 0 for r odd; < 0 for r ≡ 2 mod 4; = 0 for 4|r. (χ(rl)χ(l) = χ(l)² for r odd, −1·[l odd] for r≡2(4), 0 for 4|r.)
## FactorialCriticalPrimeScaleCoupling
- Toeplitz: P∞(S,b) = (4/π⁴)Σ_{i,j}b_ib_jκ(|i−j|), κ(k) = k-th cosine coefficient of R. κ(0) = singleton limit ΣA(m)D(m)/m⁴. κ(k) (k≥1) = Σ_m (A(m)/m³)∫_0^{π/6}(π/6−ξ)ξ sin(mξ)/(4π²k²−ξ²)dξ; |κ(k)| ≤ (Σ|A|/m³)(π/6)³/6/(4π²k²−(π/6)²) = O(1/k²).
- Isotropy law: |P∞(S,b) − (4/π⁴)κ(0)Σb²| ≤ (4/π⁴)·budget·Σb², budget = curvature budget of R about its mean.
## FactorialCriticalPrimeSingletonNegative
- Composite charges: A(6)=3log3−2log2, A(9)=12log3, A(10)=5log5−2log2, A(14)=7log7−2log2, A(15)=3log3+5log5, A(18)=12log3−2log2. A(2)D(2)/16 ≤ −(5/36)log2.
- Finite budget Σ_{m<20}A(m)D(m)/m⁴ ≤ (−61/7220 − 1/390)log2; tail m≥20 via |A|≤m log m, D≤6/5 and ∫_{19}^∞ log x/x³ = (log19+1/2)/722; total singleton limit ≤ −log2/390 < 0.
- Singleton prime limit P∞ ≤ (4/π⁴)(−log2/390) < 0; translated singleton {j}: b_j²·P∞.
## FactorialCriticalPrimeToeplitzSymbolRange
- R symmetric ⇒ sine moments vanish; Fourier coeff of R = κ(|n|); Σ|κ| < ∞; symbol law R(t) = Σ_{n∈ℤ}κ(|n|)cos(2πnt).
- Toeplitz counting identity Σ_{i,j<L}γ(|i−j|) = Σ_{n<L}(L−n)ε_nγ(n). Cosine+sine patterns at frequency t: (P∞(cos)+P∞(sin))/L → (4/π⁴)R(t) (Fejér/Cesàro).
- SHARP SPECTRAL RANGE: Rayleigh quotients of P∞ fill [(4/π⁴)min R, (4/π⁴)max R] (sup/inf exact); max R ≤ −1/7000; optimal negativity constant = −(4/π⁴)max R.
## FactorialCriticalRationalDilationLaw (start)
- Critical correlation at real dilation ρ: harmonic pairs (k,l) survive only if k = ρl ⇒ limit vanishes at irrational ρ; at reduced p/q equals (4/π⁴)Σ_t w_{pt}w_{qt}J_{pt}(b). Limiting autocorrelation supported on log ℚ_{>0}; prime channel samples integer atoms log r.
- Resonance: slow-phase pair (i+1/12, j+1/12) four-term combination = ∫v^{−2}cos(2πa(i−j)v)(1−cos(2πav/12)) — the collar defect is the "1/12" slow phase; summed over pattern gives J_k(S,b).
- Translated dilation correlation at real ρ>0 → D(S,b,ρ) = (4/π⁴)Σ_{k=ρl}w_kw_lJ_k. D(irrational)=0; D(p/q) = (4/π⁴)Σ_t w_{pt}w_{qt}J_{pt}. Autocorrelation of translated critical source at shift x → e^{−x/2}D(S,b,e^x).
## FactorialCriticalTranslatedCorrelationLimit
- Full translated pattern correlations at integer dilation r: dominated convergence over harmonic pairs (|w_k||w_l|·4(Σ|b|)²).
## FactorialCriticalTranslatedHarmonicLimit / TranslatedCorrelationLimit
- Translated harmonic layers (k,l) at integer dilation r: limit = [k=rl]·J_k(S,b) (fixed offset phases i,j survive only on resonance; their quadratic sum = pattern mass). Full correlation → (4/π⁴)Σ_l w_{rl}w_lJ_{rl}(S,b).
## FactorialCriticalTranslatedPrimeHarmonicDiagonal
- P∞(S,b) = (4/π⁴)Σ_m A(m)J_m(S,b)/m⁴ (absolute). |P∞(S,b)| ≤ (16/π⁴)C_prime(Σ|w|)Σb² (ℓ²-bounded, support-independent).
- Harmonic sign: term<0 ⇔ m=2 & b≠0; =0 ⇔ b=0 or m=1 or 4|m; >0 ⇔ b≠0, m>2, 4∤m.
## FactorialCriticalTranslatedPrimeLimit
- Translated majorant constant 12Σ|b|·(8Σ|b|+14Σ(j+1)|b|) independent of n (reciprocal scale moment cancels direct one).
- Translated correlation |corr| ≤ C_tr(S,b)/r uniform in n; translated prime energy → P∞(S,b) by dominated convergence.
## FactorialPhaseBohrCoercivityAndTailIndependence
- Clamped kernel C(u) = {u}(1−{u})/2 continuous 1-periodic ⇒ P(cv) periodic ⇒ phase combinations Bohr almost periodic; Bohr square mean exists.
- Window lower bound (π⁴/4)∫_0^L|B_b|² ≥ (L/16 − 7K/16)Σ|b|² (first-harmonic dominance θ=3/4, MV layer bounds). Bohr coercivity: mean ≥ Σ|b|²/(8π⁴).
- Corrected Müntz tails linearly independent over ℂ (vanishing combination ⇒ Bohr mean 0 ⇒ b=0). Normalized tails √(n+1)T_n form a Riesz sequence: 144A Σ|c|² ≤ ∫|Σc_n√(n+1)T_n|² ≤ 225B Σ|c|².
## FactorialPhaseHarmonicLayers
- C(u) = 1/12 − (1/(2π²))Σcos(2πku)/k². χ(k) = 1 − 2[2|k] + [4|k] (=1 odd, −1 if ≡2(4), 0 if 4|k). P(u) − 3/16 = −(2/π²)Σχ(k)cos(2πku)/k². Φ_N = P(λ_Nv) − P(Nv) ⇒ B_b = −(2/π²)Σ_k w_kH_k, w_k = χ(k)/k², Σ_{k≥2}|w_k| ≤ 3/4, Σ|w| ≤ 7/4.
- H_k(rv) = exponential sum over four signed branches ±kr(n+1), ±krλ_{n+1} coeffs ∓b/2; separation k/15 ⇒ MV interval bounds (ℓ ∓ K/k)Σ|b|² with K = 390/π.
- |Φ_N| ≤ 2 (|P| ≤ 1); |B_b| ≤ 2Σ|b|.
## FactorialPhaseWindowAndPhysicalRieszBounds
- Weighted Cauchy–Schwarz ‖Σw_kz_k‖² ≤ (Σ|w|)(Σ|w||z|²). Pointwise dominance ‖x+y‖² ≥ (1−θ)‖x‖² − (1/θ−1)‖y‖². First-harmonic dominance lemma (w_1=1, Σ_{k≥2}|w| ≤ τ).
- Window coercivity: on every window length L = 16K = 6240/π: ∫|B_b|² ≥ (L/(16π⁴))Σ|b|² (θ=4/5). Dilated upper: ∫_a^{a+ℓ}|B_b(rv)|² ≤ (49/(4π⁴))(ℓ+K)Σ|b|² (r≥1).
- Weighted: AΣ|b|² ≤ ∫_{v>1}v^{−4}|B_b|² and ∫v^{−4}|B_b(rv)|² ≤ BΣ|b|², A = L/(16π⁴(1+L)⁴), B = 49(1+K)/(3π⁴).
- Clock change v = e^{−x}: tail combination Σc_nT_n = 1_{x≤0}e^{3x/2}B_{c·a}(e^{−x}); ∫|ΣcT|² = ∫_{v>1}v^{−4}|B|² ⇒ 144AΣ|c|²/(n+1) ≤ ∫|ΣcT|² ≤ 225BΣ|c|²/(n+1).
## FactorialRampFullWeilSmoothingLimit
- Mollification continuity of the COMPLETE Weil energy (archimedean Γ-const·ac(0) + Lévy jump − 2·(prime − polar)) for compact continuous real source with finite Lévy jump energy: jump integrands of mollified source squeezed 0 ≤ ... ≤ source's (averaging contracts squared translation increments) ⇒ dominated convergence; finitely many prime powers (support); polar on compact window.
- Ramp r_n = sourceFactorialRamp(n+1): complete Weil energy = ramp diagonal factorialSpanWeil n 1 0. Smoothed ramp zero-side W = complete energy (smooth compact test).
- Ramp diagonal: eventually log(n+1)/(4096(n+1)) ≤ A_n ≤ C(1+log(n+1))/(n+1).
- Ramp–tent span margin: eventually for all c,d: Q_n(c,d) ≥ (log(n+1)/(8192(n+1)))c² + ((n+1)/2)d². Min ramp energy ≥ log(n+1)/(8192(n+1)).
## FactorialRampSmoothingAndGramMargin (start)
- Readout splitting r_{n,k} = H_{n,k} − U_{n,k} (corrected − tail). Z(H) ≤ C_H/(n+1); Z(U) ≤ C_U(1+log(n+1))/(n+1); tail diagonal Re W(U,U) ≥ log(n+1)/(2048(n+1)) eventually ⇒ Re W(r,r) ≥ log(n+1)/(4096(n+1)) eventually in n then k; |W(r,r)| ≤ 2(C_H+C_U)(1+log)/(n+1); relative margin Re W ≥ δ Z.
- |W(f,f)| ≤ Z(f) (zero-square mass), mixed |W(f,g)| ≤ √(Z(f)Z(g)).
- Binary Gram form Q = Ac² + Mcd + Dd²; Schur: Q ≥ c²(A − B²/(2N)) + (D/2)d² when D ≥ N, |M| ≤ B. Transfer of smoothed bounds to k→∞ limit.
- RANK-ONE ZERO READOUT: every multi-scale corrected combination H_{S,a,k} has zero readout = 2Λ_pole(S,a)·readout(H_{0,k}) at every zero (boundary coefficient c(0)=1/2) ⇒ Z(H_{S,a,k}) = 4|Λ_pole|²Z(H_{0,k}) ≤ 4C_H|Λ_pole|² and W(H_{S,a,k}) = 4|Λ_pole|²W(H_{0,k}) EXACTLY. Single smoothing threshold k₀ (independent of S,a): W(H)≥0 with equality iff on pole-free hyperplane Λ_pole(S,a)=0.
- Ramp combination R = H − U: Re W(R,R) ≥ Re W(U,U) − 4|Λ_pole|√(C_H Z(U)) (no |S| penalty; equality on pole-free hyperplane).
## FactorialSpanTestMellinLowFrequency (start)
- Span test f_b(x) = e^{3x/2}B_b(e^{−x})1_{x≤0}; Fourier readout F_b(t) = ∫_{v>1}v^{−5/2}B_b(v)e^{−it log v}dv. Nonstationary bound 5/|θ| for frequencies 2πkλ ≥ 2πk(n+1) when |t| ≤ π(n+1) ⇒ |F_b(t)| ≤ (15/π³)Σ|b_n|/(n+1); |F_b|² ≤ (2D²/M)Σ|b|² for |t| ≤ πM (support n+1≥M).
- Low-freq constant D = 15/π³. Unit-interval L¹ ≤ √(JΣ|b|²) (J = 49(1+K)/(4π⁴)). Polar readouts P₀ = ∫_{v>1}v^{−2}B_b (γ=i/2), P₁ = ∫v^{−3}B_b (γ=−i/2): |P₀| ≤ 2√(JS), |P₁| ≤ (3/2)√(JS) ⇒ |2Re P₀ conj P₁| ≤ 6JS.
- Span correlation C_b(r) = r^{−3/2}∫v^{−4}B_b(v)conj B_b(rv): |C_b(r)| ≤ B r^{−3/2}S ⇒ prime atoms ≤ 2BS·Λ(r)/r²; |Σ prime| ≤ 2B·C_prime·S (ℓ²-bounded, support-independent).
- High-scale span coercivity assembly: W ≥ ((A/2)log M − offset)S given archimedean lower bound ≥ ((A/2)log M − ...)S for supports n+1 ≥ M.
## FactorialSpanTestPolarPrimeGammaBudgets (start)
- Gamma bracket quarter inequality: G(τ) ≥ log r − C₀ + 1/4 − r⁴/(4(τ²+1/4)²); global G(τ) ≥ −(G₀+log2); G(τ) ≥ log R − G₀ for |τ| ≥ R.
- Real tail combination correlation at lag y: e^{−3y/2}∫v^{−4}…, ≤ BSe^{−3y/2}.
- Pole readouts of span test: F_b(i/2) = ∫v^{−2}B_b, F_b(−i/2) = ∫v^{−3}B_b (complex Mellin readout ∫v^{−5/2}B_b e^{−iz log v}). Real tail combination cross-correlation |C_g(y)| ≤ BSe^{−3|y|/2}; prime pairing |T_Λ(g⋆g̃)| ≤ 2BS·C_prime.
## FactorialTailCombinationExplicitFormula
- Zero pairing Hermitian: W(u,v) = conj W(v,u) (reflection perm); real for real sources (conjugation perm) ⇒ W(u+iv,u+iv) = W(u,u)+W(v,v).
- Raw tail Gamma density integrable (log Fourier bound per tail, |G(r)| ≤ K + log(2+|r|)); mollified Gamma channel converges (kernel readout |κ_k| ≤ e, → 1).
- EXPLICIT FORMULA for raw (non-smooth) real tail combinations: archPoleEnergy(g) = Re W(g,g) + T_Λ(g⋆g̃) (Gamma integral + both polar readouts + full von Mangoldt atom series). Extended to complex coefficients via Hermitian cross-correlations.
- Exact Weil identity (complex b): Re W(f_b,f_b) = (1/2π)∫|F_b|²G + 2Re(F_b(i/2)conj F_b(−i/2)) − T_Λ(C_b); prime series real; cross term in Gamma channel odd ⇒ vanishes; pole readouts of real sources are real.
## FactorialTailCombinationSmoothingChannels
- Real tail combination g = Σd_nT_n, |g(x)| ≤ C_d e^{−3|x|/2}, C_d = Σ|d_n|·12e^{3/2}/√(n+1). Smoothed combination g_k in ExpDecayTest class (explicit formula holds); readout factorization F_{g_k}(γ(s)) = κ_k(s)F_g(γ(s)) (Re s > −1), |κ_k| ≤ e on strip, κ_k → 1 ⇒ zero side, polar readouts, band spectral mass, atom pairing all converge (dominated). Plancherel (1/2π)∫|F_g|² = ∫g².
- Correlation decay of tail combination |C(y)| ≤ K e^{−5/4|y|} (uniform in k) ⇒ atom majorant Λ(n)/n^{7/4}; explicit formula holds for smoothed combos via ExpDecayTest.
## FactorialTailDiskSampling
- Holomorphic mean-square at center: πR²|F(c)|² ≤ ∫_{B(c,R)}|F|² (Gutzmer). Tail readout (analytic on Re s > −1): (π/16)|readout_n(ρ)|² ≤ ∫_{B(ρ,1/4)}|readout_n|² for every center in closed strip (no zero-location hypothesis).
## FactorialTailFourierEnergy
- Weighted tail in log-Fourier domain uniformly on enlarged Mellin strip: Gamma form ∫w_ccm|F̂|² = ∫(weighted tail)² + Lévy energy (exact Gamma–Lévy identity); ≤ (96 + C_Lévy)(1+log(n+1))/(n+1). Log Fourier ∫suzukiLogWeight|F̂|² ≤ C(1+log(n+1))/(n+1).
## FactorialTailLevyEnergy
- Lévy density ≤ 1/h on (0,1]; far mass finite. Tail Lévy energy ≤ C_L(1+log(n+1))/(n+1) (near: log-translation energy; far: translation energy ≤ 384/(n+1)).
## FactorialTailLogTranslation
- Log translation energy ∫_0^1 E(h)/h ≤ C(1+log(n+1))/(n+1): split at h = 1/(n+1); linear regime E ≤ Ch (h ≤ 1/(n+1)), saturated E ≤ C/(n+1) beyond ⇒ log factor.
## FactorialTailPhase
- Tail phase = remainder read along exponential clock, |phase| ≤ 25/32, Lipschitz 14(n+1)|e^{−x}−e^{−y}|; squared increment ≤ 28(n+1)|e^{−x}−e^{−y}| (bounded×Lipschitz; no derivative at integer joins).
- Amplitude a_n = 1/((n+1)ε_{n+1}√(n+1)) ≤ 15/√(n+1). Corrected tail T_n(x) = 1_{x≤0}a_n e^{3x/2}phase_n(x) exactly.
## FactorialTailReadout
- Tail Mellin readout analytic on Re s > −1 (corrected − compact ramp identity); Fourier convention fixed.
## FactorialTailRelativeMargin
- |W(f,f)| ≤ Z(f) (reflection symmetrization). Smoothed tail: Z ≥ log(n+1)/(2048(n+1)) eventually (log is necessary); relative margin W ≥ δZ, δ = 1/(4096C) — individual sources only, not span.
## FactorialTailSampling
- Raw tail zero-square mass Z(T_n) ≤ C(1+log(n+1))/(n+1), summable (disk mean-square at each zero + zero disk overlap ≤ D(1+log(2+|Im|)) + strip energy). No Weil positivity / zero location used.
- Smoothed tail Z ≤ e²·Z(raw); joint bound raw+smoothed ≤ C(1+log)/(n+1).
## FactorialTailSpanWeilCoercivity (KEY)
- Split archimedean: (1/2π)∫|F̂|²G ≥ −(G₀+log2)E_low + (log R − G₀)E_high. Low band |r| ≤ ηM carries ≤ (A/2)S of Plancherel mass (nonstationary Mellin) for supports n+1 ≥ M.
- THEOREM: ∃c>0, C≥0: ∀M≥2, ∀ complex b supported on n+1≥M: zeta Weil sum absolutely convergent and Re W(f_b,f_b) ≥ (c log M − C)Σ|b_n|², f_b = Σ(b_n/a_n)T_n (literal correction tails). c = A/2. Positive definite for M > e^{C/c}. Real & imaginary parts split.
## FactorialTailStripEnergy
- Strip density (1+log(2+|Im z|))|readout|² on Re ∈ [−1/4, 5/4]: integrable, ∫ ≤ (3/2)C_v(1+log(n+1))/(n+1) (Fubini over vertical lines).
## FactorialTailTranslation
- Translation energy ≤ 384/(n+1) (= 4×mass ≤ 4·96/(n+1)); |a_n|² ≤ 225/(n+1); interior increment bounds via phase clock (no derivative at joins).
- Linear translation budget E(h) ≤ C_T·h, C_T = 4050e⁶+25344 (interior: tilt + phase; boundary jump region (−h,0] ≤ 144/(n+1)); E(h) ≤ C_T min(1/(n+1), h).
## FactorialTailVerticalEnergy
- Vertical line density (1+log(2+|t|))|readout(σ+it)|² integrable, ∫ ≤ C_v(1+log(n+1))/(n+1), uniformly σ ∈ [−1/4,5/4].
## FactorialTailWeightedMass
- Sampling abscissae [−1/4,5/4] (contains zero strip in interior). Weighted tail e^{(σ−1/2)x}T_n = 1_{x≤0}a_n e^{(σ+1)x}phase; |·|² ≤ 144e^{2(σ+1)x}/(n+1); ∫ ≤ 96/(n+1).
## FactorialTailWindowRieszCoercivity
- K = 390/π (MV penalty 26/(πD), D=k/15), L = 16K = 6240/π; √(L−K) ≥ (15/16)√L, √(L+K) ≤ (17/16)√L; net dominance √(L−K) − (3/4)√(L+K) ≥ √L/8 ⇒ window lower (L/(16π⁴))S; upper (49/(4π⁴))(ℓ+K)S. Σ_{j≥1}j^{−4} ≤ 4/3. A = L/(16π⁴(1+L)⁴) (tiny ~10^{−17}), B = 49(1+K)/(3π⁴), J = 49(1+K)/(4π⁴).
- Amplitude two-sided: 144/(n+1) ≤ a_n² ≤ 225/(n+1).
## FactorialTentActualZetaDetectionAndFullZeroFormBridge (KEY BRIDGE)
- Universal reflection identity (any ZeroConfig, any square-summable f): SquareMass(f) − Re W(f,f) = ReflectionDefect(f) = Σ m_ρ/2·|f̂(γ_ρ) − f̂(conj γ_ρ)|². Tempered configs ⇒ summable on C_c².
- Pole term of real compact source = 2·even² − 2·odd² (Lorentz moments, cosh/sinh moments). FIVE-WAY identity: fullZeroForm (ACT) = compactFullWeilEnergy (APT) = Re weilFullFunctional_Λ (RHTower) on C_c (no C² needed); on C_c² also = Re ζ-W = SquareMass − ReflectionDefect.
- ACT pole-free variation form 2S_a − D_a + V_a = actual-zeta SquareMass − ReflectionDefect on Φ(ω_a u). Theta-span plateau invariance.
- Re ζ-W(f,f) = fullZeroForm(Re f) + fullZeroForm(Im f). Negative complex test ⇒ negative real test with half energy, same support.
- Grid tent detector: any real C_c² φ with fullZeroForm < 0 ⇒ eventually single-scale grid tent pattern P_n (coefficients G(a+iw)…, G = e^{−3x/2}φ) has energy ≤ −2μ (μ = −F(φ)/4) and smoothed detector D_{n,q} ≤ −μ in all channels; reflection gap ≥ μ.
- UNCONDITIONAL: every actual off-line ζ zero is detected eventually (large n) by a single-scale grid tent pattern + smoothed detector with margin μ>0 (via offLine_visible from SquareRootThreshold). Finite off-line sets detected at explicit Nyquist–Ingham aperture.
- RH ⇔ ∀ G,R: eventually compactFullWeilEnergy(gridTentPattern) ≥ 0 (grid tent patterns complete for Weil positivity). ¬RH ⇒ single-shift origin-vanishing Doob profile with negative pole-free variation form, detected by grid tents.
## FactorialTentClusterAndLatticeDetection
- Period difference f(x) − f(x+L) at vertical lattice point ½+δ+ik(2π/L): Weil summand multiplied by −2(cosh(δL)−1), independent of k; on-line (δ=0) annihilated, off-line strictly negative.
- Off-line lattice: below Nyquist [−L/2,L/2] seed is depth-blind (W = 2L‖f‖²) but period difference has W = −4L(cosh δL − 1)‖f‖² < 0.
- Finite cluster/run configs: period difference annihilates on-line background; W, square mass, reflection defect reduce to finite sums over S; coherent phase sector (|k·2π/L|R ≤ 1/4) ⇒ constructive negative margin. Factorial tent detector = period difference of smoothed right source.
- Thin nonnegative seed (mass ≥1, radius R, |γ_k|R ≤ 1/4): each cluster pair contributes ≤ −(e^{δL}−1)(1−e^{−δL})e^{−2δR}; cluster scale ⌈32πK/L⌉ makes factorial tent detector (radius 3/(n+1)) thin for |k|≤K. Run of |S| equal-depth pairs: margin ∝ |S|.
- Blindness vs visibility: small-TV clusters (4r ≤ L, r·TV(d)·sinh(2δr) ≤ 1) are Weil-nonneg on every C² test in [−r,r] and windowed-nonneg, yet the un-averaged factorial tent detector is strictly negative.
## FactorialTentDepthGapClusterAndPolarGraphBridge
- Small aperture a ≤ 1/100: ReflectionDefect + (1/25)∫|f|² ≤ SquareMass; fullZeroForm F ≥ (1/25)∫F² (unconditional L² coercivity). High height shift: SquareMass ≥ ReflectionDefect above horizon Ξ(f).
- Polar Doob: polarEnergy(v) = coshMass(v²) − 2coshMass(v)² + 2sinhMass(v)²; odd v: = coshMass(v²) + 2sinhMass². Six-way identity for compactLift v (weilForm = fullBV = fullZeroForm(Φv) = compactFullWeilEnergy = archJump + primeJump − polarEnergy = SquareMass − ReflDefect).
- RH ⇔ polar-strengthened odd Doob Poincaré ⇔ ∀ source graph weilForm ≥ 0 ⇔ polarEnergy ≤ edge norm².
- Depth-gap detection (explicit aperture inequality with local count A₀); contrapositive: eventual grid tent positivity at aperture a forces a deep companion zero within R. Equal-depth cluster detection.
- Dyadic prime-window functional on two-bump test = SquareMass − ReflDefect exactly; off-line depth > σ ⇒ two-bump tests with ReflDefect − SquareMass > Ke^{σv}.
- Attained maximal-depth zero (no gap/finiteness) detected by grid tents ⇒ eventual grid-tent positivity ⇒ AsymptoticAbscissaLaw. RH ⇔ ZerosApproachLine ∧ eventual grid-tent positivity ⇔ EventualSlicePositivity ∧ grid-tent positivity.
## FactorialTentOffLineDetection
- Right factorial source r_n(x) = e^{x/2}·tent density (support [0,2d_n], d_n ≤ 1/(n+1)), ∫ ≥ 1, nonneg; smoothed thin: support radius 3/(n+1) once k ≥ n.
- Period-difference tent pattern f(x) − f(x−L); detection scale ⌈32π/L⌉; margin (e^{δL}−1)(1−e^{−δL})e^{−6δ/(n+1)} > 0. Single C² detector with full-Weil approximation 1/(q+1) + negative margin on isolated pair config + reflection gap; detector readout vanishes on on-line lattice.
## FactorialTentPatternWeilCompleteness
- Unit ramp; Σ_{j<M} ramp(u−j) = clamp(u,0,M). Grid tent pattern on a + j d_n = e^{3x/2}·piecewise-linear interpolant of nodal data (Abel summation); interpolant keeps Lipschitz const, error ≤ 2Ld ⇒ Q(f_n) → Q(g) for compact g with Lipschitz e^{−3x/2}g. RH ⇔ complete Weil energy ≥ 0 on finite translated factorial tent patterns.
- Factorial hat = difference of two unit ramps. Exact grid representation: gridTentPattern(G) = e^{3x/2}·interpolant(G) when G vanishes at grid ends. e^{3x/2} preserves Lipschitz on window. Grid convergence rate: |Q(f_n) − Q(g)| ≤ C·d_{n+1} (L¹-gap × full-Weil Lipschitz constant, prime cutoff beyond horizon).
- RH ⇔ ∀ finite factorial tent patterns: compactFullWeilEnergy ≥ 0 (via smoothing error C/(k+1) one way; grid convergence other way).
## FactorialTranslatedTentApproximation
- Right factorial tent |r_n| ≤ 30(n+1), Lipschitz ≤ 2000(n+1)², support ⊂ [−1,1]. Pattern bounds: value 30Σ|b|(n+1), slope 2000Σ|b|(n+1)², radius 1+Σ|t|. Smoothing error ≤ Cost(radius,value,slope)/(k+1); smoothing index ⌈(q+1)Cost⌉ pays 1/(q+1).
## FromTheCriticalFamilyToTheReceiver (start)
- Theme: critical-family positivity is driven by log M Lévy gain; receiver tests (RH, zero width) have no scale M → need quantitative finite-scale approximation, parity projection (odd sector), graded reflected-prime/polar ledger.
- (1) Explicit grid-tent approximation constants O(d_{n+1}) ≤ O(1/(12(n+1))) in all 5 forms + L² mass.
- (2) Parity split on C_c: ac(even)+ac(odd) = ac(f) ⇒ all channels split additively; critical truncated source (support (−∞,0], vanishes at 0): odd/even projections each carry half L² mass and each satisfies Lévy coercivity ≥ (s_T/2)(log M − c)Σb².
- (3) Norm-controlled subfamily transfer: floor −Ce^{2σr}∫g² with ∫g² ≤ αe^{2βr}∫F² ⇒ zetaZeroWidth ≤ σ+β; β=0 for grid tents; subexponential/constant floor ⇒ width 0 ⇒ RH.
- (4) Reflected-prime/polar ledgers; unconditional floors −75e^r, −((3+ε)e^r + C), de la Vallée Poussin Sobolev; converse width<β ⇒ floor(2β).
- (5) Small aperture: (1/5000)∫F² ≤ Q(F) on [−3/10,3/10] all profiles; (1/1000)∫F² on [−181/500,181/500] (past log2/2) odd profiles; transferred to grid tents/detectors.
- Grid tent error ≤ C_grid(R,Mg,Kg,L)·d_{n+1} ≤ C_grid/(12(n+1)); same for fullZeroForm and L² mass; smoothed detector error ≤ C_grid·d + 1/(q+1) in W, ζ-W, SquareMass−ReflDefect.
- Parity split exact on C_c: even/odd parts Lipschitz with same K; ac, L², Lévy, prime-polar pairing, compactFullWeilEnergy, fullZeroForm all additive.
- g^V(x)g^V(−x) = 0 (support (−∞,0], vanishes at 0) ⇒ odd and even projections each carry exactly half the L² mass; each projection Lévy-coercive with slope s_T/2 and offset 3 + log(1/η(A_c/4, D_c)), V ≥ max(2+L, 16U/A_c).
- Odd/even projections each Lévy-coercive: low band ≤ 3A/8·E, high band ≥ A/8·E ⇒ Lévy ≥ e^{−1/2}(log R − 3)(A/8)E.
- Grid tent family has (1,0)-norm-controlled receiver transfer (approximates odd receiver tests in energy and L² with no exponential loss). Graded floor at rate σ on grid tents ⇒ zetaZeroWidth ≤ σ. RH ⇔ subexponential odd grid-tent floor ⇔ constant (bounded-below) floor (self-improving).
- Ledgers transferred: Q = budget − reflectedPrimePolarCost = budget − ∫_{(0,2r]} Chebyshev two-pole defect·(…) = budget − ∫ critical-scale prefix·(…). Unconditional floors: −78e^r∫F² (also grid tents up to ε), −((8+ε)e^r + C)∫F² (sharp PNT), de la Vallée Poussin Sobolev −Ke^r e^{−c√r}(∫F² + ½∫F'²). Width < β ⇒ floor −C(1+A)e^{2βA}(∫F²+D) inherited by grid tents up to C_grid d.
- Small aperture: [−3/10,3/10] all profiles Q ≥ (1/5000)∫F²; [−181/500,181/500] (past log2/2, prime 2 enters) odd profiles Q ≥ (1/1000)∫F²; transferred to grid tents/detectors at explicit n.
## GeneralDivisorBernoulliFilterClassification
- C(u) = {u}(1−{u})/2 ∈ [0,1/8], mean 1/12. Divisor stencil filter P_{D,α}(u) = Σα(d)C(du); constant mode Σα/12 cancels in every collar difference (any stencil).
- Harmonic multiplier M_{D,α}(k) = Σ_{d|k}α(d)d². DYADIC UNIQUENESS: on {1,2,4}, M(1)=4, M(2)=−4, M(4)=0 ⇔ α = (4,−2,1/4) (the canonical stencil P = C(4u)/4 − 2C(2u) + 4C(u)); then M(k) = 4χ(k). Two-scale obstruction: on {1,2}, M(1)=4, M(2)=0 forces α=(4,−1), linear ramp residual 2 ≠ 0.
- Two-divisor {1,d}: drift-free (linear L = Σdα, quadratic Q = Σd²α both 0) ⇔ α ≡ 0 ⇒ cannot normalize first harmonic.
- q-adic {1,q,q²}: sign-flip+extinction ⇔ α = (c, −2c/q², c/q⁴), linear residual c(1−1/q)² (=1 at (2,4), matching 1/2 Müntz ramp). Drift-free ⇔ α = (c, −(q+1)c/q², c/q³).
- Φ_{n+1}(v) = Müntz tail remainder at (n+1)v; T_n(x) = 1_{x≤0}a_n e^{3x/2}Φ_{n+1}(e^{−x}).
- First-harmonic margin 1 − Σ_{k≥2}|χ|/k² ≥ 1/4.
## InghamHuxleyHeightBoxZeroMajorant (start)
- Route-T zero-free region annihilates high-abscissa height boxes; truncated layer-cake majorant; Ingham–Huxley density on off-line slabs replaces abscissa-blind O(log T).
- Route-T: ∃A,T₁: height boxes with σ > 1 − routeTWidthPolylogLower(A,4T/3) empty; truncated layer-cake on dyadic shells. Ingham–Huxley count on slabs ½+m/(2M): ≤ D(1+log T)^B T^{(IH(σ)+ε)(1−σ)}.
- Off-line lattice spacing 2π/L: Weil ≥ 0 on all C² tests in [−a,a] ⇔ a ≤ L/2 (Nyquist); super-Nyquist negative witness.
## LacunaryCriticalBlockPositivity
- Truncation V: only dilations 2 ≤ r ≤ ⌈2V⌉ see the doubly collared source ⇒ prime channel = finite sum Σ(Λ(r)/r)∫ψχ(rv/V)B(v)B(rv). Union of disjoint blocks ⇒ prime channel = Σ block-pair couplings; diagonal = block prime channel ≤ C_T Σb².
- Lacunary family: M₀ ≥ 3, M_{i+1} ≥ M_i⁸ (⇒ M_i ≥ 256^i, Σ M_i^{−1/8} ≤ 2). τ(m,n) ≤ 50m^{−1/16}n^{−1/16} for m⁸ ≤ n. Off-diagonal ≤ 50K w_iw_{i'}‖b_i‖‖b_{i'}‖ ⇒ total ≤ 100KΣb² (Cauchy–Schwarz).
- Prime channel on lacunary union: |P| ≤ (C_T + 100K)Σb², ANY number of blocks. Channel constant |Ω(0)|U + 288 a_R a_E + 2(C_T+100K). E(g^V) ≥ (s_T(log M₀ − c_T) − K_lac)Σb² uniformly in V and #blocks.
- THEOREM (lacunary): ∃M₀: every lacunary family with M_0 ≥ M₀, any J, V ≥ V₀, nonzero b ⇒ complete energy > 0 AND compactFullWeilEnergy(g^V) > 0 (Weil positivity of ζ on these tests; scales M₀ … M₀^{8^{J−1}}).
## LowScaleCoupledPositivityAndSchurComplement (claims to resolve Open Problem 7.1)
- Clock profile F_V(v) = χ(v/V)σ(v−1)B(v), g^V(y) = e^{y/2}F_V(e^{−y}); |F_V| ≤ 2Σ|b|; F_V globally Lipschitz uniform in V ≥ 1.
- Interpolation |Δ|⁴ = |Δ||Δ|³: (g^V(u) − g^V(u+x))² ≤ K²√x e^{u/2} (u ≤ 0, x ∈ [0,1]) ⇒ ac(0) − ac(x) ≤ K²√x; 0 ≤ jump ≤ 2UΣb² globally.
- Window ScaleWindow S 1 L: K² ≤ (4σ'+20)²L³Σb² ⇒ low-window Lévy energy ≤ C L³ Σb² INDEPENDENT of high scale M and V. Lévy weight ≤ 3/x on (0,1].
- Lévy weight ≤ 48x^{−2} on x ≥ 1. Low-window Lévy ceiling: Lévy(g^V_low) ≤ (6(4σ'+20)²L³ + 96U)Σ_low b² (split (0,1]: K²√x·3/x; (1,∞): 2UE·48x^{−2}).
- Spectral jump split: ½Δ_high ≤ Δ_union + Δ_low ⇒ Lévy(union) ≥ ½Lévy(high) − Lévy(low) ⇒ scale-free two-band law: Lévy(union) ≥ (s_T/2)(log M − c_T)E_high − C_low(L)E_low (low penalty independent of M, V).
- Shift-adapted Young weight β(x) = γx^{1/4} on (0,1], γ beyond: Lévy(union) ≥ Lévy(low) + Lévy(high) − γ⁻¹·2C_low E_low − γ·120U E_high (keeps 100% of both diagonals).
- compactFullWeilEnergy(g^V) = Lévy + Ω(0)ac(0) + 2·readout·endpoint − 2·prime (real-valued, exact).
- Low window + lacunary (L_low⁸ ≤ M₀): Q ≥ ((s_T/2)(log M₀ − c_T) − C_Γpol − 2(C_lac+100K))E_high − TotalPenalty(L_low)E_low; penalty independent of M₀, J, V. Also low window + high window [M,LM] version (low penalty grows only with (3+log(LM))²).
- Polar readout/endpoint additive over disjoint supports. Gamma+polar bilinear Young bound with γ.
- Low–lacunary prime cross coupling: 2|cross| ≤ γ⁻¹·1300K E_low + γ·200K E_high (low window split into dyadic slices, Σ low weights² ≤ 13).
- EXACT SCHUR: Q(low∪high) ≥ Q(low) + Q(high) − (γ⁻¹C_SL E_low + γC_SH E_high), optimized: ≥ Q(low) + Q(high) − 2√(C_SL C_SH)√(E_low E_high). C_SL = 2C_Lévy(L) + C_Γpol + 1300K; C_SH = 120U + C_Γpol + 200K.
- Low-mode certificate: if Q(low) ≥ μ_low E_low (μ_low>0) and 2C_SL C_SH/μ_low + μ_low/2 ≤ s_T(log M₀ − c_T) − C_Γpol − 2C_lac then Q(union) ≥ (μ_low/2)(E_low + E_high) > 0.
- Dominance cone E_low ≤ ΛE_high: explicit threshold M₀(L_low,Λ) = max(3, L_low⁸, ⌈exp(target)⌉) ⇒ Q(union) ≥ (s_T/4)log M₀·E_high > 0, AND positivity transfers to all five form realizations + grid-tent patterns + smooth C² detectors (weilFullFunctional, zetaZeroConfig.W, SquareMass − ReflectionDefect).
- Coupled sources Σ b_low(n)(g_n + γ(n)g_{φ(n)}) with |γ| ≥ γ₀ and φ: S_low ↪ S_high: E_high ≥ γ₀²E_low ⇒ dominance cone Λ = γ₀^{−2} ⇒ positive for EVERY nonzero b_low (including scale M = 1, n = 0). CAVEAT: low modes are positive only when coupled to high modes; pure low-mode sources (b supported on S_low alone) are NOT covered — need a separate low-mode certificate μ_low.
## MarkovPoleHyperbolicCapacityAndApertureThresholds
- Exact finite-aperture decomposition (RHTower.WeilMarkovPole): W(g) = M_N(g) + cosh(g)²/2 − sinh(g)²/2, M_N(g) = V_N‖g‖² + LévyJump(g) + primeJump_N(g) Markovian (Dirichlet-form), pole plane rank-two hyperbolic is the sole anti-Markov part; cosh(g) = ∫g·2cosh(u/2), sinh(g) = ∫g·2sinh(u/2). Valid when supp shifts by log n > log N vanish (aperture N).
- Parity: cosh pairing kills odd g, sinh pairing kills even g; pole form diagonalizes over even/odd with no cross term.
- Even g: W = M_N + cosh²/2 ≥ M_N. Odd g: W = M_N − sinh²/2; W ≥ 0 ⇔ sinh² ≤ 2M_N (odd-mode sinh-capacity is the exact RH obstruction at aperture N).
- Creation potential V_N = Ω(0) − 2Σ_{2≤n≤N}Λ(n)/√n, antitone in N; V_{N₁} − V_{N₂} = 2Σ_{(N₁,N₂]}Λ(n)/√n. (V_N → −∞ ~ −4√N: Markov diagonal goes negative at large aperture.)
## MultiScaleLowModeAndGridTentSchurBridge (header)
- Polar Cauchy–Schwarz: (Σ_S |b_n|/(n+1))² ≤ (π²/6)Σ_S b² on EVERY S (no M ≥ 2 barrier for Gamma/polar channels).
- Two-band Lévy: Lévy(low ∪ high) ≥ s_T(log M − c_T)(E_high − (16U/A_c)E_low) (older, weaker than scale-free version).
- Cross-window prime: low+[M,LM] via polarization b^± = αb_low ± α⁻¹b_high, α = √(3+log LM): coupling ≤ C_TW(3+log LM)²E_low + C_TW E_high (no lacunary gap). Low window + lacunary: Σ_k(2^k)^{−1/8} ≤ 13 ⇒ cross ≤ 650K E_low + 100K E_high, total low prime coefficient O(log L_low).
- Translation invariance of compactFullWeilEnergy and fullZeroForm; G(x) = e^{−3x/2}g(x) Lipschitz ⇒ grid tents and smoothed C² detectors converge to Q(g) and inherit positivity.
- Gamma+polar on any S: Ω(0)ac(0) + 2RE ≥ −(|Ω(0)|U + 48π²a_R a_E)Σb²; |R·E| ≤ 24π²a_R a_E Σb² (Euler–Basel Σ1/(n+1)² ≤ π²/6).
- Two-band old law proof: spectral split |ĝ|² ≤ 2|ĝ_c,high|² + 4|ĥ_tail|² + 4|ĝ_low|²; low-band Plancherel |t| ≤ ηM bounded by collar low-frequency constant 2D²/M; tail L² ≤ U/V; low L² ≤ U E_low; mass ≥ A E_total ⇒ high-band mass ≥ (A/4)(E_high − (16U/A)E_low).
- Prime energy over disjoint union = P(S₁) + P(S₂) + coupling(S₁,S₂) + coupling(S₂,S₁); bilinear scaling; polarization identity: cross = (P(b⁺) − P(b⁻))/2 with b^± = αb_low ± α⁻¹b_high.
- Low + window [M,LM]: |P(union)| ≤ 2C_TW(3+log LM)²E_low + C_TW(4+log L)E_high (no lacunary gap).
- Dyadic slices of low window: Σ_k ((2^k)^{−1/16})² ≤ Σ(12/13)^k ≤ 13 (since (13/12)⁸ ≤ 2). L_low⁸ ≤ M₀ ⇒ low window disjoint from lacunary blocks.
- Pair coupling bound between blocks at scales a ≤ b with a⁸ ≤ b: |coupling| ≤ 50K (a^{−1/16}√X_a)(b^{−1/16}√X_b) ⇒ low×lacunary cross ≤ 50K·A·B, A² ≤ 13E_low, B² ≤ 2E_high.
- Older combined bounds use two-band law with low penalty s_T(log M − c_T)(16U/A)E_low (grows with log M) — superseded by scale-free version in LowScaleCoupled.
- Translation invariance: weilTest(g(·+τ)) = weilTest(g) ⇒ Q and fullZeroForm translation invariant (crossing x = 0 into v < 1 changes nothing).
- Grid-tent transfer for any criticalTruncatedTest: G(x) = e^{−3x/2}g^V(x), R = log 2V, Lipschitz constant e^{3R/2}(K + 3M/2); tents → Q(g^V); if Q ≥ 2μ then eventually tents ≥ μ and smooth C² detectors (q with 1/(q+1) ≤ μ/2) ≥ μ/2 in weilFullFunctional, zetaZeroConfig.W, SquareMass − ReflectionDefect.
- Lacunary and polynomial-window families: ∃ M₀, all grid tents/detectors from these sources positive (μ = (s_T/8)log M Σb² for windows).
## NonstationaryMellinLowFrequencyExclusion (APT-ROOT-SPAN-COERCIVITY)
- Phase Φ_N(v) = P(λ_N v) − P(Nv); low band |t| ≤ πM ≤ πN, harmonic |ω| ≥ 2πN ⇒ |ω − t/v| ≥ |ω|/2 on v ≥ 1 (no stationary point). IBP majorant ≤ 5/|ω|; Σk^{−3} ≤ 3/2 ⇒ Mellin readout ≤ D/N, D = 15/π³. Σ_{N≥M}N^{−2} ≤ 2/M.
- Cutoff η(A,D) = min(1, π, Aπ/(4D²)): low-band Plancherel energy on |t| ≤ ηM ≤ (A/2)S.
- Abstract assembly: A S ≤ E_tot ≤ B S, E_low ≤ (A/2)S, Gamma growth log|t| ⇒ E_arch ≥ ((A/2)log M − B(G+log2) − (A/2)log(1/η))S; with polar ≤ 6JS, prime ≤ 2B·C_prime·S: W ≥ ((A/2)log M − C)S; positive ⇔ M > exp(2C/A).
## PeriodDifferenceOffLineDetection
- Period difference f − f(·−L) (shiftPair f (−1) L) has FT vanishing at every lattice frequency 2πk/L: annihilates the entire on-line lattice {1/2 + 2πik/L}.
- Pair readout at γ = 2π/L, shift α: (1 − e^{αL})·f̂(γ − iα). Nonnegative thin source (γR ≤ 1/4, ∫f ≥ 1): f̂ within quarter-sector of tilt mass ≥ e^{−|α|R}.
- Isolated pair config (lattice + off-line pair 1/2 ± δ + iγ): W(Δf) ≤ −(e^{δL}−1)(1−e^{−δL})e^{−2δR} < 0. Exact detection; on-line budget zero; SquareMass − W = ReflectionDefect, defect ≥ the same explicit gap.
## QuantitativeGridTentDetection
- Re W_ζ(f,f) = Q(Re f) + Q(Im f) for complex C²_c f (real/imag splitting); finite-scale tent approximation |Q(P_re)+Q(P_im) − Re W(f)| ≤ 2C_grid(R,Mg,Kg,L)·d_{n+1} ≤ C/(6(n+1)).
- Single-scale certificate: tents nonneg at ONE scale n ⇒ Re W(f) ≥ −2C·d_{n+1} (finite-scale exclusion of witnesses with more negative W).
- Unmodulated difference lag test twoBump(modScaledBump w 0) v (−1) is real and odd ⇒ Re W = Q(φ), one odd seed suffices.
- FIXED-RADIUS EQUIVALENCE: eventual tent nonnegativity for all seeds in [−R,R] ⇒ ZetaWindowPositive R ⇒ HodgeIndexAtLevel R ⇒ Re W(f) ≥ 0 on C²_c([−R,R]) ⇒ ground energy ≥ 0 and (¬RH ⇒ R ≤ zetaContactAperture). So RH ⇔ tent positivity at every radius R; failure of RH gives a finite contact aperture.
- Unconditional: odd lag tests with v/2 + w ≤ 353/1000 (past first prime (log 2)/2) have Q(φ) ≥ (1/1000)∫φ²; tents at fine enough scale ≥ (1/2000)∫|f|².
- Negative lag test on [0,V] ⇒ ground energy < 0 at aperture V/2 + w, contact aperture ≤ V/2 + w, and eventually tents/detectors ≤ −μ in all five forms (detection transported from SquareRootThreshold lag hierarchy: one-param near-top, polylog, loglog under OffLineCopiesLocallyBounded, attained-top O(1/g) and O(log 1/g) lags).
- Contrapositive horizon forcing: tent positivity at radius V/2+w + generic bump nonvanishing at zeros ⇒ every off-line zero inside the horizon forces a deeper zero beyond the horizon (infinite ascent).
- Excluded-depth laws from tent positivity at aperture R ≥ e⁶: every zero with 2 ≤ |γ| ≤ exp(R/(10⁵A₀ log²R)) − 306 has |β − 1/2| < 1/R = 2/log X (X = e^{2R}); local count refinement Nd ≤ k up to exp(R/100 − (k+1)log²R)/A₀ − 4. Near-top excluded depths (one-param, polylog, loglog under bounded copies), equal-depth k-pair clusters.
- Duality: log(horizon height) ≤ 7000e^R + O(1); zero-to-aperture: if zeros up to horizon have depth ≤ δ and density ≤ D, polar-constrained real seeds (even and odd pole moments zero) have tents ≥ −(7000(2R+3)De^{2δ(R+2)} + 2)∫F² − C d_{n+1}. Horizon height is DOUBLY EXPONENTIAL in R (needs zeros up to height exp(7000e^R) to control aperture R).
## RankOnePoleReadoutAndZeroNullspace
- Corrected source H_{n,k} = r_{n,k} (smoothed compact ramp) + U_{n,k} (smoothed noncompact tail); readouts additive on Re s > −1.
- F_{H_{n,k}}(ρ) = F_{η_k}(ρ)·c_n/ρ, c_n = 1/(2√(n+1)): all corrected sources span ONE dimension in zero-side evaluation space (single mode 1/ρ); pole functional Λ_pole(S,a) = Σa_n c_n. On hyperplane Λ_pole = 0 compact ramp readouts = −tail readouts at every zero; unsmoothed corrected combination has zero readout at ρ ⇔ Λ_pole = 0.
- Pole-free hyperplane Λ_pole(S,a) = 0: corrected combination H_{S,a,k} has ZERO readout at every zero ⇒ zero-square mass 0 and W(H,·) = W(·,H) = 0 (invisible to zeros). Ramp combination and tail combination have equal zero-square mass and equal W. Canonical two-scale pole-free pair a(n₁) = c_{n₂}, a(n₂) = −c_{n₁}. Re W(r) = W(H,H) + W(U,U) − W(H,U) − W(U,H). Interpretation: corrected sources carry no zero information beyond one scalar; compact ramps reduce to noncompact tails on the hyperplane.
## RpowMellinNonstationaryPhaseBound
- ‖∫_1^∞ v^{−5/2}e^{i(ωv − t log v)}dv‖ ≤ 5/|ω| for |t| ≤ |ω|/2 (van der Corput IBP, h = v^{−5/2}/(ω − t/v), |h| ≤ (2/|ω|)v^{−5/2}); cosine version same bound.
## SelbergExponentialNearLineAndThreeRegimeZeroDensity (classical zero-density imports)
- Selberg near-line: #zeros (with mult) in Re ρ ≥ 1/2 + (51/50)a/log S, heights ~[2S/3, 4S/3] ≤ (log S/(2πa))((T₂−T₁)Ae^{−22a/25} + K log S), 1 ≤ a ≤ log S/100; second version exp(−a/1200) at Re ≥ 1/2 + 2a/log U.
- Uniform hybrid density: N(σ,T) ≤ D(1+log T)^B T^{e(σ)}, e = (12/5+ε)(1−σ) on [1/2,5/6), (2+ε)(1−σ) on [5/6,1], uniform on [1/2,1] incl σ = 1/2.
- Layer-cake: Σ_{zeros at height [T,2T]} x^{β−1} ≤ 4D(1+log T)^B Σ_m x^{σ_{m+1}−1}T^{e(σ_m)} over slabs below 1 − Route-T zero-free width.
## SingleHeightPhaseSelectiveApertureAndPowerSaving
- Localized explicit formula at aperture a (X = e^{2a}), height 2πξ: W_ζ(S_ξ f, S_ξ f) = A_f(ξ) − Π_f(⌊X⌋, ξ) (arch+pole minus finite prime trig polynomial). Height-uniform bounds cost full ℓ¹ prime mass O(√X) ⇒ unconditional single-height positivity only for X ≲ (log|ξ|)².
- Syndetic Bohr–Kronecker: for every N, phase pattern θ, δ > 0, ∃ L: every [T₀, T₀+L] contains ξ with e^{2πiξ log p} within δ of e^{iθ(p)} for all p ≤ N. Hence PX X τ returns syndetically to PX X 0.
- OBSTRUCTIONS: no bound PX X τ ≥ −(c√X + C)/π with c < 2, and no power saving PX ≥ −CX^{θ/2} with θ < 1, even eventually in height τ ≥ T₁(X). Smooth C² endpoint-pair interferometer (L² ∈ [1/2048, 8], B_f ≤ 336) saturates: prime-only envelope − prime-power tail > κ₀e^a∫|f|²; no height-eventual power saving for smooth tests either.
- Syndetic coherent peaks AND troughs of the prime polynomial at level ±B for any B < primeOnly − tail envelope.
- Composite prime powers: Σ_{n≤x, n composite} Λ(n)/√n ≤ 2 log x + log²x (Abel + ψ − θ ≤ 2√x log x) ⇒ prime-power tail envelope ≤ 2‖f‖²(4a + 4a²) = O(a²‖f‖²) — negligible vs prime-only √X.
- Endpoint-pair interferometer: unit bell (1−u²)₊^{5/2} (|φ''| ≤ 20, ∫|φ''| ≤ 40), two bells at ±(a−1); autocorrelation ≥ 1/2048 on lags [2a − 9/4, 2a − 7/4]; prime shell (a − 9/8, a − 7/8) carries mass ≥ δ₀e^a, δ₀ = e^{−7/8} − e^{−9/8} ⇒ saturation κ₀ = δ₀/16384.
- High-height pole decay: |Re(pole terms of S_ξ f)| ≤ 2e^a B_f²/(1+2π|ξ|)⁴ (B_f = 4(‖f‖₁ + ‖f''‖₁)), removes the height-independent 2S(a) ≈ e^a pole barrier.
- Shifted symbol: ∫|f̂(τ+2πξ)|²w(τ) ≥ (log(1+π|ξ|/4) − E)‖f‖² − B_f²/(8(1+π|ξ|)) when w ≥ (log(1+|τ|/4) − E)/2π. Re A_f(ξ) ≥ (log(1+π|ξ|/4) − 10)‖f‖² − errors; Re A_f(ξ) ≤ pole decay + B_f²(1/2 + πC) + ‖f‖² log(1+2π|ξ|).
- Sharp horizon: ∀ε ∃C: Re W_ζ(S_ξ f) ≥ 0 when C + (4+ε)e^a + 2 ≤ log(1+π|ξ|/4) (optimal symbol coefficient (4+ε)e^a = (4+ε)√X).
- Post-pole desert: W ≥ 0 forbids Re Π_f > B where ‖f‖² log(1+2π|ξ|) ≤ B − 1 − B_f²(1/2+πC).
- Dichotomy: ∃ξ > T past pole zone with Re Π_f > B and (W(S_ξ f) < 0 or log-height escape). Under RH: Bohr recurrence gaps L and heights forced superexponential: e^{c₀e^a} < 1 + 2π(e^a + 336² + L) for endpoint pairs. (Conditional on RH — consequence, not proof.)
- Phase-selective single-height positivity: Re Π_f(ξ) ≤ M‖f‖² and 12 + M ≤ log(1+π|ξ|/4) ⇒ Re W(S_ξ f) ≥ 0. Power saving Re Π ≤ ce^{θa}‖f‖² ⇒ positivity up to X ≍ (log|ξ|)^{2/θ}; destructive cone Re Π ≤ 0 ⇒ positivity up to X ≲ |ξ|⁸.
- Single-height power saving at ξ₀ = −γ₀/2π on sinhTest a δ (with a ≳ (1/2δ)log log|γ₀|, θ < 2δ) forces an off-line companion zero within ordinate R of an off-line zero ρ₀ = 1/2+δ+iγ₀ (no isolated off-line zeros under single-height saving).
- Bad heights: windowed measure of heights violating θ-power saving ≤ ‖η‖²·2(2a(2a+C))/(c²e^{2θa}) = O(X^{−θ}log²X‖η‖²), universal in f (prime variance ≤ 2‖f‖⁴·2a(2a+C)). So power saving holds for most heights; Kronecker shows it fails syndetically.
## SourceRelativeSchurMarginAndPerturbationCalculus
- Zero-side Cauchy–Schwarz: ‖W(f,g)‖ ≤ √(Z(f)Z(g)), Z = multiplicity-weighted zero-square mass Σ m_ρ|f̂(γ_ρ)|² (reflection invariance of zero set).
- Relative margin: r = h − u, Re W(u) ≥ δZ(u), Z(h) ≤ εZ(u) ⇒ Re W(r) ≥ (δ − ε − 2√ε)Z(u); factor > 0 ⇔ ε < (√(1+δ) − 1)²; sharp via two-mode involution extremizer.
- Two-mode involution model W₂(x,y) = x₁y₂ + x₂y₁ (reflection-coupled zero pair ρ, 1−ρ̄): saturates Cauchy–Schwarz; W₂(h,h) = −Z₂(h) attained (antisymmetric). Binary Schur: Ac² + Mcd + Dd² ≥ 0 ∀ ⇔ M² ≤ 4AD (D > 0), witness (2D, −M).
## SourceSelectionInTheFullWeilCone
- Full Weil cone {λ: WeilPositiveFull λ} = ∅ if ¬RH, = {Λ} (on n ≥ 2) if RH.
- Narrow pair test pairTest m σ = h_m(u) + σh_m(u − log m), h_m supported in |u| ≤ 1/(4(m+1)): ℓ-vector supported only at index m; Re W_w(pairTest) = Arch − w(m)·2σ∫h_m²/√m. Coordinates of w on n ≥ 2 are recovered exactly by pair tests (explicit inversion).
- Single-index perturbation Λ + δ1_{n=m}: Riemann-kernel exposure atomPairing = (δ/√m)(K(log m) + K(−log m)), K = riemannKernelAutocorr > 0 everywhere; unconditionally (no RH) truncated Riemann kernels at L ≥ L₀ make W < 0 for δ > 0; WeilPositiveFull(Λ + δ1_m) ⇔ RH ∧ δ = 0.
- One-sided cones (no summability premise): PositiveOnNonposCone U ⇔ RH ∧ Λ ≤ U on n ≥ 2; PositiveOnNonnegCone L ⇔ RH ∧ L ≤ Λ; full cone = intersection.
- SOURCE IDENTIFICATION ≠ SIGN: pair tests identify λ = Λ on n ≥ 2 unconditionally, but WeilPositiveFull λ ⇔ RH. For identified source, WeilPositiveFull ⇔ each of: one-sided cone positivity; prime-power node-deletion symbol slack ∀ prime powers m; constant-in-aperture odd tent floor −C∫F²; subexponential odd tent floor −C_σe^{2σr}∫F² ∀σ>0; same on fullZeroForm; RH. (These are RH-equivalent reformulations.)
- Graded: (α,β)-norm-controlled transfer + rate-2σ floor ⇒ zetaZeroWidth ≤ σ + β; fixed-aperture smooth-detector positivity ⇒ ZetaWindowPositive R + depth exclusion below cluster horizon.
## SpectralRealisationAndOperatorConstraints (CCM / Connes–Consani)
- Scaling unitaries ϑ_u on even subspace (≅ L²(ℝ) additive translation by −u) → 0 weakly as |u| → ∞; every trace-class T: Tr(Tϑ_u) → 0; Sonin Toeplitz kernel τ_Λ(u) = Tr(G_Λϑ_u) → 0 at ±∞.
- Zero-origin Toeplitz indefiniteness: bounded continuous real even τ with τ(0) = 0 gives nonneg Toeplitz form on all compact Schwartz log tests ⇔ τ ≡ 0; τ_1 ≢ 0.
- Small-support bump (inside Connes–Consani small-support radius) has strictly negative cutoff-1 Sonin Toeplitz form (CC domination FAILS for nonneg bumps); proof of zero-origin indefiniteness: two-bump h + σh(·−u₀), I₀ ≈ 0 (τ(0)=0), cross ≈ κ(u₀)M², σ = ±1 forces κ(u₀) = 0.
- G_Λ scaling-conjugate trace nonneg on all compact Schwartz tests ⇔ τ_Λ ≡ 0.
- Multi-packet decoupling: τ continuous bounded → 0 at ±∞; packets Σc_i g₀(x − α_iL), α injective: ∃L₀ (uniform in c) with |Toeplitz(packet) − Σ|c_i|²·Toeplitz(g₀)| ≤ ηΣ|c_i|² (off-diagonal ≤ δA²).
- Large-support refutation of CC Sonin-trace domination at cutoff Λ = 1: odd mean-zero two-packet φ(x−L) − φ(x+L) has trace → 2Q_{τ₁}(φ) < 0.
- Pole-free four-packet: nodes (L,−L,2L,−2L), coeffs (1, −1, −w, w), w = 1/(2cosh(L/2)), kills ∫g, ∫g e^{x/2}, ∫g e^{−x/2} (identity e^{2u} − e^{−2u} = (e^u − e^{−u})2cosh u) — still negative.
- Dyadic nodes 4^k·(±1,±2) injective, separation ≥ 1 ⇒ d-dim linearly independent pole-free mean-zero subspace with uniformly negative trace ⇒ INFINITE negative Morse index at cutoff 1; fails on every finite-codimension moment subspace.
- Positive survivor at Λ > 1: physical+Fourier shells P_Λ − P_1 inject trace budget 2 log Λ ∫|g|²; profiles in (−ε,ε), ε < log Λ/(‖G_Λ‖₁ + 1) ⇒ uniform multi-packet CC domination at cutoff Λ for every c (large separation). DICHOTOMY: ∀Λ>1 ∀ finitely many moment constraints, one test g fails cutoff-1 and satisfies cutoff-Λ domination. Cutoff 1 is a sharp boundary.
- Operator constraints: any zero-free-gauge self-adjoint Hilbert–Carleman realization of Ξ (Ξ = H·det₂(I − zK)) lies in S_q ∀q>1, not S_1, not weak S_{1,∞}; log-enhanced weak trace with residue 1/π; Σ_{n<N}s_n ~ (log N)²/(2π). Finite prime Euler Gram combinations noncompact; Sonin principal-relative ideal ⊂ S_1; raw linear-prime nuclear source not summable; S(T) unbounded; unitary S with det S = ΠS_ii is diagonal with unimodular entries (no central p^{−1/2} Euler weights from unitary producers).
- CCM finite-packet D_log dichotomy holds; real-rooted full ground states exist at every aperture; RH ⇔ restricted Weil source quadratic ≥ 0 on real-rooted form-domain vectors; Gaussian-growth or Poisson-balanced real-rooted ground-state sequences force RH (criteria, not proofs).
## SquareRootThresholdPrimeTailAndSelbergTwistSpectrum (re-exports)
- RH ⇔ Re Π_f(ξ) ≤ Re A_f(ξ) ∀a,f,ξ ⇔ 2×2 CCM pole compression |cross(a)| ≤ diagonal(a) ∀a. Unconditionally arch-pole budget cannot be frozen at height 0 (∃ f with Re A_f(0) < 0 and < Re Π_f(ξ)). Every C²_c profile: Re W(S_ξ f) ≥ 0 for |ξ| ≥ Ξ(f).
- Windowed variance (2re^{2a} ≤ 1): mean square of W − A = ‖η‖²V_f, off-diagonal prime correlations vanish; V_f ≤ 2‖f‖⁴·2a(2a+C).
- Selberg class Bohr mean selects degree resonance m^{d_G} = n^{d_F}; twist spectra discrete with right gaps; θ₃'(i)/θ₃(i) = i/4.
## TheLinearWindowOfTheCriticalPrimeChannel
- Limit form P∞(b) ≤ −(4/(7000π⁴))Σb². Atom: P(b) = Σ_r Λ(r)/r ∫₁^∞ v^{−2}B(v)B(rv); dilation correlation = (4/π⁴)Σ_{k,l}w_kw_l∫v^{−2}h_k(v)h_l(rv); limit keeps only resonances k = lr with pattern masses J_k; limit correlation |C∞(r)| ≤ (4/π⁴)(7/4)(4E)/r².
- Box–tail estimate for doubly weighted series |ΣF| ≤ AW² + 2CWτ_K.
- Large dilations: |corr| ≤ (4/π⁴)K_W√(2/r)Σb² on [N,2N] window; tail σ_R = Σ_{r>R}Λ(r)r^{−3/2}.
- THEOREM: ∃δ>0, N₀: on every linear window N ≤ m+1 ≤ (1+δ)N (dimension ~δN, growing linearly), criticalPrimeEnergy ≤ −(2/(7000π⁴))Σb² (negative definite uniformly in dimension). Cutoff order: prime R, harmonic K, width δ, threshold N₀. Arbitrary accuracy: ∀η ∃δ,N₀: |P − P∞| ≤ ηΣb² on linear windows.
- Full linear window support Icc(N−1, N−1+⌊δN⌋), dim > δN: P strictly negative definite.
- PRIME SUBSIDY: on linear windows −2P ≥ (4/(7000π⁴))Σb² (prime channel HELPS); arithmetic channels ≥ (4/(7000π⁴) − |Ω(0)|U − 2304/N)Σb²; complete critical energy ≥ (s_crit(log N − c₀) + 4/(7000π⁴) − |Ω(0)|U − 2304/N)Σb². Polar decays O(1/N). NOTE: |Ω(0)|U still not beaten by 4/(7000π⁴) alone — log N archimedean gain still needed.
## WideWindowSelectivityAndBeurlingInfrastructure (Open Problem §7.7)
- Shifted pair ζ(s−a)ζ(s+a), weight Λ_a(n) ≥ Λ(n)n^{|a|}: for every a ≠ 0, nonneg bump g ⊂ [−1/4,1/4], horizon L₀, ∃ wide shift L > L₀ with window sum > pole+arch budget and Weil functional NEGATIVE on g + g(·−L). Proof: Laplace transform at σ = 1/2 + |a| of window sums vs shift majorant contradicts divergence of ΣΛ(n)/n.
- Window-ring majorant (Λ_a(r)/r)min(1,√(L/r)) diverges for |a| ≥ 1/2 on every window.
- Shifted-pair harmonic charge A_a(m) = χ(m)Σ_{d|m} dΛ_a(d)χ(m/d): A_a(2) = −2log2(2^a + 2^{−a}) unique negative; zero at m = 1 and 4|m; positive for m > 2, 4∤m; A_a(p) = p log p(p^a + p^{−a}). A_0 = 2·(ζ charge). Cumulative cubic charge: ζ (a=0) negative at N = 2,3,4; |a| ≥ 2 positive for N ≥ 3; |a| ≥ 1 positive for N ≥ 5. Σ A_a(m)/m³ diverges for |a| ≥ 2; Σ A_a(m)J_m/m⁴ diverges for |a| ≥ 3 (ζ: converges to ≤ −(log2)/390).
- TEMPERED WEIGHTS: |w(r)| ≤ CΛ(r) (no multiplicativity/sign needed): |weighted prime energy| ≤ C·C_TW(3+log L)Σb² uniformly in V ⇒ polynomial-window Weil positivity on critical family for ANY tempered w (Liouville twist λΛ, Λ·1_{r≠4}, primes-only, bounded Beurling perturbations). Beurling systems with off-line zeros (RH sensitivity threshold) are INDISTINGUISHABLE from ζ on the critical family. Re W_w(g^V) = Q_Λ(g^V) + 2P_Λ − 2P_w exactly.
- Fixed V: g^V supported in [−log 2V, 0], only r ≤ 2V enter ⇒ for EVERY weight w (incl. shifted pair) positivity holds for M ≥ M₀(w,V). Separation between tempered and shifted-pair weights is UNIFORMITY IN V (quantifier order).
- Tempered polynomial-window positivity: δ = s_T/(4(C·C_TW + 1)), M₀ depending on C only; Re W_w(g^V) ≥ (s_T/4)log M Σb² for all V ≥ threshold.
- Beurling synthesis: tempered weights pass critical-family positivity; Beurling densities with arbitrarily small reciprocal mass have off-line zeros; node-criticality (ZeroPoleBlindPositiveOn) refutes deleting 4 (price −(log 2)/2) and primes-only — the critical family is NOT selective, node-deletion tests ARE.
- Fixed V: |P_w| ≤ (Σ_{r≤2V}|w r|)(4/π⁴)K_W Σb²; ∀V ∃M₀(w,V) positivity with (s_T/2)log M.
## ZeroDiskOverlap
- Multiplicity-exact radius-1/4 disk overlap of Ξ divisor ≤ C(1 + log(2+|Im s|)) on strip −1/4 ≤ Re s ≤ 5/4, zero outside.
