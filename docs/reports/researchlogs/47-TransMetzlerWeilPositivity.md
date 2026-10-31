# 47 TransMetzlerWeilPositivity — facts log

## ExplicitPlateauParameters (uses CACT SmoothPlateausRecoverTheCompletedRobinMargin, RAPT TheCompleteWeilTrialEnergiesAreSimpleAndProper, ThePoleMomentsHaveQuadraticDilationError, ALG TheMetzlerThresholdOfTheOverlapRatioIsOne)
- Real.smoothTransition has derivative in [0, 4] (expNegInvGlue' = x⁻²e^{−1/x} ≤ 4e⁻², denominator ≥ e⁻²); 4-Lipschitz.
- transMetzlerProfile = plateau(1/1000): C^∞, support [0,1], 0 ≤ φ ≤ 1, φ(0) = 0, φ > 0 on (0,1), 8000-Lipschitz. Parameters δ₀ = 10⁻¹⁸, c₀ = 1 + δ₀, ρ₀ = 1 + δ₀/2.
- For every ρ > 1 the atomic Markov Gram at width ρ·atomSpacing N is eventually frustrated: no unimodular gauge makes it Metzler (ALG overlap-ratio threshold is exactly 1).
- ∫φ, ∫φ² ∈ [499/500, 1]; variance ∫φ² − (∫φ)² ≥ 1/128000 (left transition layer: φ ≤ ¼ on [0, 1/32000]); charge deficit 1 − completeWeilPoleShift φ 1 ≥ 1/128000; atomPoleMomentErrorConstant ≤ 6.
- log 2π < 1839/1000. completeWeilAdjunctionEnergy(φ, c, m) > 1/20 for all c ∈ (0, 1 + 1/1000], m ≥ 1 (completed shape > 1.908; −log c + c q ≥ q − 1/1000; higher conductors have larger adjunction energy, log 2 gap).
- bumpRobin φ 1 ≤ 1.045, β/‖φ‖² ≤ 21/20, e^{21/20} < π ⇒ Robin–Euler ratio e^{β/‖φ‖²}/(2π) < ½.

## TransMetzlerDecomposition (uses CACT OverlapLengthControlsTheTouchingCrossError, RAPT TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum, SSHA TheRowsAtBoundedOverlap, ALG ThePoleDefectPaysThePole)
- Geometry at width w ≤ 5/(4N), N ≥ 16: pairs with |n − j| ≥ 2 and lower-half pairs (2 max ≤ N) are strictly separated; every overlapping distinct pair is adjacent (j = n ± 1), lies in the top third (N < 3n, 3j), and has log gap ≥ 1/N.
- Top-third mass Σ_{3n>N} x_n² ≤ (6/log(N/3))(poleDefect + ψΣx²) (defect pays with a 1/log saving).
- Quadratic forms supported on overlapping pairs with entries ≤ B: |Σ a_n a_j F| ≤ 2B·top-third mass (each row has ≤ 2 overlapping neighbours).
- separatedCrossErrorKernel (cross error only on separated pairs): ≤ 316 w² max(n,j)²/|n − j|²; form ≤ 1264(wN)²‖x‖². poleMomentErrorCoeff ≤ 6w², form ≤ 12(wN)²‖x‖².
- transMetzlerMainMatrix w c* N = (log N + selfFinitePart(c*) − γ)I − fullPrimeMatrix + center(c*) − separated cross error + pole error; Hermitian; every normalized Ramanujan vector is a norm quasimode with eigenvalue completeWeilAdjunctionEnergy(φ, c*, m) for any width schedule 0 < w_N ≤ 2/N.
- Non-ratio term at 1/(2N) ≤ w ≤ (1 + δ)/N: overlap length ≤ (δ + 2/N)/N (log gap ≥ (1 − w)/N) ⇒ |term| ≤ 3(δ + 2/N)·mass·upInd; |nonRatioForm|/mass ≤ 1050(δ + 2/N)(poleDefect + Σa²).
- Numerics at ratio 5/4: e^{5/2} < 13, e^{3/2} < 9/2, log 4 < 7/5, ψ ≤ 4; nonRatioRow ≤ 192 + (45/4)(m/N)log m; Σ a²·row ≤ 350(poleDefect + Σa²).
- Center at charge 1: |⟨center(1)x, x⟩| ≤ 2·poleDefect + (2ψ + 15)‖x‖² (pole projection change ≤ 12‖x‖²; harmonic-zero part = −collar/N, collar paid by top-row defect).
- levyMixed(atom n, atom j) = levyMixed(g, g(· − |log j − log n|)) by translation; separated pairs: ∫ levyMixed = −atomCrossTerm. levyEnergy(atomic test) = Σ a_n a_j ∫ levyMixed(atom n, atom j) (bilinear at any width).
- Adjacent overlapping pair at 1/(2N) ≤ w ≤ (1+δ)/N: short shifts (0, 2w]: |levyMixed| ≤ 16000 (Cauchy–Schwarz + 8000/w Lipschitz + density ≤ e^{1/2}/(2y)), integral ≤ 32000w, normalized ≤ 64000. Long shifts y > 2w: cross products vanish, levyMixed = 2·bumpCorr(|log j − log n|)·density(y).
- Long-shift density tail: 2∫_{y>2w} density ≤ log N + selfEnergyConstant + 32000 (via levyEnergy of the 2w-dilate, disjoint far shifts). Adjacent overlap autocorr/mass ≤ 3δ (overlap length ≤ δ/N, mass ≥ 1/(3N)). Adjacent mixed Lévy/mass ≤ 3δ log N + 3δ(selfEnergyConstant + 32000) + 64000.
- normalizedFullWeilHorizonMatrix entry = markovPair(atom n, atom j)/mass + (pole moment product/mass)·arithmeticPoleKernel, at any width.
- exists_perturbation_bound_transMetzler: ∃ C_short; for N ≥ 27, 0 ≤ δ ≤ ¼, c* ≥ ½, 1/(2N) ≤ w ≤ (1+δ)/N, |wN − c*| ≤ 2/N: |⟨W x, x⟩ − ⟨main(w, c*) x, x⟩| ≤ (2000δ + C_short/log(N/3))(poleDefect + ‖x‖²).
  Exact difference = scalar drift [(levyEnergy/mass − log(1/w) − Robin) + (log c* − log wN), ≤ 6/N] + Gamma × off-diagonal Gram overlap + (wN − c*)·charge·center(1) − nonRatioForm/mass + overlapping-pair Lévy/center residue. Off-diagonal overlaps live in the top third (paid by 24/log(N/3)).
- Five pieces: scalar drift ≤ 6/log(N/3); Gamma × off-diagonal Gram ≤ 96|γ_H(0)|/log(N/3); center drift ≤ 50/log(N/3); non-ratio ≤ 1050δ + 2100/log(N/3); overlapping Lévy + center collar ≤ 288δ + 48(selfEnergyConstant + 96001)/log(N/3) (center kernel entry on adjacent pairs ≤ 1). Total 1338δ + C_short/log(N/3).

## TransMetzlerPositivity
- Main matrix coercivity for c* ≤ 1 + 1/512000, 0 < w_N ≤ 2/N: ⟨main x, x⟩ ≥ −2100000‖x‖² + (1/1024000)·poleDefect (charge ≤ 1 − 1/256000 from variance deficit; center lower bound with λ = 512000; self finite part ≥ −3).
- Main matrix eigenvalues ≥ 1/25 eventually (defect bounded ⇒ coordinate mass ≥ 1/18 on finite S; quasimode residuals with energies > 1/20 kill it).
- Floor + defect: ⟨main x, x⟩ ≥ (1/60)‖x‖² + 10⁻¹⁴·(1/1.0752)·poleDefect.
- eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near: c* ∈ [½, c₀], widths 1/(2N) ≤ w_N ≤ c₀/N with |w_N N − c*| ≤ 2/N ⇒ eventually PosDef with eigenvalue floor 1/120 (perturbation coefficient ≤ 4·10⁻¹⁵ absorbed by the defect reserve).
- eventually_completeWeilMatrix_posDef_cZero; eventually_weilQuad_atomicTest_nonneg_cZero; exists_gt_one_eventually_completeWeilMatrix_posDef: ∃ c > 1 and C^∞ φ ≥ 0, support [0,1], φ > 0 on (0,1), with eventually PosDef complete Weil matrix and weilQuad ≥ 0 on all atomic tests.
- eventually_completeWeilMatrix_posDef_of_mem_Ioc: every fixed c ∈ (0, c₀] (c < ½ via spectral count: adjunction energies > 1/20 ⇒ empty sublevel below 1/25). Also at c = 1, at width atomSpacing N = log(1 + 1/N), and at ρ₀·atomSpacing N together with Markov-Gram frustration (no unimodular gauge makes it Metzler) — positivity beyond the Metzler threshold.

## OptimizedTransMetzlerFloor
- certifiedDefectLoss K = 1 + 1024000(2100000 + 1/25); floor 1/25 − 2000Kδ; certifiedOverlapIncrement = 1/107520002048050000. Convex interpolation lemma: floor ≥ 1/25 − K·e from mass floor + coercivity + perturbation e(D + M); attained by a scalar example (optimal for these three estimates).
- eventually_completeWeilMatrix_posDef_certified: PosDef at c = 1 + δ for every 0 ≤ δ < 1/107520002048050000. Boundary concerns the estimates, not the actual sign.

## TransMetzlerReferenceFloor
- transMetzlerReferenceFloor c = selfFinitePart(c) + poleShift(c) = completeWeilAdjunctionEnergy(c, 1) (no Euler offset). Young family coercivity: (reserve(c, λ) − ε)·defect − (massLoss(c, λ) + ε)‖x‖² ≤ main form, reserve = 1 − q(c)(1 + 1/λ), massLoss = 1276c² + q(c)((1+λ)ψ + 15) − selfFinitePart(c).
- If q(c) < 1, conductor one minimizes all adjunction energies (others exceed by ≥ log 2 − …). Every μ < referenceFloor(c) is an eventual eigenvalue floor of main(c/N, c, N) for 0 < c ≤ 2 with q(c) < 1; the conductor-one quasimode attains it.
- Charge q(1) ∈ [99/100, 1). referenceFloor(c) = referenceFloor(1) − log c + (c − 1)q(1); > 1/25 for c ≥ 1 with q(c) < 1 (then c < 100/99). Self finite part < 0 for c ≥ 1 (Robin–Euler < ½ ⇒ β/‖φ‖² < log π).

## TransMetzlerYoungOptimization (uses HTGeometry OptimalYoungDefectFloor)
- Optimized Young family (parameter λ = q/x): reserve r − x, mass loss A/x + R with A = q²ψ, R = 1276c² + q(ψ + 15) − selfFP. Optimal defect root D*(c) = YoungDefect.scale; optimizedFloor(c) = referenceFloor(c) − 2000(c − 1)(1 + D*²).
- Every strict relaxation of optimizedFloor(c) is an eventual quadratic floor of the actual complete matrix wherever optimizedFloor ≥ 0.
- optimizedFloor strictly decreasing on the charge-reserve interval; positive at c = 1; negative at c = (1 + 1/q(1))/2 ⇒ unique zero transMetzlerCertifiedBoundary ∈ (1, 1/q(1)) (IVT, no numerics). PosDef for every 1 ≤ c < boundary.
- transMetzler_young_positive_certificate_iff: a positive uniform floor certificate from (reference floor, every Young bound, perturbation 2000(c − 1)(D + 1)) exists iff c < boundary (scalar witnesses; not a statement about actual signs beyond).
- No eventual floor of the main matrix exceeds referenceFloor(c) (test on the conductor-one quasimode).
- Explicit: referenceFloor(1) > 69/1000; optimizedFloor(1 + 10⁻¹⁶) ≥ 1/200 ⇒ boundary > 1 + 10⁻¹⁶; eventual floor 1/400 at c = 1 + 10⁻¹⁶.

## LiouvilleTwinSelectivity (uses RAPT TheArchimedeanFinitePartIsMinusLogTwoPi, TheAtomCrossMatrixIsCloseToItsCenterKernel, SMAP ThePoleHyperplaneSeparatesTheFullWeilForms, ALG TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing)
- robinEulerThreshold φ = e^{β(φ)/‖φ‖²}/(2π): overlap ratio where the Markov ground energy on the harmonic hyperplane changes sign. < ½ for transMetzlerProfile.
- Liouville twin λΛ: Dirichlet series ζ(2s)/ζ(s) has no pole at 1 in its prime gauge; its prime form reaches log M − γ + o(1) on the harmonic hyperplane Σ x_n/√n = 0 where both pole moments vanish.
- Fejér–Abel: Σ_{d≤M} cos(dθ)/d ≥ −4 for all M, θ (cos ≥ 0 for d|2 sin(θ/2)| ≤ 1; Abel summation with Dirichlet-kernel bound |D_k| ≤ 2/δ beyond).
- Σ_{n≠j} b_n b_j/|n − j| ≥ −8Σb² (integrate (4 + Σcos(dθ)/d)·|Σ b_n e^{inθ}|² ≥ 0 over [0, 2π]); Σ_{n≠j} b_n b_j/(n + j) ≥ −½Σb² (Hankel moments ∫₀¹ t(Σ b_n t^{n−1})² ≥ 0).
- center kernel/(√n√j) = ½(1/|n − j| + 1/(n + j)) ⇒ sum_archimedeanCenterKernel_ge: Σ x_n x_j center(n, j) ≥ −(17/4)Σ n x_n².
- Bounded-pole vectors (n x_n² ≤ 4): off-diagonal cross-error majorant Σ |x_n||x_j| max²/|n − j|² ≤ 56M² (Σ 1/d² ≤ 2).
- exists_bounded_hyperplane_liouville_witness: for ε > 0, eventually in M a vector x on [1, M] with Σ x_n/√n = 0, n x_n² ≤ 4, Σx² ≥ log M − 2, and twisted prime form atomicWeilForm(λx) ≥ (log M − γ − ε)Σx². Construction x = (λ(n) − s)·truncPole, s = (Σ λ(n)/n)/H; |Σ λ(n)/n| ≤ 2 keeps the correction small.
- Sub-horizon upper bound for the twin's complete form (pole moments vanish on the hyperplane): ≤ mass·[(log(1/(2π wM)) + β/‖φ‖² + ε + e^{1/2}w/2)Σx² + 17q(wM) + 56K₀(wM)²]. Center contribution ≤ 17q·wM (Fejér–Abel bound), cross error ≤ 56K₀(wM)².
- eventually_liouville_weilQuadTw_neg_of_gt_robinEuler: φ C² on [0,1], robinEulerThreshold φ < 1, fixed c > threshold, widths w_N with w_N N → c ⇒ eventually the Liouville twin's complete Weil form is strictly negative on some atomic test of width w_N. Proof uses sub-horizon dilution M_N = ⌊(c'/c)N⌋ with c' ∈ (threshold, 1), margin μ = log(c'/threshold): log(1/(2π c')) + β/‖φ‖² = −μ < 0 while the Σx² ~ log M term dominates the O(wM) corrections.
- Corollaries: eventually_liouville_weilQuadTw_neg_transMetzlerProfile — for transMetzlerProfile the twin is eventually negative at every fixed c ≥ ½, both at widths c·atomSpacing N and c/N (incl. c = 1 and c₀ > 1 where ζ is positive). Thin plateaus: robinEulerThreshold(plateau η) → e/(2π) ≈ 0.4326 as η → 0; every c > e/(2π) has a plateau with eventually negative twin form. Narrow-width survival: at c·atomSpacing N with c ≤ fixedWidthRatio the twin's form is nonnegative on all atomic tests for every N ≥ 1 (twin Markov + pole nonnegativity).

## EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio (uses ArithmeticCountingPositivity CofinitePrimeFlipsHaveZeroGap)
- Sign twin ω: completely multiplicative, ±1, bounded harmonic sums |Σ_{n≤M} ω(n)/n| ≤ B (no pole at s = 1). Witness x = (ω − s)·truncPole, s = S/H: hyperplane, n x² ≤ 4, Σx² ≥ log M − 2, twisted prime form ≥ (log M − γ − ε)Σx² (corrections O(B²)). Below spacing the gauge is a congruence: twin's complete form on sub-horizon witnesses = Markov form; same sub-horizon upper bound as Liouville.
- eventually_signTwin_weilQuadTw_neg_of_gt_robinEuler; eventually_signGauge_weilQuadTw_neg_of_gt_robinEuler (IsSignGauge + bounded gaugeHarmonicSum); eventually_cofiniteFlip_weilQuadTw_neg_of_gt_robinEuler: flipping all primes outside a finite F (Liouville = ∅) leaves a pole-free gauge (B = 2/c_F) whose complete form is eventually negative above the Robin–Euler ratio.

## ZeroSideStratum (uses HKT EveryReceiverAtEveryWidthIsBoundedByTheIndex, AID TheSectionComplementCarriesAllNegativeSquares, SRT WindowedPositivityNoGoForOffLineConfigurations, SSHA TheWeightOfOneZero)
- unconditional_transMetzler_positivity_interval: c₀ > 1 and every c ∈ (0, c₀] has eventually PosDef matrix and weilQuad ≥ 0 on atomic tests.
- Under RiemannHypothesis (as hypothesis): weilQuad(atomic test) ≥ 0 for every c > 0, N ≥ 1, C² profile on [0,1] (RH ⇔ real Weil positivity).
- atomicShiftWeilGram φ w N (complex Weil Gram of shifted atoms); its Hermitian form on real vectors = weilQuad of finAtomicTest.
- Finite off-line support (rightZeros zetaZeroConfig finite) ⇒ hermNegIndex(atomicShiftWeilGram φ (c/N) N) ≤ #rightZeros, uniformly in c > 0, N ≥ 1, φ.
- Cauchy–Schwarz: N² ≤ (Σ n^σ)(Σ n^{−σ}). re_Wsummand_atomicTest_const_one_ge: a real zero ρ (Im ρ = 0, Re ρ ≥ ½) on x ≡ 1 with nonnegative φ contributes ≥ m_ρ e^{−(Re ρ−½)c/N}((∫φ)²/∫φ²)·c × diagonal energy — the linear factor c in the single-zero upper bound is sharp.
- twoAtomWitness x₁ = 1, x₂ = −1: Dirichlet polynomial 1 − e^{iz log 2} vanishes on the vertical lattice ½ + 2πik/log 2. isolatedPairConfig (lattice spacing log 2, off-line pair ½ ± δ, 0 < δ ≤ ½): tempered, rightZeros = {offLinePoint δ 0}, yet Re W(f,f) = 2·A₊A₋(1 − 2^δ)(1 − 2^{−δ}) < 0 at every c > 0, N ≥ 2 (A± = ∫g e^{±δu} > 0 for nonnegative g). Fixed-ratio positivity cannot be deduced from temperedness + finite off-line support + single-zero bounds; ζ's growing zero density log T/(2π) is needed.

## SuperGevreyCriticalGrowth (uses SSHA TheDenjoyCarlemanProfiles, HTGeometry UniformCauchyLimit/UniformIteratedDerivLimit)
- Goal: one fixed smooth profile steklovDCProfile, built from dilate 2 (dcProfile 1) by infinitely many Steklov averages with radii a_m = 1/(4(m+3)log²(m+3)) (Σa_m < ½); C_c^∞([−1,1]), unit mass; ∫|φ^{(q)}| ≤ A·12^q q! (log(q+3))^{2q} — below every Gevrey class (q!)^{1+ε}, still non-quasianalytic. For every β > 2, RH ⇔ eventual weilQuad ≥ 0 on its atomic families at c_N = (log log N)(log log log N)^β, and c_N = o((log log N)^{1+ε}).
- Steklov average S_a f(x) = (2a)⁻¹∫_{−a}^{a} f(x+t)dt: derivative (2a)⁻¹(f(x+a) − f(x−a)); commutes with iterated derivatives; preserves sup bounds; |(S_a f)'| ≤ a⁻¹ sup|f|; |S_a f − f| ≤ a sup|f'|; support grows by a.
- Steklov averaging preserves total integral (for compactly supported continuous f).
- steklovRadius m = 1/(4(m+3)log²(m+3)) ≤ T(m) − T(m+1), T(m) = 1/(4 log(m+2)); so Σ_{K≤m<M} a_m ≤ 1/(4 log(K+2)) and Σ_{all} a_m ≤ ½ (log 2 > ½).
- dcLogWeight q = q!·log(q+3)^{2q}: W₀ = 1, monotone, submultiplicative W_l W_{i−l} ≤ W_i, W_p ≤ (p log²(p+3))^p; Π_{j<q} a_j⁻¹ ≤ 12^q W_q.
- steklovSeq: base dilate 2 (dcProfile 1) (support [−½,½], mass 1, sup ≤ 2/∫dcBump 1), steklovSeq(m+1) = S_{a_m} steklovSeq m. All supported in [−1,1], mass 1; |∂^q steklovSeq m| ≤ sup·Π_{j<q} a_j⁻¹ for q ≤ m (each average costs one derivative a_j⁻¹). Step m → m+1 moves ∂^q by ≤ C_q a_m (q+1 ≤ m) ⇒ uniform Cauchy in every derivative (tail ≤ C_q/(4 log(K+2))).
- steklovDCProfile = uniform limit; C^∞, vanishes off [−1,1], ∫ = 1, |∂^q| ≤ sup·12^q W_q, ∫|∂^q| ≤ 2·sup·12^q W_q.
- Euler–Maclaurin machinery generalised to weights W_q: logTower L¹ bounds with W_{j+p}; Leibniz product bound M·A·W_i(b + B')^i via submultiplicativity; abs_dcLogSynth_sub_le: atomic EM synthesis error ≤ M A ((2m+2) log²(2m+5) (b + Bk + 2m+2)/n₀)^{2m+2}.
- dcSynthErr / dcSynthRatio: synthesis error at EM order m = gevOrder k (= ⌈log log k⌉); OverlapGrowthSuperGevrey κ: κ → ∞ and (N/κ_N)/(log log κ · (log log log κ)²) → ∞. Key estimate: p log²(p+3) ≤ 24·(log log k)(log log log k)² for p = 2·gevOrder+2, so ratio ≤ O(log⁴N/n) + O(B/(overlap/W)) → 0; ratio ≤ e^{−1} makes ratio^p ≤ 1/log²k.
- nonneg_iff_atomicFamilies_nonneg_of_stable_superGevrey: for any StableForm Φ and φ with ∫|φ^{(q)}| ≤ A B^q W_q: global nonnegativity ⇔ eventual nonnegativity on atomic families at super-Gevrey overlap. Proof: mollify a negative g by φ (stays negative, inherits W_q bounds), then EM-synthesise at κ along N = nB.
- riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey (weilQuad stable). superGevreyRatio β N = (log log N)(log log log N)^β = o((log log N)^{1+ε}); β > 2 ⇒ N/superGevreyRatio is super-Gevrey overlap. riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey: RH ⇔ eventual weilQuad ≥ 0 on steklovDCProfile atomic families dilated by N/superGevreyRatio β N, any β > 2.

## TheFixedProfileReachesAnIteratedLogEndpoint
- endpointSuperGevreyRatio N = L(log L)² log log L, L = log log N; below every L(log L)^β, β > 2; height N/ratio → ∞. Same receiver; improves synthesis requirement only.
- riemannHypothesis_iff_steklovDCProfile_nonneg_endpoint: RH ⇔ eventual weilQuad ≥ 0 on steklovDCProfile atomic families at the endpoint overlap L(log L)² log log L (= o(L(log L)^β) ∀β > 2).

## FixedOverlapHasLogarithmicDivisorRows (uses CACT ExactSuccessorShellWindows, RAPT TheArchimedeanCrossTermsVanishOnPeriodicProfiles)
- weightedDownwardDivisorFiber g m ℓ = Σ_{k|ℓ} Λ-atom(k)·√(m/(ℓ/k))·bumpCorr g(log k − log m + log(ℓ/k)). With Schur weights n^{−½} all divisors of ℓ share lag log ℓ − log m and their Mangoldt weights sum to log ℓ: fiber = √(m/ℓ)·log ℓ·bumpCorr g(log(ℓ/m)).
- Successor divisors: each k | N+1, k ≠ 1, gives (N+1)/k ∈ [1, N] with N ≠ k·(N+1)/k — genuine non-ratio edges.
- bumpCorr(atomDilate φ w)(t) = w·bumpCorr φ(t/w); transMetzlerProfile autocorrelation > 0 for |t| < 1.
- plateauSuccessorFiber c N (row N → product N+1, mass-normalised) = √(N/(N+1))·log(N+1)·bumpCorr(firstExteriorOverlap N / c)/‖φ‖²; /log(N+1) → bumpCorr(1/c)/‖φ‖²; → ∞ for every fixed c > 1 (weighted row statement, not an operator norm).

## TheSuccessorFiberHasAnExactOpenThreshold (uses CACT BoundaryVanishingControlsTheTouchingAutocorrelation)
- transMetzlerProfile bumpCorr(t) > 0 ⇔ |t| < 1 (endpoint value 0 via |bumpCorr| ≤ (8000²/4)(1−|t|)²).
- plateauSuccessorFiber c N > 0 ⇔ firstExteriorOverlap N < c (= N log(1+1/N) < 1); zero at or below. Touching c = 1: positive at every N ≥ 1 but ≤ (8000²/4)·log(N+1)/N²/‖φ‖² ≤ const/N → 0. Every fixed c < 1: eventually exactly zero.

## FactorialSuccessorsForceUnboundedPrimeCorrections (uses CACT TheNonRatioMatrixIsTheActualPrimeCorrection, RHTower Sieve PrimeLogSqLower)
- Horizon N = 2·Y! − 1: every prime p ≤ Y gives the successor edge p·2(Y!/p) = N+1; coordinates 2(Y!/p) distinct, in [2, N], non-dividing with N.
- fullWeilNonRatioMatrix entry (N, 2Y!/p) ≥ plateauSuccessorCorrelation c N·(log p/√p) (prime pair term survives subtraction of the exact-ratio kernel; nonnegative profile so one shift lower-bounds primePair).
- factorialSuccessor_action_sq_ge: ‖A e_N‖² ≥ q_c(N)²·Σ_{p≤Y}(log p)²/p (A = fullWeilNonRatioMatrix, Hermitian). Σ(log p)²/p ≥ ½log²Y − 39 log Y − 25 → ∞. So ‖A e_N‖ → ∞ along N = 2Y!−1 for every c > 1.
- eventually_bounded_fullWeilNonRatio_action_iff: eventual Euclidean boundedness of the actual plateau non-ratio prime matrix ⇔ c ≤ 1 (on c ≤ 1 it is even eventually small uniformly). Sharp boundary at touching; says nothing about the sign of the complete matrix.

## CompleteWeilLengthHeight (uses SSHA OverlapCoordinates, RAPT OverlapForcesNewRamanujanTerms)
- completeWeilMatrixAtHeight φ N T = normalized full Weil matrix at width T⁻¹; at T = height N c = N/c equals completeWeilMatrix φ c N.
- Every fixed overlap 0 < c < 1 + certifiedOverlapIncrement: eventually PosDef at T = N/c; certified floor transports. overlap X T < 1+δ* ⇔ X < (1+δ*)T — the excess is a linear length excess.
- Plateau diagonal after removing the prime log: |2γ_H(0) + levy/mass − log N + log c − (finitePart(1) − γ)| ≤ (e^{½}/2)(c/N) — self-energy loses log c.

## SuperGevreyLengthHeight
- superGevreyHeight β N = N/c_N. c_N → ∞; log c_N / log N → 0; log T_N ~ log N; bandwidth log N/log T_N → 1 (same limiting bandwidth as every fixed overlap); c(T_N) ~ c(N) (asymptotic only); N ~ T_N·c(T_N); N < T_N^α eventually for every α > 1. RH ⇔ steklovDCProfile receiver nonneg at height T_N.

## ThePlateauOverlapGramIsNondegenerate (uses SSHA TheGaugeEntersThroughNonRatioLags)
- Any nonzero coefficient vector synthesises a nonzero plateau test at any width w > 0 (isolate the first nonzero coefficient just right of its center, before the next center): ∫(atomic test)² > 0; the full overlap Gram Σ x_m x_n bumpCorr(log m − log n) is strictly positive definite at every width. No uniform lower bound.

## GrowingOverlapHasNoUniformGramFloor (uses SSHA TheUniversalThresholdIsFinite)
- Adjacent dipole e_N − e_{N+1} (coefficient mass 2): normalised synthesised mass = 1 − C_φ(t)/C_φ(0), t = adjacentProfileLag = (log(N+1) − log N)/(c/(N+1)) ≤ 2/c. For c ≥ 2: ratio ≤ 4·8000²/(‖φ‖² c²). Overlap c_N → ∞ ⇒ t → 0 ⇒ ratio → 0: no uniform Gram floor under growing overlap.
- no_uniform_plateau_atomic_mass_floor: along any c_N → ∞ there is no ε > 0 with ε·mass(atom)·Σx² ≤ ∫(atomic test)² eventually (adjacent dipole witness).

## APositivePrefixGivesTheExactSchurReduction (uses CACT OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching)
- Coordinates split [1,N] = prefix [1,M] ⊔ tail (M, N]. Principal prefix block of completeWeilMatrix φ c N = completeWeilMatrix φ (cM/N) M (same physical width c/N).
- eventually_plateau_posDef_uniformly_through_touching: one M₀ such that for all M ≥ M₀ and all d ∈ (0,1], completeWeilMatrix d M is PosDef (eigenvalues ≥ 1/25; adjunction energy at c = 1 > 1/20).
- Prefix block PosDef whenever cM ≤ N, M large. Then (exactly, via Schur complement) completeWeilMatrix c N PSD ⇔ plateauPrefixSchur = tail − mixedᴴ·prefix⁻¹·mixed PSD; the subtracted cost is PSD. Schur complement retains every mixed prime, Gamma, polar entry.

## BoundedOverlap/ElevenFlipAtEveryHorizon (uses BoundedOverlap/ElevenFlipNegativity)
- primeFlipWeight 11 (flip the prime 11): witness x_n = primeSquareTrial 11 n/√n at width r_N/H_N with r_N → 99/100: twisted complete form eventually < 0; normalised limit = ‖φ‖²·elevenTrialUpperMargin < 0 (margin = completeWeilSelfFinitePart(99/100) + 4log11/11 + poleShift(99/100)(101/121)² − 4 log 11/11 + 4 log 11·(2/11³ + 1/(11²·10))).
- Rounding H = ⌊(99/(100c))N⌋ and zero padding: every fixed ratio c ≥ 99/100 (incl. c = 2 and c₀ = 1 + 10⁻¹⁸) eventually has a negative eleven-flip test. So the trans-Metzler positivity at c₀ is ζ-selective against this flip.

## BoundedOverlap/LogarithmicBandMass (uses HTGeometry MontgomeryVaughanIntervalMeanSquare, SRT WindowedMeanValueDiagonalLaw, SSHA TheAtomicFamilyIsADirichletPolynomial)
- log n/(2π), n ≤ N, are 1/(2πN)-separated. Interval Montgomery–Vaughan: ∫_N^{101N} |Σ x_n n^{it}|² dt ≥ 48N·Σx_n² (100N − 52N). Band [N, 101N] avoids zero and is uniform in x — a high-frequency Gamma-energy lower bound.

## ReceiverRate/ABoundedOverlapRateSeesASemilocalWindow
- dcRate κ N = (N/κ_N)/(ℓℓ₂²), ℓ = log log κ_N; dcScale N = L(log L)², L = log log N.
- Bounded rate K sees a bounded window: rate ≥ K eventually + atomic nonnegativity ⇒ Weil ≥ 0 on every C² test in [−R, R] with 24e·B_φ·⌈1 + e^{2R+2}⌉ < K (window radius ~ ½ log K; test synthesised on block [N/B, N] whose lowest atoms see overlap c_N/B). Proof: ratio bound gives dcSynthRatio ≤ small + 24B_φB/K < e^{−1}.
- RH ⇔ ∀ K ≥ 1 atomic families at overlap K·L(log L)² are eventually nonnegative; every divergent rate (c_N/(L(log L)²) → ∞, N/c_N → ∞) is an RH receiver.
- dcScale N = L(log L)² is o(N); at overlap c_N ≥ 1 with κ_N = N/c_N → ∞, dcRate ≥ c_N/dcScale N (log log κ ≤ log log N).
- riemannHypothesis_iff_nonneg_of_divergent_rate; riemannHypothesis_iff_forall_bounded_rate (RH ⇔ ∀K ≥ 1 eventual nonnegativity at overlap K·dcScale; a single bounded K gives only a window). steklovDCProfile_window: B_φ = 12, window condition 288e⌈1 + e^{2(R+1)}⌉ < K.

## ReceiverRate/TheCriticalOverlapIsLogLogTimesLogSquared
- dcMajorant B c = inf_q B^q W_q / c^q (Fourier-tail majorant); dcCriticalOverlap B N = least c ≥ 1 with μ_B(c)² log N ≤ 1 (tail energy = Weil weight 1/log N).
- Upper: μ_B(c) ≤ exp(1 − c/(eB log²(c+3))) (take q = ⌊c/(eB log²(c+3))⌋, q! ≤ q^q). Lower (B ≥ 1, c ≥ e): μ_B(c) ≥ exp(−(4ec/log²c + √c log(ec))) (q! ≥ q^q e^{−q}, t log t ≥ −1; split q+3 ≥ √c or not); eventually ≥ exp(−8ec/log²c). μ antitone in c. So log(1/μ_B(c)) ≍ c/log²c.
- norm_fourier_le_dcMajorant: |φ̂(ξ)| ≤ A·μ_B(2π|ξ|), ξ ≠ 0 ((2π|ξ|)^q|φ̂| = |(φ^{(q)})^| ≤ ∫|φ^{(q)}|).
- eventually c*_N ≤ 4eB·L(log L)² (and that value is in the defining set).
- Eventually L(log L)²/(32e) ≤ c*_N (below it μ_B > (log N)^{−1/4}). So c*_N ≍ L(log L)².
- Rate law in critical units: every r_N c*_N with r_N → ∞ (and N/(r_N c*_N) → ∞) is an RH receiver; RH ⇔ every bounded multiple K c*_N eventually nonnegative; a single multiple K ≥ 32e sees the window 24eB⌈1 + e^{2(R+1)}⌉ < K/(32e) (radius ½ log K + O(1)). Steklov case B = 12.

## ReceiverRate/TheSincProductProfile
- sincRadius: r₀ = ¼, r_{j+1} = a_j (Steklov radii, decreasing, ≤ 1/12). boxStek β m = S_{r_{m−1}}⋯S_{r_0} β. Steklov sup ≤ (2a)⁻¹·L¹; linear.
- Peeling: if level k is bounded by B, then |∂^q level m| ≤ B·Π_{k≤j<k+q} r_j⁻¹ (k+q ≤ m). First average of an L¹-≤1 base is ≤ 2 ⇒ |∂^q boxStek β m| ≤ 2Π_{j<q} a_j⁻¹ (m ≥ q+1).
- Mean-zero base h (L¹ ≤ 2, vanishes for |u| ≥ e): after two averages |S² h| ≤ 8e/a₀ (first average = 2(H(y+¼) − H(y−¼)), H primitive supported in [−e, e], |H| ≤ 2).
- boxBase M = unit bump of width a_M (steklovBase dilated), nonnegative, ∫ = ∫|·| = 1. boxSeq M = boxStek (boxBase M) (M+1). |∂^q boxSeq M| ≤ 2Π_{j<q}a_j⁻¹ (q ≤ M). Step M → M+1 moves ∂^q by ≤ C_q a_M (new average + mean-zero base change of width a_M) ⇒ uniformly Cauchy in every derivative.
- sincProfile = uniform limit of boxSeq: C^∞, vanishes off [−1,1] (Σ radii ≤ ¾, base width ≤ 1/12), ∫ = 1, |∂^q| ≤ 2·12^q W_q, ∫|∂^q| ≤ 4·12^q W_q (log-DC class with A = 4, B = 12).

## ReceiverRate/TheSincProfileIsAProductOfSincs (uses HTGeometry NyquistLatticeSum, FourierDecayFromDerivative, FourierFirstOrderWeight, QuantitativeMonomialWallCrossingLaw; RHTower BaezDuarteDistancePlancherel)
- ∫_{−a}^{a} e^{2πitξ}dt = 2a sinc(2πaξ); Fourier(S_a f)(ξ) = sinc(2πaξ)·f̂(ξ) (Fubini).
- 𝓕(boxSeq M)(ξ) = Π_{j≤M} sinc(2πr_jξ)·𝓕(steklovBase)(a_M ξ); shrinking base → 1, so sincPartial(M+1, ξ) → 𝓕 sincProfile(ξ): the profile is the infinite convolution of normalised boxes, transform = Π sinc(2πr_jξ).
- sinc x ≥ e^{−x²/3} for |x| ≤ 1 (sinc ≥ 1 − x²/6). Lower bound: if 2πr_j|ξ| ≤ 1 for j ≥ J and Σ_{j≥J} r_j² ≤ S then |Π_{j<J} sinc|·exp(−(4π²ξ²/3)S) ≤ |𝓕 sincProfile(ξ)|.

## ReceiverRate/TheSincProfileHasALogLogTail (uses HTGeometry ArcsineLogIntegral, RHTower Sieve MertensFirst)
- Goal: ∫_c^{2c}|𝓕 sincProfile|² ≥ c·exp(−Kc/log²c), K = 8π/3 + 3000, for large c.
- ∫_A^B −log|sin| ≤ (B − A + π) log 2 (π log 2 per period); −log sinc x ≤ −log sin x + log⁺x; Σ_{i<m} log((m+3)/(i+3)) ≤ m + 3 (Stirling); log(log y/log x) ≤ log(y/x) for 3 ≤ x ≤ y; Σ_{i<m} log(a_i/a_m) ≤ 3(m+3).
- One factor: ∫_c^{2c} −log sinc(2πρξ)dξ ≤ (c + 1/(2ρ)) log 2 + c·log⁺(4πρc).
- Jensen for a finite sinc product on [c, 2c]: ∫Π sinc² ≥ c·exp(−(2/c)Σ_j∫ −log sinc) (exp∘f = product² off the countable zero set).
- K1: J ≥ 1 with πc ≤ (J+2)log²(J+2) ⇒ 4πr_j c ≤ 1 for all j ≥ J (r_j = 1/(4(j+2)log²(j+2)), j ≥ 1). K2: Σ_{j≥J} r_j² ≤ 1/(16 log⁴(J+2)(J+1)) (telescoping). K3: first J factors cost ≤ cJ log2 + 2log2·J(J+2)log²(J+2) + c(3log(J+2) + 3(J+2)).
- K4 cut J = ⌈4πc/log²c⌉ + 2 (large c): tail costs (4π/3)c/log²c, head ≤ 3000·c/log²c.
- exp_mul_le_integral_norm_fourier_sincProfile_sq: ∫_c^{2c}|𝓕 sincProfile|² ≥ c·exp(−(8π/3 + 3000)c/log²c) for large c.

## ReceiverRate/TheSincProfileHasAnExactCriticalOverlap
- sincTail c = ∫_{ξ>c}|𝓕 sincProfile|²; sincCriticalOverlap N = least c ≥ 1 with τ(c) log N ≤ 1; K_τ = 8π/3 + 3000; W = 144·W₂/π².
- |𝓕 sincProfile(ξ)| ≤ ∫|sincProfile|, ≤ 4μ₁₂(2πξ), ≤ W ξ^{−2}; tail integrable and antitone; lower τ(c) ≥ c·exp(−K_τ c/log²c) eventually; upper τ(c) ≤ 4W μ₁₂(c) for c ≥ 1.
- Eventually L(log L)²/(4K_τ) ≤ sincCriticalOverlap N ≤ 96e·L(log L)². Rate law in exact Fourier-tail units: divergent multiples r_N c*_N are RH receivers; RH ⇔ all bounded multiples K c*_N eventually nonnegative; single K ≥ 4K_τ sees window 288e⌈1 + e^{2(R+1)}⌉ < K/(4K_τ).

## BoundedOverlap/ElevenFlipNegativity (uses ElevenPacket, ElevenTrialMargin, PrimeFlipCompleteForm)
- elevenTrialTest N = atomic test with x_n = primeSquareTrial 11 n/√n at width (99/100)/N. Twisted complete form/(w log N) ≤ elevenUpperEnergy → ‖φ‖²·elevenTrialUpperMargin < 0 ⇒ eventually negative at ratio 99/100.
- atomicTest_zero_padding: zero-padding coefficients beyond M leaves the test unchanged. Rational transfer: a·c = b·(99/100) ⇒ frequently negative at ratio c (horizons b·k, same width); ratio 2 (a = 99, b = 200) and c₀ (a = 99·10¹⁸, b = 100(10¹⁸+1)).

## BoundedOverlap/ElevenPacket (uses PrimeSquareTrial, VariablePacketLimit; ArithmeticIntersectionTheory tameDifferent)
- Conductors {1, 11, 121}, orthonormal Ramanujan coefficients 101/121, −(20/121)√10, (2/121)√110; packet profile = primeSquareTrial 11 n/√n; coefficient mass 1.
- Energy Σ coef²·completeWeilAdjunctionEnergy = finitePart(c) + 4 log 11/11 + poleShift(c)·(101/121)² (tameDifferent 11 = tameDifferent 121 = log 11/10). Untwisted complete limit at ratio 99/100 retains Gamma, both poles, all prime powers.

## BoundedOverlap/ElevenTrialMargin
- bumpRobin(plateau)/‖φ‖² ≤ 21/20; log(2π) > 9/5; log 11 < 5/2; elevenPrimeTailCost = 4 log 11(2/11³ + 1/(11²·10)) < 1/40; poleShift(99/100)·(101/121)² ≤ (99/100)(7/10).
- elevenTrialUpperMargin = finitePart(99/100) + poleShift·(101/121)² + tail < 0 (finitePart = −log 2π − log(99/100) + Robin quotient).

## BoundedOverlap/PrimeFlipCompleteForm (uses ACP NearMaximalGapsDoNotForceWeilPositivity, SMAP ThePoleHyperplaneIsTheHarmonicHyperplane)
- singlePrimeGauge p = finiteFlip {p} as arithmetic function (multiplicative sign). At separated widths (w < atomSpacing N) the twist changes only the prime matrix: weilQuadTw(flip p) − weilQuad on the trial = ‖g‖²·(atomicWeilForm(trial) − atomicWeilForm(flipped trial)); Gamma and both poles identical. primeSquareTrial_complete_le: twisted ≤ untwisted + ‖g‖²·primeSquareFlipBound p N.

## BoundedOverlap/PrimeFlipTail (uses RAPT TheDeficitOfThePrimeFormIsADirichletEnergy, RHTower SummableDivisorHarmonicMean)
- Σ_{p|t, t≠p,p²} Λ(t)/t ≤ log p/(p²(p−1)) (remove p and p² from the full p-ladder log p/(p−1)).
- primeSquareFlipRow p n y = Σ_{t≤y}(1 − flip(t))Λ(t)/t·trial(n)trial(tn) ≤ [p ≤ y]·(2log p/p)·trial(n)trial(pn) + 2log p/(p²(p−1)) (p² unflipped; coprime t unflipped).
- Pole coordinates: atomicWeilForm(F/√n) = 2Σ_m (1/m)Σ_{t≤N/m} (Λ(t)/t)F(m)F(tm). Correction = 2Σ_m (1/m)·row(m, N/m).
- primeSquareFlipBound p N = (4log p/p)(−H(N/p) + (2/p²)H(N/(p³))) + (4log p/(p²(p−1)))H(N); /log N → −4log p/p + 4log p(2/p³ + 1/(p²(p−1))). First prime cancels 4log p/p; remaining cost starts at the prime cube.

## BoundedOverlap/PrimeSquareTrial (uses RAPT GcdProfilesHaveFiniteRamanujanExpansions, ACP PrimeParityRamanujanCoordinates)
- primeSquareTrial p n = 1 − 2[p|n] + 2[p²|n]: agrees with prime parity (−1)^{v_p(n)} through valuation 2; square 1; trial(pn) = −1 + 2[p|n]; trial(n)·trial(pn) = −1 + 2[p²|n].
- Ramanujan expansion on conductors 1, p, p² with coefficients 1 − 2/p + 2/p², −2/p + 2/p², 2/p² (from 1 + c_p(n) = p[p|n], 1 + c_p + c_{p²} = p²[p²|n]). Harmonic correlation Σ trial(n)trial(pn)/n = −H(N) + (2/p²)H(N/p²).

## BoundedOverlap/VariablePacketLimit (uses CACT RamanujanQuasimodesAreUniformThroughTouching, RAPT TheRamanujanPacketPoleCoordinatesSelectConductorOne)
- Adjunction energy continuous in the ratio. For r_N → c ∈ (0,1), any H_N → ∞: ⟨A(r_N, H_N) v_m, v_l⟩ → δ_{ml}·completeWeilAdjunctionEnergy(φ, c, m) (uniform quasimodes through touching).
- Finite Ramanujan packet: weilQuad(packet test)/(w log N) → ‖φ‖²·Σ_m b_m²·adjunctionEnergy(c, m) at convergent width ratios (survives integer rounding / zero padding).
