# 31 ArithmeticElectrostatics — mathematical facts log

## TheVirialLawsOfAFiniteConfiguration
- Finite configuration: distinct charges z_j ∈ ℂ, multiplicities m_j; field E_j = fieldAt m z j = Σ_{k≠j} m_k/(z_j − z_k) (from ArithmeticCorrespondencePositivity; simple Laurent coefficient of (L'/L)² divided by 2m_j).
- Newton: Σ m_j E_j = 0. Stieltjes virial: Σ m_j z_j E_j = ((Σm)² − Σm²)/2 (position-independent).
- transverseEnergy m z = ½Σ_{j≠k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²; verticalEnergy analogous with Im. Re E_j = Σ m_k(Re z_j − Re z_k)/|z_j−z_k|², −Im E_j analogous.
- Transverse virial: Σ_j m_j(Re z_j − c) Re E_j = transverseEnergy (any centre c) — Dirichlet energy on the complete graph with conductances m_j m_k/|z_j−z_k|². Vertical virial likewise. Energy count: transverse + vertical = ((Σm)² − Σm²)/2. transverseEnergy ≥ 0 for m ≥ 0.

## TransverseEquilibriumIsTheCriticalLine
- IsReflectionClosed m z σ: m > 0, z injective, involution σ with z(σj) = 1 − z̄_j, m(σj) = m_j. Then z_j − z_{σj} = 2Re z_j − 1 (horizontal).
- transverseEnergy = 0 ⇔ all Re z_j equal (m > 0); reflection-closed ⇒ ⇔ all on Re = ½. transverseWork = Σ m_j(Re z_j − ½)Re E_j = transverseEnergy. critical ⇔ work ≤ 0 ⇔ all Re E_j = 0 (equilibrium) ⇔ transverseEnergy = 0.
- Quantization: an off-line pair contributes exactly m_j m_{σj} to the energy at every depth; transverseEnergy ≥ ½Σ_{off-line} m_j m_{σj}. With m ≥ 1: non-critical ⇒ energy ≥ 1; critical ⇔ energy < 1 (gap).
- Maximum principle: rightmost charge feels Re E > 0 if some charge is strictly left; leftmost feels Re E < 0. Off-line ⇒ ∃ charge right of ½ with outward field and one left with inward field.
- What no identity gives: an upper bound for the field below the quantum.

## TheTransverseEnergyOfTheZeroDivisor
- divisorTransverseEnergy 𝓔 = ½Σ_j angularEnergy j ∈ [0,∞] (unit charge per distinct ξ-zero; RHTower.angularEnergy). 𝓔 = 0 ⇔ RH; RH ⇔ 𝓔 < 1 (each off-line zero has angularEnergy ≥ 1 from its partner); any finite off-line set has card ≤ 2𝓔.
- 𝓔 < ∞ ⇔ offLineSupport finite (critical–critical pairs contribute 0; finite F ⇒ Σ angular ≤ 2Σ_{k∈F} angular k).
- angularEnergyTerm j k = δ_j F_{jk} + δ_k F_{kj} (δ = Re − ½, transverseForceTerm). Finite off-line index ⇒ Σ angular = 2Σ_{off-line} δ_j F(j) (work = energy), 𝓔 = Σ δ_j F_j; RH ⇔ work < 1; #off-line ≤ 2·work.

## TheFieldLawHasAThreshold
- exists_local_outward_field_witness (ArithmeticCorrespondencePositivity): every off-line zero has within C log γ a locally rightmost p of depth δ ∈ (0,½) with xiTransverseField p ≥ mult/(2δ) + cδ log(|γ_p|+4).
- RH ⇔ every right zero has transverse field ≤ 1 (partner alone gives 1/(2δ) > 1). ∃c > 0: RH ⇔ every right zero has field < √(2c log(|γ|+4)) (AM–GM over unknown δ). The needed arithmetic input is an upper bound max(1, √(2c log γ)), not exact equilibrium.

## TheRenormalizedSquareIsSelbergsSource
- Counterterm identity: F''/F = (F'/F)² + (F'/F)'. At a zero of order m with regular part R of F'/F: (F'/F)² has double-pole coefficient m², F''/F has m(m−1); both residues = 2mR(ρ). Renormalization lowers self-term m² → m(m−1) (zero at simple zeros), field untouched.
- selbergSource Λ₂ = Λ·log + Λ⋆Λ = μ⋆log² ≥ 0; Λ₂(p^k) = (2k−1)(log p)²; L(Λ₂,s) = ζ''(s)/ζ(s) for Re s > 1 (L(Λ log) = (ζ'/ζ)', L(Λ⋆Λ) = (ζ'/ζ)²). Counterterm Λ(n)log n = weight × degree of T_n.

## TheSelfIntersectionOfATorsionOrbit
- Torsion orbit O_n (primitive n-th roots, φ(n) unit charges); orbitIntersection I(m,n) = Σ log|ζ−η|; Hecke law I(m,mt) = φ(m)Λ(t) (ArithmeticEffectivityTheory).
- localCorrection D = φ⋆Λ ≥ 0; Σ_{d|k}(φ(d)log d + D(d)) = k log k; kLogKernel n = φ(n)log n + D(n). Self-intersection I(n,n) = φ(n)log n − D(n) ≤ φ(n)log n.
- D(p^{a+1}) = p^a log p; I(p^{a+1},p^{a+1}) = φ(p^{a+1})(a+1)log p − p^a log p. Tower: I(p^{a+2}) = p·I(p^{a+1}) + φ(p^{a+1})·p log p; per point grows by exactly log p.
- D = (φ⋆μ)⋆log = φ(n)·tameDifferent(n) (Σ_{p|n} log p/(p−1)). Leibniz on coprime: D(ab) = φ(a)D(b) + φ(b)D(a) ⇒ I(ab,ab) = φ(b)I(a,a) + φ(a)I(b,b) (per-point additive).
- Conjugation preserves each orbit (η̄ = η^{n−1}); Hermitian Abel energy torsionEnergy r m n = bilinear Σ −log|1 − rζη|: collided and reflection pairings coincide on torsion cycles.

## TheTorsionCountertermIsLogarithmic
- torsionPairing N y = Σ_{m,n≤N} y_m y_n I(m,n); selfMass = Σ φ(n)y_n²; RenormalizesAt N κ: pairing ≤ κ·selfMass for all y.
- I(m,n) ≥ 0 off diagonal (Hecke: φ(m)Λ(n/m) if m|n). t ≤ 2φ(t) at prime powers; φ super-multiplicative ⇒ down-tower term ≤ 2φ(m)Λ(m/n).
- Schur test with weights 1/n: off-diagonal row Σ_{n≠m} I(m,n)m/n ≤ φ(m)(3log N + log4 + 4) (up: φ(m)Σ_{t≤N/m}Λ(t)/t ≤ φ(m)(log N + log 4 + 4) Mertens; down: 2φ(m)log m). Diagonal I(n,n) ≤ φ(n)log N.
- renormalizesAt_log: κ = 4 log N + log4 + 4 works. Lower: single prime orbit p ≤ N: (p−2)log p ≤ κ(p−1); Bertrand ⇒ κ ≥ ½log(N/2) for N ≥ 4. torsionCounterterm_rate: minimal counterterm ∈ [½log(N/2), 4log N + O(1)] — logarithmic divergence (archimedean self-energy log(1/ε) at width ε ~ 1/N).

## TheArithmeticPointCarriesTheDivergence
- Only z = 1 on |z| = 1 is fixed by squaring; O_1 = {1}; I(1,n) = Λ(n) (n ≥ 2), I(1,1) = 0. D(n) ≤ φ(n)log n ⇒ I(n,n) = log|disc Φ_n| ≥ 0.
- RenormalizesWith N c (per-order counterterm c(n)): c(1) ≥ Σ_{2≤n≤N} Λ(n)²/(c(n)φ(n)) (test y_1 = 1, y_n = Λ(n)/(c(n)φ(n)); Cauchy–Schwarz defect). Constant κ: κ² ≥ Σ Λ(n)²/φ(n) ≥ log2·(log N − log4 − 4) (Λ² ≥ log2·Λ, Mertens). Divergence carried by the arithmetic point.

## TheWeilPrimeFormOnAtomsIsLogarithmic
- atomicWeilForm N x = Σ x_m x_n P(m,n), weilPrimeKernel P(m,n) = Λ(n/m)(n/m)^{−1/2} for m|n, m ≠ n (symmetric, ≥ 0, P(n,n) = 0, P(1,n) = Λ(n)/√n).
- Schur weights n^{−1/2}: row Σ_n P(m,n)√(m/n) ≤ 2log N + log4 + 4 (up: Σ_{t≤N/m}Λ(t)/t Mertens; down: Σ_{t|m}Λ(t) = log m). atomicWeilForm ≤ (2log N + log4 + 4)Σx².
- Lower: any κ bounding the form has κ² ≥ Σ_{2≤n≤N} Λ(n)²/n ≥ log2·(log N − log4 − 4) (test at arithmetic point, mass 2). Counterterm needed at atomic resolution N grows logarithmically; matches archimedean self-energy log(1/ε) only at ε ~ N^{−c}.

## TheTorsionIsTheStableEquilibriumOfTheCircle
- Fekete via Hadamard: N distinct unit-circle points: Σ_{i≠j} log|z_i − z_j| ≤ N log N (Vandermonde with unimodular entries, |det| ≤ N^{N/2}). N-th roots of unity attain it: logEnergy N N = N log N. Torsion = minimal-energy (stable) configuration on the circle.

## QuantizationTurnsWindowsIntoPoints
- zeroWindow T H = {ρ : |Im ρ − T| ≤ H} (finite). windowEnergy = Σ_{ρ∈W} angularEnergy ρ ≥ #off-line in W; off-line zero + partner (same ordinate) ⇒ windowEnergy ≥ 2; < 2 ⇒ window critical. RH ⇔ every unit window has energy < 2.
- affineMap λ κ s = ½ + λ(s − ½) + iκ preserves transverseEnergy and scales field by λ⁻¹ (archimedean twist invisible to electrostatics).
- Gauge twist: for completely multiplicative ω, source of ωΛ is ωΛ₂ (pmul commutes with convolution). Λ₂(p) = (log p)² > 0 ⇒ twisted source ≥ 0 forces ω(p) ≥ 0; sign gauge ⇒ ω(p) = 1. Gauge charge enters through arithmetic, not geometry.

## PowerMapsAreSimilitudesOfTheAbelEnergy
- fullTorsionEnergy T_r(A,B) = Σ_{ζ^A=1,η^B=1} −log|1 − rζη̄| = Σ_k (r^k/k) Re(Ŝ_A(k) conj Ŝ_B(k)), Ŝ_A(k) = A[A|k]. Closed form: T_r(A,B) = gcd(A,B)·log(1/(1 − r^{lcm(A,B)})). PSD on every finite set of orders (Σ_k (r^k/k)|Σ x_A Ŝ_A(k)|²).
- Similitude: T_r(At,Bt) = t·T_{r^t}(A,B) (power map multiplies energy by degree, rescales cutoff r ↦ r^t).
- Renormalized limit: T_r(A,B) − gcd·log(1/(1−r)) → −gcd(A,B)log lcm(A,B) = −J(A,B) (logEnergy). Adjunction: J(At,Bt) = t(J(A,B) + gcd(A,B)log t).

## TheExternalFieldIsAPrimeSum
- Re s > 1: ξ'/ξ = archFactor'/archFactor + ζ'/ζ; Re ξ'/ξ(s) = Σ_ρ Re 1/(s−ρ), each term (σ−β)/|s−ρ|² > 0. Re L(Λ,s) = −Re ζ'/ζ = Σ Λ(n)n^{−σ}cos(t log n).
- External field law: Re L(Λ,s) + Σ_{ρ∈F} Re 1/(s−ρ) ≤ Re archFactor'/archFactor(s) for any finite F. Anti-alignment: at s = σ + iγ (γ ordinate of zero of real part β, multiplicity m): Σ Λ(n)n^{−σ}cos(γ log n) ≤ Re arch'/arch(s) − m/(σ−β).
- transverseForce ≡ 0 (marginality) + divisorTransverseEnergy < ∞ ⇒ RH (finite off-line + harmonic).

## TheHeckeDefectIsTheMomentOfInertia
- heckeDefect E_f(L) = Σ m (2cosh(2δL) − 2)|f̂(ρ)|² (δ = Re ρ − ½); depthSecondMoment M_f = Σ m δ²|f̂(ρ)|².
- cosh(ay) − 1 ≤ a²(cosh y − 1) for a² ≤ 1 ⇒ depthKernel L δ ≤ 4δ²·depthKernel L ½ on |δ| ≤ ½. 4L²M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f; E_f(L)/L² → 4M_f. Defect question = second-moment question; RH = all moments of inertia vanish.

## ReflectedTransverseWork (pure real inequalities)
- transverseAngular x d = x²/(x²+d²); reflectedEnergy x y d = angular(x) + angular(y); reflectedCross = xy(1/(x²+d²) + 1/(y²+d²)); reflectedWork x y d v w = ((v+w)E + (v−w)C)/2. With x = a−b, y = a+b: reflectedWork = (va − wb)(a−b)/((a−b)²+d²) + (va + wb)(a+b)/((a+b)²+d²) (pair and its reflection).
- Near (x²+y² ≤ 1, d² ≤ 1): |d·C| ≤ 2E (Cauchy–Schwarz C² ≤ E·B, d²B ≤ (d²+x²+y²)E). Far (d² ≥ 1): |C| ≤ E (E ± C = (x∓y)²(d² ∓ xy)/(...) ≥ 0). |(v−w)C| ≤ (v+w)E ⇒ 0 ≤ work ≤ (v+w)E.
- heightDamping R t = R⁴/(R²+t²)² ∈ [0,1]; R|D(t) − D(u)| ≤ |t−u|(D(t)+D(u)). For R ≥ 4 the damped cross term is dominated ⇒ damped reflected work ∈ [0, (D_t+D_u)E]. angular(x, t−u) ≤ 2(1+t²)/(1+u²) ⇒ D(t)·angular ≤ 2R⁴/((1+t²)(1+u²)); (D_t+D_u)E ≤ 8R⁴/((1+t²)(1+u²)) (product of summable tails).
- heightTaper N t = max(0, 1 − |t|/(N+1)), 1-Lipschitz, ∈ [0,1]; tapered damped work |·| ≤ 2(D_t+D_u)E uniformly in N.

## TheSelbergWorkExhaustsTheTransverseEnergy
- On ξ zero copies (multiplicity kept): signed depth δ_p ∈ [−½,½] (δ² ≤ ¼), pair bound (δ_p−δ_q)² + (δ_p+δ_q)² ≤ 1. xiDampedPairWork R p q = reflected damped work ≥ 0 (R ≥ 4), |·| ≤ xiWorkMajorant = 16R⁴/((1+γ_p²)(1+γ_q²)) summable over pairs ⇒ absolutely summable. xiDampedSourceWork R = Σ_{pairs} work/4 ≥ 0.
- xiTaperedSourceWork R N = Σ_{p in height box} δ_p D_R(γ_p) taper_N(γ_p)·xiSourceField p (finite sum of actual Laurent-residue fields of (ζ'/ζ)², full exterior rows). Rows absolutely summable; reflection pairing (swap, line conjugation) gives xiTaperedSourceWork = Σ tapered pair work/4 exactly; → xiDampedSourceWork as N → ∞ (dominated convergence).
- xiDampedPairWork ≤ 2·reflectedPairEnergy; xiCopyTransverseEnergy (ENNReal, multiplicity copies) = Σ ofReal(reflected pair energy/4) = ½Σ (Re ρ − Re ρ')²/|ρ − ρ'|². xiDampedSourceWork(n+4) → xiCopyTransverseEnergy in [0,∞] (finite: dominated convergence; infinite: finite partial sums exceed any bound).
- Meaning: damped arithmetic source work of (ζ'/ζ)² residues is nonnegative and exhausts the transverse energy as damping is removed.

## LargeValuesAtZeroOrdinates
- Dirichlet polynomial F(t) = Σ_{n≤N} a_n n^{it}; coeffMass = Σ|a_n|²; derivative multiplies mass by ≤ log²N. Cell Sobolev: |F(t)|² ≤ 2∫_c^{c+1}|F|² + ∫_c^{c+1}|F'|². Window mean value: ∫_A^{A+R}|F|² ≤ (R + 8N(1+log N))Σ|a_n|².
- Zero ordinates (local ceiling: O(log) zero copies per unit cell): Σ_{γ∈(A,A+R]}|F(γ)|² ≤ K log(A+R+1)(R + 8N(1+log N))(2 + log²N)Σ|a_n|²; large values: #{|F(γ)| ≥ V}·V² ≤ same.
- Prime polynomial a_n = w_nΛ(n)/√n, |w| ≤ 1: mass ≤ log N(log N + log4 + 4). Alignment law: #{γ : |Σ w_nΛ(n)n^{−1/2+iγ}| ≥ V} explicit. For a_n = Λ(n)/√n, n ≤ X: #{γ ∈ (T,2T] : |F(γ)| ≥ (1−η)log T} = O(T log⁴X/log T) — vanishing proportion if log X = o(√log T).

## TheGaugeMarginOfTheRenormalizedSource
- Twin source at prime: ωΛ₂(p) = ω(p)log²p. Flip ω(p) = −1: ωΛ₂(p) = −log²p, margin Λ₂(p) − ωΛ₂(p) = 2log²p. Window law: Λ₂ ≥ 0 everywhere and a flipped p ≤ N gives some n ≤ N with ωΛ₂(n) ≤ −log²2 (margin fixed by smallest flipped prime, window-independent).
- Λ₂(n) ≤ 3log²n (Λ⋆Λ ≤ 2log²n); Σ Λ₂(n)n^{−σ} converges σ > 1. L-series margin: L(Λ₂,σ) − L(ωΛ₂,σ) ≥ 2log²p·p^{−σ} for sign gauges (terms (1−ω(n))Λ₂(n)n^{−σ} ≥ 0).
- Coefficient margin ≠ form margin: forms on signed tests do not inherit it.

## TheStabilityLawAtAtomicResolution
- Disjoint shift: if f(u)f(u+x) = 0 for all u, ∫(f(u) − f(u+x))² = 2∫f². Lévy gain: if all shifts x ∈ (w,s] (s ≤ 1) are disjoint, levyEnergy f ≥ e^{−1/2}log(s/w)∫f² (archLevyDensity x ≥ e^{−1/2}/(2x)).
- atomicTest N x g = Σ_{n≤N} x_n g(u − log n), g ∈ C² supported in [0,w]; atomSpacing δ_N = log(1 + 1/N) ≤ log 2 < 1; log b − log a ≥ δ_N for a ≤ N < … (a < b). Below spacing atoms are orthogonal: ∫f² = Σx_n²∫g². For w ≤ δ_N/4: levyEnergy ≥ e^{−1/2}log(δ_N/(2w))∫f².
- primeSum(atomicTest) = (∫g²)·atomicWeilForm N x for w < δ_N (only exact Hecke relations m = nk survive; vonMangoldtAtom k = Λ(k)/√k).
- Markov form M = archForm − primeSum (no pole term): M(f) ≥ (2θ'(0) + e^{−1/2}log(δ_N/(2w)) − 2log N − log4 − 4)∫f²; atomicWidth N = (δ_N/4)exp(−e^{1/2}(2log N + log4 + 4 + 2|θ'(0)|)) = N^{−O(1)}; M ≥ 0 for every atomic test of width ≤ atomicWidth N. Matching fails once width ~ spacing (gain bounded, prime counterterm ≥ √(log2(log N − C))).

## TheEnergyOfAZeroIsLogarithmic
- Pair bound: angularEnergyTerm(ρ,ρ') ≤ 2/(1 + (γ−γ')²) (real parts in strip width 1). Lorentzian zero mass Σ 1/(1+(γ−γ')²) ≤ 8(C + log(|γ|+4)) ⇒ angularEnergy ρ ≤ 16(C + log(|γ|+4)). windowEnergy ≤ #window·16(C + log(|T|+H+4)). Off-line zero: 1 ≤ E(ρ) ≤ 16(C + log(|γ|+4)). Energy controlled unconditionally (pair terms bounded); field is not (near-coincident pair gives 1/|ρ−ρ'|).

## HigherMomentsAtZeroOrdinates
- primeSupported P c (prime-supported arithmetic function), phase t n = n^{it} completely multiplicative; expSum f M t = Σ_{n≤M} f(n)n^{it} = dirPoly. F^k = expSum(a^{⋆k}, X^k) (support of a^{⋆k}: Ω(n) = k, n ≤ X^k).
- Convolution mass: |(a⋆a^{⋆k})(n)|² ≤ (k+1)Σ_{d|n}|a(d)|²|a^{⋆k}(n/d)|² (≤ k+1 prime divisors, Cauchy–Schwarz) ⇒ Σ|a^{⋆k}(n)|² ≤ k!(Σ|a(n)|²)^k.
- Large values via F^k: #{|F(γ)| ≥ V}·V^{2k} ≤ K log(A+R+1)(R + 8X^k(1+log X^k))(2 + log²X^k)k!S^k. If X^k ≤ R and kS ≤ θV²: count ≤ 9K log(A+R+1)R(1+log R)(2+log²R)θ^k.
- Detector c_p = w_p log p/√p: S ≤ log X(log X + log4 + 4). With k = ⌊log R/log X⌋ and log R(log X + 7) ≤ θV² (0 < θ ≤ 1, X ≥ 2): count ≤ K log(A+R+1)R(1+log R)(2+log²R)θ^{−1}R^{log θ/log X}. At V = η log T, X = (log T)^C, R ~ T: aligned ordinates T^{1−1/C+o(1)} (power saving).

## TheGaugeIsInvisibleAtAtomicResolution
- Sign gauge ω (completely multiplicative, ω(n) = ±1): twisted kernel P_ω(m,n) = ω(n/m)P(m,n) = ω(m)ω(n)P(m,n). twistedAtomicWeilForm ω N x = atomicWeilForm N (ωx); x ↦ ωx isometric involution ⇒ identical upper/lower spectral bounds for every twin (Schur 2log N + O(1); arithmetic-point lower bound).
- twistedPrimeSum(atomicTest x) = primeSum(atomicTest ωx) = (∫g²)·twisted atomic form. Gauge-blind stability: archForm − twistedPrimeSum ≥ 0 on atomic tests of width ≤ atomicWidth N for every sign twin.
- Positive cone: twisted form ≤ ζ form for x ≥ 0 (ω(m)ω(n) ≤ 1). Two-atom test 1_{1} + 1_{p} at flipped p ≤ N: ζ form − twin form = 4Λ(p)/√p (mass 2); twin Markov − ζ Markov = 2Λ(p)/√p·∫f² (ζ is the minimum of its gauge orbit on nonnegative atomic tests, window-independent margin — wrong side for separating ζ).
- twinMarkov_atomicTest_eq: M_ω(f_x) = M(f_{ωx}) + A(f⁺ + f⁻) − A(f⁺ − f⁻) (x⁺ neutral, x⁻ charged; A = archForm): every difference is archimedean interaction across the charge.

## TheWeilFormAtAtomicResolution
- Re W(f) = M(f) + 2C(f)² − 2S(f)² (C = ∫f cosh(u/2), S = ∫f sinh(u/2); pole term signature (1,1)). On atomic tests of width ≤ atomicWidth N: Re W + 2S² ≥ 0 (rank-one counterterm); Re W ≥ 0 when |S| ≤ |C|, in particular for nonnegative weights and nonnegative bump (atoms in u ≥ 0 where 0 ≤ sinh ≤ cosh). Does not reach spacing scale w ~ 1/N.

## TheStabilityLawWithTheSharpCounterterm
- Sharp prime counterterm (RenormalizedArithmeticPotentialTheory): atomicWeilForm ≤ (log N + log4 + 4)|x|² (Schur with pole vector n^{−1/2}); pole vector attains ≥ (log N − log8 − 4)|u|².
- widthAt N κ = (δ_N/4)exp(−e^{1/2}(κ + 2|θ'(0)|)); for w ≤ widthAt, Lévy gain ≥ κ − 2θ'(0). sharpAtomicWidth N = widthAt N (log N + log4 + 4) ~ δ_N N^{−e^{1/2}} (exponent of atomicWidth halved).
- M(f) ≥ (2θ'(0) + e^{−1/2}log(δ_N/(2w)) − log N − log4 − 4)∫f²; M ≥ 0 below sharpAtomicWidth. Pole test: primeSum ≥ (log N − log8 − 4)∫f² ⇒ archForm(pole test) ≥ (log N − log8 − 4)∫f² there. Same width for every sign twin; Re W + 2S² ≥ 0 at sharp width. Reaching spacing needs the archimedean cross kernel of overlapping shifts.

## TheRealExteriorDissipatesHeatDepth
- Even order-one entire f (f(0) ≠ 0, growth exp(C(1+|z|)log(2+|z|))): symmetric zero-ball sums Σ (z − a)⁻¹ → f'/f(z) (reflection cancels genus-one counterterms). Removing finitely many zeros N, if all others are real: Im z·Im(f'/f(z) − Σ_N (z−a)⁻¹) ≤ 0 (each real zero contributes −(Im z)²/|z−a|²).
- Heat flow: for t > 0 the nonreal heat zero set is finite (heatNonrealCopies); real exterior work nonpositive: riemannHeat_realExteriorWork_nonpos.

## TheGlobalHeatDepthIsContinuous
- heatGlobalVerticalEnergy t = Σ_{nonreal copies} (Im z)² ≥ 0 = heatWeightedZeroSum (Im z)² (multiplicity). On [a,∞), a > 0, all nonreal heat zeros lie in a fixed ball (real for t > 1/8; |Im| ≤ ½ and |Re| < X for t ≤ 1/8). continuousOn (0,∞) via compactly clamped zero-sum continuity (multiplicity conservation through collisions).

## TheSimpleHeatPacketDissipatesDepth
- Simple zero has one divisor copy. 2·logDeriv(dslope f a)(a) = f''(a)/f'(a) (first jet of divided difference). Removing a simple pole from the real-exterior inequality: Im a·Im(f''(a)/f'(a) − 2Σ_{r∈N∖q}(a − r)⁻¹) ≤ 0.
- heatGlobalPacket_drift_le: for t > 0 and a conjugation-closed set S of simple heat zeros containing every nonreal zero: Σ_{a∈S} 2 Im a·Im(f''/f'(a)) ≤ −2·nonrealZeroCount t (pair drift of conjugate packet pays the count).

## SimpleHeatZeroBranches
- Simple heat zero a at time t ≥ 0: spatial Taylor + time remainder ⇒ |z − (a + h f''(a)/f'(a))| ≤ Ch² for zeros z near a at time t+h. Disk with zero count 1 contains exactly one simple zero. exists_simple_heat_zero_branch (t > 0): unique local branch ζ(h), ζ(0) = a, right derivative f''(a)/f'(a) (heat velocity), simple and isolated in ball for h ∈ [0,δ].

## TheGlobalHeatDepthHasItsZeroVelocityDerivative
- If all future nonreal zeros stay in a ball of radius R and the zeros of riemannHeat t in that ball are simple: right derivative of heatGlobalVerticalEnergy at t = Σ_{a∈S} 2 Im a·Im(f''/f'(a)) (finitely many branches; heat nonvanishing on the compact complement of isolating disks persists).

## TheGlobalHeatDepthDissipates
- Nonreal count is constant just right of each t > 0. Forward-regular interval comparison carries D ≤ −2N(s) through collisions (count antitone ⇒ integrable).
- heatGlobalVerticalEnergy_forward_derivative: every t > 0 has a punctured forward interval where right derivative D ≤ −2·nonrealZeroCount(s) (forward simple zeros, exists_compact_simple_riemannHeat_zeros_forward).
- PILLAR heatGlobalVerticalEnergy_add_integral_count_le: E(b) + 2∫_a^b N(s)ds ≤ E(a) for 0 < a ≤ b; antitoneOn (0,∞); E(t) = 0 ⇔ all zeros of riemannHeat t real. No initial-time energy assumption.
