# 36 ArithmeticLorentzianGeometry — mathematical facts log

## LorentzianFormsAtDegreeTwo (Mathlib only)
- bil xᵀQy, qf Q[x]. IsHyperbolic: Q[x]Q[y] ≤ (xᵀQy)² whenever Q[x] > 0 (Hodge index / reverse Cauchy–Schwarz). IsLorentzian: symmetric, entries ≥ 0, hyperbolic (degree-two Brändén–Huh).
- Equivalences (Q symmetric): hyperbolic ⇔ no plane on which Q is PD ⇔ Q ≤ 0 on the kernel of some functional. Hyperbolic ⇒ Q ≤ 0 on the Q-orthogonal complement of any positive vector.
- Domination (counterterm principle): Q ≤ Q' pointwise, Q' hyperbolic ⇒ Q hyperbolic; adding NSD preserves; rank one + NSD hyperbolic.
- Closure: pullback along any linear map preserves hyperbolicity; along nonnegative maps preserves Lorentzian; symmetric product of two nonnegative linear forms Lorentzian. Sums fail: x₀² + x₁² (identity of ℝ²) not hyperbolic though each Lorentzian.
- IsCND (Q ≤ 0 on Σx = 0): hyperbolic; closed under sums and nonnegative scaling (only class where local-to-global by summation preserves signature); CND + nonneg entries ⇒ Lorentzian.

## TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity (uses ACS)
- Hermitian: hermPosIndex H ≤ 1 ⇔ IsHyperbolicHerm (H[x]H[y] ≤ |x*Hy|² for H[x] > 0) (orthogonal splitting; PD plane gives posIndex ≥ 2; converse via functional kernel neg-index bound).
- riemannHypothesis_iff_intersectionGram_isHyperbolicHerm: RH ⇔ for every finite family of C² compact tests the ACS intersection Gram on H, V, f_i satisfies D²E² ≤ |D·E|² whenever D² > 0 (Khovanskii–Teissier form).
- Nef shift f_i ↦ f_i + t(H+V) (pole plane H² = V² = 0, H·V = 1): signature unchanged; all entries ≥ 0 for large t ⇒ "Lorentzian in some nef basis" ⇔ hyperbolic: nonnegativity of coefficients carries information only in a fixed basis.

## TheHodgeIndexTricklesDown
- rowSum D = Q·1; IsMetzler (off-diagonal ≥ 0); IsConnectedSupport; TrickleDownIneq (TD): Q[v] ≤ Σ_i(Qv)_i²/D_i. Graph Laplacian Σ D_jv_j² − Q[v] = ½Σ Q_jk(v_j − v_k)² ⇒ Metzler: Q[v] ≤ ‖v‖²_D, equality only constant along positive entries.
- Hyperbolic ⇒ (TD) (split v = a·1 + z, Engel Cauchy–Schwarz). Links: symmetric hyperbolic T_i, ΣT_i = Q, T_i·1 = Qe_i ⇒ (TD) (reverse C–S in each link against 1).
- Variational: max of Q on D-unit sphere of {ΣD_iv_i = 0} is a generalized eigenvector Qv₀ = mDv₀ (exists_max_generalizedEigen). (TD) ⇒ m ≤ m²; Laplacian ⇒ m ≤ 1 with equality only on constants ⇒ m ≤ 0 ⇒ hyperbolic (connected Metzler).
- Metzler Hodge index theorem: connected Metzler, positive row sums: one positive square ⇔ (TD) ⇔ hyperbolic links (can be rank one + NSD: T_i = c_ic_iᵀ + N/|ι|, c_i = D_i^{−1/2}Qe_i, N = Q − Σc_ic_iᵀ NSD). (TD) ⇔ links needs no sign. (TD) says Q − QD⁻¹Q NSD: change of class to a sum-closed one.
- Quantitative: (TD) up to ε‖v‖²_D + gap Q ≤ (1−g)D on hyperplane excluding μ₊ ⇒ Q ≤ μ₋(ε)D, μ₋ = (1 − √(1−4ε))/2.
- Both conditions necessary: identity of ℝ² (disconnected) has links and two positive squares; [[2,−1],[−1,2]] (not Metzler) satisfies (TD) but PD.

## TheSignIsAGaugeFixing (uses ArithmeticElectrostatics weilPrimeKernel, BiarithmeticGaugeGeometry PrimeGauge, RHTower archLevyDensity)
- Atoms log n, 1 ≤ n ≤ N. Twin χ: completely multiplicative, |χ(n)| = 1. archAtomKernel A(m,n) = ω(|log n − log m|) (Gamma Lévy density, > 0 for m ≠ n). twinPrimeKernel conj χ(m)χ(n)P(m,n), P = Λ(n/m)(n/m)^{−1/2} on prime-power ratios. coupledKernel K_t = A + t·twisted P. Gauge g_n unimodular: conj g_m g_n K(m,n); HasNonnegGauge on [1,N].
- Each kernel alone gauge-trivial: twisted prime kernel ≥ 0 in gauge g = conj χ; A ≥ 0 in trivial gauge.
- P(m, m+1) = 0 for m ≥ 2 (successors share no prime ladder); P(1,6) = 0; P(1,p) = log p/√p. Unimodular rigidity: conj a·b·r ≥ 0, r > 0 ⇒ a = b. ω(log p) = p^{−1/2}/(1 − p^{−2}) < t log p/√p for t ≥ 2.
- exists_nonneg_gauge_iff (N ≥ 6, t ≥ 2): K_t has a nonneg gauge on [1,N] ⇔ χ(p) = 1 for all primes p ≤ N. Proof: A fixes g along the successor 2..N, (1,6) links g_1, then (1,p) forces χ(p) = 1 (χ(p) = −1 loses to ω). Liouville twin fails; Euler gauge works for all t ≥ 0.
- Archimedean characters: shifted kernel conj(m^{iτ})n^{iτ}A + tP_χ (archimedean kernel of ζ(s − iτ)); gauge g·n^{iτ} intertwines with relative twin χ(n)n^{−iτ}. Nonneg gauge ⇔ χ(p) = p^{iτ} for p ≤ N. Lorentzian locus of the prime gauge torus = archimedean characters, each with its own archimedean kernel; Kronecker twin p^{iτ} works.
- Moral: the sign hypothesis is a gauge-fixing performed by the archimedean place along the successor; invisible to any prime-kernel-only form.

## TheMetzlerDichotomy
- diagConj π Q = diag π Q diag π: preserves symmetry, Metzler (π > 0), connectivity; rowSum = π_i(Qπ)_i; hyperbolicity invariant for nowhere-zero π.
- Weighted Laplacian: Σ(Qπ)_i/π_i v_i² − Q[v] = ½ΣQ_jkπ_jπ_k(v_j/π_j − v_k/π_k)².
- Stability regime: Metzler, Qπ ≤ 0 for some π > 0 ⇒ Q NSD (diagonal self-energy pays weighted row sums; shape of every unconditional atomic Weil positivity, cf. AE stability law).
- Trickle-down regime: Metzler connected, Qπ > 0 ⇒ (one positive square ⇔ Q[v] ≤ Σπ_i(Qv)_i²/(Qπ)_i (TD_π)). π free: any positive vector with positive image.

## TheFrobeniusLadderIsMetzler (uses ACS CurveDatum, FakeCurvesAndTheWindowLaw)
- Curve datum: β_i normalized Frobenius eigenvalues, N_j = q^j + 1 − q^{j/2}Σβ_i^j. frobeniusGram on H, V, Γ_0..Γ_K: H² = V² = 0, H·V = 1, Γ_k·H = 1, Γ_k·V = q^k, Γ_k·Γ_l = q^{min(k,l)}N_{|k−l|}.
- Block Hodge index: for any symmetric form with pole plane realPolePlane, Q[(p,d)] = 2(p_H + d·V)(p_V + d·H) − δ(d), polar defect δ(d) = 2(d·H)(d·V) − L[d]; hyperbolic ⇔ δ ≥ 0 (isHyperbolic_fromBlocks_iff). For curves δ = ACS span defect; unitary data hyperbolic (span defect = Σ|·|² Toeplitz).
- Bézout ⇔ Metzler: frobeniusGram Metzler ⇔ N_j ≥ 0 for 1 ≤ j ≤ K. Sign hypothesis = effectivity.
- Every curve datum: connected support (through H) and weight π = (t,t,1,…,1), t = 1 + Σ|Γ_k·Γ_l|, with Qπ > 0 ⇒ trickle-down regime; nonneg counts ⇒ (Hodge index ⇔ TD_π).
- Golden fake curve (q = 5, β = φ, φ⁻¹): positive counts, Metzler, connected, TD regime, violates Hodge index on H,V,Γ_0,Γ_1 ⇒ violates TD_π. Sign does not carry Weil; trickle-down does: Weil's theorem = NSD of Q − QD⁻¹Q.

## TheTrickleDownInequalityIsTheSquareRootCount (uses ACS FrobeniusSpanHodgeIndexIsRH, UpperLefschetzBounds…, AET TheHyperellipticCalibration)
- spanDefect_eq_of_subset: span defect on S = span defect of d·1_S on larger window ⇒ hyperbolic on every ladder ⇔ Hodge index on full span ⇔ unitary (|β_i| = 1).
- Nonneg counts: TD_π on every ladder ⇔ unitary ⇔ ∃C ∀k N_k ≥ q^k + 1 − Cq^{k/2} (one-sided square-root count).
- Hyperelliptic y² = f(x) (f squarefree odd degree, odd char): counts positive, datum unitary (Stepanov) ⇒ every ladder satisfies TD_π and weighted Gram has hyperbolic links (rank one + NSD).
- Golden datum fails every square-root lower bound.
- Over 𝔽_q the local-to-global trickle-down is supplied by a count (auxiliary function with many zeros), not a surface; that count is what a ℤ construction must replace.

## TheLocalFactorTricklesDownByRamanujan (uses ACS Pontryagin law / span defect counts outer eigenvalues; RHTower WeilKloostermanBound)
- Finite depth decides: Hodge index on ladder H,V,Γ_0..Γ_{2g−1} ⇒ unitary (span defect = Toeplitz form of power sums; nonneg on real ⇒ nonneg on complex (re/im split) ⇒ neg index 0 ⇒ |β_i| = 1). Hence TD_π on every ladder.
- Genus one (local factor 1 − aT + qT², t = a/√q): Gram on H,V,Γ_0,Γ_1 hyperbolic ⇔ |t| ≤ 2 ⇔ |a| ≤ 2√q (Toeplitz [[2,t],[t,2]]). Depth one decides genus one; depth zero never decides (every genus-one datum passes; golden fake passes depth 0, fails depth 1).
- ramanujanDatum: t/2 ± i√(1 − t²/4); unitary, trace 1 = a/√q; unitary genus one ⇒ N_j ≥ (q^{j/2} − 1)² ≥ 0 ⇒ every ladder Metzler, TD_π, hyperbolic links.
- Kloosterman sum real (x ↦ −x); Weil bound |K(a)| ≤ 2√p ⇒ 1 + K(a)T + pT² is the Ramanujan datum of −K(a): every ladder Metzler, TD_π, links.
- Local Lorentzian input at a prime = RH over 𝔽_p for the local factor; with Euler-product closure the whole Hodge index over ℤ sits in the local-to-global step.

## TheSuccessorConnectionIsTheArchimedeanGaugeField
- succShiftProfile (Sx)_n = x_{n−1}: atomicWeilForm_{N+1}(Sx) = Σ x_mx_n P(m+1,n+1) (shifted-divisor correlation).
- Successor not monotone on the nonneg cone: lowers on δ_1+δ_3 (log2/√2 < log3/√3), raises on δ_2+δ_5. No transfer-matrix positivity along successor at prime-form level.
- P(m, mp) = log p/√p; P(m,n) = 0 for coprime m,n ≥ 2.
- In gauge g = conj χ (prime kernel Euler), archimedean kernel on successor edge (n,n+1) carries conj A_ω(n), A_ω(n) = conj χ(n)χ(n+1) (BGG succConn). Nonneg on all successor edges of [1,N+1] ⇔ connection flat ⇔ ω(p) = 1 for p ≤ N+1.
- Positive survivor of successor-monotonicity: successor connection = gauge field seen by archimedean kernel; flatness = Lorentzian sign hypothesis.

## APeriodicSuccessorHolonomyIsFlat
- Ratio rigidity: completely multiplicative f, no zeros on n ≥ 1, f(n+q+1)f(n) = f(n+1)f(n+q) ⇒ f ≡ 1 (f(n+q) = cf(n), n = mq gives f(m+1) = cf(m), f(4) = f(2)² ⇒ c = 1).
- On the torus: succConn periodic ⇔ Euler point; archimedean characters n^{iτ}, τ ≠ 0, aperiodic.
- Off torus: periodic completely multiplicative f ≢ 1 vanishes somewhere (Dirichlet characters). Euler point is the only one with periodic holonomy and unimodular.

## LorentzianPolynomialsAndTheTuranLayer (uses RHTower XiTaylorCoefficientsLogConcave)
- Lagrange identity 2×2: Q[x]Q[y] − (xᵀQy)² = det Q·(x₀y₁ − x₁y₀)²; Q₀₀ ≥ 0 ⇒ (hyperbolic ⇔ det Q ≤ 0).
- IsLorentzianPoly d c (coefficient form): c ≥ 0, homogeneous degree d, M-convex support, every quadDeriv (Hessian of ∂^α f, entries (α+e_i+e_j)! c_{α+e_i+e_j}) hyperbolic.
- Bivariate Σa_kx^ky^{d−k}, a ≥ 0: Lorentzian ⇔ interval support (⇔ M-convex) and ultra-log-concave (a_i/C(d,i))(a_{i+2}/C(d,i+2)) ≤ (a_{i+1}/C(d,i+1))².
- Turán sequence (γ ≥ 0, γ_k² ≥ γ_{k−1}γ_{k+1}) ⇒ every homogenized Jensen polynomial ΣC(d,k)γ_{n+k}x^ky^{d−k} Lorentzian (zero after nonzero kills tail ⇒ interval support).
- xi_jensen_isLorentzianPoly: Taylor coefficients of ξ(½ + x) = Σγ_kx^{2k} form a Turán sequence unconditionally ⇒ all Jensen polynomials of ξ at the centre Lorentzian, all d, n. Lorentzian = log-concavity layer of real stability, strictly weaker at d ≥ 3; Pólya factorial normalization k!γ_k needs sharper Newton γ_k² ≥ (1+1/k)γ_{k−1}γ_{k+1}.

## FrobeniusIsConformalHeckeIsABoost (uses AIT TheHeckeCocycleOfRenormalization)
- Over 𝔽_q: Frobenius pullback (H ↦ qH, V ↦ V, Γ_k ↦ Γ_{k+1}) is nonneg and conformal: Tᵀ G_{K+1} T = q G_K (graphPair(k+1,l+1) = q graphPair(k,l)); generates the ladder from Γ_0.
- Over ℤ: Hecke dilation n ↦ pn preserves the coupled kernel of every twin (A depends on log ratios, P(pm,pn) = P(m,n), |χ(p)| = 1); acts on pole plane by boost diag(p^{−1/2}, p^{1/2}), an isometry (factor 1). A boost cannot yield Hasse–Weil (needs factor q).
- Power maps n ↦ n^k (k ≥ 2) not conformal for P (pair (1,4) vs (1,16) scales differ). Successor not conformal (vanishing-form profile δ_2+δ_5 ↦ positive form).
- No atom map over ℤ is conformal with factor ≠ 1: Frobenius is a symmetry of a different kind (conformal) from all ℤ symmetries (isometries).

## AnIsometricLadderCarriesNoPositiveSquare
- toeplitzLadder T_K = (c_{|i−j|}) (Gram of translates g(· − k log p) under isometric dilations). Metzler couplings c_k ≥ 0 (k ≥ 1).
- Stability: c_0 + 2Σ_{1≤k≤n}c_k ≤ 0 ∀n ⇒ every depth NSD (weight 1).
- Two far copies: c_k → 0 and some depth has a positive square ⇒ a deeper ladder has two (vector and far translate almost orthogonal, |bil| ≤ s²ε < q).
- Decaying couplings: hyperbolic at every depth ⇔ NSD at every depth.
- Conformal ladder G_ij = λ^{min(i,j)}a_{|i−j|} (Frobenius law G_{i+1,j+1} = λG_ij) is congruent via diag(λ^{−i/2}) to Toeplitz ladder of normalized couplings λ^{−k/2}a_k; decaying normalized couplings ⇒ Hodge index only in stability regime. Frobenius escapes: normalized couplings grow like q^{k/2}.
- Single positive square must come from outside the ladder (pole plane) or growing couplings; the prime pairing on a p-ladder at lag k log p has weight ≍ w p^{k/2} (PNT main term), growing like pole plane conformal weight.

## RHIsReflectionPositivityOfTheCayleyLadder (uses RHTower LiCriterion, LiSubexponentialCriterion, RiemannXiZerosInfinite, RiemannXiRealAxisNonvanishing)
- Cayley w = 1 − 1/s: critical line → unit circle, s ↦ 1 − s → w ↦ w⁻¹; with conjugation, zeros invariant under r(w) = 1/w̄. Multiplication by w plays Frobenius.
- liCoupling ℓ(n) = Re Σ_a m_a(2 − w_a^n − w_a^{−n}); cayleyLadder = toeplitzLadder ℓ. ℓ(0) = 0.
- Reflection formula: Q_K[c] = Re Σ m_a(2(Σc)² − 2p_c(w_a)p_c(w_a⁻¹)), p_c(z) = Σc_iz^i. Primitive (Σc = 0): −2Re Σ m_a p_c(w_a)·p_c(rw_a)‾.
- Unitary points (|w_a| = 1): −Q_K[c] = Σ2m_a|p_c(w_a)|² on primitive vectors ⇒ NSD on primitive (m ≥ 0). Shift c ↦ (0,c) multiplies p_c by z: preserves reflected pairing, conformal factor |w_a|² for evaluation.
- Depth-one probe: Q_{n+1}[e_n − e_0] = 2ℓ(0) − 2ℓ(n); NSD on primitive at every depth ⇒ ℓ(n) ≥ 0. NSD on primitive ⇒ hyperbolic.
- ζ: xiMult, xiCayley; ℓ = Re of paired Li 2λ_n. RH ⇔ every Cayley ladder NSD on primitive vectors ⇔ every Cayley ladder entrywise ≥ 0 (Li). Under RH every Cayley ladder Lorentzian; −Q = Σ2m_ρ|p_c(w_ρ)|²; Re 2λ_1 > 0 under RH.
- not_tendsto_xiLiPaired_re_zero (unconditional): Re 2λ_n ↛ 0 (decay ⇒ bounded below ⇒ RH by subexponential Li ⇒ hyperbolic decaying ladders NSD, contradicting 2λ_1 > 0 at depth two).
- In Cayley coordinates the Metzler sign implies the Hodge index; trickle-down hidden in the sign (Li positivity ⇔ RH).
- 𝔽_q: ℓ(n) = 2(2g − Σβ_i^n); ℓ(n) ≥ 0 ⇔ N_n ≥ q^n + 1 − 2g q^{n/2} (sharp Weil); unitary ⇔ Cayley ladders reflection positive; golden fails.

## LocalFactorsAndTheEulerProductClosure
- p-ladder 1, p, …, p⁵ prime kernel log p·p^{−|i−j|/2} (Metzler) is not hyperbolic for every prime: δ_1+δ_p and δ_{p⁴}+δ_{p⁵} span a PD plane (4 ≤ t⁴(1+t)⁴ impossible for t = p^{−1/2} ≤ 2^{−1/2}). Each Euler factor alone has ≥ 2 positive squares.
- Jump form A − diag(A·1), A Metzler: NSD (archimedean place contributes no positive square; self-energy pays row sums).
- esymm2Form Σ_{p≠q}M_pM_qᵀ = (ΣM_p)(ΣM_p)ᵀ − ΣM_pM_pᵀ: rank one minus PSD ⇒ Lorentzian for all nonneg M.
- eulerHessian: Hessian of ∏_p⟨L_p, X⟩ at y (eval_pderiv_pderiv_eulerProduct via pderiv_finsetProd) = (∏⟨L_r,y⟩)·esymm2(L_p/⟨L_p,y⟩): Lorentzian for every nonneg local data with positive factors.
- Products preserve the class where sums do not, but the closure is blind (Beurling systems, fake curves give nonneg local factors). Euler-point selection comes from archimedean gauge-fixing and the trickle-down defect, not from the multiplicative closure.

## TheHessianOfALorentzianPolynomialTricklesDown (part 1)
- hess ∇²f(x) = Σ_{|α|=m}(x^α/α!)Q_α, Q_α = quadDeriv. coeffDeriv (∂_i c)_β = (β_i+1)c_{β+e_i}; quadDeriv(∂_i c, α) = quadDeriv(c, α + e_i).
- Euler identity: (n+1)∇²f(x) = Σx_i∇²(∂_if)(x); link condition Σ_k∇²(∂_if)(x)_{jk}x_k = (n+1)∇²f(x)_{ji}.
- Differentiation preserves IsLorentzianPoly (slice {β : β+e_a ∈ S} of M-convex set is M-convex).
- Hessian entries ≥ 0 for x ≥ 0.
- (cont.) hess_pos: entry positive iff a monomial γ ≥ e_j + e_k occurs (x > 0). Nonneg matrix vanishing on a positive vector is zero.
- mconvex_path: w constant on the variables of each monomial of an M-convex set of degree ≥ 2 ⇒ constant on all occurring variables (walk by single exchanges, consecutive monomials share a variable).
- weightedTrickleDown_hess: hyperbolic Hessians of ∂_if ⇒ ∇²f(x) satisfies TD_x (reverse C–S in each link against x).
- isHyperbolic_of_weightedTrickleDown_active: symmetric nonneg Q, TD_x for x > 0, connected on active variables {(Qx)_i > 0} ⇒ hyperbolic (inactive rows are zero; weighted Metzler Hodge index on active block).
- isHyperbolic_hess (Brändén–Huh basic property, proved by trickle-down induction on degree): Lorentzian polynomial of degree n+2 ⇒ ∇²f(x) hyperbolic for every x > 0; closure of hyperbolicity under limits ⇒ every x ≥ 0 (isHyperbolic_hess_of_nonneg).

## TheMixedHessiansOfALorentzianPolynomialAreHyperbolic
- dval c [v_1..v_m] γ = ∂_{v_1}⋯∂_{v_m}∂^γf (∂^γf = γ!c_γ); mixHess c vs γ = Hessian of ∂_{vs}∂^γ f; symmetric in directions (dval_perm).
- Polarization is linkage: mixHess(v::vs, γ) = Σv_i mixHess(vs, γ+e_i); links H_i(u,v) = (Hu)_i. weightedTrickleDown_of_links (hyperbolic, symmetric, nonneg links summing with weights x).
- dval > 0 for positive directions ⇔ monomial above γ of right degree; support above γ M-convex.
- isHyperbolic_mixHess: Lorentzian f, nonneg directions ⇒ every mixed Hessian hyperbolic (induction on #directions + continuity).
- alexandrov_fenchel: D(u,v,vs)² ≥ D(u,u,vs)D(v,v,vs) for u, vs ≥ 0, any v. khovanskii_teissier: k ↦ D(u^k, v^{n−k}) log-concave for u,v ≥ 0.

## TheLorentzianClassIsClosedUnderNonnegativeSubstitution (uses HTGeometry JacobianAlgebraicIndependence, CoordinateDerivationCommute)
- MvPolynomial setting: dirDeriv ∂_v, dirDerivs, hess0 (Hessian at 0), hessAt ∇²p(x). IsLorentzianPolynomial = IsLorentzianPoly on coefficients. IsMixedLorentzian d p: coeff ≥ 0, homogeneous d, hess0(∂_{vs}p) hyperbolic for every nonneg direction list of length d−2.
- hess0(∂_{vs}p) = mixHess(coeff p, vs, 0) ⇒ Lorentzian ⇒ mixed-Lorentzian.
- Differentiation along v ≥ 0 preserves mixed-Lorentzian.
- Nonnegative substitution p(Ay), A ≥ 0, preserves mixed-Lorentzian: chain rule ∂_w(q∘A) = (∂_{Aw}q)∘A, Hessian pullback ∇²(q∘A) = Aᵀ∇²qA, nonneg coefficients preserved.
- Euler for Hessian: (d−2)!∇²p(x) = ∇²(∂_x^{d−2}p) ⇒ ∇²p(x) hyperbolic at every x ≥ 0.
- Strong log-concavity: d p(x)∂_v²p(x) ≤ (d−1)(∂_vp(x))² for x ≥ 0, any v (reverse C–S against x using ∇²p(x)x = (d−1)∇p(x)); Newton inequality of degree-d real-rooted restriction at t = 0.

## TheEulerProductOfLorentzianLocalFactorsIsLorentzian
- Products in complementary variables: p, q Lorentzian supported in V / ¬V ⇒ pq Lorentzian (support = product of M-convex sets; each quadratic derivative is a nonneg multiple of a quadratic derivative of one factor, or symmProd of two nonneg linear forms, or zero).
- Injective renaming preserves Lorentzian (quadratic derivatives pulled back by renameMatrix; zero off image).
- disjointProd ∏ f_p(x_{p,·}) Lorentzian; merge x_{p,i} ↦ x_i is a nonneg substitution ⇒ ∏_p f_p of Lorentzian local factors is mixed-Lorentzian (isMixedLorentzian_prod), also after any nonneg substitution (isMixedLorentzian_prod_subst); product of two Lorentzian is mixed-Lorentzian.
- Nonneg linear forms Lorentzian of degree 1 ⇒ eulerProduct mixed-Lorentzian; isLorentzian_eulerHessian_of_nonneg: Hessian of ∏⟨L_p, X⟩ Lorentzian at every y ≥ 0 (no positivity of local factors needed).

## TheSupportOfAMixedLorentzianPolynomialIsMConvex
- IsHyperbolic.exchange: Q ≥ 0 symmetric hyperbolic, Q_ai > 0, Q_jk > 0 ⇒ Q_aj > 0 or Q_ak > 0 (else e_a + te_i, e_j + e_k span PD plane for small t). Quadratic exchange for mixed-Lorentzian quadratics.
- Exchange for common variable passes to ∂_k p (lower degree); coprime monomials (degree ≥ 3): differentiate along e_a + e_k, exchange lands or produces monomial sharing x^μ, second exchange concludes.
- IsMixedLorentzian.isMConvex by induction on degree ⇒ isMixedLorentzian_iff_isLorentzianPolynomial: signature along nonneg directions forces M-convex support; the two classes coincide (∂^α = ∂ along unit-vector list, exists_unitList).
- quadDeriv_minor: a_{μ+2e_i}a_{μ+2e_j} ≤ a_{μ+e_i+e_j}² (2×2 principal minors nonpositive).
- Coefficient-form closure: products (IsLorentzianPolynomial.mul), nonneg substitution, nonneg directional derivatives, Euler product of Lorentzian local factors after scale map (isLorentzianPolynomial_prod_subst); support of product M-convex.

## TheClosureProducesExactlyTheLorentzianForms
- Hessian of mixed-Lorentzian polynomial at x ≥ 0 is Lorentzian; in particular every Euler product of Lorentzian local factors after nonneg substitution.
- Every Lorentzian Q = Hessian of mixed-Lorentzian quadratic ½xᵀQx (quadForm). isLorentzian_iff_exists_hessAt: Q Lorentzian ⇔ Hessian at nonneg point of a mixed-Lorentzian polynomial. Negative entry ⇒ never a closure Hessian.
- Hessians extract nothing beyond the Lorentzian signature; the atomic intersection form of ζ (negative atom diagonal) is reached only after a change of coordinates (nef shift) — by identification.

## RamanujanAndLorentzianMeetOnlyAtTheWeilBound
- Positive log-concave b with b_0 = 1 ⇒ b_k ≤ b_1^k.
- Local factor Σa_kT^k, a_0 = 1, sign-normalized positive, homogenized: Lorentzian with a_d = (√q)^d ⇒ a_1 ≥ d√q (opposite of Ramanujan a_1 ≤ d√q). Rigidity: Ramanujan + Lorentzian ⇒ a_1 = d√q (maximal factor (1 + √qT)^d, which is Lorentzian).
- At a prime with integral trace: never Lorentzian (d√p irrational). Elliptic: 1 + tT + qT² Lorentzian ⇔ t² ≥ 4q (reverse Hasse); no prime reaches a² = 4p.
- Local L-factors over prime fields are never Lorentzian; positivity at a prime is the Frobenius-ladder trickle-down (Gram), not the local polynomial; Euler-product-closure inputs cannot be local L-factors themselves.

## TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine
- bivPoly homogenization; eval/derivatives at (s,1) are those of J(s) = Σa_ks^k.
- Lorentzian bivariate form ⇒ Laguerre d J J'' ≤ (d−1)J'² on s ≥ 0 (strong log-concavity at (s,1) along (1,0)); J > 0 ⇒ J^{1/d} concave on [0,∞).
- xi_jensen_laguerre_halfLine: every Jensen polynomial ΣC(d,k)γ_{n+k}s^k of ξ satisfies Laguerre on s ≥ 0 unconditionally (d = 2: Turán). RH (real roots, all negative) is the same family on the negative half-line.

## TheAtomicFormIsMetzlerBelowTheSpacing (uses SSHA WeilsFormIsContinuousInTheLevyNorm) — part 1
- Atomic tests f_x = Σ_{n≤N}x_n g(· − log n), g ≥ 0 supported in [0,w]. Weil Q(f) = M(f) + 2C(f)² − 2S(f)², Markov form M = 2θ'(0)‖·‖² + levyEnergy − primeSum.
- markovPair (polar form: L² term + Lévy mixed energy − primePair) symmetric, bilinear on C² compact tests; primePair finite sum on [−R,R]. levyMarkovForm(atomicTest) = Σx_mx_n markovPair(g_m,g_n).
- markovPair_atom_nonpos: |log n − log m| > w ⇒ markovPair(g_m,g_n) ≤ 0 (overlap 0, Lévy cross integrand −g_m g_n(·+y) − g_m(·+y)g_n ≤ 0, prime pairing ≥ 0).
- (cont.) atomicIntersectionGram on H, V, g_1..g_N: pole plane, pole row (∫g_n e^{−u/2}, ∫g_n e^{u/2}), atom block −markovPair. For g ≥ 0 and w < atomSpacing δ_N it is Metzler (Euler gauge). Pole-plane Gram with positive H-row: connected; poleWeight (t,t,1,…,1) gives positive image ⇒ trickle-down regime.
- polarDefect of atomic Gram = weilQuad(finAtomicTest) (2C² − 2S² = 2(∫fe^{−u/2})(∫fe^{u/2})). Hyperbolic ⇔ Weil ≥ 0 on atomic family.
- weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown: nonneg nonzero C² bump on [0,w], w < δ_N: Weil ≥ 0 on atomic family ⇔ TD_π for the atomic Gram. Sign hypothesis is satisfied by ζ on separated atoms; remaining content of Weil positivity there is exactly trickle-down.

## TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing (uses SSHA TheStabilityLawAtTheSpacingScale) — part 1
- (∫|g|)² ≤ w∫g² on [0,w]; shifted bump moments bounded by sup·‖g‖₁; weighted Cauchy–Schwarz (Σ|x_m|a_m)² ≤ (Σμ_mx_m²)(Σa_m²/μ_m).
- atomMargin μ_m = 2θ'(0) + log(1/w) − cross_m − (log N + 2(log4 + 4) − (m/4N) log m); tilted margin: ‖g‖²Σμ_mx_m² ≤ 2θ'(0)‖f_x‖² + levyEnergy − ‖g‖²P_N(y), |y| = |x|, w ≤ δ_N/2.
- fixedWidthRatio c★ = (c₁/2)e^{−(C + 2|θ'(0)| + 1)}; at w ≤ c★δ_N: separated, wN ≤ 1/64, margin grows along the pole μ_m ≥ 1 + (m/8N) log m. m(1 + log N) ≤ 16N + 2m log m.
- (cont.) Pole paid by the tilted margin: A = ∫fe^{−u/2}, B = ∫fe^{u/2}; A² ≤ X‖g‖₁²Σ1/(mμ_m) ≤ X‖g‖₁²(1 + log N); B² ≤ Xe^w‖g‖₁²Σm/μ_m ≤ Xe^w‖g‖₁²·16N²/(1 + log N) ⇒ A²B² ≤ 16e^w(wN)²‖g‖⁴X² ⇒ 2|AB| ≤ ‖g‖²X at w ≤ c★δ_N.
- weilQuad_atomicTest_nonneg (UNCONDITIONAL): real C² bump on [0,w], 0 < w ≤ c★δ_N ⇒ Weil Q(f) ≥ 0 for every real atomic test Σ_{n≤N}x_ng(· − log n), every N ≥ 1. Same for every completely multiplicative sign twin ω (twin_markov_add_pole_nonneg: archForm − twistedPrimeSum + 2AB ≥ 0).
- atomicIntersectionGram_isHyperbolic, weightedTrickleDown_atomicIntersectionGram, hasHyperbolicLinks_atomicIntersectionGram: Lorentzian structure of ζ at the spacing scale (w ≤ c★δ_N, nonneg nonzero bump), pole plane included, uniformly in N. Twist-blind; trickle-down regime c★ < K untouched. Tilted margin grows along the pole direction n^{1/2}, unlike a uniform margin.

## ThePoleDefectControlsTheVRow (uses RAPT TheDeficitOfThePrimeFormIsADirichletEnergy, SSHA TheTiltedPrimeRows)
- H-row n^{−1/2}, V-row n^{1/2}. Pole defect D_N(x) = Σ_{mt≤N}Λ(t)(x_{mt} − x_m/√t)² (Dirichlet energy of pole relations, RAPT deficit).
- vRow_eq: Σ√n x_n = x_1 + edgePart + Σ_m √m x_m R_m, up-row R_m = Σ_{t≤N/m}Λ(t)/log(mt) (distribute √n x_n over edges n/t → n with weights Λ(t)/log n, Σ_{t|n}Λ = log n).
- edgePart² ≤ D_N·Σn/log n ≤ D_N·5N²/log N (N ≥ 3). m R_m ≤ 2BN/log N + √N (Chebyshev, split mt ≷ √N), B = log 4 + 4; Σ mR_m² ≤ (16B² + 16)N²/log N.
- sq_vRow_le (multiplicative Hardy inequality): (Σ_{n≤N}√n x_n)² ≤ (48B² + 51)(N²/log N)(D_N(x) + |x|²), N ≥ 3. Recovers the log N lost by plain Cauchy–Schwarz (N²|x|²).

## ThePoleDefectPaysThePole (uses RAPT TheFinitePartOfTheMarkovFormAtTheSpacing)
- W(f) = M(f) + 2AB (A = ∫fe^{−u/2}, B = ∫fe^{u/2}). Uniform margin pays pole only up to K√log N; tilted margin pays with c★ ≈ 10⁻¹¹; here the Dirichlet energy of pole relations pays it, eventually in N.
- Markov form keeps its defect (eventually in N, atom φ(·/w), w ≤ δ_N/2, wN ≤ markovOverlapBound): M(f) ≥ φ₀‖f‖² + ‖g‖²c₀D_N(x), φ₀ = 2θ'(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2)w − A·wN (A = markovCrossConstant), c₀ = 1 − ε − 32e²wN.
- Defect of |x| ≤ defect of x. Defect pays pole: 2|AB| ≤ c_P e^{w/2} wN ‖g‖²(2|x|² + D_N(x)), c_P = √(2C_H), C_H = 48B² + 51 (H-row by C–S with harmonic sum ≤ 2 log N; V-row by multiplicative Hardy).
- Weil ≥ 0 on every atomic test when φ₀ ≥ 2c_Pe^{w/2}wN and c₀ ≥ c_Pe^{w/2}wN. defectFraction K★(φ,ε) = min(overlap bound, 1/(4(c_Pe^{1/2} + 32e²)), 1/(A + 2c_Pe^{1/2}), exp(2θ'(0) + κ_L(φ) + γ − ε − 2)) > 0: eventually in N, Weil ≥ 0 on every atomic test at w ≤ K★δ_N; Hodge index of atomic Gram at K★ eventually.
- Pole paid by the deficit of the prime form below its sharp counterterm, not by a tilt: vectors with large pole term are far from the pole line, where the defect is large. K★ limited by Chebyshev constants of the cross penalty; finite part vanishes at the Robin–Euler threshold.

## WeilsFormIsPositiveOnEveryTestNearTheLogarithms (uses HTGeometry IntegralCauchySchwarz)
- windowTest f = Σ_{n≤N}G_n(· − log n), arbitrary C² profiles G_n on [0,w]; window norms y_n = ‖G_n‖₂.
- Below the spacing: windows disjoint ⇒ ‖f‖² = Σ‖G_n‖²; lags −log k / +log k pick m = nk / n = mk exactly ⇒ primeSum = Σ_{m,n}P(m,n)⟨G_m,G_n⟩ ≤ atomicWeilForm(y) (|⟨G_m,G_n⟩| ≤ y_my_n, P ≥ 0).
- Lévy energy of window test ≥ Σ levyEnergy(G_m) − 2Σ_{m≠n}y_my_n·(Lévy mass of [log(n/m) ± w] on (0,∞)) ≤ … 2w(1/|log(n/m)| + 1); pair correlation c_mn(s) = 0 for |s| > w.
- levyEnergy_profile_ge: C² bump in [0,w], w ≤ 1 ⇒ levyEnergy G ≥ (log(1/w) + 2c_∞ − (e^{1/2}/2)w)‖G‖² (shape term β ≥ 0 dropped; archRobinConstant = 2c_∞).
- Markov form of window test ≥ φ₀|y|² + c₀D_N(y) with profile-free φ₀ (2c_∞ replaces κ_L(φ)); defect pays pole 2|AB| ≤ c_Pe^{w/2}wN(2|y|² + D_N(y)) (∫|G_n| ≤ √w y_n).
- windowFraction K★_∞(ε) > 0: eventually in N, Weil ≥ 0 on every window test at w ≤ K★_∞δ_N.
- windowTest_of_support: every C² f vanishing off ⋃_{n≤N}[log n, log n + w] (w < δ_N) is a window test (cut f(·+log n) on (−η, w+η), η = (δ_N − w)/2).
- eventually_weilQuad_nonneg_of_support (UNCONDITIONAL): 0 < ε ≤ 1/4, eventually in N, 0 < w ≤ K★_∞(ε)δ_N: Weil(f) ≥ 0 for every C² f supported in ⋃_{n≤N}[log n, log n + w]. Infinite-dimensional space; prime lags log(n/m) reach every rational lag of the horizon.

## TheArchimedeanCrossEnergyIsOneSided
- One-sidedness: pair window [s ± w] with s ≤ −2w carries no Lévy mass on (0,∞); with s ≥ 2w carries ≤ 2wω(s − w) (ω decreasing). Only pairs m < n meet at positive shifts.
- 1/|log n − log m| ≤ m/|n − m| + 1 (log(1+u) ≥ u/(1+u)); sharp rows Σ_{n≠m}1/|log(n/m)| ≤ 2m(1 + log(N+1)) + N.
- psiConstant B_ψ = log 4 + 4/e; ψ(q) ≤ B_ψ q for q ≥ 1. Top atoms with parameter λ > 0: Σ(n/N) log n·x_n² ≤ (1 + 1/λ)D_N(x) + (1 + λ)B_ψ|x|² (edge inequality a² ≤ (1+1/λ)(a−b)² + (1+λ)b²).
- (m/N)(1 + log(N+1)) ≤ (m/N) log m + 1 + log 2.
- Sharp cross penalty (w ≤ κδ_N, 0 ≤ κ ≤ 1/2, λ > 0): levyEnergy f ≥ Σ levyEnergy G_m − wN[(2(1+1/λ)/(1−κ))D_N(y) + L_{λ,κ}|y|²], L_{λ,κ} = (2(1+λ)B_ψ + 2(1 + log 2) + 1)/(1−κ) + 2 (W_mn + W_nm ≤ k_mn, symmetric Schur bound). Constants ≈ 6.7 and 16 at λ = 1/2, κ = 1/10 (vs 236 and 1517 limiting K★ ≈ 6·10⁻⁴).
- With shape term β(G_n) ≥ β‖G_n‖² (bumpRobin): eventually in N, M(f) ≥ φ₀|y|² + c₀D_N(y), φ₀ = 2θ'(0) + log(1/(wN)) + 2c_∞ + β + γ − ε − (e^{1/2}/2)w − L_{λ,κ}wN, c₀ = 1 − ε − (2(1+1/λ)/(1−κ))wN.

## TheSharpMultiplicativeHardyInequality
- Split at N^b (b < 1) instead of √N: n > N^b ⇒ log n > b log N.
- Edge weight E_N: Σn/log n ≤ N(N+1)/(2b log N) + N·N^b/log 2. Up-rows: mR_m ≤ mψ(N/m)/(b log N) + N^b ≤ B_ψN/(b log N) + N^b; U_N: ΣmR_m² ≤ (B_ψN/(b log N) + N^b)²(1 + log N).
- sq_vRow_le_of_upRow_le / sq_vRow_le_split: (Σ√n x_n)² ≤ (1+θ)E_N D_N(x) + (1+1/θ)((1+ζ)U + 1 + 1/ζ)|x|² for any bound U on ΣmR_m²; θ, ζ > 0.
- Asymptotically sharp (next module): E_N ≤ (1/(2b) + η)N²/log N, (1+ζ)U_N + 1 + 1/ζ ≤ ((1+ζ)B_ψ²/b² + η)N²/log N eventually.

## TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold (part 1)
- Pole rows of window test: |A| ≤ √w Σy_n n^{−1/2}, |B| ≤ e^{w/2}√w Σy_n√n.
- Sharp pole bound: 2|AB| ≤ we^{w/2}(ρ'(1 + log N)|y|² + ((1+θ)E_N D_N(y) + (1+1/θ)((1+ζ)U_N + 1 + 1/ζ)|y|²)/ρ') (AM-GM with ρ').
- N^b log N ≤ cN eventually (b < 1); eventually_edgeWeight_le; (c+q)²(1+δ) ≤ c² + δ(c² + 4c + 2); eventually_upWeight_le.
- (cont.) Sharp constants: λ = 1/2, κ = 1/10, b = 9/10, θ = 4, ζ = 1/10, ρ' = 4N/log N. sharpCE = 1/(2b) + 1/100, sharpCU = (1+ζ)(B_ψ/b)² + 1/100; pole bound 2|AB| ≤ wN(sharpPoleX|y|² + sharpPoleD D_N(y)) for log N ≥ 100, w ≤ 1/50.
- sharpFraction K★_sharp(β,ε,a) = min(1/10, 1/(2·sharpCostD), a/sharpCostX, exp(2θ'(0) + 2c_∞ + β + γ − ε − a − 1/25)), C_X ≈ 24.
- eventually_weilQuad_windowTest_nonneg_sharp (UNCONDITIONAL): 0 < ε ≤ 1/2, a > 0; eventually in N, for all β, w ≤ K★_sharp δ_N, window tests with shape term β(G_n) ≥ β‖G_n‖²: Weil ≥ 0. ≈ 0.06 of the spacing for plateau profiles (β → 1, a = 3/2), ≈ 0.03 for arbitrary profiles (β = 0). Constants 1517, 107 → 16, 8.

## TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses (part 1)
- pairCorr c_mn(τ) continuous, supported in [−w,w]; Fubini ∫|c_mn| ≤ ‖G_m‖₁‖G_n‖₁ (≤ w‖G_m‖₂‖G_n‖₂).
- One pair right (s ≥ 2w): ∫_0^∞ω(t)|c_mn(t − s)| ≤ ω(s − w)‖G_m‖₁‖G_n‖₁; left (s ≤ −2w): 0.
- levyEnergy_windowTest_ge_masses: levyEnergy f ≥ Σ levyEnergy G_m − 2Σ_{m≠n}∫_0^∞ω|c_mn(t − log(n/m))|.
- (cont.) two_mul_sum_cross_le: any nonneg array V with V_mn + V_nm ≤ y_my_n·2w(1/(2(1−κ)|log(n/m)|) + 1) has 2Σ_{m≠n}V_mn ≤ wN[(2(1+1/λ)/(1−κ))D_N(y) + L_{λ,κ}|y|²] (reusable cross-penalty lemma).
- ‖G_m‖₁‖G_n‖₁ ≤ w y_my_n; ω(s − w) ≤ 1/(2(1−κ)s) + 1 for w ≤ κs.
- levyEnergy_windowTest_ge_fubini: halved cross penalty, levyEnergy f ≥ ΣlevyEnergy G_m − (wN/2)[…]. Markov form: φ₀ with L_{λ,κ}/2, c₀ = 1 − ε − ((1+1/λ)/(1−κ))wN.

## TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold (uses RHTower ChebyshevPsiErrorInputs) — part 1
- PNT input: ∀η > 0 ∃X₀ ≥ 1, ψ(x) ≤ (1+η)x for x ≥ X₀ (tendsto_psi_div_self).
- upWeightPNT: low atoms N/m ≥ X₀ use PNT (mR_m ≤ (1+η)N/(b log N) + N^b), high atoms m > N/Y keep Chebyshev but form tail of size ≤ Y ⇒ ΣmR_m² ≤ upWeightPNT ≤ ((1+ζ)((1+η)/b)² + η')N²/log N eventually (B_ψ² ≈ 8.2 replaced by 1).
- Parameters λ = 1/4, κ = 3/20, b = 19/20, θ = 2, ζ = 1/20, ρ = 3/2; quarterCE, quarterCU, quarterPoleX/D, quarterCostX = L/2 + poleX.
- (cont.) quarterFraction K★_q(β,ε,a) = min(3/20, (3/4)/C_D, a/C_X, exp(2θ'(0) + 2c_∞ + β + γ − ε − a − 1/25)), C_X ≈ 10.5, C_D ≈ 7.0.
- eventually_weilQuad_windowTest_nonneg_quarter (UNCONDITIONAL, uses PNT): 0 < ε ≤ 1/4, a > 0; eventually in N, every β, w ≤ K★_q δ_N, shape β(G_n) ≥ β‖G_n‖²: Weil ≥ 0. ≈ 0.108 of the spacing for plateau profiles (quarter of Robin–Euler threshold ≈ 0.43), ≈ 0.072 for every profile (vs ≈ 0.16). With |·| on the pole term the linear costs keep this method below ≈ half the threshold even with optimal constants.

## TheOverlapRatioIsTheCoveredMeasure
- atomCover ⋃[log n, log n + w] has measure ≤ Nw; Nδ_N ≤ 1 ⇒ atomic test of overlap ratio K = w/δ_N lives on measure ≤ K.
- ∫_{[a,a+L]}(1 − f)² ≥ L − Nw ≥ L − K. At c★: every atomic test is L²-distance ≥ √(1 − c★) from a unit-interval indicator: proved Hodge-index families not exhaustive.
- Exhaustion needs unbounded overlap: approximating an interval of length L to L²-error ε forces K ≥ L − ε²; covering [0, log N] forces K ≥ log N − ε² (the regime where fixed-width positivity of atomic Weil Grams is RH).
- Adapted families: width w_n ≤ c log(1 + 1/n) (fraction c of local spacing); Σlog(1 + 1/n) = log(N+1); cover ≤ c log(N+1); cells disjoint for c < 1 (Nyquist rate = ratio 1); ∫_{[0,log(N+1)]}(1 − f)² ≥ (1 − c)log(N+1). markovPair_nonpos_of_disjoint (nonneg disjoint ⇒ ≤ 0); adapted atomic Gram Metzler below Nyquist.

## TheStabilityRegimeEndsAtTheRobinEulerThreshold (uses SSHA TheDiamagneticInequality)
- finPole = pole vector n^{−1/2}; qf(−atomicMarkovGram)[d] = −M(Σd_jg_{j+1}).
- Eventually in N, w ≤ δ_N/2 with 2θ'(0) + log(1/(wN)) + κ_L(φ) + γ + ε + (e^{1/2}/2)w < 0 (φ ≥ 0): M(pole test) < 0.
- eventually_not_stability_atomBlock: then no positive π has (−M)π ≤ 0 — atom block has a positive square carried by the pole vector. Stability regime ends at overlap ratio wN ≈ exp(2θ'(0) + κ_L(φ) + γ) (Robin–Euler threshold); beyond, Hodge index of full Gram ⇔ pole plane absorbs it ⇔ TD_π (trickle-down regime proper up to the spacing).

## TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar (uses ACT ShiftedGroundStateOddProfileCoordinates)
- forall_add_two_mul_nonneg_iff: quadratic Q, linear A, B: Q + 2AB ≥ 0 ⇔ Q ≥ 0 on ker A and Q + 2B ≥ 0 on {A = 1}.
- H-row is the pole functional at every width (overlap included): ∫f_x e^{−u/2} = (∫ge^{−v/2})·p(x), p(x) = Σx_n/√n. V-row functional vRowFunctional.
- forall_weilQuad_atomicTest_nonneg_iff: Weil ≥ 0 on all atomic tests ⇔ M ≥ 0 on pole complement {p = 0} and M(f_x) + 2a₀B(f_x) ≥ 0 on {p = 1}, a₀ = ∫ge^{−v/2}. Second condition = one scalar (inf of a quadratic over an affine hyperplane).
- Beyond Robin–Euler threshold: M(pole vector) < 0 with p(pole) = H_N > 0; if Weil ≥ 0 on the atomic family then M ≥ 0 on {p = 0} ⇒ M has exactly one negative direction, paid by the scalar condition. The gap on the pole complement (spectral gap of the prime form below its pole, sharpened by Lévy self-energy) is the open content of the window.

## TheUniformMarginPaysThePoleOnlyUpToARootLogarithm
- Rank-two bound 2(a·d)(b·d) ≥ (a·b − ‖a‖‖b‖)‖d‖², equality at d = ‖b‖a − ‖a‖b.
- marginModel (pole plane, rows a, b, atom block −m·1): hyperbolic ⇔ ‖a‖‖b‖ − a·b ≤ m.
- Atomic pole rows a_n = n^{−1/2}α, b_n = n^{1/2}β ⇒ ‖a‖‖b‖ − a·b ≥ αβN(√(log(N+1)/2) − 1) (H_N ≥ log(N+1), S_N ≥ N²/2).
- not_isHyperbolic_marginModel_eventually: dilated bump at fixed overlap K > 0 and fixed relative margin μ ⇒ margin model not hyperbolic for large N; gap grows like K√log N. Only a margin growing along n^{1/2} (tilt of prime rows) removes the logarithm.

## TheOverlapFrustratesTheMetzlerGauge (uses SSHA TheSelfEnergyOfAnAtomHasConstantOne)
- Negative triangle K_ab, K_bc, K_ac < 0 admits no unimodular gauge making all three nonneg (forces g_i = −g_j around an odd cycle).
- markovPair translation-invariant; test supported in [0,ℓ], ℓ < log 2, has no prime sum; polarization M(a+b) − M(a−b) = 4M(a,b).
- markovPair_shift_pos: nonneg K-Lipschitz C² bump on [0,w], 2w < log 2, κ = 2θ'(0) + log(1/(2w)) > 0, 0 < s ≤ w, 4e^{1/2}K²w²s + 2wK²(2log(1/w) + C₁ + 2|θ'(0)|)s² < κ‖g‖² ⇒ M(g, g(·−s)) > 0 (close atoms meet positively: sum is a narrow bump with self-energy ≈ log(1/w)‖g‖², difference small in Lévy norm).
- atomicMarkovGram_frustrated(_eventually): atoms N−2, N−1, N within the window form a negative triangle of −M ⇒ no gauge makes atom block Metzler; at fixed width for every large N; scale-covariant ⇒ every large fixed overlap ratio once log(1/w) large. Metzler fails beyond the spacing in every gauge: trickle-down at unbounded overlap cannot use atomic coordinates.

## TheMetzlerThresholdOfTheOverlapRatioIsOne (uses SSHA TheSelfEnergyOfAnAtomIsExactlyLogarithmic)
- Odd triangle (one negative, two positive entries) admits no unimodular gauge.
- levyMixed far (y > joint support): = 2⟨a,b⟩ω(y); near shifts (K-Lipschitz, y ≤ 1): ≥ −e^{1/2}K(‖a‖₁ + ‖b‖₁)/2.
- Overlap law markovPair_shift_ge: nonneg K-Lip C² bump on [0,w], 2w < log 2, 0 ≤ s ≤ w: M(g, g(·−s)) ≥ (2θ'(0) + log(1/(2w)))⟨g, g(·−s)⟩ − 2e^{1/2}Kw‖g‖₁ (ω(y) ≥ 1/(2y) integrates to log(1/(2w))).
- markovPair_atom_neg: separated atoms (log(n/m) > w), nonzero bump ⇒ M(g_m,g_n) < 0 strictly (translate overlap ≥ ‖g‖²/2 near y = log(n/m)).
- dilate g₁(·/w): Lipschitz ∝ 1/w, ∫ ∝ w; overlap Lipschitz in shift. Close dilated atoms meet positively for small w if profile overlap at τ₀ is positive.
- δ_N ≥ 1/(N+1); last gap log N − log(N−1) ∈ [δ_N, 1/(N−1)].
- metzlerThreshold_overlapRatio: profile g₁ ≥ 0, positive on (0,1), Lipschitz C²: ρ < 1 ⇒ atomic Gram of g₁(·/(ρδ_N)) Metzler (Euler gauge, all N); ρ > 1 ⇒ for large N atoms N−1, N (overlapping, positive) and 1 (separated, negative) form an odd triangle: no unimodular gauge makes atom block Metzler. Metzler holds exactly up to atomic resolution; trickle-down at ρ > 1 must leave diagonal gauges of the atomic basis.

## TheAtomicMetzlerPropertyIsSelective
- Real twin ω: twinPrimePair Σ ω(k)Λ_k(…), twinMarkovPair, twinMarkovGram, twinAtomicIntersectionGram (pole plane, pole row of ζ; atom block −M^ω). ω ≡ 1 recovers ζ.
- Pole row fixes the gauge: positive H-row ⇒ nonneg unimodular gauge constant on the atoms.
- Pair (1,p), separated atoms: twinPrimePair = ω(p)(log p/√p)‖g‖² (only lag log p meets); Lévy cross ≥ −2wω(log p − w)‖g‖² ⇒ −M^ω(g_1,g_p) ≤ (2wω(log p − w) + ω(p)Λ_p)‖g‖².
- Selectivity: ω(p) = −1 at a prime p ≤ N and 2wω(log p − w) < log p/√p ⇒ twin's Gram has no nonneg gauge; ω ≡ 1 Metzler. Euler-point selection by pole row + archimedean place.

## HyperbolicityIsBlindTheSignIsNot
- twinPrimePair/twinMarkovPair symmetric, bilinear on C² compact tests; twinMarkovPair_self = archForm − twistedPrimeSum; polarDefect_twin = M_ω(f) + 2AB.
- twinAtomicIntersectionGram_isHyperbolic: at w ≤ c★δ_N every completely multiplicative sign twin's Gram has one positive square (tilted margin pays pole for all alike).
- liouville_isHyperbolic_and_not_metzler: Liouville twin λ(n) = (−1)^{Ω(n)} (ζ(2s)/ζ(s), pole on critical line) — Gram hyperbolic at same widths, but N ≥ 2 ⇒ no unimodular nonneg gauge; ζ's Gram Metzler. Hodge index at proved scales carries no arithmetic; the sign hypothesis sees the Euler point.

## TheTowerDeficitIsARowSum (uses RAPT TheSignOfTheTowerFinitePart)
- towerMatrix: 2γ_p + log p on diagonal minus log p·q^{|i−j|} (KMS), q = p^{−1/2}; qf = tower finite part F_p(b) = 2γ_p|b|² + log p(|b|² − K_q(b)). −F_p Metzler.
- KMS row ≤ (1+q)/(1−q); rowSum(−F_p) ≤ 2d_p, d_p = √p log p/(p−1) − γ (tower deficit).
- towerFinitePart_add_nonneg_iff_rowSum: F_p + c|·|² ≥ 0 on every depth ⇔ c dominates every row sum of −F_p on every depth (stability regime π = 1 one way, RAPT sharp sign law c ≥ 2d_p other way). Deficit 2d_p > 0 at small primes is a positive row sum another place must cancel; link accounting = row-sum accounting.

## PolarGluingAndDispersion (uses HTGeometry QuotientFusionProjectionGenesis schurComplement_sum_eq; file ends with `#print axioms` lines)
- anchorSquare (rank-one form agreeing with Q along positive anchor e); anchorReserve R_Q(x) = (xᵀQe)²/Q[e] − Q[x]. Positive anchor: hyperbolic ⇔ reserve ≥ 0 everywhere.
- polarDispersion Σ_i Q_i[e](b_i(x)/Q_i[e] − b(x)/Q[e])² (weighted variance of normalized polar rows); polarGluingCorrection = Σ anchorSquare(Q_i) − anchorSquare(ΣQ_i), quadratic form = dispersion ≥ 0 (Schur complement identity).
- Exact gluing law: R_{ΣQ_i} = ΣR_{Q_i} − dispersion. isHyperbolic_sum_iff_dispersion_le: ΣQ_i hyperbolic ⇔ dispersion ≤ Σ local reserves (no local signature assumed). Zero local reserve: hyperbolic ⇔ all normalized polar readings agree (alignment).
- polarGlue = ΣQ_i − correction: preserves anchor row; reserves add exactly; hyperbolic local forms ⇒ glued form hyperbolic (construction of a new form, not a signature theorem for a given form). Grouping associative; commutes with anchor-preserving pullback.
- Calibration: tiltedPlane(t,r) = [[1,t],[t,t²−r]] hyperbolic ⇔ r ≥ 0; opposite slopes ±t sum hyperbolic ⇔ t² ≤ r; correction = diag(0, 2t²).

## TheTiltedMarginPaysThePolarDispersion
- atomPiece at m: share J/N of pole plane, pole couplings of g_m, tilted margin −‖g‖²μ_m; pieces sum to tiltedModel; Q_m[e] = 2/N at anchor e = H + V.
- Exact decomposition: atomicIntersectionGram = tiltedModel + tiltedResidual (‖g‖²diag(μ) − M), residual NSD at w ≤ δ_N/2 (row-by-row stability law).
- tiltedModel hyperbolic at w ≤ c★δ_N; polarDispersion_le_sum_anchorReserve: dispersion of atom pieces' polar rows ≤ Σ local reserves. Answers polar compatibility in the stability regime: archimedean self-energy, distributed by the tilt of prime rows, pays the polar dispersion. Twist-blind.

## TheHalfDefectIsTheOptimalHodgeRepair (uses ACS TheFrobeniusSpanDefectCountsTheOuterEigenvalues, WhichArithmeticDataForceTheSign; HTGeometry ExponentialKernelAlternatingInertia; has `#print axioms` lines)
- Frobenius evaluation split under circle reflection z ↦ 1/z̄: even part (β^k + r(β)^k)/2, odd part (β^k − r(β)^k)/2. spanGram + oddGram = evenGram (PSD); halfDefectRepair = oddGram PSD.
- Odd Gram energy = Σ|(eval at β − eval at r(β))/2|²; on real classes = half the Frobenius reflection defect. Commutes with window restriction.
- Rank: oddEval factors through one coordinate per distinct outer eigenvalue (|z| > 1) ⇒ rank ≤ #outerSpectrum; any R with spanGram + R PSD (window ≥ #spectrum) has rank R ≥ #outerSpectrum (neg index of spanGram = #outer). Exact: rank = #outer; ∃ PSD repair of rank ≤ r ⇔ #outer ≤ r.
- Sharp scalar: spanGram + t·repair PSD ⇔ unitary or t ≥ 1 (pairClass test vector has zero even evaluation).
- hodgeCompletion B G = fromBlocks(polePlane, B, Bᴴ, BᴴPB − G): posIndex = 1 + negIndex G; hyperbolic ⇔ G PSD; correcting G changes only the graph block (pole couplings preserved).
- optimal_frobenius_hodge_repair: on the spectrum window, half-defect repair is PSD, has minimal rank #outer, restores Hodge index for every pole row B, sharp threshold t ≥ 1. Zero row/column at the diagonal graph Γ_0. spanDefect + ½ reflection defect ≥ 0 for all real d.

## ThePoleIsInfinitesimalRelativeToThePrimeDefect (has `#print axioms` lines after end)
- ∫g(u − log n)e^{u/2} = √n∫ge^{v/2}; positive pole moment = atom moment × Σ√n x_n (exact square-root row).
- p(x)² ≤ |x|²·2 log N (harmonic C–S); (A_gB_g)² ≤ e^w(w‖g‖²)².
- sq_poleMoments_le_defect: (AB)² ≤ 2C_He^w(wN)²‖g‖⁴|x|²(D_N(x) + |x|²).
- Weighted Young: 2|AB| ≤ ‖g‖²(εD_N(x) + (ε + 2C_He^w(wN)²/ε)|x|²) for every ε > 0.
- poleRelativeCost(K,ε) = ε + 2C_He K²/ε; at bounded overlap w ≤ K/N, w ≤ 1: 2|AB| ≤ ‖g‖²(εD_N + poleRelativeCost(K,ε)|x|²) — pole source infinitesimally bounded relative to the prime defect, horizon-independent mass cost.
