# 33 RenormalizedArithmeticPotentialTheory — mathematical facts log

## TheCoupledSurvivalLaw
- Positive symmetric form: quad B x = 0 ⇔ Bx = 0; survivalCone B = ker B (RBG survivalCone). Coupled counterterm [[A, C],[Cᵀ, D]] positive ⇒ Dw = 0 ⇒ Cw = 0, rank C ≤ rank D. Survival (u,w): Au + Cw = 0, Cᵀu + Dw = 0.
- A nondegenerate: no pure prime vector survives; dim survival ≤ #β; rank ≥ #α; prime projection of survival has dim ≤ rank D (a partner pays at most its rank).
- Rank-one partner [[1, C],[Cᵀ, vvᵀ]] ⇒ C = b vᵀ with |b| ≤ 1; prime survival = ℝb if |b| = 1, else 0.
- Counterterm of a symmetric family is symmetric. Torsion germ prime block ⇒ prime block of counterterm = c·1, c > 0; coupled_torsion_survival: no pure torsion survival, rank ≥ #S, torsion survival dim ≤ rank of partner block; coupled to archimedean lattice germ (counterterm 𝟙𝟙ᵀ) at most one torsion direction survives.

## TheArchimedeanPlacePaysTheArithmeticPoint
- c_1 ≡ 1 (Ramanujan mode of O_1 is constant). jointMode: c_n/√φ(n) on orbits, 1 on k archimedean nodes; jointGram = Cesàro Gram over common period q. Ramanujan orthogonality mean(c_m c_n) = φ(n)δ_{mn}.
- jointGram = [[1, e₁𝟙ᵀ],[𝟙e₁ᵀ, 𝟙𝟙ᵀ]] (e₁ = arithmetic point, norm 1 if 1 ∈ S). Prime survival = ℝe₁ if 1 ∈ S else 0: archimedean place pays exactly the arithmetic point; no orbit of order ≥ 2 survives.
- jointGerm (twisted Abel germ of joint modes at nonnegative nodes) is PSD, regularized with counterterm jointGram; renormalized limit ≥ 0 on (−s e₁, w) with Σw = s; survival prime part = −(Σw)e₁.

## GardingIsAFiniteRankSurvival
- NonnegOnKernel A ℓ: A ≥ 0 on common kernel of k functionals. functionalCounterterm Σℓ_iℓ_iᵀ: PSD, symmetric, rank ≤ k, survival cone = common kernel. Conversely A ≥ 0 on survival cone of PSD rank-≤k B ⇒ NonnegOnKernel with k functionals spanning range B.
- garding_iff_survival; garding_iff_regularized: ⇔ A + sB + ε|x|² eventually ≥ 0 for every ε. finrank_le_of_garding: negative-definite subspaces have dim ≤ k. RH (W ≥ 0) ⇔ counterterm of Weil's form can be zero.

## TheCovariantCountertermIsTheAnomaly
- renormalizedPrimeForm S h x = −Σ x_m x_n P(m,n) + Σ h(n)x_n². Hecke transport changes it by Σ(h(tn) − h(n))x_n²; covariant ⇔ h(tn) = h(n) ⇔ h constant on positive orders (scalar ⇒ survival cone {0}: covariance and survival exclude each other for diagonal counterterms).
- Exact Schur-weighted row: Σ_n P(m,n)√(m/n) = A(⌊N/m⌋) + log m, A(y) = mertensSum y = Σ_{t≤y}Λ(t)/t (up: Mertens sum; down: log m). Row bounds: log N − log8 − 4 ≤ A(N/m) + log m ≤ log N + log4 + 4.
- poleVector u_n = n^{−1/2}: (Pu)_m = (A(N/m) + log m)u_m — approximate eigenvector with eigenvalue log N. atomicWeilForm ≤ (log N + log4 + 4)|x|²; P_N(u) ≥ (log N − log8 − 4)|u|²; covariantCounterterm_sandwich: optimal scalar counterterm ∈ [log N − log8 − 4, log N + log4 + 4] (= regulator anomaly log N = log #ker[N], constant one).

## TheAnomalyCostsHalfALogarithm
- harmonicSum H_N ≤ 1 + log N, ≥ 1 for N ≥ 1; Σu_n² = H_N. φ(mt) ≤ tφ(m) ⇒ normalized intersection Λ(t)√(φ(m)/φ(mt)) ≥ P(m,mt) = Λ(t)/√t.
- torsionTest y_n = (nφ(n))^{−1/2}: off-diagonal y_m y_n I(m,n) ≥ u_m u_n P(m,n); diagonal y_n² I(n,n) = c(n)/n; torsionPairing(y) ≥ P_N(u) + Σ c(n)/n; selfMass(y) = H_N.
- Σ_{n≤N} log n/n ≥ ½log²(N+1) − 1 (telescoping log²; Σ1/n² ≤ 2 − 1/N). log p/(p(p−1)) ≤ 4p^{−3/2}; Σ d(n)/n ≤ K·H_N (tameConstant K = Σ4n^{−3/2}).
- torsionCounterterm_ge: κ ≥ (3/2)log N − (log8 + 4 + K + 3/2). anomaly_cost: torsion counterterm exceeds covariant one by ≥ ½log N − C (self-intersection = potential of cocycle costs half a logarithm; continuum model predicts e/(e−1)).

## TheTorsionCountertermIsAtMostTwoLogarithms
- heckeExcess e(t) = Λ(t)(φ(t)^{−1/2} − t^{−1/2}) ≥ 0; e(p^k) ≤ (log p/(p−1))/√(p^k); Σ_k e(p^k) ≤ (log p/(p−1))/(√p − 1) ≤ 32p^{−5/4}; Σ_{t≤N} e(t) ≤ C_e = Σ32n^{−5/4} uniformly.
- normalizedCharge z_n = √φ(n)y_n (self-mass = |z|²). φ(m)φ(t) ≤ φ(mt) ≤ tφ(m) ⇒ on Hecke pairs y_m y_{mt}I(m,mt) ≤ z_m z_{mt}Λ(t)/√t + ½(z_m² + z_{mt}²)e(t); off-diagonal torsion pairing ≤ Weil kernel + excess (upExcess). Excess Schur rows ≤ 2C_e.
- renormalizesAt_two_log: κ = 2log N + log4 + 4 + 2C_e works (diagonal c(n) ≤ log n; Weil form log N + O(1); excess). torsionCounterterm_window: minimal κ ∈ [(3/2)log N − C₁, 2log N + C₂]; anomaly cost between ½log N − C and log N + C.

## TheHorizonCountertermIsPolar
- truncPole u^{(M)}_n = n^{−1/2}𝟙_{n≤M}; stepProfile Σc_i u^{(M_i)}; primeBilinear; polarFunctional ℓ(x) = Σx_n n^{−1/2} (one factor of Weil's pole term).
- Pole rows: ⟨u^{(M)}, P u^{(M')}⟩ = Σ_{m≤M}(A(⌊M'/m⌋) + log m)/m for M ≤ M' ≤ N; sandwich (log M' − log8 − 4)H_M ≤ · ≤ (log M' + log4 + 4)H_M; log M ≤ H_M ≤ 1 + log M. |⟨u^{(M)},Pu^{(M')}⟩ − H_M H_{M'}| ≤ (log8 + 5)H_{min}.
- Step profiles: |P_N(x) − ℓ(x)²| ≤ (log8 + 5)Σ|c_i||c_j|H_{min(M_i,M_j)}; |x|² = Σc_ic_jH_{min}; on polar hyperplane ℓ = 0 the prime form is bounded by absolute mass. Horizon divergence = ℓ(x)² (rank one, polar) — same shape as archimedean lattice germ counterterm 𝟙𝟙ᵀ; Rayleigh quotient log N(∫g)²/∫g² + O(1).

## TheHorizonDivergenceLivesOnTheTorsionOrbits
- Fix prime p. Λ-atoms divisible by p are powers of p: Σ_{p|t}Λ(t)/t ≤ log p/(p−1); Σ_{t|m,p|t}Λ(t) ≤ v_p(m)log p. Changing valuation along a Hecke pair needs p | n/m. offClassRow (row restricted to other valuations) ≤ log p/(p−1) + v_p(m)log p.
- classPole w_j = u^{(M)}𝟙_{v_p(n)=j} (valuation classes = torsion orbits O_{p^{J+1−j}}). ⟨w_j,Pw_j⟩ ≥ (log M − c_j)|w_j|², c_j = log8 + 4 + log p/(p−1) + j log p; j ≠ j': 0 ≤ ⟨w_{j'},Pw_j⟩ ≤ (log p/(p−1) + j'log p)|w_{j'}|²; disjoint supports.
- atomicWeilForm_classCombination_ge: P_M(Σa_jw_j) ≥ (log M − C_{p,J})|x|². horizonCounterterm_rank_unbounded: for every J, K, large M, any J functionals have a common nonzero zero x with P_M(x) > K|x|² — no rank-≤J counterterm plus bounded scalar renormalizes at the horizon. Horizon counterterm ~ identity on arithmetic factor ⊗ polar projection on log-scale factor.

## TheHorizonCountertermIsATensorProduct
- classDensity δ_j = (1 − 1/p)/p^j = φ(p^{J+1−j})/p^{J+1} (orbit size per point of μ_{p^{J+1}}). unitHarmonic Σ_{k≤X,p∤k}1/k = H_X − H_{X/p}/p = (1 − 1/p)log X + O(2 + log p). classMass = unitHarmonic(M/p^j)/p^j = δ_j log M + O(3 + (j+1)log p).
- Class Gram two horizons: ⟨w_j^{(M)},Pw_{j'}^{(M')}⟩ = Σ_{m∈class j}classRow/m. One class: |⟨w_j^{(M)},Pw_j^{(M')}⟩ − δ_j^{−1}|w_j^{(M)}|²|w_j^{(M')}|²| ≤ C_{p,J}|w_j^{(M)}|² (tensorConstant). Cross classes: 0 ≤ · ≤ C_{p,J}|w_j^{(M)}|².
- Tensor law: class-wise step profiles x: |P_N(x) − Σ_j δ_j^{−1}ℓ_j(x)²| ≤ C_{p,J}H_N(Σ|c|)², ℓ_j = classPolar. Survival = class-wise polar hyperplane. Horizon counterterm = (torsion counterterm diagonal weighted by φ) ⊗ (archimedean polar projection).

## TheHorizonCountertermIsHeckeCovariant
- heckeShift (T_t x)(n) = x(n/t) on multiples of t. P_{tN}(T_t x) = P_N(x) (Hecke invariance of Weil kernel). T_p w_j^{(M)} = √p·w_{j+1}^{(pM)}; ℓ_{j+1}(T_p x) = ℓ_j(x)/√p, ℓ_0(T_p x) = 0; δ_{j+1} = δ_j/p.
- tensorCounterterm C(x) = Σ_j δ_j^{−1}ℓ_j(x)²: C_{J+1}(T_p x) at pN = C_J(x) at N; finite part P − C exactly invariant under [p] (no anomaly at the horizon: degree appears as density scaling 1/p compensated by p^{−1/2} of polar functional).

## TheFinitePartIsEulersConstant
- Σ_{t≤y}Λ(t)/t = log y − γ + o(1) (RHTower, from −ζ'/ζ Laurent + PNT); H_M = log M + γ + o(1). Roundoff 0 ≤ log M' − log⌊M'/m⌋ − log m ≤ 1/⌊M'/m⌋.
- For every η > 0 ∃C: |⟨u^{(M)},Pu^{(M')}⟩ − H_M H_{M'} + 2γH_M| ≤ ηH_M + C. Step profiles: P_N(x) = ℓ(x)² − 2γ|x|² + o(|c|-mass); polar hyperplane: P_N(x) = −2γ|x|² + o. Renormalized prime place = scalar −2γ on survival cone (constant term of −ζ'/ζ once per Hecke direction); enters Weil's form with minus ⇒ +2γ per unit mass (positive).

## TheHorizonLawsHoldForProfilesOfBoundedVariation
- Summation by parts: G(n)n^{−1/2} = Σ_{n≤m≤N}∂G(m)u^{(m)}_n, ∂G(m) = G(m) − G(m+1), ∂G(N) = G(N); every vector is a step profile; horizonVariation V_N(G) = Σ|∂G(m)|.
- Every profile: |P_N(x) − ℓ(x)²| ≤ (log8 + 5)H_N V_N(G)²; ∀η ∃C: |P_N(x) − ℓ(x)² + 2γ|x|²| ≤ (ηH_N + C)V_N(G)². Class-wise profiles: tensor law with C_{p,J}H_N(ΣV_N(G_j))².
- G(n) = g(log n/log N), g ∈ BV[0,1]: V_N(G) ≤ Var g + |g(1)| uniformly in N (points log n/log N partition [0,1]). Hence P_N(x) = ℓ(x)² − 2γ|x|² + o(log N); classwise P_N = Σδ_j^{−1}ℓ_j² + O(log N). ℓ² ~ (log N)², mass ~ log N: laws determine horizon form of every BV profile up to o(mass).

## TheFinitePartIsTheTowerForm
- localEuler γ_p = γ + log p/(p−1). pPowerMertensSum Σ_{t≤y,p|t}Λ(t)/t → log p/(p−1); unitMertensSum A_{p'}(y) = log y − γ_p + o(1). unitHarmonic − (1−1/p)log X → (1−1/p)γ + log p/p; classMass = δ_j(log M − j log p + γ_p) + o(1).
- Exact rows: Σ_{t|m,p|t}Λ(t) = v_p(m)log p; v_p(mt) = v_p(m) ⇔ p∤t. Inside class (v_p(m) = j): classRow_j(m) = A_{p'}(⌊M/m⌋) + log m − j log p exactly. Across (j < v_p(m)): classRow_j(m) = log p exactly (single term n₀ = m/p^{v−j}, Λ(p^k)). ⇒ ⟨w_{j'},Pw_j⟩ = log p·|w_{j'}|² exactly for j < j'.
- Inside class: ⟨w_j,Pw_j⟩ = δ_j^{−1}|w_j|⁴ − 2γ_p|w_j|² + o(|w_j|²). Class combinations: P_M(x) = Σδ_j^{−1}(a_jm_j)² − 2γ_pΣa_j²m_j + log pΣ_{j≠j'}a_ja_{j'}m_{max(j,j')} + Σa_j²(ηm_j + C).
- δ_{j+k} = δ_j/p^k; normalized coupling m_max/√(m_jm_{j'}) → p^{−|j−j'|/2}: finite part = −2γ_p·1 + log p(K_{p^{−1/2}} − 1) = AIT tower form of p with local Euler constant. Summed over all classes tower couplings 2Σjδ_j log p = 2log p/(p−1) cancel local Euler shift ⇒ uniform −2γ recovered.

## TheFiniteSieveCountertermIsHeckeCovariant (finite sieve Q, classes d supported on Q)
- SieveSupported Q t: t | primorial(Q)^k. sieveClassPole Q (td)(tn) = u_t·sieveClassPole Q d n; sieveClassPolar(td, tM, T_t x) = sieveClassPolar(d,M,x)/√t; sieveClassDensity(td) = density(d)/t.
- sieveTensorCounterterm (Σ_i polar_i²/density_i) invariant under every supported Hecke shift; finite part primeBilinear − counterterm exactly Hecke covariant for arbitrary signs. Counterterm = 0 ⇔ every class polar = 0. Class mass > 0 once d ≤ M. Polar coordinates surjective (independent) once all classes visible (normalizedSieveProfile).

## TheFiniteSieveCountertermIsPolarOnStepProfiles
- sieveTruncTowerKernel(d,e,A,B) = u_d u_e P(d,e)·sievedHarmonic(min(A/d,B/e)); sieveStepProfile Σ_r c_r sieveTruncPole(d(a r), M r).
- Same-class mass |Σ|² = Σc_rc_s[d_r = d_s]classMass(min). Counterterm expands into same-class mass products / density.
- exists_sieveStepProfile_finitePart_bound: |P_N(x) − C(x) + 2γ_Q|x|² − Σc_rc_s towerKernel| ≤ (ηH_N + C)(Σ|c|)², C independent of class orders, cutoffs, number of generators. Cross-class Grams exact (primeBilinear_sieveTruncPole_cross = u_du_eP(d,e)·sievedHarmonic(min)). exists_sieveStepProfile_tensor_bound: |P_N − C| ≤ K(H_N + 1)(Σ|c|)².

## TheSignOfTheTowerFinitePart
- towerFinitePart F_p(b) = 2γ_p|b|² + log p(|b|² − K_q(b)), q = p^{−1/2}, K_q = KMS form (AIT kmsForm, entries q^{|i−j|}). towerDeficit d_p = √p log p/(p−1) − γ; γ_p − log p·q/(1−q) = −d_p.
- F_p(b) ≥ −2d_p|b|² (K_q ≤ (1+q)/(1−q)). K_q(1_N) = N(1+q)/(1−q) − 2q(1−q^N)/(1−q)²; F_p(1_N) = −2Nd_p + 2q log p(1−q^N)/(1−q)² (uniform profile extremal).
- Sign law: F_p + c|·|² ≥ 0 at every depth ⇔ c ≥ 2d_p; F_p ≥ 0 ⇔ d_p ≤ 0 ⇔ √p log p ≤ γ(p−1). d_2 > 0; d_p ≤ 0 for p ≥ 2^16.

## TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven
- √x log x/(x−1) = u/sinh u, u = log x/2; d_p = u/sinh u − γ strictly decreasing in p, > −γ. 0.5753 < γ < 0.5777 (Euler–Maclaurin n=4, n=2). d_43 > 0 > d_47. Prime p: d_p > 0 ⇔ p ≤ 43; F_p ≥ 0 at every depth ⇔ p ≥ 47. Exactly 14 primes 2..43 carry deficit 2d_p.

## TheArchimedeanPlacePaysTheTowerDeficit
- valuationGram: diagonal −m_j(j + 1/(p−1)), off-diagonal m_{max(j,j')}; Metzler, symmetric; for m_{j+1} ≤ m_j/p row sums ≤ 0 (tails ≤ m_j/(p−1)) ⇒ NSD (ALG Metzler dichotomy): Σ_{j≠j'}a_ja_{j'}m_{max} ≤ Σa_j²m_j(j + 1/(p−1)).
- classMass_succ_le: |w_{j+1}|² ≤ |w_j|²/p at every horizon.
- towerFinitePart_add_valuation_ge: F_p(b) + Σ j log p·b_j² ≥ (γ + γ_p)|b|² for every prime (valuation potential j log p left by archimedean matching pays the deficit; uses m_j = p^{−j}, a_j = b_j p^{j/2}).
- eventually_atomicWeilForm_classCombination_le: ∀J, η, eventually in M, every class combination: P_M(x) ≤ (log M − γ + η)|x|². Sharpness: P_M(u^{(M)}) ≥ (log M − γ − η)|u|² eventually. Pole = extremal class profile; operator diag(j log p) + γ_p + log p − log p K_{p^{−1/2}} has exact eigenvector p^{−j/2} with eigenvalue γ.

## TheMatchedPrimePlaceHasAHodgeIndexOnTheClasses
- Raw prime kernel on ladder 1,p,…,p⁵ has two positive squares (no local Lorentzian structure); matched against log M − γ it has Hodge index.
- sum_cross_add_gap_le_valuation: Metzler stability identity keeping Laplacian ½Σm_max(a_j−a_k)²; m_max ≥ m_jm_k/m_0 ⇒ Σ_{j≠j'}a_ja_{j'}m_max + (SΣm_ja_j² − (Σm_ja_j)²)/m_0 ≤ Σa_j²m_j(j + 1/(p−1)).
- ℓ(Σa_jw_j) = Σa_j|w_j|². towerMass g_J = Σ_{j≤J}p^{−j}; Σ_j|w_j|² ≥ (g_J − η)|w_0|² eventually; |w_0|² → ∞.
- Gap: P_M(x) + (g_J − η)log p|x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²)ℓ(x)²; on ℓ = 0: P_M ≤ (log M − γ − g_J log p + 2η)|x|².
- eventually_isHyperbolic_classHodgeGram: 0 < η ≤ min(1/2, log p/4): Gram of P_M − (log M − γ − η)|·|² on class poles has ≤ 1 positive square (pole carries it). Gap → p log p/(p−1) as J → ∞ (first excitation of valuation tower operator above ground γ); minimum 2log2 at p = 2.

## ThePoleIsTheTopOfThePrimeForm
- Weighted Schur test: v > 0, Pv ≤ Rv entrywise ⇒ P_N(x) ≤ R|x|².
- Rows of √n: Σ_nP(m,n)√n ≤ √m(ψ(⌊N/m⌋) + ½log m) (up-tower = Chebyshev ψ; down ratios n/m ≤ ½). ψ(q) ≤ (log4 + 4)q.
- Tilted pole v_n = n^{−1/2}(1 + ηn/N), η = ε/(2(log4+4)): eventually (Pv)_m ≤ (log N − γ + ε)v_m for all m ≤ N (bulk rows by Mertens A(⌊N/m⌋) + log m ≤ log N − γ + ε/2; top rows tilt pays (ηm/N)(½log N − γ)).
- covariantCounterterm_sharp: eventually P_N ≤ (log N − γ + ε)|·|² on every vector, and every dominating scalar ≥ log N − γ − ε. Pole is extremal over all atomic vectors; prime place finite part −γ.

## TheValuationTowerIsExactlySolvable
- Tower operator (H_p b)_i = (i log p + γ_p + log p)b_i − log pΣ_j q^{|i−j|}b_j; pole gauge b_j = q^jy_j: H_p = γ + log p·L, L Dirichlet form of μ_j = p^{−j} (Σ_{i<j}p^{−j}(y_i − y_j)²); towerGaugeOp.
- Exact eigenvectors (infinite tower): pole 1 ↦ γ; valuationStep y_k = 1_{j≥k} − (p−1)^{−1}1_{j=k−1} (k ≥ 1) ↦ γ_p + k log p. Spectrum {γ} ∪ {γ_p + k log p}; first gap p log p/(p−1), later gaps log p.
- Sharp gap: row sums of valuation Gram ≤ −m_J/(p−1) (deeper mass); completed tower mass Σ_{j≤J}|w_j|² + |w_J|²/(p−1) ≥ (p/(p−1) − η)|w_0|² eventually (Σp^{−j} + p^{−J}/(p−1) = p/(p−1)).
- eventually_atomicWeilForm_classCombination_sharpGap_le: P_M(x) + (p/(p−1) − η)log p|x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²)ℓ(x)², uniformly in depth J. At p = 2 gap 2log2 = observed gap between top two eigenvalues of atomic prime form.

## TheAdjunctionEnergySeparatesValuations
- primeExcitationWeight(p,k) = k + [k≠0]/(p−1) ∈ ℚ, strictly increasing in k. finitePrimeExcitationEnergy Σ_p weight(p,e_p)log p injective in valuation labels (ℚ-linear independence of log p). tameDifferent n ≥ 0, ≤ log n (torsion adjunction selfIntersection ≥ 0).

## TheConductorEnergyKeepsALogarithmicReserve
- n ≤ 2φ(n)² (odd n: n ≤ φ(n)²; only p = 2 loses). |ramanujanLagCoefficient m h| ≤ h² for h > 0 (gcd-divisor formula Σ_{d|(m,h)} dμ(m/d)).
- φ ∈ C², supp ⊆ [0,1]: |shellCorrection φ c m| ≤ 2c⁴/φ(m); ≤ 1 once m ≥ 8c⁸ (polynomial conductor cutoff). completeWeilSelfFinitePart(φ,c) = (·,1) − log c.
- completedConductorEnergy_ge_logarithmic_reserve: for δ ∈ [0,1]: δ(ramanujanAdjunctionEnergy m − conductorLogarithmicLoss φ c) ≤ completedConductorEnergy φ c m, loss = |γ| + |finitePart_1 − γ| + 2log8 + 16log(2c) + 1 (small conductors: positivity; large: shell ≤ 1).

## TheSieveClassesAreValuationCoordinates
- sieveValuationEquiv: SieveClass Q (supported positive integers) ≃ (Q → ℕ), no exponent cutoff; log n = Σ_p e_p log p; agreement off one sieve prime ⇔ agreement of complementary coordinates.

## TheSieveExcitationsHaveAdjunctionEnergy
- primeBlaschkeParameter q_p = p^{−1/2}; q²/(1−q²) = 1/(p−1). hardyNumberEnergy(q_p,k) + 1/(p−1) = primeExcitationWeight(p,k) (ground correction cancels Euler constant).
- tameDifferent n = Σ_{p|n} log p/(p−1) (sum over occupied sieve primes). finitePrimeExcitationEnergy(e) = log n + tameDifferent n (n ↔ e). n ↦ log n + tameDifferent n injective on SieveClass Q; 1 + log n + tame ≥ 1, → ∞ cofinitely (no finite accumulation).

## TheSievePrimeKernelIsABoundedOperator
- SieveClassL2 Q = ℓ²(SieveClass Q); sieveCoordinateUnitary ℓ²(SieveClass) ≅ ℓ²(Q → ℕ) via valuations. sievePrimeCoordinateOperator = Σ_{p∈Q} log p·(KMS_{p^{−1/2}} on coordinate p − 1): bounded self-adjoint; matrix entries = weilPrimeKernel(m,n) exactly (each fibre = ladderKernel: nonzero only if m,n agree off p, value log p·(q^{|v_p(m)−v_p(n)|} − δ)). sievePrimeOperator = bounded self-adjoint extension of literal prime kernel on supported integers.

## TheSieveOperatorHasTheAdjunctionEigenbasis
- sieveAdjunctionOperator = (log n + γ_Q)·x − P x on maximal log-weighted domain (closed, self-adjoint; unitary conjugate of finiteBlaschkeNumberOperator). Domain ⇔ (log n·x_n) ∈ ℓ².
- sieveAdjunctionBasis: Hilbert basis indexed by SieveClass Q, coefficients = Π_p hardyBlaschkeCoefficient(q_p, v_p(m), v_p(n)) (product of local Blaschke/Hardy number bases).
- Eigenvalues matchedSieveEnergy(m) = γ + log m + tameDifferent m = γ + 2log m − selfIntersection(m) (torsion adjunction); injective ⇒ every eigenspace a line; no other point eigenvalues. Local Euler corrections cancel on unexcited primes (finiteBlaschkeEnergy_sieve).

## TheInversePrimeKernelHasSubcriticalValuationCoordinates
- inversePrimeKernel(m,n) = Λ(n/m)/(n/m) (multiplier 1/t instead of t^{−1/2}); on ladder c·p^i: log p·kmsEntry(1/p,i,j) off diagonal (parameter 1/p, subcritical). Nonzero entry changes exactly one prime coordinate; sieve sum over ladders; fibre = log p(KMS_{1/p} − 1).

## TheInversePrimeNumberOperatorHasOccupationEnergy
- inversePrimeParameter 1/p; inversePrimeEuler Σ log p/(p²−1) = Σ_k Λ(p^{k+1})/p^{2(k+1)} (outgoing inverse-square mass). inversePrimeOccupationEnergy Σ_p log p·[e_p≠0](e_p + 1/(p²−1)) ≥ 0.
- inversePrimeCoordinateKernel bounded, entries = inversePrimeKernel. Number operator (log n + γ_inv)x − Kx with complete product eigenbasis; finite literal vectors in domain; finite energy Σ(log m + γ_inv)f² − ΣΣ f f K = Σ_e occupation(e)|coeff|² ≥ 0 (positive).

## TheFiniteSieveHorizonDefectHasTheClassEnergy
- normalizedSieveProfile norm = Σb_i²·mass_i/density_i; mass/density − log M → γ_Q − log d; (mass/density)/log M → 1.
- (counterterm − log M|x|²)/log M → Σb_i²(γ_Q − log d_i). Matched defect: (P_M(x) − log M|x|²)/log M → −Σ(γ_Q + log d_i)b_i² + ΣΣb_ib_jP(d_i,d_j) = −quadratic form of diag(log d) + γ_Q − P_Q.

## TheAdjunctionResolventIsCompact
- Shifted operator (1 − γ) + adjunction has eigenvalues 1 + log m + tame(m) ≥ 1; inverse bounded on whole ℓ², maps into domain, compact (energies → ∞ cofinitely).

## TheSieveHorizonDefectIsTheAdjunctionOperator
- Finite real class vectors in domain; ⟨x, A x⟩ = Σ(γ_Q + log d_i)b_i² − ΣΣb_ib_jP(d_i,d_j). tendsto_sieveHorizonDefect_adjunction: matched horizon defect/log M → −⟨x, A x⟩ (actual sieve adjunction operator).

## FiniteSieveProfilesHaveLogarithmicConductorTails
- On domain: Σ_m(log m + tame m)|⟨e_m,x⟩|² = ⟨x,Ax⟩ − γ|x|² (energy above Euler ground). Finite class vectors: Σ_m(log m + tame)|coeff|² = Σ(log d_i + γ_Q − γ)b_i² − ΣΣb_ib_jP(d_i,d_j) ≥ 0, and ≤ 2Σ(log d_i + γ_Q − γ)b_i² (positivity on |b| pays signed kernel since P ≥ 0).
- Conductor tail: Σ_{m>R}|coeff_m|² ≤ 2Σ(log d_i + γ_Q − γ)b_i²/log R; with d_i ≤ A: ≤ 2(log A + γ_Q − γ)/log R·|b|². Independent of sieve modulus.

## TheSieveEigenbasisIsTheRamanujanBasis
- normalizedRamanujanMode multiplicative on coprime moduli; at p^{k+1}: √φ(p^{k+1})·valuationStep(k+1, v_p(n)). Local Hardy–Blaschke coefficient = √(1−q²)q^{v_p(n)}·normalizedRamanujanMode(p^k, n).
- Π_p√(1−q_p²)q_p^{v_p(n)} = √sieveClassDensity(n), density(n) = Π_{p∈Q}(1−1/p)/n.
- sieveAdjunctionBasis(m)(n) = √density(n)·normalizedRamanujanMode(m)(n) — eigenbasis = density-weighted normalized Ramanujan basis. Σ_n density(n) = 1 (ground vector m = 1 has unit norm): class densities form a probability distribution on supported integers.

## TheSieveGroundMassHasALogarithmicMoment
- Divisor-closed S: Σ_{m,n∈S}u_mu_nP(m,n) = 2Σ_{n∈S}log n/n (downward row exact by Σ_{d|n}Λ = log n; up/down symmetric).
- Positivity ⇒ Σ_S log n/n ≤ (γ_Q − γ)Σ_S 1/n; γ_Q − γ = Σ_{p∈Q}log p/(p−1) ≥ 0.
- Σ_n log n·density(n) ≤ γ_Q − γ (summable, no primorial cutoff); Σ_{n>R}density(n) ≤ (γ_Q − γ)/log R.

## TheTowerNumberFormIsAWeightedSquareSum
- For every real q: Σ_{j<N}(j+1)x_j² − K_q(x) = −q²T_0² + Σ_{j<N}(j+1)(qT_j − T_{j+1})², T = towerTail (x_j = T_j − qT_{j+1}). One negative ground term + positive integer-weighted excitation squares.

## ThePrimeRowsReadPoleProfiles
- poleProfileUp(g,y,n) = Σ_{t≤y}g(nt)Λ(t)/t; poleProfileDown(g,n) = Σ_{d|n}g(d)Λ(n/d). Σ_n P(m,n)g(n)u_n = (Up(g,N/m,m) + Down(g,m))u_m exactly.
- Up + Down = (A(y) + log n)g(n) + correction, correction = Σ_{t≤y}(g(nt)−g(n))Λ(t)/t + Σ_{d|n}(g(n/d)−g(n))Λ(d) (jump form).

## ThePrimeRowCorrectionControlsTheResidual
- poleProfileResidual = Pu_g − (log N − γ − κ)u_g. If |g| ≤ B and |correction(g,y,n) + κg(n)| ≤ T(y) → 0 uniformly, then Σ_n residual²/log N → 0 (harmonic quotient square error; Mertens remainder + floor roundoff).

## TheRamanujanModesAreValuationSteps
- c_m(nt) = c_m(n) for (m,t) = 1 (ramanujanLagCoefficient). c_{p^k}(n) = φ(p^k)·valuationStep(p,k,v_p(n)) (n ≠ 0). c_{p^kr}(n) = φ(p^k)step·c_r(n). A prime-power jump changes at most one of two coprime conductor factors ⇒ exact product rule for up/down differences across coprime conductors.

## PrimePowerMangoldtReindex
- Λ-atoms divisible by p are p^{j+1}: reindex HasSum over t to sum over j; Σ_{t|n,p|t}F(t)Λ(t) = Σ_{j<v_p(n)}F(p^{j+1})log p.

## TheValuationStepsHaveCompletedPrimeRows
- |valuationStep| ≤ 1; geometric tails summable. Completed row: log p(Σ_j(step(v+1+j) − step(v))/p^{j+1} + Σ_{j≤v}(step(j) − step(v))) = −(log p^k + tame(p^k))·step(v) (from towerOp_step).
- Ramanujan c_{p^k}: down correction = φ(p^k)log p·Σ_{j≤v}(step_j − step_v); up correction HasSum geometric; total completed correction of c_{p^k} = −(log p^k + tame p^k)·c_{p^k}(n) (exact torsion-adjunction energy, every integer n).

## TheRamanujanPrimeRowsHaveAdjunctionEnergy
- hasSum_ramanujan_correction: for every m, n > 0: Σ_t(c_m(nt) − c_m(n))Λ(t)/t = −(log m + tame m)c_m(n) − Σ_{d|n}(c_m(n/d) − c_m(n))Λ(d). Induction over prime powers × coprime (product rule; log and tame additive on coprimes).

## TheRamanujanPrimeCorrectionHasAUniformTail
- Only primes p | m change c_m. localMangoldtMass p t = [p|t]Λ(t)/t summable. Majorant 2φ(m)Σ_{p|m}localMass(p,t) bounds every row term (|c_m| ≤ φ(m)), uniformly in n. Truncated correction error ≤ tail(m,N) → 0.

## TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal
- Periodic sequence: harmonic mean Σ_{n≤N}p(n)/n / log N → period mean. normalizedRamanujanMode = c_m/√φ(m); period mean of products = δ_{ml}. ramanujanPoleProfile c_m(n)/√(φ(m)n): Gram/log N → δ_{ml} (asymptotically orthonormal), mass ~ log N.

## TheRamanujanPoleProfilesArePrimeQuasimodes
- ramanujanAdjunctionEnergy E(m) = γ + log m + tame m. For fixed m > 0: Σ_n((Pr_m)_n − (log N − E(m))r_m(n))²/log N → 0 (quasimode of full prime matrix).

## TheRamanujanAdjunctionEnergiesAreDistinct
- E injective on positive integers (any two lie in a common finite sieve).

## TheFullPrimeMatrixHasRamanujanSpectralPoints
- fullPrimeMatrix N (all n ≤ N) Hermitian. For each m > 0, ε > 0, eventually ∃ eigenvalue within ε of log N − E(m) (Hermitian residual ⇒ eigenvalue).

## TheFullPrimeMatrixRealizesFiniteAdjunctionPackets
- Finite S ⊂ ℕ_{>0}: eventually distinct eigenvalues eig(m) ∈ spectrum with |eig(m) − (log N − E(m))| < ε (separation of distinct energies).

## TheRoughHarmonicMeasureTensorizesUniformly
- exists_rough_harmonicVar_le_glauberForm: ∃C > 0 ∀Q, X, f: harmonicVar Q X f ≤ C·glauberForm Q X f (rough interval = integers ≤ X with no prime factor < Q, harmonic weights 1/n; Glauber form = prime-ladder edge Dirichlet form). Proof: strong induction peeling prime Q, potential Ψ = −A·Σ_{q<Q}(log q/q)/log X ≤ 0, shellTau rate, Mertens Σ_{q≤p}log q/q ≤ log p + log4.

## PrimeDefectControlsValuationMoments
- poleDefect N x = Σ_m Σ_{t≤N/m}Λ(t)(x_{mt} − x_m/√t)². log p·Σ_n v_p(n)x_n² ≤ 2poleDefect + 2(log p/(p−1))|x|² (each n top of v_p(n) prime-power edges).

## TheRoughPrimeDefectControlsVariance
- roughPoleDefect (bottom vertex in rough interval). log Q·glauberForm(poleGauge x) ≤ roughPoleDefect (rough ladders have weight ≥ log Q; distinct edges). ⇒ harmonicVar Q N(poleGauge x) ≤ (C/log Q)·roughPoleDefect.

## TheHorizonSplitsIntoSmoothRoughFibres
- Σ_{n≤N}F(n) = Σ_{d Q-smooth ≤ N}Σ_{k∈rough(Q,N/d)}F(dk); smoothPart(dk) = d.

## TheSmoothRoughMeanApproximatesBoundedDefect
- smoothRoughPoleProjection: harmonic mean of poleGauge x over smooth fibre, transported back /√n. Fibre errors sum = |x − proj|²; scaled rough defects partition poleDefect exactly.
- exists_smoothRoughPoleProjection_error_le: |x − proj_Q x|² ≤ (C/log Q)·poleDefect N x uniformly in N: bounded defect ⇒ x close to functions of the Q-smooth part.

## GcdProfilesHaveFiniteRamanujanExpansions
- Σ_{q|d}c_q(n) = d·[d|n]. F(gcd(n,M)) = Σ_{d|M}[d|n]·(μ*F)(d) (Möbius). ⇒ every gcd profile mod M is a finite combination Σ_{q|M}a_q c_q(n) (also of normalized modes).

## ValuationBoxesAreFiniteRamanujanSpans
- primeValuationBoxModulus(P,L) = Π_{p<P}p^L. primeValuationBox: v_p(n) < L ∀p < P; preserved by gcd with modulus; inside box gcd(n, modulus) = (P−1)-smooth part of n. Truncated smooth-part profile = gcd profile ⇒ finite normalized Ramanujan expansion over divisors of the modulus (conductor set independent of profile).

## PrimeValuationBoxesCaptureBoundedDefect
- primeValuationTailConstant(P) = Σ_{p<P}(2/log p + 2/(p−1)). L·(mass outside box) ≤ Σ_{p<P}Σ_n v_p(n)x_n² ≤ C_P(poleDefect + |x|²) ⇒ outside mass ≤ (C_P/L)(defect + mass).

## BoundedPrimeDefectHasFiniteRamanujanApproximation
- exists_finite_ramanujan_approximation_of_poleDefect_le: ∀K, η > 0 ∃ finite S ⊂ ℕ_{>0} s.t. ∀N, ∀x with |x|² ≤ 1, poleDefect ≤ K: ∃a, |x − Σ_{m∈S}a_m r_m|² ≤ η (choose P with C(K+1)/log P small, then L; uniform in N — arithmetic compactness).

## TheRenormalizedPrimeEnergyControlsTheDefect
- primeHorizonExtension; atomicWeilForm(ext x) = ⟨Px,x⟩. renormalizedPrimeEnergy E_N(x) = log N|x|² − ⟨Px,x⟩. Eventually: unit x with E_N(x) ≤ T ⇒ poleDefect ≤ max(0, 2(T − γ + 1)) (from eventually_atomicWeilForm_add_poleDefect_le with ½). ⇒ fixed finite Ramanujan span approximates all bounded-energy unit vectors within η.

## BoundedPrimeEnergyHasFiniteRamanujanCoordinates
- normalizedRamanujanHorizonVector r_m/√log N: Gram → δ_{ml}; residual norm → 0. exists_finite_ramanujan_coordinate_certificate: ∀T ∃ finite S: eventually every unit x with E_N(x) ≤ T has Σ_{m∈S}⟨x, r̂_m⟩² ≥ 1/18.

## TheAdjunctionEnergyHasFiniteSublevels
- log m ≤ E(m) − γ ⇒ {m > 0 : E(m) < T} finite (adjunctionEnergySublevel); positive gap below T.

## TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum
- fullPrimeEnergyEigenvalue = log N − λ_i(P_N). Lower count: eventually #{m: E(m) < T} ≤ #{i: log N − λ_i < T} (packets). Upper count (T not an energy): finite coordinate certificate + residual/gap bounds force every low-energy unit vector to have coordinate mass < 1/18 on non-sublevel Ramanujan vectors and 0 on sublevel ones (if orthogonal) ⇒ rank bound.
- eventually_fullPrime_spectral_count_eq: for T ∉ {E(m)}, eventually #{i: log N − λ_i(P_N) < T} = #{m > 0: γ + log m + tame(m) < T}. Bounded window of renormalized full prime matrix is exhausted with multiplicity by the simple adjunction energies.

## TheSimplePrimeEigenlinesConvergeToRamanujanLines
- Each E(m) isolated (radius δ). Eventually exactly one eigenvalue in window [E(m) − δ, E(m) + δ); it converges to E(m); spectral projection of normalized Ramanujan vector r̂_m onto window → r̂_m (error² ≤ residual²/δ²). exists_simple_fullPrime_eigenline.

## TheDeficitOfThePrimeFormIsADirichletEnergy
- poleDefect D_N(x) = Σ_{mt≤N}Λ(t)(x_{mt} − x_m/√t)² (Dirichlet energy of pole relations x_{mt} = t^{−1/2}x_m on prime-power edges). upKernel; P = up + upᵀ; P_N(x) = 2Σ_{mt≤N}(Λ(t)/√t)x_mx_{mt}. Edges by top: Σ_mΣ_{t≤N/m}F(mt,t) = Σ_nΣ_{t|n}F(n,t).
- Ground-state identity (exact): P_N(x) + D_N(x) = Σ_n(A(⌊N/n⌋) + log n)x_n².
- Defect pays top atoms: Σ_n(n/N)log n·x_n² ≤ 2D_N + 2(log4 + 4)|x|² (Chebyshev).
- eventually_atomicWeilForm_add_poleDefect_le: ∀ε eventually P_N(x) + (1−ε)D_N(x) ≤ (log N − γ + ε)|x|² (no tilt needed).
- p-ladders {up^j} partition [1,N]; ladderDefect E_p; log p·E_p ≤ D_N. Lagrange identity ⇒ on a ladder orthogonal to pole profile p^{−j/2}: E_p ≥ (1 + 1/p)|x|² (|b|² ≥ 1 + 1/p with two rungs).
- eventually_atomicWeilForm_le_of_ladderOrthogonal: x ⊥ all p-ladder poles ⇒ P_N(x) ≤ (log N − γ − (1 + 1/p)log p + ε)|x|² on the whole space.

## TheFinitePartOfTheMarkovFormAtTheSpacing (uses SpacingScaleHarmonicAnalysis)
- Atomic test f = Σ_{n≤N}x_n g(· − log n), g = φ(·/w), φ C² on [0,1], width w ≤ δ_N/2 (δ_N atom spacing). Markov form M(f) = 2θ'(0)‖f‖² + levyEnergy f − ‖g‖²P_N(x) (markovEnergy = archForm − primeSum).
- Lévy density ω(y) ≤ 1/(2y) + 1; window [s−w,s+w] (|s| ≥ 2w) carries ≤ 2w(1/|s| + 1) of ω. levyEnergy f ≥ |x|²levy(g) − 2‖g‖²Σ_{m≠n}|x_m||x_n|2w(1/|log(n/m)| + 1); for g, x ≥ 0: levyEnergy f ≤ |x|²levy(g).
- Rows Σ_{n≠m}(1/|log n − log m| + 1) ≤ 2e²m(1 + log(N+1)) + (3/2)N. (m/N)log N ≤ 2(m/N)log m + 2. Cross penalty ≤ wN((16e² + 3 + 16e²(log4+4))|x|² + 16e²D_N(x)) — top atoms paid by pole defect.
- eventually_markovEnergy_atomicTest_ge: φ K-Lipschitz, 0 < ε ≤ ½, wN ≤ 1/(64e²): M(f) ≥ (2θ'(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2)w − A·wN)‖f‖², A = markovCrossConstant. Pole attains it for φ ≥ 0: M ≤ (2θ'(0) + log(1/(wN)) + κ_L(φ) + γ + ε + (e^{1/2}/2)w)‖f‖². Finite part of Markov form = Robin constant κ_L(φ) + Euler γ.

## TheArchimedeanFinitePartIsMinusLogTwoPi
- 2θ'(0) + 2c_∞ + γ = −log 2π (2c_∞ = 2log2 + π/2 archRobinConstant; ψ(1/4) = −γ − π/2 − 3log2). 2θ'(0) + κ_L(φ) + γ = −log 2π + β(φ)/‖φ‖².
- Markov form at spacing: ground energy = log(1/(2πwN)) + β(φ)/‖φ‖² + O(wN) + o(1) (lower bound all x; pole attains for φ ≥ 0). Gamma factor + atom self-energy + prime pole cancel to conductor −log 2π; critical width wN = e^{β/‖φ‖²}/(2π).

## TheTorsionCountertermIsTheGoldenRatio
- T_N = diag(log n) + P_N (torsion pairing up to bounded excess). Golden split: a² ≤ φ²(a−b)² + φb² (defect φ(a − φb)²) on each edge ⇒ Σlog n·x² ≤ φ²D_N + φΣA(⌊N/m⌋)x_m² ⇒ T_N ≤ φΣ(A + log n)x² ≤ φ(log N + log4 + 4)|x|² (identities 2 − φ^{−2} = φ, 1 + φ^{−1} = φ).
- Golden vector x_n = φ^{ω(n)}/√n: coprime edge x_{mt} = φx_m/√t (equality case). Non-coprime edges carry tame different: Σ_{t≤X,(m,t)>1}Λ(t)/t ≤ tame(m); multiples of p carry ≤ φ²/(p−1) of golden mass; Σ golden·tame ≤ 2φ²K·S. Lower bound T_N(x) ≥ (φ(log N − log2 − log4 − 4) − 2φ²K)|x|².
- torsionCounterterm_golden: κ_tor(N) ∈ [φ(log N − log2 − log4 − 4) − 4φ²K, φ(log N + log4 + 4) + 2C_e] for every N ≥ 1: κ_tor = φ log N + O(1), φ golden ratio (beats continuum prediction e/(e−1) < φ). Extremal charges φ^{ω(n)} multiplicative; φ fixed point of z ↦ 1 + 1/z.

## TheSelfIntersectionFamilyObeysAFixedPointLaw
- T_α = α·diag(log n) + P_N. Twisted pole defect D_κ(x) = Σ_{mt≤N}Λ(t)(x_{mt} − κx_m/√t)² = Σlog n·x² − κP_N + κ²ΣA(⌊N/m⌋)x_m².
- Fixed-point identity (κ ≠ 0, α = κ − 1/κ): αΣlog n·x² + P_N(x) + D_κ(x)/κ = κΣ(A(⌊N/n⌋) + log n)x_n². Rows: (log N − log2 − log4 − 4)|x|² ≤ Σ(A + log n)x² ≤ (log N + log4 + 4)|x|².
- Top (κ > 0): T_α ≤ κ(log N + log4 + 4); bottom (κ < 0): T_α ≥ κ(log N + log4 + 4). Fixed-point vector κ^{ω(n)}/√n: coprime edges exact, D_κ ≤ (1−κ)²κ²·2K|x|² ⇒ both ends attained up to O(1). Spectrum of T_α fills [κ₋log N, κ₊log N], κ₊κ₋ = −1, κ² = ακ + 1. α = 0: [−log N, log N]; α = 1: [−log N/φ, φ log N] (bottom = largest positive square of renormalized torsion form, alternating charges (−1/φ)^{ω}).
- Semicircle law: |P_N(x)| ≤ 2√(H(L'S − H)), H = Σlog n·x², L' = log N + log4 + 4. Joint numerical range of (log n/log N, P_N/log N) → disk v² ≤ 4u(1−u) (large spin).

## TheRoughHarmonicMeasureHasThinShells
- roughInterval Q X (prime factors ≥ Q), roughHarmonic F_Q(X) = Σ1/K ∈ [1, 1 + log X]. Levels: R(p,X) = ⊔_j p^j·R(p+1, X/p^j); F_p(X) = Σ_j p^{−j}F_{p+1}(X/p^j). Buchstab: (1 − 1/p)F_p ≤ F_{p+1}. Mass: F_{n+1}(X) ≥ log(X+1)·Π_{q≤n}(1 − 1/q); Π_{q≤n}(1−1/q)log n ≥ c > 0 (Mertens third).
- Thin shells: ∃C ∀p prime, 1 ≤ Y, X ≤ p(Y+1): Σ_{(p+1)-rough K∈(Y,X]}1/K ≤ C (Selberg/Brun–Titchmarsh sieve level min(p, x^{1/4}) on dyadic blocks; block mass ≤ 2/log z + 5z(1+log z)³/x; (1 + log x)³ ≤ 343√x).
- shellTau τ(p,X) = Σ_j p^{−j}(F_0 − F_j)/F_0: τ ≤ C log p/(p log X) and τ ≤ 1 − 1/(1 + 2C) < 1 (the only coupling between prime coordinates of harmonic measure on [1,X]).

## TheHarmonicMeasureTensorizesOverPrimes
- Weighted variance toolkit: wMean, wVar; Steiner Σw(v−c)² = Var + W(mean−c)²; Jensen; weighted Cauchy–Schwarz; nested means: W_A(mean_A − mean_s)²W_s ≤ Var_s(W_s − W_A). (x+y)² ≤ (1+η)x² + (1+1/η)y².
- ladder q u X = {j: uq^j ≤ X}, harmonic weights 1/(uq^j); ladderVar; harmonicVar Q X (1/n on rough interval); glauberForm Q X = Σ_{q≥Q prime}Σ_{u rough, q∤u}ladderVar. Glauber form splits at p into p-ladders + p^{−j}-weighted level forms.
- peel: if levels satisfy constant B then (1 − (1+1/η)τ(p,X))Var ≤ max(B, 1+η)·Glauber on R(p,X) (h-part = p-ladder variance via Jensen; g-part = ladder means, nested-means cost τ; ladder means vary less than f).
- exists_harmonicVar_le_glauberForm(_rough): ∃C ∀Q,X,f: Var_{1/n,R(Q,X)}(f) ≤ C·Glauber (approximate Efron–Stein: harmonic measure on [1,X] is a product over primes up to bounded constant). Induction with potential Ψ = −AΣ_{q<Q}(log q/q)/log X ∈ [−3A,0].

## ThePrimeFormHasASpectralGapBelowItsPole
- poleGauge y_n = √n x_n: defect edge = (y_{mt} − y_m)²/(mt) (Dirichlet form of multiplicative walk under 1/n); pole orthogonality = 1/n-mean zero ⇒ harmonicVar = |x|².
- Ladder Poincaré: ladderVar ≤ base-edge energy. log2·Glauber(y) ≤ D_N(x) (distinct prime powers are distinct edges).
- exists_poleDefect_ge: ∃g > 0 ∀N: x ⊥ pole ⇒ D_N(x) ≥ g|x|² (g = log2/C, C tensorization constant).
- exists_atomicWeilForm_le_of_pole_orthogonal: ∃g > 0 ∀ε eventually: x ⊥ pole ⇒ P_N(x) ≤ (log N − γ − g + ε)|x|² — uniform spectral gap below the pole.

## ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin
- Σ_{d|m}λ(d) = 1_□(m); Σ_{n≤N}λ(n)⌊N/n⌋ = #squares ≤ N; |Σ_{n≤N}λ(n)/n| ≤ 2.
- Pole in kernel of defect: D_N(b + u) = D_N(u). Polarization at pole: P_N(b + u) = P_N(b) + P_N(u) + 2Σ(A(⌊N/n⌋) + log n)b_nu_n. Rows within log4 + 4 + log2 + γ of log N − γ.
- exists_pole_hyperplane_separates_liouville: ∃g > 0 ∀ε eventually: on pole hyperplane ζ's P_N ≤ (log N − γ − g + ε)|x|², while Liouville twin P_N(λx) reaches (log N − γ − ε)|x|² at some x on it (witness: (λ(n) − S/H)n^{−1/2}). P_N(x) and P_N(λx) unitarily equivalent but tops point in different directions; margin g uniform in N, carried by pole term.

## TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo
- smoothBox J Q: Q-smooth numbers with exponents ≤ J (product of geometric ladders); Box(Q+1) = ⊔_{j≤J}Q^j·Box(Q). Exact Efron–Stein on boxes: boxVar ≤ boxGlauber (induction, commuting ladder means).
- Pairwise variance: 2W·Var = Σ_{i,j}w_iw_j(v_i − v_j)². Sharp ladder Poincaré: boxLadderVar ≤ ladderEnergy/(log p·W_p(J)), W_p(J) = Σ_{i≤J}p^{−i}. boxGap g_J = 2log2(1 − 2^{−J−1}) ≤ log p·W_p(J) for all p (p = 2 equality; p = 3: (4/3)log3 ≥ 2log2 since 81 ≥ 64; p ≥ 5: log p ≥ 2log2). Box Poincaré g_J·Var ≤ boxEnergy.
- Truncation to [1,X]: smoothSet/smoothVar/smoothEnergy (edges a → ap^k, conductance log p/(ap^k)). log a = Σv_p(a)log p; halo bound Σ(1/a)log a·u² ≤ 2E + 2M_QΣ(1/a)u² (M_Q = Σ_{p<Q}log p/(p−1)). Zero extension costs boundary edges: weight ≤ 4(log p/a)√(a/X); boundary ≤ 4L_Q·Σ(1/a)(h−c)²√(a/X).
- (g_X − 4L/X^{1/4} − 16LM/log X)Var ≤ (1 + 16L/log X)E. eventually_smoothVar_le_smoothEnergy: ∀Q, ε eventually (2log2 − ε)Var ≤ E on Q-smooth numbers of [1,X]: finite-prime valuation chain has gap 2log2 (valuation step at p = 2).

## TheSpectralGapOfThePrimeFormIsTwoLogTwo (module docstring still says "work in progress"; theorems complete)
- Smooth–rough decomposition [1,N] = ⊔_{a Q-smooth}a·R(Q, N/a); two fibrations commute. walkEnergy N s y = Σ_{mt≤N, s(t)}Λ(t)/(mt)(y_{mt} − y_m)²; small (minFac t < Q) + large (≥ Q) parts sum to poleDefect in pole gauge. Large primes act within fibres: walkEnergy_large = Σ_a(1/a)roughEnergy(Q, N/a). log Q·Glauber(Q) ≤ roughEnergy ⇒ Σ_a(1/a)Var_fibre ≤ (K/log Q)E_large.
- Small edges = smooth chain rescaled by rough part; halo Σ(1/a)log a·(fibre mass) ≤ 2D_S + 2M_Q·W. Shell (Y/t, Y] rough mass ≤ 1 + log t. One edge of fibre-mean chain: F(N)(h_{at} − h_a)² ≤ (F/G)((1+η)e + (1+1/η)((1+log t)/G)V_a). Σ_k(log p/p^k)(1 + log p^k) ≤ 8log p.
- two_scale_le + gap_of_two_scale ⇒ eventually_mul_harmonicVar_le_poleDefect: ∀ε eventually (2log2 − ε)Var_{1/n,[1,N]}(√n x) ≤ D_N(x) — multiplicative walk has Poincaré constant 2log2.
- eventually_atomicWeilForm_le_two_log_two: ∀ε eventually x ⊥ n^{−1/2} ⇒ P_N(x) ≤ (log N − γ − 2log2 + ε)|x|². Sharp spectral gap 2log2 below pole.

## TheFirstExcitedStateOfThePrimeFormIsTheTwoAdicStep
- harmonicMass H_N, evenMass E_N = ½H_{⌊N/2⌋} ≤ H_N/2, ≥ log(N/2+1)/2. twoAdicStep x_n = (1_{2|n} − E_N/H_N)/√n: ⊥ pole; |x|² = E_N − E_N²/H_N ≥ E_N/2.
- poleDefect(twoAdicStep) = log2·E_N exactly (large primes odd keep parity; only edges m → m2^k with m odd move parity; Σ = E_N by 2-adic ladders) ⇒ D_N ≤ 2log2|x|²: Poincaré constant ≤ 2log2 for every N.
- Rows from below (Mertens): ⌊N/n⌋ ≥ R ⇒ A + log n ≥ log N − γ − ε. eventually_exists_atomicWeilForm_ge: 2-adic step has P_N ≥ (log N − γ − 2log2 − ε)|x|².
- eventually_atomicWeilForm_below_pole_two_log_two: top of P_N on pole hyperplane = log N − γ − 2log2 + o(1) (two-sided); first excited state = 2-adic step.

## TheTruncatedValuationLadderIsExactlySolvable (imports only Mathlib)
- One p-ladder in pole gauge: chain on {0..J}, weights w_j = p^{−j}, all-pairs Dirichlet form E(g) = Σ_{i<j}log p·w_j(g_j − g_i)² (ladForm).
- Modes ψ_0 = 1, ψ_k = 1_{j≥k} − c_k1_{j=k−1}, c_k = (1 − p^{−(J−k+1)})/(p−1) (Σ_{j≥k}w_j = w_{k−1}c_k). Orthogonal (ψ_k = 1 on supp ψ_l for k < l), eigenvectors B(ψ_k,g) = λ_k⟨ψ_k,g⟩ with λ_k = log p(k + c_k) → k log p + log p/(p−1). Complete (tail sum induction) ⇒ expansion, Parseval, E(g) = Σλ_k⟨g,ψ_k⟩²/‖ψ_k‖².
- log p(k + 1/(p−1)) − log p·p^{−(J−k+1)}/(p−1) ≤ λ_k ≤ log p(k + 1/(p−1)).

## TheFinitePrimeChainHasTheSpectrumOfTheIntegers
- Box (Q-smooth, exponents ≤ J) with weights 1/a and all prime-power-edge Dirichlet form. Product modes boxMode Ψ_m(a) = Π_{p<Q}ψ_{p,v_p(m)}(v_p(a)), indexed by the box; eigenvalues boxEig λ(m) = Σ_pλ_{p,v_p(m)} → log m + Σ_{p|m}log p/(p−1) as J → ∞.
- boxSpectral: ∀T, f: T‖f‖² − Σ_{λ(m)<T}(T − λ(m))⟨f,Ψ_m⟩²/‖Ψ_m‖² ≤ E(f) (induction over primes: expand slices in top-ladder eigenbasis; energy splits Σ_k‖ψ_k‖²(E_Q(c_k) + λ_k‖c_k‖²); ⟨f,Ψ_{Q^km}⟩ = ‖ψ_k‖²⟨c_k,Ψ_m⟩).

## TheTopSpectrumOfThePrimeFormIsExhaustedByTheIntegers
- boxEig(1) = 0, boxMode(1) = 1. Smooth chain orthogonal to all modes with λ(m) < T: mean 0 and (T − 4L/X^{1/4} − 16LM/log X)Var ≤ (1 + 16L/log X)E (boxSpectral with zero penalty).
- modeVec v_m: ⟨x, v_m⟩ = Σ_{a≤X}(1/a)Ψ_m(a)·fibreMean(√n x)(a). Box mode below T sits at integer level: log m + tame(m) ≤ λ(m) + L_Q·2^{−(X+1−⌈T/log2⌉)}.
- eventually_mul_sum_sq_le_poleDefect: ∀T, ε eventually ∃Q, X, finite S ⊂ {m: log m + tame(m) < T}: x ⊥ all v_m ⇒ D_N(x) ≥ (T − ε)|x|².
- eventually_atomicWeilForm_le_of_modes: same S, x ⊥ v_m ⇒ P_N(x) ≤ (log N − γ − T + ε)|x|². Courant–Fischer: P_N has at most #{m: log m + tame(m) < T} eigenvalues above log N − γ − T + ε (top spectrum exhausted by integers).

## PeriodicPairSumsOfADecreasingKernelAreLinear (imports only Mathlib)
- Periodic partial sums: |Σ_{i<k}u_i − kμ| ≤ 2qU. Abel summation bound; variation of product of increasing×decreasing nonneg sequences ≤ 2UV. Σ_J 1/((J+1)√(J+2)) ≤ 3.
- abs_sum_periodicPair_le: ψ q-periodic, mean 0, |ψ| ≤ B; Φ ≥ 0 decreasing, Φ(t) ≤ A(1/t + 1): |Σ_{1≤m<n≤N}(ψ(m)/√m)(ψ(n)/√n)Φ(log n − log m)| ≤ 42qB²AN (a priori A N log N; mean zero makes it linear). Proof: reindex by gap J, split autocorrelation c_J (periodic mean 0) × decreasing row sums T_J plus centred error per gap O(AN J^{−3/2}).

## TheArchimedeanCrossTermsVanishOnPeriodicProfiles
- Cross kernel Ω(t) = ∫_0^∞ω(s)G(s−t)ds (G autocorrelation of bump g ≥ 0 on [0,w]); ≥ 0, decreasing in t > w, ≤ 2w‖g‖²(1/t + 1) for t ≥ 4w; lives on window [t−w, t+w].
- Exact expansion (w < δ_N): L(f_x) = |x|²L(g) − 2Σ_{m<n}x_mx_nΩ(log n − log m).
- Periodic profiles x_n = ψ(n)/√n (ψ q-periodic mean 0, |ψ| ≤ B), 4w ≤ δ_N: |L(f_x) − |x|²L(g)| ≤ 168qB²(wN)‖g‖² — cross terms O(wN/log N) per unit mass, vanish at fixed overlap wN; on the pole ψ = 1 they are a nonzero constant per unit mass.

## TheWeilEnergiesOfTheArithmeticModes
- Periodic mean-zero ψ: |Σ_{n≤N}ψ(n)/n| ≤ 2qB, |Σψ(n)| ≤ 2qB (Abel). Weil form of periodic profile, 4w ≤ δ_N: |W(f_x) − (|x|²(2θ'(0)‖g‖² + L(g)) − ‖g‖²P_N(x))| ≤ 168qB²(wN)‖g‖² + 8q²B²e^{w/2}(∫g)² (cross terms + pole term bounded). Rayleigh form version.
- Ramanujan mode m ≥ 2 has period mean 0; normalizedRamanujanMode 1 = 1. P_N(y_m)/|y_m|² − (log N − E(m)) → 0 (from quasimode residual + Cauchy–Schwarz).
- arithmeticMode φ K m N = atomic test of Ramanujan pole profile with φ dilated to width K/N. tendsto_weilQuad_arithmeticMode: φ ≥ 0 Lipschitz C², m ≥ 2, 0 < K < 1/4: W(f_N)/‖f_N‖² → log(1/K) − log2π + β(φ)/‖φ‖² + log m + tame(m) = log(K_m/K), K_m = m·e^{tame(m)}·e^{β/‖φ‖²}/(2π).

## TheLiouvilleGaugeFlipsThePolarDivergence
- liouvilleSign λ(n) = (−1)^{Ω(n)} completely multiplicative, λ² = 1. Twisted Mertens A_λ(y) = Σλ(t)Λ(t)/t ∈ [−log y − log4 − 4, −log y + log4 + 4 + K] (even prime powers Σ(1+λ)Λ/t ≤ K = tameConstant via 2log q/s² ≤ 4s^{−3/2}).
- Dirichlet hyperbola: Σ_{m≤M}(Σ_{t|m}g(t))/m = Σ_{k≤M}(Σ_{t≤M/k}g(t)/t)/k. Σ_{n≤M}log n/n ≤ ½log²M + ½.
- Liouville pole rows: (Pλu)_m = (A_λ(⌊M/m⌋) + D_λ(m))λ(m)u_m, D_λ(m) = Σ_{t|m}λ(t)Λ(t); Gram |⟨λu^{(M)},Pλu^{(M')}⟩ + H_MH_{M'}| ≤ C_λH_M (flipConstant = 2log8 + 10 + 2K).
- |P_N(x)| ≤ (log N + log4 + 4)|x|² (P ≥ 0 entrywise). Spectrum ends: pole vector ≥ (log N − log8 − 4)|u|²; Liouville pole P_N(λu) ≤ −(log N − C_λ)|λu|². Spectrum fills [−log N, log N] up to O(1).
- Polar flip: |P_N(λx) + ℓ(x)²| ≤ C_λΣ|c_i||c_j|H_min on step profiles (ζ: +ℓ², Liouville twin: −ℓ²). Each place's counterterm gauge blind; polar matching gauge charged.

## PolarMatchingReadsTheDensityOfTheGauge
- IsSignGauge ε: completely multiplicative ±1 on positive integers. Gauged rows (Pεu)_m = (A_ε(⌊M/m⌋) + D_ε(m))ε(m)u_m; gauged pole Gram = Σ_{m≤M}(A_ε(⌊M'/m⌋) + D_ε(m))/m.
- Matching law: |A_ε(y) − κ log y| ≤ K (|κ| ≤ 1) ⇒ |⟨εu^{(M)},Pεu^{(M')}⟩ − κH_MH_{M'}| ≤ (2K + 2log2 + 4)H_M and P_N(εx) = κℓ(x)² + O(|c|-mass) on step profiles. κ = polar matching coefficient = log p/p-weighted density of unflipped minus flipped primes.
- Instances: Euler κ = 1 (K = log4 + 4); Liouville κ = −1; finiteFlip_F (flip primes in finite F) κ = 1 with K = log4 + 4 + 2Σ_{p∈F}log p/(p−1). Twins differing at finitely many primes are matched exactly as ζ: separation must come from finite parts (AES: margin 2log²p in renormalized source per flipped prime).

## PolarMatchingNeedsOnlyTheLeadingOrder
- gaugeMertensError E(y) = A_ε(y) − κ log y. |Σ_{m≤M}log⌊X/m⌋/m − (H_M log X − Σlog m/m)| ≤ log2·H_M.
- Transfer law (no hypothesis on ε): |⟨εu^{(M)},Pεu^{(M')}⟩ − κH_MH_{M'} − Σ_{m≤M}(E(⌊M'/m⌋) + E(⌊M/m⌋))/m| ≤ (2log2 + 4)H_M — horizon remainder = harmonic convolution of Mertens error.
- Local law: |E| ≤ g on [1,M'] ⇒ bound (2g + 2log2 + 4)H_M (Gram sees A_ε only on [1,M']).
- Soft law: E(y) ≤ η log y + C_η (∀η), in particular A_ε(y)/log y → κ ⇒ |P_N(εx) − κℓ(x)²| ≤ (η log N + C)Σ|c_i||c_j|H_min: polar divergence (order (log N)²) read off leading order of A_ε alone.
- gaugePole_bounded_iff: ⟨εu^{(M)},Pεu^{(M)}⟩ = κH_M² + O(H_M) ∀M ⇔ Σ_{m≤M}E(⌊M/m⌋)/m = O(H_M) (Mertens error bounded in log mean).

## TheFinitePartIsTwiceTheMertensLimit
- Gauged pole Gram = Σ_{m≤M}(A_ε(⌊M'/m⌋) + A_ε(⌊M/m⌋))/m (Mertens convolution). Convergent convolutions: D → β ⇒ Σ_{m≤M}D(⌊X/m⌋)/m = βH_M + o(H_M) + O(1) uniformly in X ≥ M.
- Finite-part law: A_ε(y) − κ log y → α, |κ| ≤ 1 ⇒ ⟨εu^{(M)},Pεu^{(M')}⟩ = κH_MH_{M'} + 2αH_M + o(H_M) + O(1); on step profiles P_N(εx) = κℓ(x)² + 2α|x|² + o(mass). (Gauge minus κ·Euler has convergent Mertens sum, limit α + κγ.) Mertens expansion A_ε = κ log y + α + o(1): divergence reads κ, finite part 2α; ζ: κ = 1, α = −γ.

## TheFinitePartIsTheHarmonicMeanOfTheMertensError
- Diagonal Gram ⟨εu^{(M)},Pεu^{(M)}⟩ = 2Σ_{m≤M}A_ε(⌊M/m⌋)/m. 2Σ_{m≤M}log⌊M/m⌋/m = H_M² + o(H_M) (read off ζ).
- gaugePole_finitePart_iff: ⟨εu^{(M)},Pεu^{(M)}⟩ = κH_M² + 2αH_M + o(H_M) ⇔ Σ_{m≤M}E(⌊M/m⌋)/m = αH_M + o(H_M): finite part on pole = harmonic mean of Mertens error (convergence of E is Abelian sufficient; harmonic mean necessary and sufficient).

## TheFinitePartSeparatesZetaFromItsLiouvilleTwin
- liouvilleEvenSum T(y) = Σ(1+λ(t))Λ(t)/t increasing, bounded by K ⇒ limit τ (= 2Σ_p log p/(p²−1)), τ ≥ log2/2 (from t = 4). A_λ = −A + T ⇒ A_λ(y) + log y → γ + τ.
- Liouville finite part: P_N(λx) = −ℓ(x)² + 2(γ+τ)|x|² + o(mass). Separation on polar hyperplane: P_N(λx) − P_N(x) = 2(2γ + τ)|x|² + o(mass), 2γ + τ > 0.

## TheFinitePartSeesEveryFlippedPrime
- finiteFlipDeficit D_F(y) = Σ(1 − ε_F(t))Λ(t)/t increasing, bounded ⇒ limit δ_F (= 2Σ_{p∈F}p log p/(p²−1)); δ_F ≥ 2log p/p for each p ∈ F. A_{ε_F} = A − D_F ⇒ A_{ε_F}(y) − log y → −γ − δ_F.
- Separation: P_N(ε_Fx) − P_N(x) = −2δ_F|x|² + o(mass) on all step profiles (divergences cancel).
- Rigidity finitePartLimit_le_and_eq_iff: sign gauge with A_ε − log y → α ⇒ α ≤ −γ, equality iff ε ≡ 1 (gauge deficit monotone nonneg; zero limit ⇒ ε(p) = 1 ∀p ⇒ ε ≡ 1). ζ unique maximizer of finite part among κ = 1 twins; each flipped prime lowers it by ≥ 4log p/p. Mirror: κ = −1 gauges have α ≥ γ + τ, equality iff ε = λ.
- exists_abs_gaugeForm_sub_zetaForm_sub_le: κ = 1 gauge with convergent error ⇒ P_N(εx) − P_N(x) = 2(α + γ)|x|² + o(mass), α + γ ≤ 0, = 0 iff ε ≡ 1. Sign gauge facts: ε(1) = 1, ε(p^k) = ε(p)^k, gauges agreeing at primes agree everywhere; λ(t) ≤ ε(t) on prime powers. liouvilleLimit_le_and_eq_iff: κ = −1 gauge with A_ε + log y → α ⇒ α ≥ γ + τ, equality iff ε = λ.

## MertensTheoremForCharacters
- Abel with decreasing weights: ‖Σf(i)g(i)‖ ≤ f(0)C. Shifted non-trivial character partial sums ≤ 2q. ‖L(σ,χ) − Σ_{n<M}χ(n)n^{−σ}‖ ≤ 2q/M (σ > 1; σ = 1 by continuity of L(·,χ)). ‖charLogSum‖ = ‖Σ_{n≤M}χ(n)log n/n‖ ≤ 1 + 2q (log x/x decreasing from 3).
- Hyperbola: Σ_{n≤M}χ(n)log n/n = Σ_{t≤M}χ(t)Λ(t)/t·S_χ(M/t). exists_norm_charMertensSum_le: χ ≠ 1 ⇒ A_χ(y) = Σχ(t)Λ(t)/t bounded by (1 + 2q + 2q(log4+4))/|L(1,χ)| (uses L(1,χ) ≠ 0 from Mathlib, Chebyshev).

## CharactersAreInvisibleToPolarMatching
- Real character χ ≠ 1 mod prime ℓ: charGauge ε(n) = Re χ(n'), n' ℓ-free part; sign gauge (real character ±1 on units); ε = χ off ℓ, 1 on powers of ℓ: ε(t)Λ(t) = Re χ(t)Λ(t) + [ℓ|t]Λ(t).
- charGauge_matching: κ = 0, |A_ε(y)| ≤ C_χ + log ℓ/(ℓ−1). abs_charGaugeForm_stepProfile_le: |P_N(εx)| ≤ C·mass, no polar term. Dirichlet's theorem (L(1,χ) ≠ 0) at horizon = vanishing of matching coefficient.

## TheCharacterMertensSumConverges
- Abel: A_χ(N) = ψ(N,χ)/(N+1) + Σ_{n≤N}ψ(n,χ)/(n(n+1)). e^{−ρL^{1/10}} ≤ 4·20!/ρ^{20}·(1+L)^{−2} (L ≥ 1). With PNT for characters ψ(x,χ) = O(x e^{−ρ(log x)^{1/10}}) (RHTower) the Abel series is summable ⇒ A_χ(y) → α_χ = Σψ(n,χ)/(n(n+1)) for χ ≠ 1.
- Character gauge finite part: A_ε(y) → Re α_χ + lim Σ_{t≤y,ℓ|t}Λ(t)/t =: α_ε; P_N(εx) = 2α_ε|x|² + o(mass).

## TheCharacterMertensLimitIsTheLogarithmicDerivative
- abelWeight w_n(σ) = n^{1−σ} − (n+1)^{1−σ} ≥ 0 (σ ≥ 1), Σ_{n≤N}w_n = 1 − (N+1)^{1−σ}. Summation by parts Σ_{n≤N}χ(n)Λ(n)n^{−σ} = A_χ(N)(N+1)^{1−σ} + ΣA_χ(n)w_n(σ). Abel: L-series of χΛ at σ → 1+ tends to α_χ.
- charMertensLimit_eq_neg_logDeriv: α_χ = −L'/L(1,χ) (series = −L'/L(s,χ) for Re s > 1, continuous at 1 since L entire and L(1,χ) ≠ 0). Character gauge Mertens limit = Re(−L'/L(1,χ)) + lim Σ_{ℓ|t}Λ(t)/t; horizon finite part = twice that. ζ: −2γ = twice constant term of −ζ'/ζ at pole.

## MertensTheoremInResidueClassesWithItsConstant
- nonCoprimeMertens Q_q(y) = Σ_{(t,q)>1}Λ(t)/t increasing to Q_q ≤ Σ_{p|q}log p/(p−1). Principal character: A_{χ₀}(y) − log y → −γ − Q_q.
- tendsto_classMertensSum_sub: r unit mod q: A(y;r) − log y/φ(q) → c_r; classMertensConstant_eq: φ(q)c_r = −γ − Q_q + Re Σ_{χ≠1}χ(r^{−1})(−L'/L(1,χ)).

## ResiduePatternGaugesAreMatchedByTheirMean
- primeClassGauge ε_f(n) = Π_p f(p mod q)^{v_p(n)} (f: ℤ/q → ±1; abelian Chebotarev sign patterns): sign gauge, ε_f(p^k) = f(p)^k. Correction (ε_f(t) − f(t))Λ(t)/t supported on proper prime powers, |·| ≤ 2·notPrimeΛ(t)/t, summable (Σ ≤ 8 + mertensTail) ⇒ R(y) → R_∞.
- A_{ε_f}(y) = Σ_a f(a)A(y;a) + R(y). Non-unit classes converge (only prime powers of p|q). κ_f = φ(q)^{−1}Σ_{u unit}f(u); α_f = Σ_u f(u)c_u + Σ_{a non-unit}f(a)ν_a + R_∞. tendsto_primeClassMertensError: A_{ε_f} − κ_f log y → α_f.
- |κ_f| ≤ 1. exists_abs_primeClassGaugeForm_finitePart_le: P_N(ε_fx) = κ_fℓ(x)² + 2α_f|x|² + o(mass) — polar coefficient of abelian Chebotarev pattern = mean of pattern over units.

## TheMatchingCoefficientIsTheLogarithmicDensity
- primeSignGauge ε_g(n) = Π_p g(p)^{v_p(n)} for any prime sign pattern g. A_{ε_g}(y) = Σ_{p≤y}g(p)log p/p + R(y), |R| ≤ 8 + mertensTail.
- Density gives matching: Σ_{p≤y}g(p)log p/p / log y → κ ⇒ A_{ε_g}/log y → κ, |κ| ≤ 1, soft law on step profiles. flipGauge_kappa: flipping primes S of logarithmic density ϑ gives κ = 1 − 2ϑ. Polar divergence of a sign twin = (1 − 2ϑ)ℓ².

## NonAbelianChebotarevPatternsAreMatchedByTheirMean (uses ArtinMertens)
- Galois group G of number field L/ℚ, Frobenius choice frob, f: G → ±1 division-constant; chebotarevPattern g(p) = f(Frob_p) (unramified), 1 at ramified (bounded contribution, divide disc L ≠ 0).
- Log mean of pattern = classMean f = |G|^{−1}Σ_σ f(σ) ⇒ κ = ⟨f,1⟩ (soft law); with bounded-error Frobenius density theorem in Mertens form (ArtinMertens), Mertens error bounded and mass-scale law |P_N(ε_gx) − ⟨f,1⟩ℓ(x)²| ≤ C·mass.

## ClassHarmonicSumsHaveConstants
- 0 ≤ H_M − log M − γ ≤ 1/M. Cauchy with rate: |f(M') − f(M)| ≤ K/M ⇒ limit d with |f(M) − d| ≤ K/M.
- Shifted classes: S_{a+1} − S_a has Cauchy rate 2/M (shift m ↦ m+1, classTail τ_a); class differences rate 2q/M. exists_classHarmonic_constant: ∃d_a: |qS_a(M) − log M − d_a| ≤ (1 + 2q²)/M (class analogue of Euler's constant). Log class sum: |qL_a(M) − (log M)²/2 − d_a log M| ≤ 2(K + ½).

## TheFinitePartOnResidueClasses
- Residue Gram as class Mertens sums: ⟨w_a^{(M)},Pw_b^{(M')}⟩ = Σ_{m≤M,m≡a}A(⌊M'/m⌋;a^{−1}b)/m + Σ_{n≤M,n≡b}A(⌊M/n⌋;b^{−1}a)/n (units a, b).
- Floors: 0 ≤ Σ_{m≤M}(log X − log m − log⌊X/m⌋)/m ≤ 2.
- Log model Gram exact to O(1): L_a(M) + log(M'/M)S_a(M) + L_b(M) = qS_a(M)S_b(M') + O(1) (constants d_a, d_b cancel).
- exists_abs_residueGram_finitePart_le: ⟨w_a^{(M)},Pw_b^{(M')}⟩ = (q/φ(q))S_a(M)S_b(M') + c_{a⁻¹b}S_a(M) + c_{b⁻¹a}S_b(M) + O(ηH_M + C_η). Finite part on residues = convolution by class Mertens constants (pair carries c_{a⁻¹b} + c_{b⁻¹a}).

## TheResidueFinitePartIsDiagonalizedByCharacters
- residueSpectralValue β_χ = −L'/L(1,χ) (χ ≠ 1), β_1 = −γ − Q_q. α_{χ⁻¹} = conj α_χ. φ(q)c_r = Σ_χ χ(r⁻¹)β_χ (real).
- Fourier inversion Σ_{u unit}c_uχ(u) = β_χ. sum_residueFinitePart_mul_char: Σ_b(c_{a⁻¹b} + c_{b⁻¹a})χ(b) = 2Re β_χ·χ(a): every character is an eigenvector of residue finite part; eigenvalues 2Re(−L'/L(1,χ)) (χ ≠ 1) and 2(−γ − Q_q) (trivial, carrying rank-one divergence). Residues invisible to divergence, fully visible to finite part.

## TheTwistedPoleReadsTheLogarithmicDerivative
- unitPole x = Σ_u f(u)w_u^{(M)}: mass Σf(u)²S_u(M); expands over residue Grams. Eigenprofiles (|f| ≤ 1, Σf = 0, Σ_v(c_{u⁻¹v} + c_{v⁻¹u})f(v) = 2βf(u)): |P_N(x) − 2β|x|²| ≤ ηH_M + C (mean 0 kills divergence; eigenrelation makes finite part scalar).
- charPole = Re χ(n)u_n^{(M)}: P_N = 2Re(−L'/L(1,χ))|x|² + O(ηH_M + C) for every χ ≠ 1 (any modulus, real or complex).

## MertensTheoremInResidueClasses
- classMertensSum A(y;r), principalMertensSum A_{χ₀}. Orthogonality φ(q)A(y;r) = Σ_χ χ(r⁻¹)A_χ(y). |A_{χ₀}(y) − log y| ≤ log4 + 4 + Σ_{p|q}log p/(p−1); non-principal O(1) ⇒ A(y;r) = log y/φ(q) + O(1) for every unit r (classes not separated by prime place).

## TheHorizonCountertermIsBlindToResidueClasses
- classHarmonic S_a(M) = Σ_{m≤M,m≡a}1/m: neighbouring classes |S_{a+1} − S_a| ≤ 2; all classes |S_b − S_a| ≤ 2q; |S_a(M) − log M/q| ≤ 2q + 1. classLogSum L_a(M) = Σ log(M/m)/m: L_a(M+1) = L_a(M) + log((M+1)/M)S_a(M); |L_a − (log M)²/(2q)| ≤ (2q+2)log M.
- residuePole w_a^{(M)} = u^{(M)}𝟙_{n≡a}; classMertensRow R_b(m,X) = Σ_{t≤X/m,mt≡b}Λ(t)/t; Gram = Σ_{m≡a}R_b(m,M')/m + Σ_{n≡b}R_a(n,M)/n; for unit a and m ≡ a the row is the class Mertens sum A(·; a⁻¹b).
- Residue law: units a, b ⇒ |⟨w_a^{(M)},Pw_b^{(M')}⟩ − (q/φ(q))S_a(M)S_b(M')| ≤ K H_{min(M,M')} (uniform K over units). Rank one: on unit-class step profiles |P_N(x) − (q/φ(q))ℓ(x)²| ≤ KΣ|c_α||c_β|H_{min}; on ℓ = 0 bounded by mass. Counterterm weight q/φ(q) = Π_{p|q}(1−1/p)⁻¹ (inverse unit density); refining by residues adds no divergent direction — at the horizon Dirichlet's theorem says residue classes are invisible. Non-unit classes mix valuations (excluded).

## TheHorizonSeesOnlyTheMeanOfAClassFunction
- classFunctionProfile: step profile Σc_iu^{(M_i)} twisted by f(n mod q) on units. ℓ(x) = (Σ_a f(a)/q)Σc_i log M_i + O((2q+1)Σ|f|Σ|c|). Class-function law: P_N(x) = κ_f(Σc_i log M_i)² + O((1 + log N)(Σ|c_i|)²), κ_f = (Σ_{a unit}f(a))²/(qφ(q)) = (φ(q)/q)⟨f⟩².
- f = 1: κ = φ(q)/q (unit density); sieved pole divergence (φ(q)/q)ℓ₀² = tensor-law weight δ⁻¹ℓ_u² with ℓ_u ≈ δℓ₀. Re χ, Im χ (χ ≠ 1, any modulus) have |P_N| ≤ K(1 + log N)(Σ|c_i|)²: no (log N)² divergence. The horizon reads only the mean of a class function.

## TheMatchedStabilityLaw (Markov form at atomic resolution)
- Covariant counterterm (log N + O(1), replacing Schur 2log N) in AES stability argument: M(f) ≥ (2θ'(0) + e^{−1/2}log(δ_N/(2w)) − log N − log4 − 4)∫f². Nonneg for w ≤ matchedAtomicWidth = (δ_N/4)exp(−e^{1/2}(log N + log4 + 4 + 2|θ'(0)|)) ≈ δ_N N^{−e^{1/2}} (AES: δ_N N^{−2e^{1/2}}).
- Remaining gap to spacing δ_N ≍ 1/N: the Lévy-gain constant e^{−1/2}.

## TheSelfEnergyHasConstantOne
- Lévy density ω(x) = e^{−x/2}/(1 − e^{−2x}) ≥ e^{−s/2}/(2x) on (0,s]. Sharp Lévy gain: levyEnergy f ≥ e^{−s/2}log(s/w)∫f² if shifts in (w,s] move support off itself; atomic tests: e^{−δ_N/4}log(δ_N/(2w))∫f² (constant 1 − O(1/N)).
- Stability law with constant one: M(f) ≥ (2θ'(0) + e^{−δ_N/4}log(δ_N/(2w)) − log N − log4 − 4)∫f²; nonneg for w ≤ sharpAtomicWidth = (δ_N/4)exp(−e^{δ_N/4}(log N + C₀)), C₀ = log4 + 4 + 2|θ'(0)|; sharpAtomicWidth ≥ (δ_N/4)e^{−(3C₀+1)/2}/N (width exponent one: cδ_N/N). Residual factor N = 1/δ_N: self-energy counted relative to spacing because larger shifts make distinct atoms overlap.

## TheStabilityLawReachesTheSpacingUpToALogarithm
- Keep all shifts s ∈ (w,1]: each atom full self-energy log(1/w); atoms interact archimedeanly. Shift expansion ∫(f − f(·+s))² = 2∫f² − 2Σx_mx_nc_{mn}(s), bumpPairing c_{mn}(s) = ∫g(u − log m)g(u + s − log n): |c| ≤ ∫g², c = 0 unless |s − log(n/m)| ≤ w.
- Lévy density 1/(2s) − 1/4 ≤ ω(s) ≤ 1/(2s) + 1. Cross terms: at shift s only pairs log(n/m) ∈ [s−w, s+w] with weight ≤ 2/(3log(n/m)) + 1; each pair costs 2w after integrating s. |log n − log m| ≥ |n−m|/N; Hilbert row Σ_{n≠m}1/|n−m| ≤ 2H_N; H_N ≤ 1 + log N.
- Cross kernel O(N log N): Σcross ≤ N((4/3)H_N + 1)|x|² (pair kernel 2N/(3|n−m|) + 1). Lévy energy with interaction: levyEnergy f ≥ (log(1/w) − ½ − 4wN((4/3)H_N + 1))∫f².
- Markov form M(f) ≥ (2θ'(0) + log(1/w) − ½ − 4wN((4/3)H_N+1) − log N − log4 − 4)∫f²; nonneg for w ≤ logSpacingWidth = e^{−C₁}/(N(1 + log N)), C₁ = 29/2 + log4 + 2|θ'(0)|. δ_N ≥ 1/(2N).
- Reading: archimedean place pays the prime place down to width δ_N/(C log N); self-energy log N + loglog N + O(1) beats covariant counterterm with margin loglog N; atom interaction (Hilbert kernel w/|log n − log m|) norm O(wN log N) = O(1). At width cδ_N the interaction norm ≍ c log N = order of counterterm: interaction, pole and prime form must be weighed together.

## TheLawsOfRenormalizedArithmeticPotentialTheory (capstone renormalized_arithmetic_potential_theory_laws)
- 26 conjuncts: rank-one survival; Hecke covariance ⇔ constant; covariant counterterm log N + O(1) sandwich (lower log N − log8 − 4); torsion ≥ (3/2)log N − C; horizon unbounded rank on p-adic classes; tensor counterterm [p]-invariant; spectrum ends ±(log N + O(1)) (pole top, Liouville pole bottom, flipConstant); finite flips matched (|A_ε − log y| ≤ log4 + 4 + 2Σ_F log p/(p−1)); finite part −2γ on step profiles; cross p-adic Gram = log p·classMass; torsion renormalizes at 2log N + C; tower sign law ⇔ towerDeficit ≤ 0; stability to logSpacingWidth; residue rank one; characters invisible; leading-order matching; BV finite part; sign table p ≥ 47; finite part = 2α; −L'/L(1,χ); Liouville separation 2(2γ+τ) > 0; residue Mertens constant; character diagonalization; twisted pole; ζ maximizes (α ≤ −γ, equality iff ε = 1); residue-pattern gauges.

## TheFullWeilMatrixIsTheActualAtomicForm
- atomicWeilGram = atomicMarkovGram + both pole outer products (atomPoleRow 0,1 symmetrized): qf = polarDefect(atomPoleRow, −Markov) = weilQuad(finAtomicTest). primeHorizonFinEquiv (n ↦ n−1) puts it on PrimeHorizonIndex N: fullWeilHorizonMatrix, ⟨Ax,x⟩ = weilQuad(atomicTest N (extension x) g); normalized by ∫g² (atom mass).

## TheLogarithmicCenterKernelIsHarmonic
- ω(log t) = t√t/(t² − 1) (t > 1); ω(log(b/a)) = b√(ab)/(b² − a²). archimedeanCenterKernel(a,b) = ω(|log b − log a|) off diagonal. Pole gauge: kernel/(√n√j) = ½(1/|n − j| + 1/(n + j)) exactly (inverse-difference + inverse-sum harmonic kernel, zero diagonal).

## TheSeparatedAtomPairingsAreThePrimeKernel
- Below spacing (w < δ_N): ∫atom_m·atom_n = δ_{mn}∫g²; negative Hecke shift log k meets pair iff m = nk; positive iff n = mk.
- primePair(atom_m, atom_n) = (∫g²)·weilPrimeKernel(m,n) (literal finite prime kernel; vanishes for k > N).

## TheSeparatedMarkovMatrixHasExactCrossEntries
- levyMixed of ordered separated atoms = −ω(y)·bumpAutocorr(g)(y − log(n/m)); integrated = −atomCrossTerm(g, log n − log m). markovPair(atom_m, atom_n) = [m=n: 2θ'(0)∫g² + levyEnergy g; else −atomCrossTerm(|log n − log m|)] − (∫g²)weilPrimeKernel(m,n).

## TheFullWeilMatrixSplitsAtTheSpacing
- Pole rows: atomPoleRow 0 = (∫g e^{−u/2})/√n, row 1 = √n(∫g e^{u/2}). arithmeticPoleKernel(n,j) = √n/√j + √j/√n. Full matrix entry = self-energy diag / −cross off-diag − (∫g²)Λ-kernel + (∫ge^{−u/2})(∫ge^{u/2})·poleKernel. Normalized by ∫g²: prime kernel coefficient exactly −1.

## TheLogarithmicCenterRowCancelsThePole
- Σ_j centerKernel(n,j)/√j = √n((H_{N−n} + H_{N+n})/2 − 3/(4n)). Pole rows Σ_j(√n/√j + √j/√n)/√j = √n H_N + N/√n. (Pole − center) on 1/√j = N/√n + √n(H_N − (H_{N−n}+H_{N+n})/2 + 3/(4n)): restored poles cancel harmonic bulk, leaving boundary layer.

## TheAtomCrossMatrixIsCloseToItsCenterKernel
- atomCrossErrorKernel = atomCrossTerm/∫g² − ((∫g)²/∫g²)·centerKernel. At w ≤ c/N (c < 1): |error| ≤ (38w(∫|g|)²/∫g²/(1−c)²)·max(n,j)²/|n−j|². For dilates atomDilate φ w: quadratic in w: ≤ (38(∫|φ|)²/(∫φ²(1−c)²))w²max²/|n−j|².

## TheAtomCrossReplacementHasUniformErrors
- At w = c/N: |Σx_nx_j error| ≤ 4·atomCrossErrorConstant·c²|x|² (uniform in N); on pole profiles a_j/√j with |a| ≤ A: Σ_n(Σ_j error·a_j/√j)² ≤ (36·const·A·c²)².

## TheCenterCollarIsPaidByTheTopAtoms
- Center row potential Σ_j center(n,j)/√j ≤ √n(H_N + 1). Weighted Schur (weights 1/√n): collar quadratic ≤ Σ n(H_N + 1)x_n² (no max over row index). (n/N)(H_N + 1) ≤ (n/N)log n + 3 (top-atom potential).
- Collar/N ≤ Σ(n/N)log n·x_n² + 3|x|² (top-atom potential + three masses).

## TheCompleteWeilTrialEnergiesAreSimpleAndProper
- completeWeilSelfFinitePart = log(1/(2πc)) + Robin(φ)/∫φ²; poleShift = c(∫φ)²/∫φ² ∈ [0, c] (Cauchy–Schwarz on [0,1]). Trial energy E(m) = self + adjunction(m) − γ + [m=1]poleShift. For c < 1: E(1) < E(m) ∀m ≥ 2 (pole shift < 1 ≤ 2log2 ≤ first excitation gap); E injective on positive conductors; sublevels finite (proper).

## ThePoleMomentsHaveQuadraticDilationError
- atomExponentialMoment(g,t) = ∫g e^{tu}; |t| ≤ ½, supp ⊂ [0,w]: |moment − ∫g| ≤ (w/2)e^{1/2}∫|g|; |moment| ≤ e^{1/2}∫|g|. Dilate: |M_{−1/2}M_{1/2}/∫g² − w(∫φ)²/∫φ²| ≤ const·w² (const = e^{1/2}(e^{1/2}+1)/2·(∫|φ|)²/∫φ²).

## TheMeanZeroCenterRowsAreUniformlyBounded
- For a with bounded interval sums |Σ_{Ico}a| ≤ B and |a| ≤ A: |Σ_j center(n,j)a_j/√j| ≤ (2B + A)√n; pole rows ≤ 2B√n; (pole − collar) rows ≤ (4B + A)√n; after division by N: Σ_n((α/N)·row)² ≤ α²(4B + A)² (uniform; mean-zero periodic profiles).

## TheCenterCorrectionHasBoundedPoleResidual
- Center correction shifts the pole by its charge: Σ_n((α/N)Σ_j(pole − center)/√j − α/√n)² ≤ 6α² (harmonic boundary square bound).

## TheCompleteWeilSelfEnergyHasItsFinitePart
- 0 < c < 1 ⇒ eventually c/N < δ_N (strict separation). completeWeilSelfError = 2θ'(0) + levyEnergy(dilate)/mass − log N − (selfFinitePart − γ); |error| ≤ (e^{1/2}/2)(c/N) (C² compact profiles are Lipschitz; Robin remainder) → 0. Scalar identity: 2θ'(0) + log(N/c) + profileRobin − log N = selfFinitePart − γ.

## OverlapForcesNewRamanujanTerms
- selfFinitePart(c) = selfFinitePart(1) − log c; nonpolar trial energy E_m(c) = E_m(1) − log c (pole shift only at m = 1); E_m(c) < 0 ⇔ c > exp(E_m(1)); every finite nonpolar family is negative at some overlap c > 1. Self-error O(c/N) holds for all c ≤ N (no separation needed). Reference formula ≠ actual quasimodes beyond separation: growing overlap brings new archimedean overlaps and non-ratio prime terms. (#print axioms lines in source.)

## TheCenterCorrectionSelectsTheConstantRamanujanMode
- Normalized Ramanujan mode 1 ≡ 1; m ≠ 1 has period sum 0 ⇒ bounded interval sums. Center correction on ramanujanPoleProfile m: bounded square residual, with charge shift α only at m = 1 (residual ≤ 6α² for m = 1; α²(9A)² otherwise).

## TheTwoPoleReplacementHasUniformErrors
- atomPoleErrorCoefficient = actual normalized two-pole product − poleShift/N: |·| ≤ const(c/N)². Quadratic-form cost ≤ 2·const·c²|x|² (uniform); on bounded pole profiles residual ≤ 4const²A²c⁴.

## TheCompleteWeilMatrixHasAnExactErrorDecomposition
- completeWeilMatrix(φ,c,N) = normalized full Weil matrix of atomDilate φ (c/N). Under c/N < δ_N: = (log N + selfFinitePart − γ + selfError)·I − fullPrimeMatrix + centerMatrix(poleShift) − crossErrorMatrix + poleErrorMatrix; centerMatrix(α) = (α/N)(poleKernel − centerKernel).
- ⟨completeWeilMatrix x, x⟩ = weilQuad(atomicTest of dilate)/atom mass (canonical normalized actual Weil functional).

## HorizonKernelEuclideanIdentities
- horizonProfileVector/horizonKernelMatrix: matrix rows = literal integer-kernel sums; squared residual norms and quadratic forms = literal finite sums (zero extension inverse to restriction).

## TheWeilReplacementErrorsVanishOnRamanujanModes
- Uniformly square-bounded horizon vectors vanish after normalization by √log N. On normalized Ramanujan vectors: center correction residual → (if m=1 then α) shift; cross-error and pole-error matrices → 0 in norm (0 < c < 1).

## TheCompleteWeilMatrixHasRamanujanQuasimodes
- For 0 < c < 1 and every conductor m > 0: ‖W_N v_m − E(m)v_m‖ → 0, E(m) = completeWeilAdjunctionEnergy = selfFinitePart(c) + adjunction(m) − γ + [m=1]c(∫φ)²/∫φ². Residual = prime residual + self-error + center + cross-error + pole-error, each → 0. (Actual complete Weil matrix, both poles, literal integrals.)

## ThePoleProjectionIsTheEuclideanGroundProjection
- horizonPoleVector 1/√n has ‖·‖² = harmonicMass N ≥ 1. Arithmetic poleProj = orthogonal Euclidean projection off normalized pole; projected vector on harmonic hyperplane; poleDefect unchanged; norm contracts.

## TheCenterCorrectionIsBoundedOnThePole
- ‖C_α·pole − α·pole‖² ≤ 6α²; for α ≥ 0: ‖C_α·normalized pole‖ ≤ 4α (harmonic mass ≥ 1).

## TheCenterCorrectionRetainsThePrimeDefect
- Two-pole form = 2·harmonicSum(a)·Σa_n√n ⇒ vanishes on harmonic hyperplane; there center form = −α·collar/N. Young: center form ≥ −α(1 + 1/λ)poleDefect − α((1+λ)ψ + 3)|x|² on hyperplane; whole horizon (ground-projection transfer, symmetric-form lemma, action ≤ 4α on pole): ≥ −α(1+1/λ)poleDefect − α((1+λ)ψ + 15)|x|².

## TheCompleteWeilEnergyControlsThePrimeDefect
- completeWeilEnergy = renormalizedPrimeEnergy + (selfFinitePart − γ + selfError)|x|² + center − crossError + poleError (exact). |crossError form| ≤ 4·const·c²|x|², |poleError form| ≤ 2·const·c²|x|².
- Coercivity (0 < c < 1): ∃a, eventually ∀x: a|x|² + ((1−c)/4)poleDefect ≤ completeWeilEnergy (Young λ = 2c/(1−c), α ≤ c ⇒ α(1+1/λ) ≤ (1+c)/2).

## BoundedCompleteWeilEnergyHasFiniteRamanujanCoordinates
- Bounded energy ⇒ bounded poleDefect ⇒ uniform finite Ramanujan approximation (any η); unit vectors with energy ≤ T have Σ_{m∈S}⟨x, v_m⟩² ≥ 1/18 for fixed finite S (no limiting operator assumed).

## TheCompleteWeilMatrixRealizesFiniteAdjunctionPackets
- Each conductor m: eventually an eigenvalue of W_N within ε of E(m). Fixed finite packets: distinct eigenvalues, each within ε (trial energies separated). Finite strict sublevels stay δ below threshold.

## TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum
- Lower count: #{m > 0: E(m) < T} ≤ #{eigenvalues of W_N < T} eventually (packets). Upper count (T ∉ {E(m)}): low eigenvectors have ≥ 1/18 Ramanujan coordinate mass; residuals suppress coordinates with E(m) > T (inner² ≤ residual²/gap²); rank bound. Equality: every bounded window of the literal complete Weil matrix is exhausted, with multiplicity, by the simple adjunction energies E(m).

## TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines
- Isolating radius δ around each E(m); window [E − δ, E + δ) eventually contains exactly one eigenvalue, converging to E(m); window projection of v_m captures it: ‖v_m − P v_m‖² ≤ residual²/δ² → 0.

## TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets
- ⟨W_N v_m, v_l⟩ → δ_{ml}E(m); packet Gram → Σb_md_m; ⟨W_N packet_b, packet_d⟩ → Σb_md_mE(m) (diagonal on fixed finite packets, incl. conductor-one pole shift). Packet normalization = (log N)^{−1/2}·literal profile; matrix forms scale by 1/log N.

## TheRamanujanPacketPoleCoordinatesSelectConductorOne
- Harmonic pole coordinate Σ_n r_m(n)/√n/log N → [m=1]; ordinary mean Σ r_m(n)/N → [m=1] (period sum 0 for m ≠ 1). Packets: both pole coordinates → ground coefficient b_1. N·(normalized two-pole product) → poleShift. Both actual poles on packet test: 2(∫Te^{−u/2})(∫Te^{u/2})/((c/N)log N) → 2c(∫φ)²b_1².

## TheMarkovAndWeilPacketFormsHaveOppositePoleShifts
- ramanujanPacketTest = atomicTest of packet profile with atomDilate φ (c/N). Mass/((c/N)log N) → ∫φ²Σb_m². weilQuad/((c/N)log N) → ∫φ²Σb_m²(selfFinitePart + log m + tame(m)) + c(∫φ)²b_1². Markov (= Weil − two poles) → same − c(∫φ)²b_1²: opposite conductor-one pole shifts.

## ThePrimeDefectLocalizesAtAMacroscopicCutoff
- cutoffPrimeCost(M,N) = log N − log M + log4 + 4 + log8 + 4 bounds outgoing Mertens mass A(N/m) − A(M/m). Outgoing tail edges ≤ cutoffPrimeCost·|x|². logarithmicTailMass(M,N,x) = Σ_{n>M}log n·x_n² = incoming tail edges; ≤ (1+1/u)poleDefect + (1+u)cutoffPrimeCost·|x|² (no factor N/M).
- poleDefect = Σ_n Σ_{t|n}Λ(t)(x_n − x_{n/t}/√t)² (upper-endpoint indexing). poleDefect N = poleDefect M + crossing edges. poleDefect N ≤ poleDefect M + 2·logTail + 2·cutoffPrimeCost·|x|². (#print axioms lines in source.)

## TheArithmeticTailPaysForItsLogarithmicMass
- atomicTailCoefficients (n > M); atomicTest N = prefix (M) + tail exactly; masses split. w < δ_M ⇒ prefix and tail supports ordered (gap between log M + w and log(M+1)). poleDefect monotone in horizon. log N·tail mass ≤ (1+1/u)poleDefect + ((1+u)cutoffPrimeCost + log N − log M)|x|².

## CompletedShell/TheCompletedShellEnergyIsAPositiveFourierIntegral (namespace ...CompletedShell)
- φ ∈ C², supp [0,1], M = ∫φ², G autocorrelation, P(t) = |φ̂(2πt)|². Completed shell energy E(c) = log(1/(2πc)) + β(φ)/M + cq − (2/M)Σ_{1≤h<c}∫_{h/c}^1 G(u)/u du (q = (∫φ)²/M).
- G = 0 for |x| ≥ 1, G(0) = M, G ∈ C², P(0) = (∫φ)², P even, quartic decay. Poisson on ℤ/s: Σ_k P(ks) = s⁻¹Σ_m G(m/s) = s⁻¹(M + 2Σ_{1≤j<K}G(j/s)) (s ≤ K); one-sided Σ_{n≥1}P(ns) = (s⁻¹(M + 2Σ G(j/s)) − (∫φ)²)/2.
- Increment law E(c) − E(C) = (2/M)Σ_k(1/k)∫_{kc}^{kC}P; E(c) → 0 as c → ∞ (Stirling: −log 2π is Stirling's constant); E(c) = (2/M)Σ_k(1/k)∫_{kc}^∞P ≥ 0, antitone; for c ≤ 1 E(c) = conductor-one complete-Weil energy.
- Shell change of variables ∫_c^C s⁻¹G(j/s)ds = ∫_{j/C}^{j/c}G(u)/u du; increment proof integrates one-sided Poisson over s ∈ [c,C] (dominated convergence by quartic decay).
- Cell averaging: continuous H ⇒ n∫_0^1 uH − Σ_{1≤h<n}∫_{h/n}^1 H → ½∫_0^1 H (mean-zero weight nu − j − ½ per cell + uniform continuity).
- shellRegular H(u) = (G(0) − G(u))/u, continuous (G'(0) = 0 by evenness). β(φ) = bumpRobin = ∫_0^1 H. 2∫_0^1 G = (∫φ)². ∫_a^1 G/u = G(0)log(1/a) − ∫_a^1 H. Exact Stirling form at integers: E(m+1) = 2log stirlingSeq(m+1) − log π − (2/M)(R_{m+1} − ½∫H), R_n = cell average. Marginality along integers then squeeze by antitonicity; positivity from limit; Fourier series by dominated convergence of the increment series.

## CompletedShell/TheShellsRepayEveryConductor
- Reference energy E_m^ref(c) = log(1/(2πc)) + β/M + log m + τ(m) + [m=1]cq; past touching loses log c (negative). Completed conductor energy E_m(c) = φ(m)⁻¹Σ_{d|m}μ(m/d)d·E(c/d) (Möbius inversion of conductor-one E).
- Σ_{d|m}μ(m/d) = [m=1]; Σ_{d|m}μ(m/d)d = φ(m); Σ_{e|m,e|k}μ(e) = [(m,k)=1]. shellSum(c/d) = shells h ≡ 0 mod d of shellSum(c).
- Shell form: E_m(c) = E_m^ref(c) − (2/(Mφ(m)))Σ_{1≤h<c}c_m(h)∫_{h/c}^1 G/u (Ramanujan sums c_m(h) = ramanujanLagCoefficient). Uses Σμ(m/d)d log d = φ(m)(log m + τ(m)) (CACT). E_m = E_m^ref for c ≤ 1.
- Repayment: E_m(c) = (2/(Mφ(m)))Σ_{a≥1,(a,m)=1}(m/a)∫_{ac/m}^∞|φ̂(2πt)|²dt ≥ 0 (Möbius signs collapse to coprimality). E_m → 0.
- Repayment proof: each divisor term's Fourier series reindexed n+1 = (k+1)(m/d); pointwise Σ_{d: (m/d)|(n+1)}μ(m/d) = [(m,n+1)=1].

## TheCompleteWeilMatrixDecomposesAtEveryOverlap
- atomArchPair(g,n,j) = 2θ'(0)⟨a_n,a_j⟩ + ∫levyMixed; markovPair = archPair − primePair; diagonal = self-energy; separated (> w) pairs = −atomCrossTerm.
- Exact identity for every c > 0: W = (log N + self(c) − γ + selfErr)I − P + Center(cq) − CrossErr^sep + PoleErr + Ov − NR. separatedCrossErrorMatrix: pairs with log-distance > 2w; overlapMatrix: near distinct pairs (≤ 2w) carrying literal archPair/mass + center kernel added back; NR = non-ratio prime matrix (CACT fullWeilNonRatioMatrix). Threshold 2w keeps far cross error under reciprocal-square bound.

## TheNearAtomsHaveALogarithmicPairing
- Robin shape scales: β(φ_w, wR) = wβ(φ,R); β(φ,R) = β(φ) + ∫φ²·log R for R ≥ 1. Dilated autocorrelation ∫φ_w(u)φ_w(u−s) = wG(s/w). archPair reads only log-distance. Single-atom shape on window ≤ 3w ≤ w(β + ∫φ²log 3); unit combination a·atom + translate has ≤ 4× shape term.
- Target: Arch(n,j)/(w∫φ²) = log(1/w)·G(s/w)/∫φ² + O_φ(1) uniformly for 0 ≤ s ≤ 2w, w ≤ 1/3.
- Mixed shape |mixedBumpRobin(φ_w, translate, W)| ≤ 2w(β + ∫φ²log3) (polarization of unit combinations). Near-pair theorem exists_abs_atomArchPair_near_sub_le: K = |2θ'(0)| + |c_∞| + log3 + 2(β/M + log3) + e^{1/2}; |Arch/(w∫φ²) − log(1/w)G(s/w)/∫φ²| ≤ K for s ≤ 2w, w ≤ 1/3 (mixed Robin expansion on window W = w + s ≤ 3w).

## ThePrimeFormCollapsesOnThePoleProfile
- horizonDivisorMangoldt Λ_N(ℓ) = Σ_{d|ℓ, ℓ/d≤N}Λ(d): = log ℓ if ℓ ≤ N; 0 ≤ Λ_N ≤ log ℓ. Λ-atom(k)·k... : vonMangoldtAtom(k)·m^{−1/2} = Λ(k)(km)^{−1/2}.
- On pole profile x_n = n^{−1/2}: NR_g(x) = 2Σ_{n≤N}Σ_{ℓ≠n}n^{−1/2}ℓ^{−1/2}Λ_N(ℓ)G(log ℓ − log n) (ℓ ≤ ⌈Ne^w⌉): unique factorization collapses the non-ratio prime form; prime side of shells becomes archimedean absolute value log ℓ.

## TheShellPairSumsAreRiemannSums
- Right Riemann sums of F continuous on [0,1] converge. Shell h pair sum Σ_{n+h≤N}(n(n+h))^{−1/2}G(N log(1+h/n)/c) → ∫_{h/c}^1 G(u)/u du; total off-diagonal pole pair sum → 2S(c) (twice shell sum of completed energy).
- Shell proof: shellProfile y ↦ G(h/(cy))/y continuous on [0,1], ∫ = ∫_{h/c}^1 G/u. 0 ≤ 1/n − (n(n+h))^{−1/2} ≤ h/(2n²); |log(1+x) − x| ≤ x². Terms vanish for n < hN/(4c); interior terms differ from Riemann values by O(c²/N²) (Lipschitz G), h boundary terms O(1/N) ⇒ shell sum = Riemann sum + O(1/N). poleProfilePairSum = 2Σ_{1≤h≤⌈c⌉}shellPairSum (pairs beyond distance c vanish).

## TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
- upwardPrimeRow (partners j ≈ kn, j = kn removed), downwardPrimeRow (kj ≈ n). Downward row on Ramanujan modes collapses by divisor jet Σ_{a|ℓ}Λ(a)c_m(ℓ/a) = c_m(ℓ)log ℓ − J_m(ℓ); upward row is affine prime window with Ramanujan average c_m(n)c_m(h)/φ(m) ⇒ shellCorrection κ_m(c) = (2/(Mφ(m)))Σ_{1≤h<c}c_m(h)∫_{h/c}^1 G/u. completedConductorEnergy = reference − κ_m. Hecke pairings of atoms = bumpCorr(log k ∓ (log n − log j)).
- primePair(atom_n, atom_j) − (∫g²)Λ-kernel(n,j) = Σ_k Λ-atom(k)(downward + upward non-ratio bumpCorr values) (finitely supported in lagRange). Row identity: non-ratio matrix row n = (downwardPrimeRow + upwardPrimeRow)/atom mass.

## TheReplacementErrorsVanishAtEveryOverlap
- For any fixed c > 0 (once c ≤ N): self-error ≤ (e^{1/2}/2)(c/N) → 0; two-pole coefficient ≤ const(c/N)² ⇒ pole-error on Ramanujan modes → 0; far cross error (s > 2w ⇒ s − w > s/2) obeys |E| ≤ 152(∫|φ|)²/∫φ²·w²max²/|n−j|² ⇒ vanishes on Ramanujan modes.

## TheCompleteWeilResidualIsTheUpwardDefect (start)
- upwardPrimeVector/downwardPrimeVector (rows/atom mass); nearCenterVector (center kernel on near pairs). Near pairs: log-gap ∈ [1/N, 2c/N] ⇒ center entry ω(y) ≤ N/2 + e^{1/2}/4; with coefficient α/N bounded.
- Claim: at every c > 0, W v_m − E_m(c)v_m = −(Up v/‖g‖² − S_m(c)v) + o(1); near block: archimedean log(N/c)G of nearby atoms cancelled by downward prime products via Σ_{d|ℓ}Λ(d) = log ℓ.
- Near center vector → 0 (near rows have bounded width nearRowRadius; /log N). Overlap row on Ramanujan mode = downward prime vector + φ(m)^{−1/2}·near-Gamma-downward residual (CACT, → 0) + near center.
- Exact residual at every overlap: W v − E_m(c)v = −(prime residual) + selfErr + center residual − sepCross + poleErr + nearGamma + nearCenter − (Up v − κ_m v). tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm: ‖W v − E_m(c)v + (Up v − κ_m(c)v)‖ → 0 for every c > 0.

## TheUpwardPrimeWindowsCarryTheShellCorrection (start)
- |G| ≤ M, G Lipschitz. |log(1+δ) − δ| ≤ δ²; |−log(1−δ) − δ| ≤ 2δ² (δ ≤ ½). upwardModePair/upwardModeRow (scale √(n log N)√φ(m)); cutoff k ≤ ⌈Ne^c⌉ + 1. Row identity Up_n/G₀ = upwardModeRow/(√n√log N√φ(m)).
- c_m(p + (m−1)h) = c_m(p − h); c_m((m−1)h) = c_m(h). Real Mertens window Σ_{aX<k≤X}Λ(k)/k ≤ log(2/a) + mertensWindowConstant.
- Plan: row ≈ (1/M)Σ_h[shell(n,h) + shell(n,(m−1)h)] + O(1/N) + O(log X/X) boundary (X = N/n); weighted affine prime theorem (CACT) gives c_m(n)κ_m(c); rows with bounded X have harmonic mass O(1/log N) ⇒ Up acts as κ_m(c) in ℓ².
- Pair vs affine-shell model: |√(p/j)G(|log p − log j|N/c) − G(hN/(cp))| ≤ (4cHM + 8cH²ℓ)/N for p > N/(2c), both 0 below (j = p ± h, 1 ≤ h ≤ H, 4cH ≤ N). Pairs farther than H ≥ 2c carry no G. Window model upwardShellModel = Σ_h(c_m(p+h) + c_m(p+(m−1)h))G(hN/(cp))/M (down shift p − h ≡ p + (m−1)h mod m). Upward mode row = Σ_k Λ(k)/k·window(kn).
- Row vs model ≤ H φ(m)(2E/(MN))(log(2/a) + C_Mertens) + 3Hφ(m)·boundaryMass; boundaryMass ≤ 2H·2log(2X)/X (X = N/n). Model = (1/M)Σ_h[affineRamanujanPrimeShell(m,n,h) + (m,n,(m−1)h)] (CACT); κ_m(c)c_m(n) = mean of reciprocal shells c_m(n)c_m(h)/φ(m)∫G/u (both orientations).
- Rows with Jn ≤ N within ε of κ_m(c)c_m(n) (CACT eventually_affineRamanujanPrimeShell_uniform); rows N < Jn bounded by B. Squared row defect = (row − κc_m(n))²/(n log N φ(m)). tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection: ‖Up v − κ_m(c)v‖² → 0 (near rows contribute ε²(1 + log N)/log N, far rows B²J/log N).

## TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum
- Min-max lemma: k almost-orthonormal quasimodes (Gram error η, residual ρ, energies ≤ T − δ, |E − T| ≤ B; kη ≤ 1, kBη + ρ(k+1) < δ) ⇒ ≥ k eigenvalues < T (coincident energies allowed).
- |κ_m(c)| ≤ (2/M)Σ_{h<c}|∫_{h/c}^1 G/u| uniformly in m (|c_m(h)| ≤ φ(m)) ⇒ completed sublevels finite.
- Conditional exact count (hypotheses: prime-defect reserve a|x|² + β·poleDefect ≤ energy, and norm quasimodes against E_m(c) for all m): #{eigenvalues < T} = #{m: E_m(c) < T} eventually (T off energy set). completedEnergyFloor = inf_m E_m(c) ≥ 0, attained, → 0 as c → ∞ (margin vanishes). Under the same hypotheses all eigenvalues > floor − ε and one within ε of floor.
- TRAP: these spectral-count theorems at general overlap take reserve + quasimode hypotheses as explicit binders (proved unconditionally only for c < 1 elsewhere).

## LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis (header)
- Complete Weil matrix = Weil form on atoms φ((u − log n)/w), w = c/N; recentred unit-mass profile φ_S(s) = φ((s+1)/2)/(2∫φ) on [−1,1] dilated by κ = 2/w is the same atom (translation invariance). Second-order overlap law (SSHA) transfers: c_N⁴/log N → ∞ and c_N = o(N) ⇒ [complete Weil matrices eventually PSD ⇔ RH]. c_N = 2(log N)^α, α > 1/4, holds for tilted unit spline.
- Proof: recentredProfile ∫ = 1 (needs ∫φ ≠ 0); weilQuad translation invariant; forall_completeWeilEnergy_nonneg_iff (fixed N) ⇔ Weil form ≥ 0 on atomic tests of recentred dilate; then SSHA riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo (OverlapGrowthTwo κ_N = 2N/c_N). Tilted unit spline: ∫ ≠ 0, ∫² > 0; c_N = 2(log N)^α, α > 1/4 qualifies (overlapGrowthTwo_log).

## CompletedShell/ThePoleConductorMinimizesTheCompletedEnergy
- Coprime repayment series grouped into blocks of m residues: each block pays the conductor-one term (φ(m) reduced residues per block, T antitone); first block leaves surplus (m−1)T(1). completedConductorEnergy(1) = completedShellEnergy.
- E_m(c) ≥ E_1(c) + ((m−1)/φ(m))(2/M)∫_c^∞P; conductor one minimizes; nonpolar gap ≥ (2/M)∫_c^∞P (φ(m) ≤ m − 1). Tilted spline: tail integral > 0 ⇒ strict gap; E_m = E_1 iff m = 1. (#print axioms lines in source.)

## TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy
- completedEnergyFloor = completedShellEnergy (conductor one minimizes). Tilted unit spline, every c > 0 (reserve from CACT exists_tiltedUnitSpline_completeWeilEnergy_reserve, quasimodes from CACT tendsto_completeWeilMatrix_ramanujan_quasimode_norm): exact low spectral counts = completed conductor counts; spectrum bottom → E(c) = (2/M)Σ_k(1/k)∫_{kc}^∞|φ̂(2πt)|² > 0; E(c) → 0 as c → ∞.
- tiltedUnitSpline_overlap_window: ∀c > 0 eventually PosDef (unconditional; CACT eventually_tiltedUnitSpline_completeWeilMatrix_posDef) ∧ ∀α > 1/4 (RH ⇔ eventually PSD at c = 2(log N)^α).
- exists_unbounded_overlap_schedule_posDef: ∃ s_N → ∞ with W(c = s_N + 1) eventually PosDef (diagonalization). Critical growth lies strictly above some unbounded schedule; a proof that every unbounded growth decides RH would prove RH.

## TheLowCompleteWeilSpectrumLivesOnTheLowConductors
- Near-orthonormal (kη ≤ ½) family: Σa² ≤ 2‖Σa_kw_k‖²; dim U vectors in U form a basis with controlled coefficients. completeWeilLowSpace U_N(T) = span of eigenvectors < T, dim = spectral count. Davis–Kahan: ‖v − P_{<T}v‖ ≤ ‖(A − E)v‖/(T − E).
- Under reserve + quasimodes: every v_m (E_m < T) within ε of U_N(T), and every x ∈ U_N(T) within ε‖x‖ of span{v_m : E_m(c) < T} (eigenvector localization on low conductors). Tilted unit spline: holds at every c > 0. Diagonal schedule lemma; thresholds T' ∈ (T, T+1] off energy set; localization persists along an unbounded overlap schedule c = s(N) + 1 with error 1/(s(N)+1).

## EveryLowConductorSeesTheFlipSet
- Flip odd powers of primes in finite S; Y_S = Π_{p∈S}F_p = Ramanujan packet Σ_{d|Q}β_de_d, Q = flipSetModulus = Πp². Normalized modes multiplicative on coprime conductors; period means factor over coprime moduli; (m,d) ↦ md injective (d = gcd(md,Q)).
- Flip does not see conductor: flip energy of (Σa_me_m)Y_S = (Σa_m²)τ_S (flipped lags are powers of primes in S, coprime to m, fix e_m). Blocks orthogonal: limiting twisted energy Σa_m²b_m, b_m = Σ_dβ_d²E_{md}(c) + τ_S.
- Min–max: negative definite on #K-dim image ⇒ ≥ #K negative eigenvalues; coefficients converging to negative diagonal ⇒ eventually negative definite.
- exists_overlap_flip_negIndex_ge: nonempty S, every n: ∃c₀, ∀c ≥ c₀ eventually S-flipped complete Weil matrix has ≥ n negative eigenvalues (n primes > Q as conductors; E_{md}(c) → 0, τ_S < 0). ζ's matrix is PosDef at every fixed overlap: twin index grows unboundedly with resolution.

## EveryFlippedPrimeIsSeenAtLargeOverlap (first half)
- pairing(atomicTest, k) = 2ΣΣx_ax_b bumpCorr(log k − (log b − log a)). Flip of one prime p changes Weil form only by p-power lags: weilQuadTw(flip_p) − weilQuad = (∫g²)(P_N(x) − P_N(ε_p x)) [exact-ratio part = separated arithmetic correction] + flipWindow (off-ratio pairs).
- Flipped coefficient (1 − ε_p(k))Λ-atom(k) nonzero only at k = p^j, |·| ≤ 2log p/√k; Σ_j 1/p^j ≤ 1. Product L = ka has ≤ 6wL neighbours at log-distance ≤ w (all > L/3). One flipped lag window ≤ 72(wN)‖g‖²/√k on trials |x_n| ≤ n^{−1/2}; whole window |flipWindow| ≤ 144(wN)log p‖g‖² = O(c), independent of N.
- Separated correction on prime-square trial F_p(n)/√n: (4log p/p)(−1 + 2/p²)log N + ≤ 2τ_p(1 − 1/p + 1/p²)log N, τ_p = 2log p/(p(p²−1)); negative for every prime. Finite packet energies Σβ_m²E_m from quasimodes.
- Prime-square trial F_p/√n = √log N·Σ_{m∈{1,p,p²}}β_m v_m (β_1 = 1 − 2/p + 2/p², β_p = (−2/p + 2/p²)√φ(p), β_{p²} = (2/p²)√φ(p²)); flipTrialEnergy = Σβ_m²E_m(c). Odd powers p^{2j+3}: Σ1/t ≤ 1/(p(p²−1)). flipGain(p) = (4log p/p)(−1 + 2/p²) + 2τ_p(1 − 1/p + 1/p²) = 4log p(−p⁴ + 4p² − p − 1)/(p³(p²−1)) < 0 for every prime.
- Flipped form on trial ≤ ‖g‖²log N(trial energy + sharpFlipBound/log N + 144c log p/log N); sharpFlipBound/log N → flipGain. If flipTrialEnergy + flipGain < 0 then eventually flipped Weil form < 0 on trial. exists_flip_negative_at_every_large_overlap: ∃c₀ ∀c ≥ c₀ (E_m(c) → 0). tiltedUnitSpline_flip_selective: beyond c₀, ζ PosDef while p-flipped twin negative on the trial.

## NoFixedOverlapSeesEveryFlip
- |pairing f k| ≤ 2∫f² (Cauchy–Schwarz); Σ_j p^{−j/2} ≤ 2/√p (p ≥ 4). Flip perturbation |weilQuadTw(flip_p) − weilQuad| ≤ (8log p/√p)∫f². Atomic mass at fixed overlap ≤ (1 + 2ce^c)‖g‖²Σx² (SSHA); ζ form ≥ (E(c)/2)‖g‖²Σx² eventually (spectrum bottom).
- eventually_flip_posDef_of_large_prime: every c > 0, all primes p ≥ p₀(c): p-flipped form eventually positive on every nonzero atomic test (tilted spline). With previous: flip threshold c*(p) finite for each p and → ∞ with p (tiltedUnitSpline_flip_threshold_finite_and_unbounded): selectivity at bounded overlap is not uniform in the prime.

## TheFlipThresholdGrowsLikeAPowerOfThePrime (start)
- Plancherel ∫P = M; tail T(y) ≤ M/2. |φ̂|² ≤ At⁻⁸ ⇒ T(y) ≤ (A/7)y⁻⁷. Harmonic head/tail bounds (head ≤ 1 + log⁺(1/y), tail Σ1/((n+1)²y) ≤ 2).
- E_m(c) ≤ (m/φ(m))E_1(c/m); T(z) ≤ Bz⁻⁷ ⇒ E_1(y) ≤ (4B/M)y⁻⁷ (y ≥ 1) and E_1(y) ≤ 1 + log⁺(1/y) + 4B/M.
- Header claims: prime-square trial energy E_1(c) − (1/p)(log c − O(1)) (log p/p excitation cancels flip gain exactly since T(0) = M/2) ⇒ every prime seen at overlap O(p^{1/7}); lower: no c ≤ (κ√p/log p)^{1/8} sees p-flip (margin E_1(c) ≥ Cc⁻⁷, Gram ≤ 1 + 2ec). Selectivity spectrum (κ√p/log p)^{1/8} ≤ c*(p) ≤ (Kp)^{1/7}.
- Tilted spline: |φ̂(2πt)|² ≤ A t⁻⁸ (A = cosh(1)⁸4⁸/(64π⁸)); T(z) ≤ (A/7)z⁻⁷; E_1(y) ≤ K₀y⁻⁷ (y ≥ 1), ≤ 1 + log⁺(1/y) + K₀.
- Upper: algebraic core (q ≥ 11, L < q, X ≤ −1): trial energy + flip gain = ((q²−1)(q² + 4X(q²−q+1)) + 4L(4q²−q−2))/(q³(q²−1)) < 0. ∃K: p ≥ K, c ≥ K, c⁷ ≥ Kp ⇒ p-flip negative on prime-square trial.
- Lower: atomic Gram ≤ (1 + 2ec)‖g‖²Σx² at c ≤ N; if 16(1+2ec)log p/√p < E(c) then p-flip positive; tilted spline E_1(c) ≥ C₀/max(c,1)⁷ (CACT polynomial floor). ∃κ: max(c,1)⁸log p ≤ κ√p ⇒ p-flip eventually positive.
- tiltedUnitSpline_flip_threshold_polynomial: (κ√p/log p)^{1/8} ≤ c*(p) ≤ (Kp)^{1/7}.

## TheTwistedCompleteWeilFormHasAPeriodicLimit
- Real twist λ: Q_λ(f) − Q(f) = Σ_k d_λ(k)pairing_k(f), twistDefect d_λ(k) = Λ-atom(k) − twistCoeff λ(k). shiftMean M(y·y(k·)); twistLimitEnergy = 2Σ_k d_λ(k)k^{−1/2}M(y·y(k·)); packetCoeff y(n)/√(n log N).
- Harmonic average cut at N/k keeps period mean (tail ≤ kG). Pairing of atomic test = ‖g‖²·ratioPairs + offRatioPairs; ratioPairs = 2Σ_{a≤N/k}x_ax_{ka}. Packets: ratioPairs → (2/√k)M(y·y(k·)), |·| ≤ 4B²; off-ratio ≤ (B²/log N)72(wN)‖g‖².
- tendsto_twistedGap_packet: Σ|d_λ| < ∞, y periodic ⇒ (Q_λ − Q)(f_N)/‖g‖² → twistLimitEnergy(λ,y,P) (overlap c drops out; twist seen only via defect × multiplicative correlations).

## ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets
- Linear algebra: Hermitian with positive form ⇒ PosDef; polarization |⟨Ax,y⟩| ≤ b‖x‖‖y‖ from |⟨Ax,x⟩| ≤ b‖x‖²; 2×2: μs² − 2Csξ + Dξ² > 0 if C² + μ ≤ μD; near-orthonormal ‖Σa v‖² ≤ 2Σa²; quasimode cross term |⟨W Σa v, z⟩| ≤ √(Σa²)‖z‖ for z ⊥ v.
- Schur estimate posDef_add_of_packets: almost orthonormal quasimodes of W (residual ≤ ε), W ≥ T on complement, |G| ≤ b, packet form of W + G ≥ μΣa², T ≥ b + (1+2b)²/μ + 1 ⇒ W + G PosDef.
- twistGapMatrix (lag-sum gap at atom mass), twistedCompleteWeilMatrix = W + G_λ; form = twisted Weil form of atomic test/atom mass. |⟨G_λx,x⟩| ≤ 2Σ|d_λ|(1 + 2ce^c)‖x‖².
- Header: packet energies E_λ(T,β) = Σβ_m²E_m(c) + 2Σd_λ(k)k^{−1/2}M(y·y(k·)), y = Σβ_me_m; complement expensive (reserve + finite Ramanujan approximation); dichotomy: all packet energies ≥ μΣβ² ⇒ eventually PosDef; some packet < 0 ⇒ eventually negative on its atomic test. Sign at fixed overlap = sign of explicit quadratic form on finite Ramanujan coordinates.
- exists_finite_orthogonal_gap: reserve ⇒ ∀T ∃ finite S: W ≥ T on vectors orthogonal to {v_m : m ∈ S} (bounded defect forces finite Ramanujan approximation; orthogonality makes approximation error = full mass).
- packetProfile, packetPeriod = Πm, packetEnergy(λ,φ,c,T,β) = Σβ_m²E_m(c) + twistLimitEnergy(λ, packet profile). tendsto_twisted_packet; negative packet energy ⇒ eventually negative on its atomic test. eventually_twistedCompleteWeilMatrix_posDef: reserve + Σ|d_λ| < ∞ + all packet energies ≥ μΣβ² ⇒ eventually PosDef (polarization gives coefficient limits; Schur estimate).

## TheOverlapThatResolvesATwistIsAnExactThreshold
- Packet energy quadratic (homogeneous degree 2). twistBound(λ,c) = 2Σ|d_λ|(1 + 2ce^c), monotone in c; |twist part of packet| ≤ twistBound·Σβ²; packetEnergy ≥ (E_1(c) − twistBound)Σβ² (all conductors ≥ pole conductor).
- resolutionBottom λ_λ(c) = inf over unit packets; bounded below; λ_λ(c)·Σβ² ≤ packetEnergy. λ_λ(c) > 0 + reserve ⇒ eventually PosDef; λ_λ(c) < 0 ⇒ unit packet with eventually negative atomic test; PosDef with y_1 ≠ 0 eventually negative test ⇒ λ_λ ≤ 0.
- E_m(c) antitone in c (strictly if φ̂ has no real zeros: spectrum P > 0); λ_λ antitone. resolutionBottom_neg_of_lt (no real Fourier zeros): λ_λ(c) ≤ 0, c < c' ⇒ λ_λ(c') < 0 (near-minimizer keeps ≥ ½ mass on finitely many conductors of energy < 2twistBound + 2, each dropping ≥ g).
- Small overlaps resolve nothing: c = e^{−X}/(2π) gives E_1(c) = log(1/(2πc)) + ... > twistBound ⇒ λ_λ > 0. resolutionThreshold c_0(λ) = sup{c: λ_λ(c) > 0}. resolutionThreshold_spec (no real Fourier zeros, Σ|d_λ| < ∞, seen at c₁): 0 < c_0 ≤ c₁; c < c_0 ⇒ eventually PosDef (reserve from CACT exists_noRealZero_completeWeilEnergy_reserve); c > c_0 ⇒ unit packet eventually negative.

## TheResolutionThresholdOfAFlippedPrimeIsExact
- Flip ω_p: defect 2log p·p^{−k/2} on odd powers of p, summable; Σ|d| ≤ 4log p/√p (p ≥ 4). Explicit flip energy: twistLimitEnergy = 4log p Σ_j p^{−(2j+1)}M(y·y(p^{2j+1}·)) (even powers cancel). |shiftMean| ≤ (Σ_{period}|y|)².
- Resolution–distance law: twist at square-root distance D = Σ|d_λ| unresolved where E_1(c) > twistBound; |packet twist energy| ≤ 2DΣβ² (c → 0 limit, independent of overlap); λ_λ(c) ≥ E_1(c) − 2D; above threshold E_1(c) ≤ 2D.
- Every flipped prime seen (exists_primeFlip_resolutionBottom_neg); primeFlip_resolutionThreshold_spec (profiles without real Fourier zeros): exact finite positive threshold c_0(ω_p). le_primeFlip_resolutionThreshold: c_0(ω_p) → ∞. Above threshold E_1(c) ≤ 8log p/√p; tilted spline: C₀√p ≤ 8log p·max(c,1)⁷ ⇒ c_0(ω_p) ≥ (C₀√p/(8log p))^{1/7}. Tilted spline has no real Fourier zeros (paperFT_tiltedUnitSpline_real_ne_zero).

## EveryFiniteFlipSetHasAnExactResolutionThreshold
- finiteFlipWeight S; defect = Σ_{p∈S} single-prime defects (summable); limit twist energy additive over S. flipSetTrial Y_S = Π_{p∈S}F_p, F_p = 1 − 2·1_{p|n} + 2·1_{p²|n} (unit square); Y_S(n)Y_S(q^kn) = F_q(n)F_q(q^kn) (other primes blind to q^k).
- Prime-square trial flip energy ≤ (4log q/q)(−1 + 2/q² + 1/(q²−1)) < 0 (first lag mean −1 + 2/q², later ≤ 1). Y_S depends on gcd(n, Πp²) ⇒ finite Ramanujan packet on divisors of flipSetModulus. Product trial flip energy < 0; packet energy → it as c → ∞ ⇒ every nonempty finite flip set seen.
- finiteFlip_resolutionThreshold_spec: exact threshold (profiles without real Fourier zeros; tilted spline instance). (#print axioms lines in source.)

## TheFlipThresholdIsSetByTheConductorsOfThePrime
- Period-mean Cauchy–Schwarz; dilation M(v(k·)²) ≤ kM(v²). Modes of conductor prime to q blind to dilation by q. Split packet y = u (conductors ∤ p) + v (conductors p|): u ⊥ v in period mean; M(y_{S₁}y_{S₂}) = Σ_{S₁∩S₂}β².
- flipCoupling κ_p = 4log p·√p/(p−1) = 4log p Σ_j p^{−(2j+1)/2}. One lag: M(y·y(p^k·)) ≥ −p^{k/2}(√α√b + b) (α = mass on u, b on v). Flip energy ≥ −κ_p(√α√b + b): flip meets u only through v.
- Möbius at a prime: E_{pm}(c) ≥ E_m(c/p) (identity if p|m; else E_{pm} = (pE_m(c/p) − E_m(c))/(p−1) and E_m antitone); p-divisible conductors cost ≥ E_1(c/p) = log(p/(2πc)) + O(1).
- resolutionBottom_primeFlip_ge: D = E(c/p) − κ_p − E(c) > 0 ⇒ λ_p(c) ≥ E(c) − κ_p²/(4D) (2×2 minimization). Header: above threshold 4E(c)(E(c/p) − κ_p − E(c)) ≤ κ_p²; margin at resolution ~ log²p/(p log(p/c)); tilted spline c_0(ω_p)⁷ ≳ p/log p (matches upper (Kp)^{1/7} up to log).
- Proof of bottom bound: packet energy ≥ Eα + E'b − κ(√α√b + b); AM-GM κxy ≤ Dy² + κ²/(4D). margin_mul_le_of_primeFlip_resolutionThreshold_lt: above threshold 4E(c)(E(c/p) − κ_p − E(c)) ≤ κ_p². κ_p ≤ 8log p/√p. Tilted spline E_1(c/p) ≥ log(p/(2πc)) + R (c ≤ p). tiltedUnitSpline_primeFlip_resolutionThreshold_sharp_lower: ∃κ, p₀: κp ≤ log p·max(c,1)⁷ above threshold ⇒ c_0(ω_p) ≥ (κp/log p)^{1/7} (sharp order up to log).

## ThePoleModeMeetsTheZerosOnlyAtTheHorizon
- horizonBoundary B_N(s) = N^{1−s}/(s−1) − s·emTail(N,s); Σ_{n≤N}n^{−s} = ζ(s) − B_N(s) on Re s > 0 (Euler–Maclaurin); at zeros = −B_N. Li charge: emPole(s)emPole(1−s) = N/(s(1−s)); B_N(s)B_N(1−s) = N/(s(1−s)) − pole·tail cross terms + tail·tail.
- Pole mode y_n = n^{−1/2}: Dirichlet factors X_N(1−ρ), X_N(ρ). weilQuad_poleMode_eq_tsum: Q(f_pole) = Re Σ_ρ m_ρ ĝ(γ_ρ)conj ĝ(conj γ_ρ)·B_N(1−ρ)B_N(ρ) for every profile, width, horizon (no overlap condition): zeros see the pole mode only via horizon boundary.

## TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons (header)
- x_n = √n y_n = (a * 1)_n, a = x * μ: Σx_nn^{−s} = Σ_d a_d d^{−s}X_{⌊N/d⌋}(s); at zeros Dirichlet factors = −Möbius horizon H_a(s) = Σ_d a_d d^{−s}B_{⌊N/d⌋}(s). Q(f_y) = Re Σ_ρ m_ρ ĝĝ·H_a(1−ρ)H_a(ρ). Short Möbius transforms (conductor modes) see few boundaries at depth ≍ N; pole mode a = δ₁.
- Proof: regroup Σ_n(a*1)(n)n^{−s} = Σ_d a_d d^{−s}X_{⌊N/d⌋}(s); atomicMobiusTransform a = (√n y_n)*μ inverts zetaExtensionCoeff. weilQuad_atomicTest_eq_tsum_mobiusHorizon for every C² compact atom, horizon, real vector.

## TheHorizonChargeIsBlindToTheRealPartsOfTheZeros
- H_a = mobiusPole − mobiusTail; horizon charge P_a(s) = (s−1)⁻¹Σ_d(a_d/d)N_d^{1−s}, N_d = d⌊N/d⌋ ≤ N. Blindness: on 0 ≤ Re s ≤ 1, ‖P_a(s)P_a(1−s)‖ ≤ N(Σ|a_d|/d)²/‖s(1−s)‖ (N_d^{1−β}N_e^β ≤ N: off-line zero gives no N^{|β−½|} growth).
- Re 1/(ρ(1−ρ)) = β/(β²+γ²) + (1−β)/((1−β)²+γ²) > 0 in the open strip (pair of Poisson kernels); pole-mode charge Re(emPole(ρ)emPole(1−ρ)) = N·Re 1/(ρ(1−ρ)) > 0, on or off the line.

## TheThetaSourceSharesTheHorizonOfThePoleMode
- Each theta atom = seed atom f₁ at −log n with weight n^{−1/2}; truncated theta source = mirrored pole mode of seed. Transform f̂₁(z)Σ_{n≤N}n^{−1/2}e^{−iz log n}; at γ_ρ: −f̂₁(γ_ρ)B_N(ρ). Complete source transform = Ξ (vanishes at γ_ρ) ⇒ theta tail Φ − Φ_N has transform f̂₁(γ_ρ)B_N(ρ). Atomic pole mode carries B_N(1−ρ): theta and atomic positivity read the same Euler–Maclaurin boundary from the two sides of the functional equation.

## TheApertureModesCarryTheThetaApertureCharge
- Aperture mode y_n = n^{κ−1} (pole mode κ = ½), a = ½ − κ: Q(f_κ) = Re Σ_ρ m_ρĝĝ·X_N(1−ρ+a)X_N(ρ+a). Nontrivial zeros are non-real; for a ≥ 0 shifted sums = ζ − B_N. Aperture charge emPole(s+a)emPole(1−s+a) = N^{2κ}/(κ² − (s−½)²); with ρ − ½ = it: N^{2κ}/(κ² + t²); Re Σ_q 1/(κ² + t_q²) = Re(ξ'/ξ)(½+κ)/κ > 0 (theta center-mixed current). For κ < ½ ζ(ρ + a) no longer cancels.

## AWindowedApertureModeIsAnExponentialBoxTest
- Windowed aperture n^{κ−1}1_{M<n≤N}: at zeros ζ cancels between horizons: window sum = B_M − B_N exactly; Q = Re Σ m_ρĝĝ(B_M − B_N)(1−ρ+a)(B_M − B_N)(ρ+a) (κ ≤ ½, no ζ). Pole parts multiply to the zero-side summand of exponential box test e^{κu}1_{[log M, log N]}: (N^{2κ} + M^{2κ} − N^{κ−z}M^{κ+z} − M^{κ−z}N^{κ+z})/(κ² − z²), z = ρ − ½. Cross terms modulus N^{κ−Re z}M^{κ+Re z}: zero with |Re z| > κ outgrows the diagonal as N/M grows; EM tails = aliasing of the atoms.

## PrimeDefectConfinementMustRetainLowEnergyConductors
- Unit Ramanujan vectors: renormalized prime energy → adjunction energy E(m). poleDefect ≤ renormalized prime energy + (log4 + 4)|x|² (row counterterm). Every omitted conductor m yields unit vectors with defect ≤ E(m) + log4 + 4 + ε and retained-coordinate mass < ε. E(2^k) = γ + (k+1)log 2 (linear in k) ⇒ defect-only certificates need conductor cutoff ≥ 2^k for defect level ~ k log 2 (exponential cutoff forced). (#print axioms lines in source.)

## TheHarmonicSieveMassIsControlledByItsEulerCorrection
- Every n = a·b with a Q-supported, b coprime to Π_Q p (unique). H_N = Σ_{a supported ≤ N} sieveClassMass(a,N); sieveDensity·H_N = Σ_a classDensity(a)·sievedHarmonic(N/a) ≤ sievedHarmonic(N). Supported prefix + tail of geometric class density = 1; cutoff log T ≥ 2(sieveEuler − γ) retains half the ground mass.
- sievedHarmonic(N) ≤ 2·density·(log(N+1) + 2(Euler correction) + 4) (no primorial error term). Class mass ≥ density(a)(log(N+1) − log a); ≤ 2·density(a)(log(N+1) + 2E + 4). For a² ≤ N+1 and log(N+1) ≥ 2E + 4: (log(N+1)/2)density ≤ mass ≤ 4log(N+1)density. (#print axioms lines.)

## FiniteSieveProfilesHaveEffectiveRamanujanApproximations
- Spectral truncation of density-weighted sieve eigenbasis at conductor R: relative error in actual harmonic class weights ≤ (16(log A + E)/log R)·mass (A² ≤ N + 1, E = Euler correction); density and log horizon cancel.

## FiniteSieveProfilesHaveExplicitConductorCutoffs
- sieveProfileHorizon = max(A², ⌈exp(2E + 4)⌉); sieveProfileConductorCutoff = max(2, ⌈exp(16(log A + E)/η)⌉) gives relative squared error ≤ η, independent of profile coefficients.

## BoundedPrimeDefectHasAnExponentialConductorCutoff
- primePrefixSieve P (primes < P); supported ⇔ P-smooth; sieveUnits = rough interval; sieveEuler − γ = ladderConstant(P) = Σ_{p<P}log p/(p−1) ≤ 2(log P + log4 + 4). First N conductors span all data on [1,N] (exact horizon Ramanujan expansion via gcd-profile Möbius coefficients).
- Σ log(smoothPart_{<P}(n))x_n² ≤ 2poleDefect + 2ladderConstant·|x|²; mass with smooth part > A ≤ (that)/log A. Harmonic conditioning (smooth–rough mean) contracts mass; supported conductors constant on coprime fibres ⇒ physical error = class-weight error.
- exists_exponential_conductor_cutoff_of_poleDefect_le: ∀η ∃C: ∀K ∃R ≤ exp(C(K+1)) such that every x with |x|² ≤ 1, poleDefect ≤ K, any horizon N, is within η of span{ramanujanPoleProfile m : m ≤ R} (P, A, R chosen with log P, log A, log R = O(K+1); N < R case exact). Exponential cutoff (matches binary-cutoff lower bound in PrimeDefectConfinement…). (#print axioms lines.)

## OverlapGramSmoothingNeedsAQuarterDefectCorrection
- primeDefectPairing (bilinear edge energy); D(x,y) + ¼D(x−y) = ¼D(x+y). poleDefect = 0 ⇔ x ∈ ℝ·pole vector (via spectral gap of the prime form below its pole). normalizedOverlapGram (physical mass Gram / atom mass) PSD; I + Gram bijective at every overlap.
- correctedOverlapDefect τ = D(x, Gx) + τD(x − Gx) = ¼D(x+Gx) + (τ−¼)D(x−Gx) ≥ 0 for τ ≥ ¼; ground line = (I+G)⁻¹(pole line). If Gram does not preserve the pole line then τ ≥ ¼ is necessary. Tilted spline at fixed overlap c > 1: Gram does not preserve pole (first row 1, last row picks positive neighbour) ⇒ ¼ is the exact correction threshold; corrected ground direction u has poleDefect(u) > 0. (#print axioms lines.)

## ThePhysicalPrimeKernelRetainsThePoleDefect
- poleKernelDefect(K) = ½ΣK_{nj}p_np_j(x_n/p_n − x_j/p_j)² (ground-state transform by p_n = n^{−1/2}); defect + form = row potential. Exact-ratio kernel: poleKernelDefect(weilPrimeKernel) = poleDefect.
- physicalPrimeKernel = primePair(atom_n, atom_j); nonRatio part ≥ 0 for nonnegative atoms. Physical defect = ‖g‖²·poleDefect + nonRatio defect ≥ ‖g‖²poleDefect; zero set unchanged (pole line), every overlap, every horizon. weilQuad = physical defect + (Gamma + Lévy + 2cosh² − 2sinh² moments − row potential). Tilted spline: spectral gap δ‖proj x‖² ≤ physical defect/atom mass at every overlap. (#print axioms lines.)

## Signature/TheMatchedPrimeFormHasOnePositiveDirection
- matchedPrimeProfileGram(N,c,x) = primeBilinear − c·Euclidean on any finite family. ∀η < 2log2 ∃N₀: for N ≥ N₀ and every finite family (any type), the Gram matched at c = log N − γ − η is hyperbolic (nonpositive on kernel of polar functional; uses spectral gap 2log2). Pole has strictly positive matched square for η > 0. Sieve classes partition the pole on the horizon; sieveHodgeGram on all present classes: hyperbolic with exactly one positive direction (all-ones = pole), horizon N₀ independent of the sieve Q (finite sieves growing with N allowed). (#print axioms lines.)

## Conductor/CoprimeFourierOrder
- conductorPrimeSieve(m) = prime factors; density = φ(m)/m; coprime harmonic prefix ≥ (φ(m)/m)H_N. Fourier tail J = ∫_1^∞P: (2/M)J·H_N ≤ E_m(c) when Nc ≤ m; ⇒ (2/M)J(log m − log c) ≤ E_m(c). Tilted spline: uniform logarithmic conductor coercivity a(log m − log c) ≤ E_m(c) over all c, m.
- Density-weighted Abel: (φ(m)/m)Σ w_n/(n+1) ≤ Σ_{coprime} w_n/(n+1) for nonneg antitone w ⇒ E_1(c/m) ≤ E_m(c) (completed conductor dominates pole at natural overlap c/m). log m − log c + min(0, selfFinitePart(1)) ≤ E_m(c). (#print axioms lines.)

## Conductor/PositiveAbelSurplus
- coprimeHarmonicSurplus(m,N) = (m/φ(m))Σ_{coprime ≤ N}1/a − H_N ≥ 0, → sieveEuler(prime factors of m) − γ. E_m(c) − E_1(c/m) = Σ_n conductorSurplusBand ≥ 0 (surplus × Fourier band ∫_{(n+1)c/m}^{(n+2)c/m}P; Abel boundary → 0). Tilted spline instance. (#print axioms lines.)

## TheFiniteSieveHasOneEulerConstant
- sieveEuler(Q) = γ + Σ_{p∈Q}log p/(p−1). Deleting p: sievedHarmonic(Q∪p, N) = sievedHarmonic(Q,N) − sievedHarmonic(Q, N/p)/p. sievedHarmonic(Q,N) − δ_Q log N → δ_Q·sieveEuler(Q) (γ occurs once; correction = sum of local Euler shifts); equals Möbius sieve harmonic constant.

## TheFiniteSieveHasTheMertensConstant
- Λ supported on one prime ⇒ deleting p removes exactly its geometric Mertens tail. sievedMertensSum(Q,N) − log N → −sieveEuler(Q): harmonic and Mertens constants are the same Euler constant with opposite signs.

## TheFiniteSieveHasTheTowerFinitePart
- On supported orders the prime kernel = Σ_{p∈Q} ladderKernel_p (transverse towers; AIT). Class mass affine law sieveClassMass(d,M) ≈ classDensity(d)(log M − log d + sieveEuler). Ordered mixed entry = Λ(e/d)·mass(e) if d|e (one prime power). Diagonal finite part −2sieveEuler·density; cross /log M → p_dp_e·Λ-kernel·density.
- Normalized (density) finite-sieve Gram finite part = −2sieveEuler·I + weilPrimeKernel; with tensor polar counterterm Σ_i polar_i²/density_i, profile finite part = −2sieveEuler Σb² + Σ_p tower forms (one shared Euler constant for the whole profile).

## TheFiniteSieveUnitGramHasTwoHorizons
- sieveUnitGram(Q,A,B) = Σ_{units k≤A, l≤B}p_kp_lΛ-kernel; exact row = Σ_k(sievedMertensSum(B/k) + log k)/k (A ≤ B). Log roundoff at quotient boundary Σ(log B − log⌊B/k⌋ − log k)/k ∈ [0,2]. Uniform: |unitGram − S(A)S(B)/δ_Q + 2sieveEuler·S(A)| ≤ ηS(A) + C_η for all A ≤ B.

## ThePrimeKernelSplitsOverAFiniteSieve
- SieveSupported Q d (d | Π_Q p^r); factorization n = d·k (d supported, k coprime) unique. Nonzero Λ-interaction changes at most one factor ⇒ exact tensor sum: Λ-kernel(dk, el) = [d=e]kernel(k,l) + [k=l]kernel(d,e) (before horizon cutoff).

## TheSieveClassesHaveExactPrimeGrams
- sieveClassPole(Q,d) = pole on {n: d|n, n/d unit}; classes disjoint; class = scaled units with horizon decimated by d; mass = sievedHarmonic(M/d)/d. Pole-weighted kernel p_mp_nK(m,n) = [m|n]Λ(n/m)/n + [n|m]Λ(m/n)/m. Unit Gram = 2Σ_{units}log n/n; class diagonal = (2/d)Σ_{units ≤ M/d}log n/n; cross (d < e) = p_dp_eK(d,e)·sievedHarmonic(M/e).

## TheSieveClassesHaveExactTruncatedGrams
- Independent cutoffs A, B: same class = unitGram(A/d, B/d)/d; distinct classes couple at min(A/d, B/e); polar coordinates and Euclidean Grams by disjointness. Uniform diagonal Euler remainder over supported orders and both cutoffs ≤ ηH_{min(A,B)} + C.

## TheSievedLogarithmHasTheSameQuadraticDivergence
- sievedLogarithmicHarmonic Σ_{units}log n/n; deletion shift identity. 2·sievedLogHarmonic − δ_Q log²N = o(log N): deleting primes changes density only, no linear log N term (decimated log shift cancels log p).
