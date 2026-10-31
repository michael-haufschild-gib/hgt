# 32 ArithmeticIntersectionTheory — mathematical facts log

## TheProjectionFormulaAndTheRegulatorAnomaly
- Power map [t]: z ↦ z^t is the Hecke correspondence of the circle; fibre over z^t is μ_t·z; ∏_{ω∈μ_t}(z − ωw) = z^t − w^t.
- Projection formula: Σ_{ω∈μ_t} log|z − ωw| = log|z^t − w^t| (z^t ≠ w^t).
- circleKernel k_r(z,w) = −log|1 − r z w̄|. Regularized projection: Σ_{ω∈μ_t} k_r(ωz, w) = k_{r^t}(z^t, w^t) on the closed disc. cycleEnergy of pullback at radius r = t·cycleEnergy of images at radius r^t.
- Regulator anomaly: log(1 − r^t) − log(1 − r) → log t as r → 1⁻; renormalized pullback energy − t·renormalized image energy → −t log t·Σx_i² (anomaly log t per point = log #ker[t] = Σ_{ω≠1}log|1−ω|).

## TheDifferentOfATorsionOrbit
- log is a derivation of Dirichlet convolution: (f⋆g)·log = (f·log)⋆g + f⋆(g·log). φ⋆1 = id; μ⋆(id·log) = φ·log + φ⋆Λ; kLogKernel n = φ(n)log n + Σ_{d|n}φ(n/d)Λ(d).
- tameDifferent n = Σ_{p|n} log p/(p−1) (additive on coprime; = log p/(p−1) at prime powers). (φ⋆Λ)(n) = φ(n)·tameDifferent(n).
- selfIntersection n = I(n,n)/φ(n) = log n − tameDifferent n = Σ_{p^a∥n}(a − 1/(p−1))log p (different of ℚ(ζ_n) per unit degree, place by place) ≥ 0.

## TheHeckeCocycleOfRenormalization
- heckeCocycle β(n,t) = c(tn) − c(n) = log t − Σ_{p|t, p∤n} log p/(p−1). Cocycle identity β(n,st) = β(n,s) + β(sn,t); 0 ≤ c(t) ≤ β(n,t) ≤ log t; saturated (primes of t divide n) ⇒ β = log t; tameDifferent(tn) = tameDifferent(n) then.
- c(2^k) = (k−1)log 2; β is not the coboundary of any bounded potential (no bounded diagonal change makes the renormalized torsion form Hecke covariant).
- weilPrimeKernel P(tm,tn) = P(m,n) (Hecke invariant). torsionForm Q_r(x) = Σ x_m x_n twistedEnergy r m n; renormalized limit −Σx_m x_n P(m,n) − Σ x_n² c(n) (AET). Hecke variation: Q_r(T_t x) − Q_r(x) → −Σ x_n² β(n,t); on saturated cycles → −log t·Σx_n² (covariance up to degree character).

## TheArchimedeanIntersectionIsALogOrder
- cyclotomicValue n m = Φ_m(ζ_n) ∈ 𝓞(ℚ(ζ_n)); under each complex embedding σ: σ(Φ_m(ζ_n)) = ∏_{ξ∈O_m}(σζ_n − ξ).
- For m ≠ n: log #(𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n))) = Σ_{η∈O_n,ξ∈O_m} log|η − ξ| = I(n,m) (absolute norm = product over embeddings). Archimedean intersection = log-order of a finite ring (product formula for torsion divisors).
- Λ(n) = log #(𝓞_{ℚ(ζ_n)}/(ζ_n − 1)) for n ≥ 2. Diagonal: I(p^k,p^k) = log|disc ℚ(ζ_{p^k})| (adjunction: self-intersection = canonical degree).

## TheTowerFormOfAPrime
- Ladder c, cp, …, cp^{N−1}: P(cp^i, cp^j) = log p·p^{−|i−j|/2} off diagonal, 0 on it. kmsForm K_q(x) = Σ x_i x_j q^{|i−j|} (Kac–Murdock–Szegő), q = p^{−1/2}. ladderForm = log p·(K_q(x) − |x|²).
- Tails T_k = Σ_{i≥k} x_i q^{i−k}, x_k = T_k − qT_{k+1}: K_q(x) = T_0² + (1−q²)Σ_{k≥1}T_k²; for q = p^{−1/2}: K_q(x) = Σ_k φ(p^k)(Σ_{i≥k} x_i p^{−i/2})² (levels weighted by orbit sizes).
- K_q ≥ 0 for q² ≤ 1; (1−q)|x|² ≤ (1+q)K_q(x), (1−q)K_q(x) ≤ (1+q)|x|² for 0 ≤ q ≤ 1. Ladder bounds: −(2q/(1+q))log p|x|² ≤ ladderForm ≤ (2q/(1−q))log p|x|² (indefiniteness on one ladder = identity subtracted from a positive form).

## ThePrimeKernelIsASumOfTransverseTowers
- p-ladders: m ~_p n iff ordCompl[p] m = ordCompl[p] n. Transversality: distinct orders share ladders for at most one prime (exponent lattice ⊕_p ℕ has independent coordinates).
- ladderKernel L_p(m,n) = log p·q^{|v_p m − v_p n|} on distinct same-ladder pairs (q = p^{−1/2}). P(m,n) = Σ_{p|mn} L_p(m,n) with exactly one prime per nonzero entry; L_p = log p·(K_p − 1) ⊗ 1 on ℓ²(⊕ ℕ).
- primeForm Σ_{m,n∈S} x_m x_n P(m,n) = Σ_p localForm Q_p(x); Q_p = log p·(towerOnSet − |x|²); towerOnSet decomposes into interval KMS forms per ladder. Local Hodge index: −2q log p|x|² ≤ (1+q)Q_p(x), (1−q)Q_p(x) ≤ 2q log p|x|². Sum of local bounds Σ_p 2log p/(√p ± 1) diverges.

## GaussDigammaIsTheFourierTransformOfTheTorsionEnergy
- rootAngle θ_a = 2πa/N; Σ_a cos(mθ_a) = N[N|m]; Σ_a cos(jθ)cos(kθ) = (N/2)([N|j+k] + [N|j+N−k]).
- torsionFourier r N k = Σ_{a<N} −log|1 − rζ^a| cos(kθ_a) = ½(r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}((N−k)/N)), latticeGerm G_s(z) = Σ_m s^m/(m+z) (RenormalizedBiarithmeticGeometry).
- gauss_digamma_theorem (0 < k < N): Σ_{0<a<N} log|1 − ζ_N^a| cos(2πak/N) = log N + γ + ½(ψ(k/N) + ψ(1 − k/N)) (renormalized germ limit; log N = regulator anomaly of [N]; (1−r^m)log(1−r) → 0).

## TheLocalFormsDoNotSum
- P ≥ 0; P(m, mt) = Λ(t)/√t. poleVector x_n = n^{−1/2}; Σ_{n≤N} x_n² = H_N. On orders 1..M²: primeForm(poleVector) ≥ H_M·Σ_{t≤M}Λ(t)/t (pairs (m, mt), m ≤ M, 2 ≤ t ≤ M).
- not_exists_primeForm_le: no C with primeForm ≤ C|x|² for all cycles (ratio ~ log M by Mertens second theorem; H_{M²} ≤ 1 + 2log M). Local boundedness at each prime does not survive summation; growth must be paid by the archimedean place.

## TheFiniteIntersectionIsGaugeBlind
- IsSignGauge ε: completely multiplicative on positive integers, ε² = 1. signTwistKernel P^ε(m,n) = ε(n/m)Λ(n/m)(n/m)^{−1/2} = ε(m)ε(n)P(m,n). Twisted form at x = primeForm at εx; |εx| = |x|; twins share spectrum, local bounds, unboundedness. Liouville λ = (−1)^Ω is a sign gauge.
- No statement about the finite intersection pairing alone separates ζ from sign twins; selectivity must come from the pole term (Σx_n√n)(Σx_n/√n) and the archimedean place.

## TheEllipticCorrespondencesOfTheCircle
- Rotations R_ζ: z ↦ ζz (|ζ| = 1) preserve the Abel kernel exactly (no anomaly). Baumslag–Solitar: [t]∘R_ζ = R_{ζ^t}∘[t].
- Point cycles Σx_a δ_{e^{iθ_a}}: energy = Σ_{j≥1}(r^j/j)(C_j² + S_j²) (archimedean Hodge index; all frequencies nonnegative weight).
- On μ_N: rootMode periodic mod N; rootCycleEnergy = (−log(1−r^N)/N)·mode₀ + Σ_{0<k<N}(r^k/N)G_{r^N}(k/N)·mode_k; eigenvalues ≥ 0; renormalized eigenvalues −(ψ(k/N) + γ + log N)/N (archimedean factor at rationals). Rotations localize in k/N ∈ ℚ/ℤ — the zeros of ζ do not appear; they enter only through Hecke gluing of levels.

## WeilsPrimeFunctionalIsTheFiniteIntersection
- logAtomTest f = Σ_{n∈S} x_n φ(u − log n), φ ∈ C² supported in [−δ/2, δ/2], S ⊆ [1,M], δ < log(1 + 1/M) (LogAtomData). Separation: |log k − (log m − log n)| < log(1+1/M) ⇒ kn = m. Autocorrelation at log k = ‖φ‖²Σ x_m x_n[kn = m].
- primeSum A = Σ_k Λ(k)k^{−1/2}(A(log k) + A(−log k)); per pair Σ_k Λ(k)/√k([kn=m] + [km=n]) = P(m,n). primeSum(logAtomAutocorr) = ‖φ‖²·primeForm = ‖φ‖²Σ_p Q_p(x).
- W = archPolarPart − prime part (literatureRHS). Under RH (conditional statement, RH as hypothesis): ‖φ‖²Σ_p Q_p(x) ≤ Re archPolarPart(f⋆f̃) for every log-atom cycle (Hodge index in tower form).

## ZeroMomentsAreRosatiPairings
- reflectPoint ρ* = 1 − ρ̄ (involution; fixed ⇔ Re = ½). Q(s) = Σ b_n n^{−(s−½)}, Q̃(s) = Σ b_n n^{s−½}, b real: Q̃(ρ) = conj Q(ρ*). On the line (QQ̃)(ρ) = |Q(ρ)|². rosatiProduct z_ρ = Q(ρ)conj Q(ρ*); z_{ρ*} = conj z_ρ; pair contributes 2Re z_ρ^k (either sign).
- Reflection-closed configuration: k-th moment is real; critical configuration ⇒ moment = sum of squares (Re ≥ 0). Zero moments are Rosati (reflection) pairings, not collided.

## TheSpacingRegulatorRemovesTheAnomaly
- spacingRadius ρ_mρ_n = e^{−ε(1/m + 1/n)} (radius scaled with spacing 2π/n). spacingEnergy Gram positive: Σ y_m y_n T_{ρ_mρ_n}(m,n) = Σ_k (1/k)|Σ y_m ρ_m^k c_m(k)|² (Ramanujan sums). spacingForm (with gcd twist) ≥ 0 for every ε > 0.
- log(1 − e^{−u}) − log u → 0. Diagonal: twistedEnergy(ρ_n²,n,n) + log(2ε) → tameDifferent n = e(n). spacingForm + log(2ε)|x|² → spacingLimit = −primeForm + Σ x_n² e(n) (scalar counterterm log(1/(2ε)) per unit mass).
- Transport under [t]: limit changes by Σ x_n²(e(tn) − e(n)) (tame ramification only; anomaly log t removed); invariant on saturated cycles.
- spacingLimit_not_nonneg: on {1,2}, x = (1,1): (1 − √2)log 2 < 0 (P(1,2) = log2/√2, e(2) = log 2). Covariance restored, sign lost (scalar counterterm has trivial null cone).

## TheSelfIntersectionDominatesTheTower
- c(cp^j) ≥ (j − 1/(p−1))log p for j ≥ 1 (p-part of the different). On a ladder, cycles vanishing at levels 0,1: (1+q)(−ladderForm − Σx_j²c(cp^j)) ≤ −(1−q)log p|x|² ⇒ renormalized torsion form negative definite above level 2; positive index ≤ 2 per ladder (arithmetic Δ² < 0).

## ThePolarPartPairsThePoleDirection
- ∫φ(u−c)e^{su} = e^{sc}∫φe^{sv}. f̂(i/2) = α Σx_n n^{−1/2}, f̂(−i/2) = β Σx_n n^{1/2} (α = ∫φe^{−u/2}, β = ∫φe^{u/2}). Polar part (weilPoleTerm) = 2αβ(Σx_n n^{−1/2})(Σx_n n^{1/2}) (rank two: pole direction n^{−1/2} vs dual n^{1/2}).
- archPolarPart = pole term + gammaPart. Under RH (hypothesis) on the polar hyperplane Σx_n n^{−1/2} = 0: ‖φ‖²Σ_p Q_p(x) ≤ Re gammaPart.

## TheSquareRootPriceOfSeparateTowers
- localForm Q_p ≤ (2log p/(√p − 1))|x|²; 2/(√p−1) ≤ 7/√p; Σ_{n≤M}Λ(n)/√n ≤ 34√M ⇒ primeForm ≤ 238√M|x|² on orders ≤ M. Separate towers cost √M; Schur with n^{−1/2} jointly gives 2log M + O(1). Summing local Hodge indices in absolute value is the square-root threshold (weight ½ vs 0).

## TheHodgeIndexInTowerCoordinates
- jumpWeight e^{y/2}/sinh y; atomSelfEnergy E_φ = γ₀Φ(0) + ∫₀^∞(Φ(0) − Φ(y))jump; archKernel K_φ(c) = ∫₀^∞ Φ(y−c)jump (Φ = autocorr φ, vanishes for |z| > δ).
- Log-atom autocorrelation h(y) = Σ x_m x_n Φ(y + log m − log n); h(0) = Φ(0)|x|²; for y > 0 only m < n pairs (separation).
- weilArchRe_logAtom: Re(arch + polar) = E_φ|x|² + 2αβ(Σx_n n^{−1/2})(Σx_n n^{1/2}) − Σ_{m<n} x_m x_n K_φ(log(n/m)) (from exact archimedean form A(h) = γ₀h(0) + ∫₀^∞[(h(0)−h(y))jump + 4h(y)cosh(y/2)]).
- atomSelfEnergy_ge: 0 < δ, 2δ < 1: E_φ ≥ ‖φ‖²(γ₀ + e^{−1/2}log((1−δ)/δ)).
- Under RH (hypothesis): ‖φ‖²Σ_pQ_p(x) + Σ_{m<n}x_m x_n K_φ(log(n/m)) ≤ E_φ|x|² + 2αβ(Σx_n n^{−1/2})(Σx_n n^{1/2}) (Hodge index in tower coordinates; RH-conditional implication, not proved unconditionally).

## TheBaseAndTheSuccessor
- Over ℤ: ladder kernels of distinct primes never charge the same pair (L_p·L_ℓ = 0). Over 𝔽_q: frobeniusTower (degree-d place charges lags divisible by d, weight q^{−lag/2}); places of degrees d, d' both charge lag lcm(d,d') (overlap on one Frobenius ladder = common base).
- Successor transverse: n, n+1 on a common p-ladder ⇔ n = 1, p = 2. Additive information invisible to each local tower (Catalan edge 3 → 4 joins 3-ladder and 2-ladder).

## TheTorsionFormHasPolynomiallyManyPositiveSquares
- torsionBilinear (symmetric bilinear of renormalizedTorsionForm R(x) = −P(x) − Σx_n²c(n)). armVector (anti-pole) v_q = δ_q − Σ_{p∈A}δ_{qp}/(2√p), base prime q ≤ B, arms primes p > B (Windows).
- R(v_q) = Σ_{p∈A} log p/p − c(q) − Σ_p c(qp)/(4p) ≥ ½Σ_{p∈A} log p/p − log q (c(n) ≤ log n; log(qp) ≤ 2log p). Distinct anti-poles R-orthogonal (no Hecke edge between supports, disjoint diagonals).
- renormalizedTorsionForm_pos_on_span: M ≥ 3, N ≥ (Q₀M)^5 (Q₀ = ⌈e^{2c₁+1}⌉, c₁ Mertens constant): R positive definite on span of ≥ M/log M anti-poles (bases primes in (M, Q₀M] via Chebyshev; arms primes in (Q₀M, N/(Q₀M)] via Mertens) ⇒ positive index on [1,N] ≥ cN^{1/5}/log N. No finite-rank counterterm renormalizes all boxes.

## ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths
- Ground-state identity (RenormalizedArithmeticPotentialTheory): P_N + D_N = Σ(A(⌊N/n⌋) + log n)x_n², A(y) = Σ_{t≤y}Λ(t)/t, D_N pole defect. Edge bound (a−b)² ≤ (3/2)a² + 3b² ⇒ D_N ≤ (3/2)Σ log n x² + 3ΣA x².
- Diagonal domination: R_N(x) ≤ Σ_n(2A(⌊N/n⌋) + d(n) − ½log n)x_n² (d = tame different). Positive index ≤ #{n ≤ N : 2A(N/n) + d(n) > ½log n} (restriction injective).
- d(n) ≤ 2log K + 2log4 + 2log n/K (split primes ≤ K / > K; log p/(p−1) ≤ 2log p/p; Mertens upper). eventually_finrank_le_rpow: positive index ≤ N^{4/5+ε} (rows beat ½log n only for n ≲ N^{4/5}). Split θ = ½ optimal.
- So positive index of the renormalized torsion form on [1,N] lies between N^{1/5−o(1)} and N^{4/5+ε}.
