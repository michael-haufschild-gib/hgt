# AdelicKreinGeometry — facts log

## Haar/PeriodDefects (uses BiarithmeticGeometry Affine.IsotropicTranslations, HeckeKreinToeplitz Index.NilpotentSubspaces)
- Setting: Hermitian kernel k on the rational affine group AffineGroupQ (x ↦ ax + b), kernel column span with left-regular representation and pairing; negIndex k = number of negative squares.
- translationPeriodDefect(q) = column(translation(q+1)) − column(translation q); translates to defect at b + q; span is translation-invariant.
- If k is 1-periodic on translations (k(b+1) = k(b)), all period defects are mutually isotropic and orthogonal to every translation column. Finite index r ⇒ period space finite with dim ≤ r; translation differences (T_b − 1)^r vanish on it.
- Integer Haar successor (HasIntegerSuccessor: k on translations depends only on whether b ∈ ℤ) ⇒ 1-periodic on translations.
- Affine period space = span of the affine orbit of one defect; contains translation period space. Conjugation g·translation(b) = translation(b/slope g)·... transfers the nilpotence exponent r to every affine defect.
- On the affine defect space, fixing translation 1 ⇒ fixed by every rational translation (fixed by ℤ, unipotent of exponent r, b·den = num ⇒ periodic unipotent is fixed).
- Affine defects are orthogonal to translation-fixed column vectors. Fixed kernel of T_1 − 1 on defect space is isotropic ⇒ dim ≤ r; nilpotent of order r ⇒ dim(affine period space) ≤ r². Holds for every integer Haar successor of finite index r.

## TheIndexOfAnInducedState (uses HeckeKreinToeplitz FiniteIndexIsPositiveMinusFiniteRank, HyperbolicPairsAndTheIndexFormula; ArithmeticPositiveDuality TheIntegerSuccessorForcesTheHeckeWeight)
- IsPosDefKernel (Krein–Toeplitz) ⇔ IsPosDefOnGroup (APD); Gram form of a Hermitian kernel is real.
- Pullback along a surjective homomorphism keeps negIndex. Any extension φ of ψ from H ≤ G has negIndex ψ ≤ negIndex φ. Blind extension ψ ∘ r along a retraction r : G →* H has index exactly κ(ψ) (index-minimal).
- Orthogonal translates: if g_j x are mutually k-orthogonal for j ∈ J, then |J|·hermNegIndex(gram k x) ≤ negIndex k (block-diagonal Gram).
- Regular extension (extension by zero off H) is Hermitian; Gram form splits into one Gram form of ψ per coset. Induction formula: κ(ext₀ψ) = [G : H]·κ(ψ) (ENat; finite index: ≤ via rank decomposition per coset, ≥ via witnesses per coset). Infinite index subgroup and κ(ψ) ≠ 0 ⇒ κ(ext₀ψ) = ∞. Contrast: in positive theory extension by zero preserves positivity.

## TheWitnessComplementIsPositive
- Witness family: finite x with hermNegIndex(gram k x) = negIndex k (exists when finite).
- Cross terms vanish on x ⊔ y when y-coefficients are k-orthogonal to x; witness complement positive: c orthogonal to every witness point ⇒ hermQuad(gram k y) c ≥ 0 (else an (m+1)-dim negative subspace).
- Escape: if every pair of finite families can be separated by a translate t (k(x_a⁻¹ t y_b) = 0), finite index ⇒ index 0; hence κ ∈ {0, ∞}. Non-commutative form of AKL's axis zero-or-infinity law; engine of all zero-or-infinity laws here.

## HeckeSupportedStatesHaveIndexZeroOrInfinity (uses APD TheCriticalLineOfTheIntegerSuccessorIsTheKakutaniWall)
- IsHeckeSupported φ on Aff(ℚ): φ(ax + b) ≠ 0 ⇒ den(a)·b ∈ ℤ. Hecke states (nd)^{−s}1[db ∈ ℤ] and Haar state are Hecke-supported.
- Large prime denominator P not dividing d, den α, den β ⇒ d(β + 1/P)/α ∉ ℤ. Arithmetic escape: translation by 1/P (P > all denominators) separates any two finite families for every Hecke-supported φ.
- Affine zero-or-infinity law: Hermitian Hecke-supported φ has κ ∈ {0, ∞}; finite index ⇒ positive definite.
- Slope weight |num|·den symmetric under inversion; Hecke states Hermitian at every exponent. Kakutani wall is an index wall: κ(heckeState s) = 0 for s ≥ ½, ∞ for s < ½.

## ThePontryaginExtensionsOfWeilsCorrelation (uses HKT TheFiniteIndexStratumOfZetaIsLindelofDeep, RHTower WeilPhiDoobPrimeAtoms)
- Weil's correlation ratCorr(r) = W(B(· + log r), B) of the cubic spline on positive rational dilations equals zetaKernel on the Hecke lattice (posUnits → HeckeLattice surjective); Hermitian; κ(ratCorr) = κ(K_ζ) = number of zeros right of the line.
- Every affine extension of ratCorr has κ ≥ κ(K_ζ). Blind extension φ(ax+b) = ratCorr(|a|) (pullback along slopeAbs retraction) has κ exactly κ(K_ζ); its successor is constant splineCorr 0.
- Dilation subgroup has infinitely many cosets (integer translations distinct). Regular extension (zero off dilations): κ = 0 under RH, ∞ otherwise.
- Hecke-supported Hermitian extension of finite index ⇒ positive ⇒ RH (via APD riemannHypothesis_iff_exists_affine_posDef); off RH every Hecke-supported extension has κ = ∞.
- Unconditional: Hecke-supported Hermitian extension with Weil's dilation part and successor c·1_ℤ (c ≠ 0), or integer successor, has κ = ∞ (finite ⇒ positive ⇒ successor blind, splineCorr_zero_of_integer_successor). Finite-index carrier with visible successor must leave Hecke support.

## MixingKillsNegativeSquares (uses HKT BoundedIndexIsClosedUnderPointwiseLimits)
- Block additivity: hermNegIndex A + hermNegIndex B ≤ hermNegIndex(fromBlocks A 0 0 B).
- Approximate escape: if every pair of finite families admits translates t_j with k(x_a⁻¹ t_j y_b) → 0, finite index ⇒ 0 (Gram on x ⊔ t_j y converges to block diagonal; lower semicontinuity of index).
- Mixing: one sequence t_j with k(g t_j h) → 0 for all g, h ⇒ κ ∈ {0, ∞}. On ℤ and on ℚ-translations: Hermitian kernels vanishing at +∞ have κ ∈ {0, ∞} (decaying additive carriers cannot hold finite nonzero index).
- slopeHeight(g) = |num a|·den a, submultiplicative. Height decay on Aff(ℚ) ⇒ κ ∈ {0, ∞} (escape along doublings x ↦ 2^j x, 2^j ≤ C·height). Hecke states decay for s > 0 ⇒ second (mixing) proof of index wall κ = ∞ for 0 < s < ½.
- Finite nonzero index needs a non-decaying carrier: over ℚ the archimedean place (orbit kernels continuous in log a).

## TheSignatureOfASeparableAssembly (uses HKT TheSelectiveIndexOfTheAtomicKernelIsOneSquare, ALG TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity)
- Matrix tools: negative-definite linear image inside V gives that many negative squares in V; nonneg form on V ⇒ negIndexOn = 0; vector H-orthogonal to a maximal negative subspace of V has nonneg form. Subadditivity on a hyperplane: hermNegIndex(Σ A_p) ≤ 1 + Σ negIndexOn(A_p, ker φ).
- polarIndex(k) = sup of negative squares on mean-zero coefficient vectors (kernel of total mass); polarIndex ≤ negIndex ≤ polarIndex + 1.
- Separable assembly K(g) = Σ_p k_p(g_p) on Π H_p (finite S). Gram is the sum of local Grams. Signature formula: Σ_p κ₀(k_p) ≤ κ(K) ≤ Σ_p κ₀(k_p) + 1 (lower: polar negative subspaces on axis families are K-orthogonal since mean-zero blocks kill constants and single-block terms; upper: total mass + κ₀ functionals per p). Gluing term ≤ one square along shared constant (pole) direction; local constant counterterms change only the gluing square.
- −|m| on ℤ: on mean-zero vectors −|z_b − z_a| = 2min(w_a, w_b) − w_a − w_b, min kernel = Σ_t |Σ_{w_a > t} c_a|² ⇒ conditionally positive, polarIndex 0.
- negLogHeight −Σ_p a_p|m_p| (a ≥ 0, some a_q > 0) has exactly one negative square (points 1, e_q give negative square; upper bound by signature formula). With a_p = log p: −log(nd) on S-units = index-one Pontryagin state glued by the pole.

## ConformalSymmetryNeedsANegativeSquare (uses HTGeometry InertiaScalingSwap)
- Positive states have no conformal symmetry: φ∘α = cφ for endomorphism α, c ≠ 1, positive definite ⇒ φ(1) = 0 ⇒ φ ≡ 0. No positive successor on ℚ-translations with a dilation acting by factor ≠ 1.
- Conformal successors φ(ub) = |u|^s φ(b), s ≠ 0 ⇒ φ(b) = |b|^s φ(1) (φ(0) = 0).
- −|b| on ℚ: Gram = (1/D)·Gram of −|m| on ℤ after scaling; conditionally positive, polarIndex 0, κ(−|b|) = 1. −|m| strictly conditionally positive on distinct integers (tail sums determine c). |b| negative definite on the polar hyperplane of distinct points (dim n − 1) ⇒ κ(|b|) = ∞. Positive scalar multiples keep index.
- Exponent-one conformal successors c|b|: κ = 0 (c = 0), 1 (c < 0), ∞ (c > 0). Conformal factor of dilation by u is archimedean |u|: over ℤ the conformal part of Frobenius sits on the additive side carried by one negative square; multiplicative side carries the boost.

## TheIndexIsTwinBlind
- Unitary character χ: χ(g⁻¹) = conj χ(g); twist k·χ is congruence by diag(χ(x_a)) ⇒ κ(k·χ) = κ(k).
- On Aff(ℚ): slope characters keep index, Hecke support, height decay; every twin of a Hecke state has the same wall at s = ½. Index calculus (induction, escape, mixing, wall) cannot separate ζ from twins; selectivity must enter through dilation data (Weil's correlation with pole and Gamma). Affine form of AKL LocalityIsTwinBlind.

## TheAdelicProductState
- Hermitian kernel positive definite ⇔ all Gram matrices PSD; Schur product of positive-definite kernels is positive definite (Hadamard).
- Haar state Hermitian, positive definite, Hecke-supported; φ·haarState is Hecke-supported ⇒ κ ∈ {0, ∞} for every Hermitian φ.
- adelicWeilState = ratCorr(|a|)·haarState: κ ∈ {0, ∞}, 0 under RH; successor W(B,B)·1_ℤ; dilation part ratCorr(r)·(nd)^{−1/2} (not Weil's correlation). Product of the two readings never has finite nonzero index; finite stratum needs finite-adelic factor outside Hecke support (haarOneNegativeSquare).

## NoFixedCountertermMakesThePrimeKernelPontryagin (uses RAPT TheArchimedeanPlacePaysTheTowerDeficit; HKT LogarithmicCharactersAndTheArithmeticIndexFormula, TheMarginIsTheWidthOfTheIndexOneWindow)
- primeLatticeKernel P on Hecke lattice ℚ_{>0}: Λ(u)u^{−1/2} on prime powers and inverses, read on reduced num/den (= weilPrimeKernel); Hermitian. Gram on atoms 1..N is the atomic prime form P_N.
- Escape by two new primes P ≠ Q above all numerators/denominators: t = PQ puts both into every numerator of x_a⁻¹ t y_b, which is then neither 1 nor a prime power nor inverse ⇒ D·δ₁ − P vanishes there.
- For every real D, κ(D·δ₁ − P) = ∞: escape ⇒ κ ∈ {0, ∞}; truncated pole vector n^{−1/2} on [1, N] has P_N-energy ≥ (log N − γ − 1)·mass > D·mass for large N. Matched local Hodge index survives only with running counterterm log N − γ; no Pontryagin limit at any fixed renormalization.

## ArchimedeanContinuityAgainstHeightDecay (part 1)
- q ≠ 1 rational ⇒ den(q)·|q − 1| ≥ 1. Double-sum bound ‖Σ c̄ E c‖ ≤ B(Σ‖c‖)².
- Near coincidence: F continuous at 1 on posUnits, ψ → 0 with denominator, ψ(1) = a > 0 ⇒ κ(F − ψ) = ∞ (points (K+i)/K: ratios within n/K of 1 with denominators ≥ N; on polar hyperplane Gram ≈ −a·I up to 2ε ⇒ L negative squares for every L).

## ArchimedeanContinuityAgainstHeightDecay (part 2)
- Large prime P not dividing d, den α, e ⇒ d(e/P)/α ∉ ℤ. Spread family: translates x ↦ x + j/P (j < P) of dilations u_k.
- Dilution: for Hermitian slope state s and Hecke-supported ψ, κ(s) ≤ κ(s(|a|) + ψ): on the spread family off-diagonal Hecke terms vanish, diagonal ones divided by P; Gram → gram s as P → ∞; lower semicontinuity.
- No continuous dilation part: ψ positive, Hecke-supported, integer successor ⇒ (nd)|ψ(dilation)|² ≤ 1 (decays with denominator); if s + ψ∘dilation is continuous at 1 then κ(s(|a|) + ψ) = ∞ (near coincidence + dilution). In particular when the dilation part is Weil's correlation (continuity of splineCorr(−log r) at 1). Covers every Hecke-supported state (s = 0) and Haar states corrected by an archimedean slope function (e.g. haarOneNegativeSquare must have dilation reading discontinuous at 1).

## TheAdditiveIndexLaw (Mathlib Fourier.ZMod)
- Kernel on ℤ/N: k(x) = Σ_ξ a_ξ e(xξ/N), a_ξ = N⁻¹Σ e(−xξ/N)k(x); Hermitian ⇒ a_ξ real. Gram form = Σ_ξ a_ξ|Σ_b c_b e(y_bξ/N)|².
- Additive index law: κ(k) = #{ξ : a_ξ < 0} (≤: one square per negative coefficient; ≥: dual characters of negative coefficients orthogonal, span a negative subspace on all of ℤ/N).
- Unit-invariant kernel ⇒ Fourier coefficients constant on unit orbits (conductor classes, Ramanujan modes). Additive integer invariant = count of negative conductor modes; at fixed overlap complete Weil matrix has nonnegative conductor energies.

## TheAdditiveIndexLawOnQModZ
- Successor state = 1-periodic Hermitian ψ on ℚ-translations (kernel on ℚ/ℤ). Level kernel k_N(x) = ψ(x/N) on ℤ/N has Gram matrices of ψ at x/N; κ(k_N) ≤ κ(ψ). Every finite family lives at one level (common denominator).
- Additive index law on ℚ/ℤ: κ(ψ) = sup_N #{ξ ∈ ℤ/N : a^{(N)}_ξ < 0}. Finite index ⇒ negative part of spectral measure on ℤ̂ has ≤ κ points; index zero ⇔ positive measure on ℤ̂ (Haar successor 1_ℤ).

## TheRamanujanIndexLaw
- Unit-invariant kernel on ℤ/N: every ξ is a unit multiple of N/ord(ξ); a_ξ = A_{ord ξ}, A_d = a_{N/d}; conductor class of d | N has φ(d) elements.
- Ramanujan index law: κ(k) = Σ_{d | N, A_d < 0} φ(d).
- On ℚ/ℤ, conductor-invariant periodic successor (ψ(mb) = ψ(b) for m coprime to den b): level kernels unit-invariant; κ(ψ) = sup_N Σ_{d | N, A_d^{(N)} < 0} φ(d). Finite index ⇒ negative Ramanujan coefficients only at finitely many conductors with Σφ(d) ≤ κ.

## StableConformalSuccessors (uses AKL LocalConstituentsMeetOnlyAtTheIdentity; Mathlib improper integrals)
- Subordination I_s(t) = ∫_0^∞ (1 − e^{−rt}) r^{−1−s} dr integrable for 0 < s < 1, t ≥ 0; I_s(t) = t^s I_s(1), I_s(1) > 0; |m|^s = I_s(|m|)/I_s(1).
- −|m|^s conditionally positive on ℤ (0 < s < 1): on mean-zero vectors form = I_s(1)⁻¹∫ r^{−1−s}·(Poisson Gram e^{−r|m|}) dr ≥ 0. κ(−|m|^s) = 1. Dilations act with conformal factor |u|^s. At s = ½ the factor |u|^{1/2} is the normalization making Hecke translations isometric boosts; boost scalar on the additive side carried by one negative square.

## TheFunctionFieldConformalSuccessor (Mathlib polynomial degree)
- Equivalence kernels 1[f(a) = f(b)] are positive (sum of squares of class sums).
- On K[X]: |p|_∞ = b^{deg p}; multiplication by X conformal with factor b. Ultrametric decomposition |p − p'|_∞ = Σ_{k ≤ D} w_k 1[p, p' differ in degrees ≥ k], w_0 = 1, w_k = b^k − b^{k−1} ≥ 0 (b ≥ 1).
- −|·|_∞ conditionally positive (each level an equivalence kernel; mass-zero kills the constant), κ = 1. Over F_q the conformal successor is quantized (uniformizer at ∞ factor q) and has the same index-one state as over ℚ; conformal mechanism does not distinguish ℤ from F_q[T], except that over F_q the factor is the size of a single place.

## TheAffineGroupOfAField (Mathlib)
- AffineGroupOf K = K ≃ᵃ[K] K; slopeOf, shiftOf; g x = a x + b; slope multiplicative, shift(gh) = slope g·shift h + shift g; shift(g⁻¹h) = slope(g)⁻¹(shift h − shift g); translations a homomorphic image of (K, +); dilations from Kˣ. Over ℚ agrees with APD AffineGroupQ.

## ThePoleIsAKreinStateOfTheAffineGroup (uses APD AContinuousArchimedeanSpectrumIsSeenByTheSuccessor)
- Positive-slope affine maps = Borel of SL(2, ℝ); form h(x, y) = i(x̄₀y₁ − x̄₁y₀) of signature (1,1). poleState(ax + b) = a^{1/2} + a^{−1/2} − i b a^{−1/2}; coefficient identity poleState(g⁻¹h) = h(w_g, w_h), w_g = (a^{1/2} − i b a^{−1/2}, −i a^{−1/2}).
- Gram = Wᴴ·krein2·W; h ≥ 0 on line x₀ = i x₁ ⇒ ≤ 1 negative square; dilation by 4 gives 2 − 2·(5/2) < 0 ⇒ κ(poleState) = 1.
- On dilations: u^{1/2} + u^{−1/2} (pole pair, boost of pole plane in Hecke normalization); on translations: 2 − ib; dilation by u multiplies successor part by conformal factor u. The pole is an index-one Pontryagin state of the whole affine group with nontrivial successor — the hyperbolic pair through which successor and dilations meet.

## TheHeckeBoostAndTheConformalSuccessorAreOneState
- Place v of field K; IsConformal v s ψ: ψ(ub) = |u|_v^s ψ(b); positive exponent and nontrivial v ⇒ ψ(0) = 0. Points of ℙ¹(K) carry k_t, k_∞ with [k_s, k_t] = ψ(t − s), [k_∞, k_t] = 1, [k_∞, k_∞] = 0; dilations act as boosts with eigenvalues |a|^{∓s/2}.
- Conformal induction Φ_ψ(ax + b) = |a|_v^{−s/2}ψ(b): Gram form = form of ψ at the shifts with weights w_g|a_g|^{−s/2}; κ(Φ_ψ) = κ(ψ).
- Pole–successor state |a|^{s/2} + |a|^{−s/2} + |a|^{−s/2}ψ(b): Gram form = 2Re(X̄Y) (X = Σ w|a|^{−s/2}, Y = Σ w|a|^{s/2}) + form of ψ with total mass X. Conditionally positive conformal ψ, nontrivial v ⇒ κ = 1 (nonneg on ker X; dilation with |u|^{s/2} > 1 gives a negative square).
- On dilations: boost pair |u|^{s/2} + |u|^{−s/2}; on translations: 2 + ψ(b). Real place: −c|b| (s = 1, c ≥ 0) gives Hecke pole–successor state |a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b| of index 1 (pole pair of Weil's kernel + archimedean successor); −c|b|^s, 0 < s < 1, also index 1 (−|b|^s conditionally positive on ℚ by integral rescaling). Boost exponent = half conformal exponent (dil_u ∘ trans_b ∘ dil_u⁻¹ = trans_{ub}).

## EveryPlaceCarriesAPoleSuccessorState (Mathlib Ostrowski)
- Ultrametric v: balls are additive subgroups ⇒ ball kernels 1[|x − y|_v ≤ r] positive. Layer cake R − t = ∫_0^R 1[t ≤ r] dr ⇒ −|b|_v conditionally positive (integral of ball forms); conformal of exponent 1.
- Nontrivial ultrametric v ⇒ local pole–successor state has κ = 1. p-adic: |a|_p^{1/2} + |a|_p^{−1/2} − c|a|_p^{−1/2}|b|_p has κ = 1; conformal induction −|a|_p^{−1/2}|b|_p has κ = 1.
- F(X) at ∞: |f|_∞ = b^{intDegree f} is an ultrametric absolute value, |X|_∞ = b; pole–successor state has κ = 1 and dilation by X is the boost b^{1/2} + b^{−1/2} (over F_q: Frobenius eigenvalues 1, q on H⁰, H² after twist q^{−1/2}).
- Every place of ℚ carries its own index-one state (local signature 1); product formula ∏|a|_v = 1 ⇒ local boosts multiply to 1 on ℚ^×: pole pairs live place by place, their product is not a boost.

## Haar/OneNegativeSquare (uses APD AMautnerPhenomenonForTheAffineGroupOfQ)
- affineLogTwo(g) = log|a|/log 2 (additive in g, odd under inverse, 0 on translations). haarOneNegativeSquare = haarState − 4·affineLogTwo²: keeps the integer successor; Hermitian.
- Completion: adding |Σ c·2(1 + L²)|² gives Haar form + |Σ 2c|² + 2|Σ c·2L|² + |Σ c·2L²|² (from −4(y−x)² + 4(1+x²)(1+y²) = 4 + 8xy + 4x²y²) ⇒ κ ≤ 1; dilation by 2 violates |φ(g)| ≤ φ(1) ⇒ κ = 1.
- Not Hecke-supported (finite nonzero index). No dilation reading continuous at 1 (would make the Haar reading continuous, contradicting positive Mautner rigidity for its nonconstant integer successor).

## Haar/IndexPreservation (uses HKT BoundedIndexIsClosedUnderPointwiseLimits, HTGeometry ReductionPencilKPositivity)
- Prime-denominator translation escape for Hecke-supported kernels; arbitrarily many mutually Haar-orthogonal translates of any finite family.
- Weighted (block-averaged) Gram compression; PSD matrix with constant diagonal δ has entries ≤ δ.
- For positive p with integer successor and Hermitian ψ on ℚˣ: κ(p + ψ∘slopeUnit) = κ(ψ) (≤: adding a positive kernel; ≥: average over N Haar-orthogonal translates of dilations ⇒ positive part has diagonal 1/N, entries ≤ 1/N → 0; slope Gram unchanged; lower semicontinuity). Haar + slope kernel keeps index (finite or infinite).

## Haar/ContinuousDilationsNeedInfiniteIndex
- height(u)·|u − 1| ≥ 1 for u ≠ 1; positive p with integer successor ⇒ |p(D_u)|² ≤ |u − 1| (u ≠ 1); dilations tending to 1 have p(D_u) → 0.
- Constant matrix minus identity is negative definite on zero-sum hyperplane (n negative squares in dim n+1).
- If p(dilation u) + ψ(u) = f(u) with f continuous at 1: slope Grams at near-identity units 1 + i/(N+1) converge to (ψ(1)+1)J − I ⇒ κ(ψ) = ∞ ⇒ κ(p + ψ∘slope) = ∞. Weil's correlation (splineCorr(−log r) continuous at 1) cannot be the dilation reading of a finite-index positive integer-successor carrier with slope correction — no Hecke support assumed.

## Haar/MixedPolynomialPerturbation (uses HKT FiniteIndexIsPositiveMinusFiniteRank, BoundedIndexIsClosedUnderPointwiseLimits)
- mixedQuadraticKernel K(ax + b) = i(1 − a⁻²)b²: vanishes on translations and dilations; Hermitian; K(g⁻¹h) = i(a_g⁻² − a_h⁻²)(b_h − b_g)². Three feature squares complete it to six positive squares ⇒ κ ≤ 3; six-point Gram (3 translations at slopes 1 and 2) has explicit negative 3-dim subspace (congruence to −3/2·I) ⇒ κ(K) = 3.
- haarMixedQuadraticState = Haar + K: same translation (integer successor) and dilation readings as Haar; κ = 3 (≤ by adding positive; ≥ by dilation conjugation scaling K by u² while Haar stays bounded, rescale by 1/u², lower semicontinuity).
- Imaginary part at slope 2 equals (3/4)b², unbounded ⇒ not (positive affine kernel + slope kernel). Finite-index Haar carriers exist outside the "positive + slope" class.

## Haar/AxisInvisibility (uses HKT Index.NullKernelRigidity; APD TheExtremalsOfTheHeckeLawAreTwistedHaarStates)
- Hermitian affine kernel vanishing on translations and dilations with κ ≤ 1 is zero (zero set is a subgroup at index ≤ 1; axes generate Aff(ℚ)). Nonzero such kernel has κ ≥ 2.

## Haar/FiniteRankPerturbations (uses HKT Index.NullSubgroupRank)
- Zero-axis Hermitian affine kernel with κ ≤ r: column space finite of dim ≤ r²; every Gram matrix has rank ≤ r² (translation subgroup = ker slopeUnit normal, g = translation·dilation).

## Haar/PolynomialPerturbations (uses HKT Index.SubgroupColumns, BiarithmeticGeometry Affine.PolynomialCoefficients, APD ArchimedeanEigenvectorsAreInvisibleToTranslations, HTGeometry ConstitutiveNilpotentSocleLaw)
- Nonzero zero-axis Hermitian affine kernel with κ ≤ r: on every translation fibre b ↦ k(translation b · dilation u) is a polynomial of degree < r (translation columns span dim ≤ r; unipotent rational action; unipotent power polynomial).

## Haar/PowerKernels (uses HKT Index.HyperbolicFeatures, Index.RescalingInvariance)
- mixedPowerKernel_d,γ(ax + b) = γ(1 − a^{−d})b^d: zero on both axes (d > 0); quotient γ(a_g^{−d} − a_h^{−d})(b_h − b_g)^d; with conj γ·(−1)^d = −γ it is a sum of d+1 hyperbolic feature pairs ⇒ Hermitian, κ ≤ d + 1.
- Translation-degree law sharpens: fibre at slope 2 is γ(1 − 2^{−d})b^d of degree d < κ ⇒ κ = d + 1 exactly (d > 0, γ ≠ 0).
- Dilation conjugation scales by u^d; rescaling invariance ⇒ any positive-definite addition keeps κ = d + 1. Canonical phase (i for even d, 1 for odd d). haarMixedPowerState_d = Haar + kernel keeps both Haar axis readings and integer successor with κ = d + 1: every index ≥ 2 realized by Haar carriers with Haar axis readings (index 1 by haarOneNegativeSquare, which changes the dilation reading).

## ThePoleSuccessorSignatureFormula
- poleSuccessor(g⁻¹h) formula; Hermitian for Hermitian conformal ψ; slopePow multiplicative.
- Upper bound κ(Φ) ≤ κ₀(ψ) + 1 (on boost-mass hyperplane X = 0 the form is ψ's polar form at weights w|a|^{−s/2}).
- Lower bound: polar negative subspace of ψ on translations and boost pair on dilations u^N, u^{N+1} decouple as N → ∞ (cross terms ~ |u|^{−(N+e)s/2}·const after compression; mass-zero kills the boost-pair part); lower semicontinuity ⇒ κ₀ + 1 ≤ κ.
- Signature formula κ(Φ) = κ₀(ψ) + 1 for conformal Hermitian ψ, s > 0, nontrivial v: one local constituent glued to the pole, gluing ε = 1 exactly.
- c|b| (c > 0) negative definite on every polar hyperplane ⇒ κ₀ = ∞. Real-place trichotomy: |a|^{1/2} + |a|^{−1/2} − c|a|^{−1/2}|b| has κ = 1 for c ≥ 0, ∞ for c < 0.
