# 49 CompletedArithmeticForms — facts log

## CyclotomicCoercivity (uses CACT AllDivisorConductorsRecoverTheDiscreteBridge, BVI ArithmeticLargeSieveForSquarefreeModuli)
- prefixPacket Q a ζ = Σ_{1≤i<Q} a_i·primitivePrefixValue ζ i (= Σ_{j<i} ζ^j); divisorGramEnergy Q a = Σ_{m|Q, m≠1} Σ_{i,j} a_i a_j primitivePrefixGram m i j = Σ_{m|Q,m≠1}Σ_{ζ prim m}|prefixPacket|² = full discrete bridge form Σ a_i a_j (Q·min(i,j) − ij).
- (1 − ζ)·prefixPacket = Σa_i − Σa_i ζ^i; Parseval over all Q-th roots: Σ_{ζ≠1}|(1−ζ)P(ζ)|² = Q((Σa)² + Σa²).
- |1−ζ|² + |1+ζ|² = 4 on the unit circle ⇒ divisorGramEnergy_completion: 4·E = Q((Σa)² + Σa²) + cyclotomicRemainder, remainder = Σ|(1+ζ)P(ζ)|² ≥ 0. Coercive; E = 0 ⇔ a = 0 on [1, Q); positive iff some interior coefficient nonzero (completing all divisor conductors removes the cyclotomic radical).

## DirichletSchurCost
- bridgeKernel Q i j = Q·min(i,j) − ij is the Green kernel of the Dirichlet second difference: Δ²_D K(·, j)(i) = Q·δ_ij for 0 < i; K vanishes at 0 and Q. Potential recovers coefficients: Δ(bridgePotential a)(i) = Q a_i. Inverse on zero-boundary functions; uniqueness from endpoints + interior second difference.
- Finite Green identity keeps both endpoint edges: Σ b_i Δb_i = dirichletEnergy Q b = Σ_{i<Q}(b_{i+1} − b_i)² for b(0) = b(Q) = 0.
- bridgeInverse Q b = Δ(zero-extension of b)/Q; bridgeSchurCost Q b = dirichletEnergy(extension)/Q. Exact completion: E(a) − 2⟨a,b⟩ + cost(b) = E(a − bridgeInverse b). So 2⟨a,b⟩ − E(a) ≤ cost(b), equality iff a = bridgeInverse b; cost attained (IsGreatest). Mixed coupling paid by local variation (incl. boundary jumps), not absolute row size.

## DivisorCovariance (uses RHTower EulerDeletionAveragedDivisorCovariance)
- divisorGramEnergy(T+1, c_j/j) = (T+1)·cumulativeEnergy c T (accumulation covariance is the normalized divisor-conductor completion).
- 4·cumulativeEnergy = (Σc_j/j)² + Σ(c_j/j)² + remainder/(T+1): coercive. Schur bound: 2Σc_j b_j − cumEnergy ≤ dirichletEnergy(T+1, ext(j·b_j)).
- Euler-deletion: fullErrorEnergy X M = finite cyclotomic Gram/(T+1) + tail Σ(1 − modular)²/((i+T+1)(i+T+2)); tail ≤ (M+1)²/(T+1); every finite weighted increment packet ≤ 4·fullErrorEnergy; truncation error in [0, (M+1)²/(T+1)].

## FinitePackets
- packetCoefficient s k a r = Σ_{i: k(i)=r} a_i (fibre sums at equal arithmetic index). Pairing preserved; injective k preserves square mass. Bridge form on packets Σ a_i a_j K(k_i, k_j) = divisorGramEnergy(packetCoefficient).
- Radical = exactly the equal-index cancellations; with injective k: Q((Σa)² + Σa²) ≤ 4·Σ a_i a_j K(k_i,k_j) (coefficient reserve survives irregular spacing). Schur: 2Σ a_i b(k_i) − bridge/Q ≤ dirichletEnergy(Q, ext b).

## PrimePacketSchur (uses BVI BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo)
- Prime block P < p ≤ 2P, packet with zero mass and zero log moment: normalized completed conductor energy (Q = 2P+2) ≤ primePacketBilinear (actual energy-centered prime form; Brownian-bridge law). Hence Σ a_p² ≤ 4·primePacketBilinear and 2Σ a_p b(p) − primePacketBilinear ≤ dirichletEnergy(2P+2, ext b) — all prime cross terms retained.

## IrregularGreen
- Increasing nodes k with k(0) = 0: meshSlope, meshDifference (difference of adjacent slopes), meshDirichletEnergy = Σ(b_{i+1}−b_i)²/(k_{i+1}−k_i), meshKernel = min(k_i,k_j) − k_i k_j/k_N (Green kernel: unit source under mesh difference; vanishes at both ends).
- Inverse on zero-boundary domain; Green identity keeps boundary slopes; meshGram = completed Gram on selected nodes /k_N; nonneg; zero iff coefficients zero.
- meshSchur_completion: meshGram(a) − 2⟨a,b⟩ + meshDirichletEnergy(b) = meshGram(a − meshDifference b); cost attained (IsGreatest) — reciprocal-gap weighting incl. boundary gaps.
- Min gap δ ⇒ meshDirichletEnergy ≤ (4/δ)Σb² ⇒ meshGram ≥ (δ/4)Σa² (spacing strengthens the reserve).

## WeilPrefixIndex (uses TMWP APositivePrefixGivesTheExactSchurReduction, TransMetzlerYoungOptimization)
- HorizonTail M N has N − M elements. If x vanishes on the tail, complete quadratic form = prefix block form.
- Tail restriction is injective on every strictly negative subspace when the prefix block is PosDef ⇒ dim(negative subspace) ≤ N − M. Eventually in M: for all N ≥ M, c with cM ≤ N, every negative subspace of completeWeilMatrix has dimension ≤ N − M (upper index bound, mixed entries kept; not positivity).
- Every fixed prefix ratio d ∈ [1, transMetzlerCertifiedBoundary) with cM = dN: negative subspace dim ≤ N − M. At overlap 3/2, length 3K: negative directions ≤ K (one third of the horizon). Grows with horizon; no positivity claim.

## GammaSuccessorReserve (uses HTGeometry PoleUnitGammaBase, GammaShiftCasoratian, BinomialNodeDeterminant, HankelSuccessorSchurStrict)
- gammaShapeMoment r n = (r)_n (ascending Pochhammer); additive: (r)_{i+j} = (r)_i (r+i)_j. Vandermonde at consecutive integers = Π i! (falling factorial basis).
- det of Gamma moment Hankel head of size N = Π_{i<N} i!·(r)_i (no positivity premise).
- scaledGammaMoment g w r n = g w^n (r)_n: Hankel = g·D_w H D_w; det = Π g w^{2i} i! (r)_i; PosDef for g, w, r > 0. Successor Schur complement = g w^{2N} N! (r)_N; relative to new diagonal: N!/(r+N)_N (mass and scale cancel).
- For r ≥ ½: N!/(r+N)_N ≤ (2/3)^N — even the positive Gamma model loses an exponential fraction of each new diagonal.

## NativeTailReserve (uses RHTower ThetaCusp ThetaCuspAllRankNativeTail)
- nativeBalancedMoment s x k = thetaCuspNativeScaledEvenJet(k+s) x (actual native signed moments). → scaledGammaMoment(gaussianMoment s, 16, s + ½) k as x → ∞; gaussianMoment(k+s) = that model.
- Every fixed Hankel head eventually PosDef; relative bounds ½G ≺ head ≺ (3/2)G. nativeBalancedSuccessor N s x → nativeGammaReserve N s = gaussianMoment s·16^{2N}·N!·(s+½)_N > 0; eventually within [½, 3/2]× of it (threshold depends on N, s).
- Relative successor/new diagonal → N!/(s+½+N)_N ≤ 2(2/3)^N eventually; no uniform positive diagonal fraction over rank (not_native_rank_uniform_relative_reserve).

## SeparatedPacketReserve
- Nonadjacent zero-boundary support: dirichletEnergy = 2Σb² exactly. Distinct nonadjacent indices: Σa² ≤ 2·(bridge/Q) (doubles the reserve). Odd prime blocks (P ≥ 2, primes in (P, 2P] are odd hence nonadjacent): Σa_p² ≤ 2·primePacketBilinear (half reserve, vs 1/4 generally).

## SignedParityTransfer (uses HTGeometry FiniteMatrixOrthogonalSum, HankelSuccessorSchurStrict; RHTower ThetaCusp CenterMixedAllOrderIntegration)
- evenMomentSequence m: interleave even moments with odd zeros. Parity permutation of Fin N = Fin ⌈N/2⌉ ⊕ Fin ⌊N/2⌋ splits the full Hankel head into the unshifted and once-shifted even heads (orthogonal sum): det = product; PosDef ⇔ both blocks PosDef; PSD likewise.
- thetaCuspNativeSignedJet = evenMomentSequence((−1)^k·reflection jet 2k). Every fixed full signed Hankel head of the native source is eventually PosDef.

## FirstAtomRankBoundary (uses RHTower ThetaCusp ThetaCuspFirstAtomScaleSevenProfiles; HTGeometry SampledSmallComplex, GammaVerticalPolynomialDecay)
- firstAtomComplexPair x z: entire continuation of the reflected first theta atom pair θ₁(x+t)θ₁(x−t) = 4q² e^{x−2q} exp(−2q(cosh 2z − 1))·((2q−3)² − 12q(cosh 2z − 1)), q = single-atom reflection scale. Jets at 0 = first-atom reflection jets. Rotated z ↦ iz: even Taylor jets are the signed moments (−1)^k J_{2k}; on the real axis it is periodic (cos 2y).
- Entire function with nonnegative real jets is nondecreasing on [0, ∞). Rotated pair at π/2 vs π: value at π/2 strictly larger (e^{4q}((2q−3)²+24q) > (2q−3)²) ⇒ exists_firstAtom_signed_moment_neg: at every center x some signed moment (−1)^k J_{2k}(x) < 0. No common ray with all signed moments ≥ 0. Some finite signed Hankel head is not PSD (negative diagonal).
- But each fixed raw signed moment is eventually > 0, each fixed shifted (balanced) head eventually PosDef (→ scaled Gamma model), full signed heads eventually PosDef. firstAtomNegativeOrder x (least negative order) and firstAtomFailureRank x (least non-PSD full head) are finite everywhere, failureRank ≤ negativeOrder + 1, and both → ∞ as x → ∞. Remainder cannot be discarded uniformly over orders at one center.

## FirstAtomEffectiveRankBoundary (uses HTGeometry ApproximateMultipointSchwarz, BesselOrderIntegral)
- Cauchy tail: entire f with |f| ≤ M on |w| = r, |z| ≤ ρ < r: Taylor tail from J ≤ M(ρ/r)^J/(1−ρ/r). Nonnegative first J jets ⇒ f(u) − f(v) ≤ 2M(v/r)^J/(1 − v/r) for 0 ≤ u ≤ v < r.
- Period-circle bound on |z| = 2π: firstAtomPeriodCircleBound = 4q²e^{x−2q}e^{2q(H+1)}((2q−3)² + 12q(H+1)), H = e^{4π}. Period decrease ≥ 24q·4q²e^{x−2q}.
- 2^{2·negOrder} ≤ e^{2q(H+1)}((2q−3)²+12q(H+1))/(6q); for x ≥ 0 (q > 3): negativeOrder ≤ firstAtomRankScaleConstant·q, constant = (9e^{4π}+2)/(2 log 2); failureRank ≤ 1 + const·q. Obstruction rank grows at most linearly in the physical first-atom scale.

## OptimalInterpolation
- meshInterpolation N k b = (k_N)⁻¹·bridgePotential of packet(meshDifference b): restricts to the mesh potential at nodes, takes values b_i at k_i, zero at both ends; its Dirichlet energy on [0, k_N] = meshDirichletEnergy (dirichletEnergy of normalized bridge potential = E/Q).
- meshDirichletEnergy_isLeast_extension: among all zero-boundary extensions u with u(k_i) = b_i, the minimum Dirichlet energy is exactly the reciprocal-gap energy, attained. Restriction/extension preserve the dual cost.
- primePacket_mesh_schur_bound: neutral prime packet pays a prescribed coupling at prime nodes by meshDirichletEnergy N k b.

## NeutralPacketDual
- meshDirichletPair (mixed reciprocal-gap variation), mixed Green summation = Σ b_i·meshDifference c_i for zero-boundary b. Zero-energy profile pairs to zero; zero-boundary mesh energy has no radical.
- meshDualProjection: b − (⟨b,g⟩/E(g))g; energy drops by exactly ⟨b,g⟩²/E(g); orthogonal even for degenerate g. Single-constraint dual cost attained: sup over a ⊥ g of 2⟨a,b⟩ − meshGram(a) = E(projection).
- Double projection (two constraints, no independence assumption): exact energy formula, orthogonal to both, attained joint dual cost; energy zero iff b ∈ span(g, h) on interior.
- meshPrimeNeutralProjection: constraints = mass profile 1 and log profile log k_i. primePacket_neutral_mesh_schur_bound: mass- and log-neutral prime packet pays a coupling by its mass/log-quotient Green norm (≤ unprojected).

## FirstAtomGaussianHorizon (uses RHTower XiCTaylorThetaTailFiniteTranslationBounds)
- |cosh w − 1 − w²/2| ≤ |w|⁴/24·e^{|w|}. firstAtomGaussianKernel q w = exp(−2q(cosh w − 1))(1 − (12q/(2q−3)²)(cosh w − 1)); for q ≥ 3, |w|² ≤ 4/q: |kernel − e^{−qw²}| ≤ D/q, D = firstAtomGaussianErrorConstant = e^{4+2e²}(24 + 10e²) (≥ 24).
- Mass θ₁(x)² = 4q²e^{x−2q}(2q−3)². Normalized rotated pair (z ↦ z/√q, divided by mass) = kernel at 2iz/√q; on |z| ≤ 1: |· − e^{4z²}| ≤ D/q. Even jets of normalized pair = scaled signed moments; even jets of e^{4z²} = gaussianMoment k = 4^k(2k)!/k!.
- Cauchy on unit circle: |scaledEvenJet_k − gaussianMoment_k| ≤ (2k)!·D/q (all orders, one estimate).
- D·k! < q ⇒ k-th signed moment > 0; so negativeOrder > K once D·K! < q. firstAtomGaussianHorizon K = max(0, log((D·K!+1)/π)/2): x ≥ horizon ⇒ negativeOrder > K (q = πe^{2x}). Simultaneous in center and order; mixed-head positivity separate.

## InverseTraceStability (uses HTGeometry PositiveDefiniteMatrixLimit)
- PosDef G: v_i² ≤ (G⁻¹)_ii·⟨v, Gv⟩ (inverse diagonal = dual cost of a coordinate); ⟨v,v⟩ ≤ tr(G⁻¹)⟨v,Gv⟩.
- Entrywise |A − G| ≤ ε ⇒ |⟨v,(A−G)v⟩| ≤ N ε tr(G⁻¹)⟨v,Gv⟩; if N ε tr(G⁻¹) < ½ then A − ½G PosDef.

## FirstAtomMixedHorizon
- gaussianShiftedHead N s = Hankel of gaussianMoment(k+s) = scaled Gamma model (PosDef; det = Π gaussianMoment s·16^{2i} i! (s+½)_i). gaussianInverseTrace = tr of inverse = adjugate trace/det.
- firstAtomMixedErrorNumerator N s = N·tr(G⁻¹)·(2(s+2N))!·D. Relative error of balanced first-atom head vs Gaussian head ≤ numerator/q × Gaussian form.
- 2·numerator < q ⇒ balanced head − ½G PosDef ⇒ balanced head PosDef ⇒ literal shifted head PosDef (diagonal congruence by f q^i, scale q^s).
- firstAtomMixedScale N = 3 + 2(num(⌈N/2⌉, 0) + num(⌊N/2⌋, 1)); q ≥ it ⇒ full signed head of size N PosDef ⇒ failureRank > N. firstAtomMixedHorizon N = max(0, log(scale/π)/2): explicit center horizon for every rank.

## NativeGaussianHorizon
- nativeGaussianErrorNumerator L = (2L)!·D + 27·24^{2L}·(e^{3π}/399)·(L+1)!. Likelihood weight q^L·regimeOneLikelihood ≤ (e^{3π}/399)(L+1)!/q.
- Infinite theta remainder (native − first atom) through order L: ≤ 27·24^{2L}(e^{3π}/399)(L+1)!/q when q ≥ 2L + 6. Native scaled even jet vs Gaussian moment ≤ numerator(L)/q.
- nativeMixedErrorNumerator N s = N·tr(G⁻¹)·numerator(s+2N); half-relative PosDef and literal nativeShiftedMatrix PosDef when 2·num < q (+ domain). nativeMixedScale N = (2(N+1)+6) + 2(num(⌈N/2⌉,0) + num(⌊N/2⌋,1)); nativeSignedHead_posDef_of_scale / of_horizon: explicit simultaneous rank–center positivity of the untruncated native theta source's full signed Hankel head.

## HyperbolicClock
- Clock u = arsinh(t/√q): firstAtomGaussianClockProfile x t = θ₁(x+u)θ₁(x−u) = A e^{−4t²}(S − 24t²) exactly (A = 4q²e^{x−2q}, S = (2q−3)²); pullback t = √q sinh u recovers the physical source.
- Profile = A((S−3)·g − (3/8)g''), g = e^{−4t²}. Signed even jets: (−1)^k ∂^{2k}(0) = A((S−3)γ_k + (3/8)γ_{k+1}) = A γ_k (S + 6k) (γ_{k+1} = 8(2k+1)γ_k). Odd jets vanish.
- Shifted clocked heads = A((S−3)G_s + (3/8)G_{s+1}) (adjacent Gamma heads): PosDef for S ≥ 3; full signed heads PosDef at every rank. For x ≥ 0 (q > 3) S ≥ 9 ⇒ one center has a positive all-rank cone in the clock coordinate, while the physical pullback has a finite failing head (firstAtomGaussianClock_positive_pullback_fails): nonlinear coordinate changes do not preserve the full signed Hankel cone.

## SuccessorComparison
- Subtracting t at the terminal moment 2N lowers the successor Schur complement by exactly t (head unchanged). successorSchur_mono: heads PosDef and (H_m − H_n) PSD at size N+1 ⇒ Schur(n) ≤ Schur(m) (successors of either sign). Scaling: Schur(c·m) = c·Schur(m). Relative sandwich αG ≼ H_m ≼ βG ⇒ αSchur(g) ≤ Schur(m) ≤ βSchur(g); full-form relative error ε < 1 ⇒ |Schur(m) − Schur(g)| ≤ ε·Schur(g) (no extra inverse loss).

## NativeSuccessorHorizon
- Shifted Gaussian successor = nativeGammaReserve N s. Native successor error ≤ (nativeMixedErrorNumerator(N+1, s)/q)·reserve. nativeSuccessorScale N s = (2(s+2(N+1))+6) + 2·num(N+1, s); q ≥ it ⇒ reserve/2 < native successor < 3·reserve/2. nativeSuccessorHorizon: explicit center horizon for each rank and shift, including the infinite theta remainder.

## SeamCoercivity (uses RHTower ThetaCusp ThetaCuspCenterTailSeamGram)
- Polynomial moments ∫x^k ∂^j Θ_full: vanish for j > k, = (−1)^k k!·∫Θ_full ≠ 0 for j = k ⇒ finite derivative packets Σ v_j ∂^jΘ_full ≡ 0 only if v = 0 (also complex). Packets bounded and integrable; ∫|packet|² > 0 for c ≠ 0.
- nativeTailHead N r = Hankel of native signed jet tails beyond r. At r = 0 it is the seam Gram (= ∫|packet|² with c_j = v_j 2^j i^j) ⇒ PosDef at every rank (zero radical).
- Moving tail endpoint by r costs ≤ r·decay constant per entry; relative error ≤ r·nativeSeamErrorRate N (= N·envelope·tr(H₀⁻¹)); radius 1/(2(1+rate)) keeps half the seam form. Tail head = ∫_{s>r} native signed Hankel form(s/2) (mixed entries kept); r ≥ 2·nativeMixedHorizon N ⇒ tail head PosDef.

## GaussianClockCone (uses RHTower Hedenmalm HedenmalmGaussianHankelRH)
- clockGaussian e^{−y²/16}: ∫y^{n+2}g = 8(n+1)∫y^n g; even moments = mass·gaussianMoment k; odd = 0.
- affineGammaMoment a b k = a γ_k + b γ_{k+1}; represented (odd-zero interleaving) by the bounded density (a + by²)e^{−y²/32} against the Gaussian window measure. Density ≥ 0 ⇔ a, b ≥ 0. Complete Hankel cone (Hedenmalm's characterization for measures with entire exponential moments) ⇔ density ≥ 0 ⇒ affineGamma_completeHankelCone_iff: all heads PSD ⇔ a ≥ 0 ∧ b ≥ 0; all heads PosDef ⇔ additionally a + b > 0.
- Clock signed jets = A·affineGamma(S − 3, 3/8): all heads PSD ⇔ S ≥ 3 ⇔ all heads PosDef. Every individual signed clock moment is ≥ 0 at every center (A γ_k(S + 6k)), yet for S < 3 some finite mixed head fails: positive individual moments do not give mixed positivity.

## ScaleJetTransport (uses RHTower ThetaCusp ThetaCuspGaussianScaleOperator)
- sourceScalePartial / sourceReflectionPartial on smooth F(q, t) commute (symmetric second derivative); every reflection jet commutes with scale differentiation.
- Gaussian scale equation −∂_t² G = 8qG + (16q² − 4q)∂_qG − 4q²∂_q²G ⇒ gaussianScaleSignedJet (k+1) = 8q·J_k + (16q² − 4q)J_k' − 4q²J_k'' (J_0 = 1), at every order and scale.
- Affine first-atom source = A(S·G(q,t) + 6q·∂_qG(q,t)) ⇒ signed first-atom moment (−1)^k J_{2k}(x) = A(S·J_k(q) + 6q·J_k'(q)) exactly.

## GaussianScalePolynomial
- positiveGaussianScalePolynomial P_k: P_0 = 1, P_{k+1} = 8X P_k + 16X·E(P_k) + 4E²(P_k), E = X·d/dX. Coefficients: c_{k+1, j+1} = 8(2j+1)c_{k,j} + 4(j+1)²c_{k,j+1}; nonneg; degree ≤ k; top coefficient = gaussianMoment k.
- Physical signed Gaussian jet J_k(q) = (−1)^k P_k(−q) (reflection of the positive envelope). First-atom signed moment = A(−1)^k·firstAtomScalePolynomial(S, k)(−q), coefficients (S + 6j)c_{k,j} ≥ 0, top (S+6k)γ_k.
- One-step bound P_{k+1}(q) ≤ (8q(2k+1) + 4k²)P_k(q). Removing the top coefficient: |(−1)^k P(−q) − c_k q^k| ≤ P(q) − c_k q^k. So |signed moment − A(S+6k)γ_k q^k| ≤ A(S+6k)(P_k(q) − γ_k q^k).

## FirstAtomPolynomialHorizon
- k² ≤ q ⇒ (8q − k(k−1))P_k(q) ≤ 8qγ_k q^k ⇒ 7P_k(q) ≤ 8γ_k q^k and 7q(P_k(q) − γ_k q^k) ≤ k²γ_k q^k.
- Signed moment ≥ (6/7)A(S+6k)γ_k q^k > 0 when q ≥ 3 and k² ≤ q ⇒ firstAtomNegativeOrder > K whenever K² ≤ q; √q < negativeOrder. Scaled even jet: |J̃_k − γ_k(1 + 6k/S)| ≤ (1 + 6k/S)(k²/(7q))γ_k; |J̃_k − γ_k| ≤ 3k²γ_k/q (quadratic, not factorial, order cost). firstAtomPolynomialHorizon K = max(0, log((3+K²)/π)/2).
- Combined with FirstAtomEffectiveRankBoundary: √q < negativeOrder ≤ const·q.

## WeightedInverseStability
- varianceInverseCost G = Σ_i G_ii(G⁻¹)_ii (≥ N). PSD: |G_ij| ≤ √G_ii √G_jj. Entry errors relative to variances |E_ij| ≤ ε√G_ii√G_jj ⇒ |⟨v,Ev⟩| ≤ N ε·varianceInverseCost·⟨v,Gv⟩; same for |A − G| ≤ ε|G| entrywise. Cofactor formula Σ G_ii adj_ii/det.

## NativePolynomialHorizon
- γ_k ≥ 8^k k!; 72^k ≤ e^{8k}; 24^{2k}q^k e^{−q} ≤ 72^k γ_k. nativePolynomialTailConstant = 27e^{3π}/399.
- Infinite theta remainder relative: |native − first atom| ≤ const·γ_k/q when q ≥ 2k+6 and q ≥ 8k. Combined: |native scaled jet − γ_k| ≤ (3k² + const)γ_k/q when also k² ≤ q. nativePolynomialOrderScale L = max(L², 8L, 2L+6) controls all orders ≤ L.

## NativeVarianceHorizon
- gaussianVarianceInverseCost N s (≥ N, cofactor formula). nativePolynomialMixedErrorNumerator N s = N·varianceCost·(3(s+2N)² + const): relative mixed error of native balanced head ≤ num/q × Gaussian form; 2num < q ⇒ half-Gamma PosDef; native successor error ≤ (num(N+1,s)/q)·reserve; nativePolynomialSuccessorScale/Horizon give the half-Gamma successor bounds (polynomial in order instead of factorial).

## GaussianRelativeKernel
- Reflection coordinate u = 2iz/√q; relative exponent −2q(cosh u − 1) − 4z² = −2q(cosh u − 1 − u²/2) (quartic remainder). gaussianRelativeProfile = e^{−4z²}·kernel = exp(relExp)(1 − affine).
- firstAtomWickKernel x z w = e^{−4z²−4w²}·normalized pair(z+w) = e^{8zw}·relProfile(z+w) (mixed Gaussian exponential exact). |cosh w − 1| ≤ e|w|² on unit disk.
- For q ≥ 3, R ≥ 1, 4R² ≤ q, R⁴ ≤ q, |z| ≤ R: |relProfile − 1| ≤ C_rel R⁴/q, C_rel = 50e·e^{2e}; Wick kernel error ≤ C_rel R⁴/q · e^{8|z||w|}.

## WickCauchyPayment
- firstComplexJet / mixedKernelJet F i j = ∂_w^j ∂_z^i F(0,0) (orders separate). Gaussian kernel e^{8zw}: mixed jet = δ_ij 8^i i! (Hermite factorial diagonal). Two-radius Cauchy: |mixed jet| ≤ i! j! M/(r^i s^j) when |F| ≤ M on |z| = r, |w| = s.
- firstAtomWickError = Wick kernel − e^{8zw}; mixed jet ≤ i! j!·(C_rel R⁴/q·e^{8rs})/(r^i s^j) for r + s ≤ R (radii matched separately to the two Hermite degrees).

## HermiteRadiusPayment (uses RHTower WholeAnchorHarmonicE3)
- hermiteContourRadius n = √((n+1)/8); hermiteGaussianNormSq n = 8^n n!; weight² = n!/(n+1)^n. Exact: n!/r_n^n = weight·√(8^n n!). n! ≤ e(n+1)(n+1)^n e^{−n} ⇒ weight² ≤ e(n+1)e^{−n}. 16 r_i r_j ≤ i + j + 2 ⇒ pair weight w_i w_j e^{8 r_i r_j} has square ≤ e⁴(i+1)(j+1) ⇒ ≤ e²(N+1) for i, j ≤ N (linear rank payment). r_i + r_j ≤ √(N+2).

## HermiteJetCongruence
- wickAmplitude e^{−4z²}; hermiteJetCoefficient n k = C(n,k)·∂^{n−k}g(0) (monic Hermite coefficients, |·| ≤ n!e⁴). wickSourceKernel F (z,w) = e^{−4w²}F(z+w)e^{−4z²}; for the first atom it is the Wick kernel; for e^{4z²} it is e^{8zw}.
- Mixed jet of Wick kernel = Σ_{a≤i, b≤j} h_{ia}h_{jb} F^{(a+b)}(0) — exact double coefficient identity. hermiteJetMatrix lower-triangular, det 1 (invertible). realWickJetMatrix = H·(moment Hankel of F)·Hᵀ (exact congruence; all cross terms kept); Gaussian comparison is diagonal diag(8^i i!).

## HermiteSourceBound
- hermiteSourceErrorNumerator N = C_rel·e²(N+1)(N+2)² (cubic). For i, j ≤ N and 4(N+2)² ≤ q: |mixed jet of first-atom Wick error| ≤ (num/q)·√(8^i i!)√(8^j j!) (adaptive radii, common disk √(N+2)).
- firstAtomHermiteError = real Wick head − hermiteGaussianHead (diag 8^i i!). Relative form error ≤ (N·num/q)·Gaussian Hermite form (quartic rank payment).

## HermiteNativeTail (uses HTGeometry SiegelIsometryVanishing)
- nativeBalancedFullMoment / firstAtomBalancedFullMoment: odd-zero interleaved scaled moments; all jets of the normalized rotated pair = first-atom balanced full moments; entire moment head of first atom = its balanced Hankel head.
- nativeHermiteHead = H·(native full Hankel)·Hᵀ. Raw tail error per moment (n ≤ 2L) ≤ const·24^{2L}q^L e^{−3q}; Hermite entry error ≤ N²(N!)²e⁸·that (coefficients |h| ≤ N!e⁴).
- n! ≤ e^{n²}, 24^{2n} ≤ e^{10n}; 16(N+2)² ≤ q ⇒ the whole tail payment ≤ const·e⁸/q (exponential source decay pays both Hermite coefficient sums on a quadratic scale).

## NativeHermiteHorizon (uses HTGeometry EvenEntireSquareFactor)
- gaussianFullHead (odd-zero interleaved Gaussian moments) PosDef; hermiteGaussianHead = H·gaussianFullHead·Hᵀ.
- nativeHermiteErrorNumerator N = hermiteSourceNum(N) + const·e⁸ (cubic); nativeHermiteFormCost N = N·num (quartic). For 16(N+2)² ≤ q: native Hermite entry error ≤ (num/q)√·√ and native Hermite form relative error ≤ cost/q.
- Since H is invertible (det 1, surjective), the same relative bound holds in the original native full Hankel form vs gaussianFullHead (no inverse-matrix penalty). 2·cost < q ⇒ native full head − ½ Gaussian full head PosDef. Polynomial (quartic) rank horizon replacing factorial ones.

## PolynomialRankHorizon
- Relative form bound survives principal restrictions with the same constant. shiftedEvenIndex (2i + s): restriction of the full odd-zero head of size M ≥ 2N + s = shifted even head N s.
- Native balanced shifted head relative error ≤ cost(2N+s)/q (quartic in rank + shift); native successor error ≤ cost(2(N+1)+s)/q·reserve. nativePolynomialRankScale M = 16(M+2)² + 2cost(M); q ≥ it ⇒ half-Gaussian reserve in every shifted direction and reserve/2 < native successor < 3reserve/2. nativePolynomialRankHorizon M = max(0, log(scale/π)/2).

## NativePhysicalRankHorizon
- Literal nativeShiftedMatrix and full native signed head PosDef once q ≥ nativePolynomialRankScale(N+1). Scale ≤ nativeRankScaleConstant·(M+2)⁴ (constant = 16 + 2C_rel e² + 2·tailconst·e⁸). nativeLogarithmicRankHorizon M = max(0, log(C/π)/2 + 2log(M+2)): center x ≥ it ⇒ full native signed head of size N PosDef (rank grows at least like e^{x/2}); same for successors.

## GaussianJetConvolution (uses RHTower XiSliceMixedClassDetection)
- gaussianMultiplierKernel h (z,w) = e^{8zw}h(z+w). Mixed jet = Σ_{r ≤ min(i,j)} C(i,r)C(j,r)8^r r!·h^{(i−r)+(j−r)}(0) (common Gaussian contraction index). First-atom Wick error = multiplier kernel of gaussianProfileError = relProfile − 1. One Cauchy radius: |∂^k error(0)| ≤ k!(C_rel R⁴/q)/R^k.

## GeometricContraction (uses HTGeometry SeparatedOffDiagonalBound, VerticalKernelDyadicSplit)
- geometricLower N ρ (lower-triangular ρ^{i−j}); geometricContraction = L Lᵀ = Σ_{r≤min(i,j)} ρ^{(i−r)+(j−r)}. Row/column sums of L ≤ (1−ρ)⁻¹; row sums of contraction ≤ (1−ρ)⁻² (dimension-free). |E_ij| ≤ B·contraction_ij w_i w_j ⇒ |⟨v,Ev⟩| ≤ B(1−ρ)⁻²Σ w_i² v_i².

## HermiteContractionPayment
- C(i,r)(i−r)!√(8^r r!) ≤ r_N^{i−r}√(8^i i!) (falling factorial ≤ (N+1)^{i−r}). With radius 4r_N: C(i,r)C(j,r)8^r r!(a+b)!/(4r_N)^{a+b} ≤ (½)^{a+b}√(8^i i!)√(8^j j!), a = i−r, b = j−r (C(a+b,a) ≤ 2^{a+b}).

## GaussianContractionBound
- gaussianContractionRadius N = 4r_N (R² = 2(N+1), R⁴ = 4(N+1)²). Bounded multiplier |h| ≤ B on |z| = R ⇒ |mixed jet| ≤ B·geometricContraction(½)_ij·√·√ (dimension-free geometric majorant).
- First-atom Hermite error entries ≤ (C_rel R⁴/q)·contraction(½)·√·√ for 16(N+2)² ≤ q. firstAtomQuadraticFormCost N = 16C_rel(N+1)²: first-atom Hermite form relative error ≤ cost/q (quadratic rank payment; (1−½)⁻² = 4).

## NativeQuadraticRank
- Hermite Gaussian norm ≥ unweighted coefficient energy (8^n n! ≥ 1). Relative form error transfers through the Hermite congruence back to the original full Hankel form vs gaussianFullHead.
- First-atom full balanced head: relative error ≤ firstAtomQuadraticFormCost/q. Transformed infinite remainder: ≤ N·const·e⁸/q (linear). nativeQuadraticFormCost N = 16C_rel(N+1)² + N·const·e⁸; native full head relative error ≤ cost/q.

## QuadraticRankHorizon
- Relative error < ½ ⇒ A − ½G PosDef. Shifted heads are restrictions of the full head ⇒ shifted native/first-atom heads relative error ≤ cost(M)/q for M ≥ 2N+s; native successor error ≤ cost(2(N+1)+s)/q·reserve.
- nativeQuadraticRankScale M = 16(M+2)² + 2·nativeQuadraticFormCost M (quadratic in M); q ≥ it ⇒ half-Gaussian reserve for native and first-atom shifted heads and reserve/2 < successor < 3reserve/2.

## PhysicalQuadraticHorizon
- Normalized (by f²q^{k+s}) shifted head PosDef ⇒ physical shifted head PosDef (diagonal congruence). On q ≥ nativeQuadraticRankScale(M), M ≥ 2N+s: literal native and first-atom shifted heads PosDef; full signed native and first-atom heads PosDef at size N when q ≥ scale(N+1) ⇒ firstAtomFailureRank > N.
- nativeQuadraticRankScale M ≤ C_q(M+2)², C_q = 16 + 32C_rel + 2·tailconst·e⁸. nativeQuadraticRankHorizon M = max(0, log(C_q/π)/2 + log(M+2)) (logarithmic in rank; rank grows like e^{x}).
- firstAtomFailureRank_sqrt_scale_lower: √(q/C_q) < failureRank + 3 (unconditional square-root lower bound). With FirstAtomEffectiveRankBoundary: √(q/C_q) − 3 < failureRank ≤ 1 + const·q.

## TailRankHorizon
- Native signed Hankel form strictly positive for every nonzero v once x ≥ nativeQuadraticRankHorizon(N+1). Tail heads PosDef for r ≥ 2·horizon. Tail difference = ∫ over (r,t] of the native form ⇒ tails strictly decreasing in Loewner order beyond the horizon; integrated successors antitone (successorSchur_mono).

## SuccessorMixture (uses RHTower ThetaCusp ThetaCuspSchurMovingMinimizerVariance)
- successorCoupling, successorMinimizer = H⁻¹·coupling; Schur = m(2N) − minimizer·coupling ≤ m(2N). Monic energy identity: (−w,1)ᵀH_{N+1}(−w,1) = Schur + (w − minimizer)ᵀH(w − minimizer); the minimizer test vector attains Schur; Schur ≤ every monic energy.
- successorSchur_add_eq: Schur(m+n) = Schur(m) + Schur(n) + mixture variance (nonnegative, = 0 iff the minimizers agree) ⇒ superadditivity.
- Native tail band moments (tail(r) − tail(t)): Schur(tail r) = Schur(band) + Schur(tail t) + variance; band head PosDef on the paid ray ⇒ integrated successor strictly decreasing beyond the quadratic rank horizon.

## WeightedCenterTail (uses RHTower ThetaCusp ThetaCuspCenterMixedSeventhRankStrict)
- nativeWeightedMoment a U k = ∫_U r sinh(ar)·native signed jet(r/2, k); center moments (critical aperture 0 ≤ a < ½) split into compact band (0, R] + tail (R, ∞). Weighted tail heads PosDef for R ≥ 2·nativeQuadraticRankHorizon(N+1) (aperture-independent); weighted tail successor > 0 for R ≥ 2·horizon(N+2).
- Center successor = band energy + tail energy at the global minimizer test vector. centerSeventhSuccessor_compact_allowance: with the strict rank-7 center head (proved elsewhere) and R ≥ 2·horizon(9): tail successor at rank 7 > 0 and band energy(test) + tail Schur ≤ center Schur at rank 7 (unconditional positive tail allowance for the next unpaid successor).

## ChebyshevCyclotomicCompletion (uses RHTower QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw, SqrtTelescopeSums)
- chebyshevCesaroIncrement j = (ψ(j−1) − (j−1))/√(j−1) (j ≥ 3); prefix sums = normalized Chebyshev Cesàro sums. chebyshevCompletedEnergy N = Σ S_n²/(n(n+1)) = divisorGram(N+1, coeff)/(N+1); 4·energy = (Σcoeff)² + Σcoeff² + cyclotomic remainder.
- Mean-square energy Σ(S_n/n)² vs completed energy: ratio in [1, 4/3]; |coeff_j| ≤ 6/√j (ψ ≤ 6x); channels ≤ 180N. So remainder ≤ 4·meanSquare and meanSquare ≤ 60N + remainder/3: every superlinear growth lives in the cyclotomic remainder.
- Exponent r ≥ 1 bounds are equivalent for mean-square energy and cyclotomic remainder. Zero strips: ξ zeros in [1/6, 5/6] ⇔ remainder ≤ C N^{5/3+ε} ∀ε; [1/4, 3/4] ⇔ remainder ≤ C N^{3/2+ε}.

## ChebyshevCyclotomicTail (uses RHTower Sieve InverseSquareTail, KuzminLandau)
- cyclotomicMode Q k = e^{2πik/Q}; order = Q/gcd(Q,k); Q ≤ order·min(k, Q−k); modes with order ≤ L are > K from both ends when KL < Q. Remainder = far (both ends > K) + near.
- |(1−ζ)P(ζ)| ≤ 24√N; |1 − ζ_k| ≥ 4min(k, Q−k)/Q; each mode ≤ 144(N+1)²N(1/k² + 1/(N+1−k)²).
- Far modes (both ends > K): energy ≤ 288N(N+1)/K (inverse-square tail Σ_{n>K}1/n² ≤ 1/K). K = ⌈√(N+1)⌉ ⇒ far ≤ 288N√(N+1) (order N^{3/2}); near set has ≤ 2K modes. So all unpaid superlinear Chebyshev energy beyond N^{3/2} sits in ≤ 2√N modes adjacent to the constant root.

## PhysicalSuccessorMass
- rescaledMoment c t m k = c t^k m(k): head = c·D_t H D_t; det scales by ∏ c t^{2i}; successor Schur scales by c t^{2N} (exact terminal-monomial payment).
- gaussianFullHead det = ∏ hermiteGaussianNormSq i; full signed Gaussian successor = hermiteGaussianNormSq N (monic Hermite norm, 8^N N!).
- On q ≥ nativeQuadraticRankScale(N+1): normalized full native successor ∈ (H_N/2, 3H_N/2). Physical native signed jet = rescaled(f², √q, normalized) ⇒ physical successor ∈ (f²q^N H_N/2, 3f²q^N H_N/2) — no inverse-head loss. nativePhysicalSuccessorFloor N x = f²q^N H_N/2, continuous, positive beyond horizon(N+1).

## WeightedSuccessorReserve
- nativeWeightedSuccessorReserve a R N = ∫_{r>R} r sinh(ar)·floor(N, r/2): integrable (dominated by terminal moment), positive for R ≥ 2·horizon(N+2). Testing every pointwise native form at the tail's own global minimizer: reserve ≤ weighted tail Schur (no inverse matrix in the allowance).
- centerSeventhSuccessor_explicit_compact_allowance: band energy(test) + explicit reserve(7) ≤ center Schur at rank 7, reserve > 0.

## TerminalCompletion
- finiteSourceEnergy c T = cumulativeEnergy c T + (Σ_{j≤T} c_j)²/(T+1) = Σ_{j,k≤T} c_j c_k / max(j,k) (full maximum-index covariance kernel; constant-prefix tail completed exactly). Increment by one coordinate: ΔE = c_{T+1}(2S_T + c_{T+1})/(T+1) (energy not monotone in T; sign set by terminal mass).
- Dual: finiteSourceDualCost b T = Dirichlet energy of i·b_i on [0,T] (terminal edge removed via constant continuation). Sharp bound 2Σc_j b_j − E(c) ≤ cost(b) − (S_T − T b_T)²/(T+1); attained (IsGreatest) by finiteSourceMaximizer = j·(local second difference of free-boundary coupling); maximizer mass = T b_T; completion identity E(c) − 2⟨c,b⟩ + cost(b) = E(c − maximizer). Covariance has trivial radical; equality iff c = maximizer.

## EulerTerminalCost (uses RHTower DeletionAveragedDivisor, DeletionCutoffAverage)
- Euler-deletion error increments: |prefix mass| ≤ M+1 (modular-source bound). |fullErrorEnergy(X,M) − finiteSourceEnergy(T)| ≤ (M+1)²/(T+1). Infinite Euler source: 2⟨err,b⟩ − fullEnergy ≤ dualCost(b,T) − mass-discrepancy²/(T+1) + (M+1)²/(T+1).

## EulerCompletionAlongGrowingSources
- eulerCompletionHorizon M δ = ⌈(M+1)²/δ⌉ gives completion error ≤ δ; schedule T = (n+1)(M+1)² gives error ≤ 1/(n+1) uniformly in X, M. Along arbitrary growing cutoffs (X_n, M_n) the completion error → 0; full energy and completed finite-source energy have the same limits.

## SourceProbeBoundary
- finiteSourceEnergy = Σ_i prefix(i+1)²/((i+1)(i+2)) over all i (literal infinite accumulation energy; carrier tail Σ 1/((i+T+1)(i+T+2)) = 1/(T+1)).
- Fixed probe b supported on [1,T], source support growing: dual cost = finiteProbeDualCost = sourceDualCost + (T b_T)² (terminal edge restored), attained at source support T+1 by a neutral (mass-zero) maximizer; stable for K ≥ T+1. Probe and source truncation agree iff T b_T = 0.

## WeilPrefixPayment (uses TransMetzlerWeilPositivity APositivePrefixGivesTheExactSchurReduction)
- Coercivity |v|² ≤ C·vᵀAv ⇒ bᵀA⁻¹b ≤ C|b|² (inverse inherits cost).
- Trans-Metzler profile complete Weil adjunction energy > 1/20 ⇒ eventually in M, for all N ≥ M, c > 0 with cM ≤ N: |v|² ≤ 20·vᵀ(plateau prefix block)v; prefix inverse quadratic ∈ [0, 20|b|²] (dimension-, horizon- and overlap-uniform).
- Schur: tail − 20|mixed·y|² ≤ yᵀ(prefix Schur)y ≤ tail (retains signed prime/Gamma/polar mixed block).

## BesselSpectralBand (uses HTGeometry BesselOrderPolyaRealZeros)
- Schläfli energy flux of K_ν(x) → 0 as x → ∞. At imaginary order ν = iτ, flux derivative density (x − τ²/x)|K|² + x|K'|² ≥ 0 when |τ| ≤ x, > 0 if |τ| < x and K ≠ 0.
- K_{iτ}(a) ≠ 0 for |τ| ≤ a (a zero gives flux 0 at a, then strictly positive increasing integral contradicting decay). Every zero in ν of K_ν(a) has Re ν = 0 and |Im ν| > a (nonoscillatory band is zero-free). K_{iτ}(a) is real and > 0 on |τ| ≤ a (IVT + eventual positivity).

## BesselBarrierPayment
- K_ν(x) → 0. Barrier flux = e^{−x}((1 + (ν+1)/x)K_ν − K_{ν+1}) = e^{−x}(K' + (1 + 1/x)K) (Wronskian against e^{−x}/x); derivative −e^{−x}(1/x + (1−ν²)/x²)K_ν; at ν = iτ real negative multiple of K ⇒ flux decreasing to 0 ⇒ flux ≥ 0 on the band.
- Hence Re K'_{iτ}(a) ≥ −(1 + 1/a)Re K_{iτ}(a); (a²+9)K + 6aK' ≥ (a² − 6a + 3)K, positive for a ≥ 6, |τ| ≤ a.

## WignerSpectralBand (uses RHTower PolyaBesselHeatKernel, ThetaCusp ThetaCuspWignerProductFiberNormalForm)
- cosTransform(Pólya kernel·cosh)(w) = −2K'_{iw}(a). thetaCuspWignerRadialTransform a b = a²((a²+9)K_{ib}(a) + 6aK'_{ib}(a)) (exact Bessel combination). Band |b| ≤ a: Re ≥ a²(a²−6a+3)K > 0 for a ≥ 6.
- Product fibre = divisor trace × radial transform: on band with scale 2πk e^{2u} ≥ 6 (automatic for k ≥ 1, u ≥ 0), sign of fibre = sign of the finite real divisor-character trace.
- Diagonal theta-atom pair Wigner (n,n) at u ≥ 0 has positive real part on its full band |b| ≤ 2πn²e^{2u} (phase trivial on the diagonal).

## WeilInverseCost (uses CACT TheCompleteWeilGroundStateIsThePole, OneHorizonMakesEveryBoundedOverlapPositive)
- tiltedWeilInverseCost c = 1/completedConductorEnergy(tiltedUnitSpline, c, 1) (pole ground energy, > 0). Eigenvalue floor C⁻¹ ⇒ |v|² ≤ C vᵀAv; eigenvector attains bᵀA⁻¹b = λ⁻¹.
- Sharp: for C > inverseCost eventually every complete-Weil inverse column costs ≤ C|b|²; for C < inverseCost eventually some unit b has bᵀA⁻¹b > C. One finite cost and horizon work uniformly for overlaps 0 < c ≤ K.

## WeilGreenModes (uses RAPT TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets, HTGeometry HilbertClosedRange)
- Quasimode inversion: |A⁻¹v − λ⁻¹v| ≤ (eλ)⁻¹|Av − λv| under coercivity floor e. Completed conductor energies E_m ≥ E_1 > 0.
- Normalized Ramanujan horizon vectors are asymptotic eigenvectors of the complete Weil inverse with eigenvalue 1/E_m; mixed Green entries → δ_{ml}/E_m; on finite Ramanujan packets the Green form → Σ b_m d_m / E_m (asymptotically diagonal, pole coordinate included).

## ConductorHeatThreshold (uses Mathlib SumPrimeReciprocals)
- log m + selfFinitePart − shellBudget ≤ E_m (all m ≥ 1); for primes E_p ≤ log p + selfFinitePart + shellBudget + 1 (tame different ≤ 1). E_n → ∞, 1/E_n → 0.
- Σ e^{−βE_n} converges ⇔ β > 1 (divergence at β ≤ 1 via Σ1/p = ∞): completed conductor spectrum has exact heat threshold 1 (same as log n). No integer power Σ E_n^{−k} converges (E ~ log n).

## ConductorGreenCompletion (uses HTGeometry BoundedDiagonalOperatorLp)
- tiltedConductorGreen: diagonal operator on ℓ²(ℕ) with weights 1/E_{n+1}; norm = tiltedWeilInverseCost exactly (pole coordinate); compact (weights → 0); injective; coordinates are eigenvectors; but no Schatten-type power sum Σ|λ_n|^k is finite (compact, not in any Schatten class).

## UpwardSourcePayment (uses CACT AffineShellErrors…, PrimeBoundaryErrors…, UpwardKernelLinearization…, SmallWidthRealizesTheUpwardPrimeOffsets, TheActualUpwardSourceIsUniformOnBoundedOverlap)
- Mertens sum to N+B (B ≤ N) ≤ (J+2)log N. Logarithmic vs linearized upward kernel: harmonic-normalized error ≤ K c⁴(B+1)⁶(log N/N)² (squared horizon decay). Reciprocal affine shells (identity + reflected): ≤ K c⁶/√log N. Linear prime strip ⌈ec⌉: (strip+1)⁶ ≤ (e+2)⁶c⁶.
- Actual upward prime residual (rows split kernel + boundary + shell, 3-term Cauchy): |residual|² ≤ C(c¹⁰(log N/N)² + c⁶/√log N) for 1 ≤ c ≤ N, strip ≤ N, 2(e+3)c·strip ≤ N; holds for tilted unit spline.

## WeilPolynomialResidual (uses CACT WeilReplacementErrorsHavePolynomialCost, NearGammaDownwardCancellationHasPolynomialGrowth, CompletedConductorQuasimodesAreUniformOnBoundedOverlap; SignedArithmeticHodgeTheory TheArithmeticResidualBudgetIsUniformInTheHorizon)
- weilResidualScale c N = c¹⁰(log N/N)² + c⁶/√log N. Normalized prime residual ≤ C/log N.
- Eight-term decomposition (prime adjunction, self error, center/pole shift, separated cross, pole error, near-Gamma downward, near-center, upward shell) with |Σ8|² ≤ 8Σ|·|²: |W·r_m − E_m r_m|² ≤ C·weilResidualScale(c,N) for 1 ≤ c ≤ N/3 with strip conditions (polynomial overlap growth, slowest decay 1/√log N).

## WeilGreenTail (uses CACT MacroscopicOverlapTiltedSplineReserve)
- Fixed c > 0, ε > 0: ∃ finite conductor set S such that eventually every v orthogonal to all normalized Ramanujan vectors r_m (m ∈ S) has |W⁻¹v| ≤ ε|v| (finite reading certificate from energy reserve + inverse quasimodes). Complete Green inverse is controlled by finitely many arithmetic coordinates.

## ConductorLogLaw (uses ArithmeticIntersectionTheory ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths)
- tameDifferent(n)/log n → 0 (split prime divisors at cutoff K); shellCorrection/log → 0 (bounded budget). completedConductorEnergy(φ, c, n)/log n → 1 for every profile φ and every c > 0.

## BesselGaussianMoments
- Differentiating the order recurrence: ∫_0^∞ t sinh t e^{−a cosh t} dt = K_0(a)/a (exact first moment). Second moment ∫ t² e^{−a cosh t} ≤ K_0(a)/a (t ≤ sinh t).
- Re K_{iτ}(a) = ∫ e^{−a cosh t}cos(τt); 1 − cos y ≤ y²/2 ⇒ 1 − τ²/(2a) ≤ K_{iτ}(a)/K_0(a) ≤ 1; ratio → 1 as a → ∞ (no asymptotic premise).

## BesselGaussianReserve
- Real band source f_τ(x) = Re K_{iτ}(x) satisfies f'' system (1 − τ²/x²)f − f'/x; K_0' ≤ −K_0 (K_0 ≤ K_1).
- Gaussian Wronskian flux e^{−τ²/x}(x f_τ' g − f_τ x g' − (τ²/x) f_τ g), g = K_0: increasing on band, → 0 ⇒ ≤ 0 ⇒ ratio f_τ/(e^{−τ²/x}g) nonincreasing to 1 ⇒ K_{iτ}(a) ≥ e^{−τ²/a}K_0(a) for |τ| ≤ a (Gaussian band reserve).
- Signed radial combination ≥ (a² − 6a + 3)e^{−τ²/a}K_0(a) for a ≥ 6.

## ConductorOverlapDecay (uses CACT TheTiltedSplineHasAPolynomialConductorFloor; BiScaleUncertainty SplineProbeFiniteShiftBounds)
- Tilted spline shell spectrum ≤ C t^{−8}; tail ∫_{>z} ≤ (C/7)z^{−7}. Pole energy E_1(c) ≤ C' c^{−7} for c ≥ 1; E_m(c) ≤ (m/φ(m))E_1(c/m).
- Two-sided: floor/c⁷ ≤ E_m(c) ≤ upper(m)/c⁷ for c ≥ m, upper(m) = C'm⁸/φ(m) (matching seventh-power overlap decay). Fixed finite conductor family: energy ratios uniformly bounded for all large overlaps.

## WeilGrowingOverlap (uses SpacingScaleHarmonicAnalysis TheGevreyWindow)
- Schedule c_N = (log N)^α: c_N → ∞, and eventually satisfies all source-domain conditions (1 ≤ c, c/N ≤ 1/3, strip ≤ N, 2(e+3)c·strip ≤ N).
- Relative to floor κ/c⁷: |W r_m − E_m r_m|²/E_m² ≤ C·c¹⁴·weilResidualScale = C(c²⁴(log N/N)² + c²⁰/√log N). For α < 1/40 this → 0 (exponent 20α − ½ < 0). So c⁷|residual| → 0 and |residual|/E_m → 0: each fixed conductor is a relative quasimode at growing overlap (no full-matrix positivity claim).

## WeilGrowingPackets (uses CACT CompletedConductorEnergiesHavePolynomialBounds; SAHT GrowingRamanujanFamiliesHaveAUniformGramBudget; HTGeometry PositiveDefiniteMatrixLimit)
- Normalized Ramanujan Gram error |⟨r_m, r_l⟩ − δ_ml| ≤ (2ml + 1)/log N.
- Scaled packet entries c⁷(⟨W r_m, r_l⟩ − δ_ml E_m) → 0 (uses E_m ≤ C c² and α·9 < 1).
- eventually_tiltedWeil_growing_packet_pos: every fixed family of distinct positive conductors gives a positive complete Weil energy for all nonzero coefficient vectors along c_N = (log N)^α, 0 < α < 1/40 (scaled diagonal ≥ κ dominates d·ε off-diagonal error).
