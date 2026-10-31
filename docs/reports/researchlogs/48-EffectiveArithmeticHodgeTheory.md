# 48 EffectiveArithmeticHodgeTheory — facts log

## TheHassePrincipleWithHeights (uses ACS OnePrimeSeesTheWholeDefectOfZeta, HKT TheFiniteIndexStratumOfZetaIsLindelofDeep, RHTower ZetaZeroCountUpperBound, GelfondSchneider)
- A cyclic subgroup ⟨u⟩ ⊂ ℚ_{>0} samples ordinates of the Weil kernel spectrum at spacing 2π/log u; two right zeros alias iff same real part and ordinates differ by a nonzero multiple of 2π/log u.
- rightZerosBelow T = right zeros with |Im| ≤ T; heightIndex κ_T = its cardinality: finite, monotone, ≤ 2N(0,T) + c₀ ≤ 2F(T) + C log²T + c₀ (Riemann–von Mangoldt). negIndex(zetaKernel) = sup_T κ_T (filtration exhausts the index).
- Nyquist separation: scale ℓ with ℓT < π ⇒ frobEig ℓ injective on points of ordinate ≤ T. π sharp: ℓT ≥ π ⇒ σ ± iπ/ℓ alias.
- Certifying tower: ℓT < π ⇒ some C² compactly supported g and window K ⊂ ℤ with κ_T ≤ hermNegIndex of the prime-side Weil Gram of translates by kℓ (deep-sparse tower law).
- Two-prime certificate: Dirichlet approximation of log 3/log 2 (irrational) gives k ≤ ⌊T log 2/π⌋ + 1, k ≤ j ≤ 2k, 0 < |log(3^k/2^j)|·T < π; tower of 3^k/2^j certifies height T. No prime tower certifies this way once T > π/log 2.
- Blind primes (tower aliases two right zeros of height ≤ T): a distinct pair aliases at most at one prime ⇒ #blind ≤ C(κ_T, 2); among any C(κ_T,2)+1 primes one tower carries all κ_T.

## TheExplicitSchedulesReachTheIndex (uses SSHA TheDenjoyCarlemanProfiles; HKT EveryReceiverAtEveryWidthIsBoundedByTheIndex, BoundedIndexIsClosedUnderPointwiseLimits; ArithmeticOrientationGeometry TheOrientationOfACycle; ACS TheReflectionSectorsOfTheHodgeDefect, WhatTheFailureOfTheHodgeIndexMeasures; RHTower WeilFullConeBochnerMeasure)
- Claim: Gevrey schedules not only decide RH but reach the index: hermNegIndex(atomic Gram at N) ≤ κ(K_ζ) for every N and ≥ every m ≤ κ for large N; indices → κ in ℕ∞.
- Real tests: W(f,g) real symmetric; polarization W(f,g) = (Q(f+g) − Q(f−g))/4 (functional equation: zero set closed under conjugation; FES symmetry).
- Perturbation norms: √∫(F+D)² ≤ √∫F² + √∫D²; √Levy(F+D) ≤ √Levy F + √Levy D; pole moments move by ≤ 2cosh(R'/2)‖D‖₁. weilErrBound majorant → 0 with e, V.
- tendsto_weilQuad_add: two-sided continuity Q(F + D_n) → Q(F) when sup e_n → 0 and synthLevy → 0 (upper bound from SSHA; lower bound = same bound read from base F + D_n whose norms stay bounded).
- Gram convergence under common-translate perturbations (synthLevy homogeneous of degree 2 in (e, L_D)).
- atomicGram ψ N = Weil Gram of translates ψ(· − log n), n ≤ N. Compression: Gram of finitely many real atomic tests at horizon N has ≤ hermNegIndex(atomicGram). Upper half: hermNegIndex(atomicGram (dilate k φ) N) ≤ κ(K_ζ) at every width (HKT receiver bound). atomicTest_extend: zero-padding.
- Sources: integer translates of the cubic spline carry every m ≤ κ (negIndex_zetaKernel = sup over integer atoms); mollifying by the dilated profile keeps m negative squares (lower semicontinuity of the index under entrywise convergence) and gives Gevrey-s families with common constants (exists_gevrey_family).
- Overlap growth Gevrey is preserved by horizon shift N ↦ N + ρ; eventually along every residue class mod B ⇒ eventually.
- eventually_le_hermNegIndex_of_synthesis: any atomic synthesis of a negative family with errors e_j → 0, synthLevy → 0 makes the atomic Grams carry its negative squares (regularity class enters only via synthesis).
- eventually_le_hermNegIndex_atomicGram (Gevrey-s profile, Gevrey overlap growth): every m ≤ κ eventually carried; tendsto_hermNegIndex_atomicGram: indices → κ(K_ζ) in ℕ∞ (finite or infinite). dcProfile_atomicGram_reaches_index: ∀α > 1 ∃ odd r, dcProfile r at width (log log N)^α/N reaches the index. Transfer statement; no selectivity; the upper half is zero-side.

## FiniteWeilPerturbationsHaveExplicitBounds
- weilPerturbationBudget F R e V = weilErrBound with explicit bounds on perturbed base norms (√∫F² + √(2R)e, √Levy F + √V, moments + 4R cosh(R/2)e). |Q(F + D) − Q(F)| ≤ budget(F, R, e, synthLevy R e L k) (upper estimate applied in both directions).
- Weil Gram entries: |W(F_i+D_i, F_j+D_j) − W(F_i, F_j)| ≤ (budget(F_i+F_j) + budget(F_i−F_j))/4 with doubled e, L (polarization).

## FiniteWeilFamiliesHaveExplicitIndexHorizonTests
- compressedEntryBudget S B i j = Σ_a Σ_b |S_ai| B_ab |S_bj|; ‖(Sᴴ E S)_ij‖ ≤ it when |E_ab| ≤ B_ab.
- le_index_of_compressed_entry_test: if SᴴAS = diag(c_i) with c_i ≤ −δ, |G − A| ≤ B entrywise and all compressed budgets ≤ δ/(2(r²+1)), then r ≤ hermNegIndex G.
- Proof of the compressed test: SᴴGS = diag(c) + E', |E'_ij| ≤ ε, ε r² < δ ⇒ SᴴGS negative definite on ℂ^r ⇒ r ≤ hermNegIndex G.
- exists_complete_negative_compression: every Hermitian A has S (negative eigenvectors), r = hermNegIndex A, SᴴAS = diag(c), c ≤ −δ < 0.
- Common translation preserves the Weil Gram of real tests (polarization + weilQuad translation invariance).
- exists_emWeil_index_horizon_test: for every finite real smooth family F (support ≤ R) there are r = its Weil index, S, δ > 0 such that for every unit-mass smooth profile φ, derivative bounds M, any order m, horizon N ≥ 2, inverse width k ≥ 1: if all compressed EM entry budgets ≤ δ/(2(r²+1)) then r ≤ hermNegIndex(atomicGram (dilate k φ) (N·blockSize R)). Certificate version supplies M from the family itself. Finite, explicit horizon test.

## SteklovIndexCertificatesAtEveryHorizon
- steklovWeilEntryBudget: full entry error of log-DC synthesis by steklovDCProfile (dcSynthErr with A = 2·steklovBaseSup, B = 12).
- exists_steklov_index_horizon_test: every d ≤ κ(K_ζ) has an explicit Steklov certificate (log-DC family F, R, M, b, r ≥ d, S, δ) valid at every integer horizon N (via N/blockSize R and zero extension of the last block) and inverse width k ≥ 1. Schedule version at k = N/superGevreyRatio β N with order gevOrder k.

## TheSteklovScheduleReachesTheIndex (uses TMWP SuperGevreyCriticalGrowth)
- exists_dcLog_family: every m ≤ κ is carried by a log-DC family (spline family mollified by φ; derivative bounds Mg·A·(B_φ m)^l W_l).
- Super-Gevrey overlap law preserved by integer shift; synthesis transports each finite negative family along each residue class (same ratio estimate as TMWP: p log²(p+3) ≤ 24ℓℓ₂²).
- tendsto_hermNegIndex_atomicGram_dcLog: for log-DC profiles and super-Gevrey overlap the atomic Gram indices → κ(K_ζ) in ℕ∞. steklovDCProfile_atomicGram_reaches_index: the fixed Steklov profile at width L(log L)^β/N, β > 2, reaches the whole index.

## IndexCarriersOfFiniteSpectra (uses HKT TheIndexOfAFiniteExponentialSum, AllButFinitelyManyPrimesSeeTheWholeIndex)
- Carries S x: evaluation matrix (χ(x_b)) has full row rank. Then Gram of the Hermitian exponential sum k = Σ_{χ∈S} a_χ χ on x has exactly κ(k) negative squares (S closed under reflection).
- Lagrange: injective nodes w on S, n ≥ |S| ⇒ powers (w_χ^k)_{k<n} span ℂ^S. window_carries: χ ↦ χ(g) injective on S ⇒ window g⁰…g^{n−1} carries S. box_carries: χ ↦ (χ(g), χ(h)) injective ⇒ box g^i h^j (i,j < n) carries S (generic linear form χ(g) + tχ(h) separates; binomial expansion).
- On ℚ_{>0}: zero characters u ↦ u^{ρ−½} are separated by two distinct primes (a pair of exponents aliases at most at one prime) ⇒ box p^i q^j, i,j < |S|, reads the index of every Hermitian exponential sum of zero characters; window p^0…p^{|S|−1} does when no two exponents alias at p. Finite sections of the Hasse principle: size = size of spectrum, no margin.

## TheBezoutTheoremOfTheMultiplicativeGroup (uses RHTower GelfondSchneider)
- Points = primes via Frobenius progressions s_j = 2πij/log p (where 1 − p^{−s} = 0); degree of D(s) = Σ_{n≤N} a_n n^{−s} is log N. frobRoot ω_p(n) = e^{−2πi log n/log p}; n^{−s_j} = ω_p(n)^j; ω_p(n) = ω_p(n') iff n/n' ∈ p^ℤ. Distinct prime progressions meet only at s = 0 (irrationality of log q/log p).
- fiber_sum_eq_zero: a finite exponential sum Σc_i ω_i^j vanishing for cofinitely many j ∈ ℤ has all fibre sums zero (Lagrange). So vanishing on the progression ⇔ every p-tower sum Σ_k a(p^k n) vanishes.
- towerQuot a p m = Σ_{l≤v_p(m)} a(m/p^l); a = F − F(·/p) (D = (1 − p^{−s})F); vanishing on progression ⇒ F has length N/p.
- dirDeriv: D^{(i)} = F^{(i)} − p^{−s}Σ_{l≤i} C(i,l)(−log p)^{i−l}F^{(l)}; off the progression (p^{−s} ≠ 1) the quotient keeps vanishing order; on it the order drops by exactly one.
- VanishesAlong a N p m: first m derivatives vanish at cofinitely many points of p's progression. One division step: quotient has length N/p, order m_p − 1 along p, same orders along other primes.
- prod_pow_le_of_vanishesAlong (Bézout of G_m(ℚ)): a nonzero Dirichlet polynomial of length N vanishing to order m_p along p's progression for every p in a finite prime set S has Π p^{m_p} ≤ N; ledger form Σ m_p log p ≤ log N. Sharp: 1 − p^{−s} (length p) vanishes on the whole progression. Vanishing at all primes ≤ y costs length e^{θ(y)}.

## TheRiemannRochTheoremOfTheMultiplicativeGroup
- sections N S m = Dirichlet polynomials of length N vanishing to order m_p along p's progression, p ∈ S (a ℂ-subspace); dirPolys N ≅ ℂ^N.
- eulerMul p (multiplication by 1 − p^{−s}) and towerQuot are inverse; sectionsEquivQuot: sections(N, m) ≅ sections(⌊N/p⌋, m − e_p).
- finrank_sections: h⁰(N, m) = ⌊N/Π p^{m_p}⌋ (exact, multiplicative). sections ≠ 0 ⇔ Π p^{m_p} ≤ N (Bézout with converse).
- Function-field calibration: polynomials of degree < n divisible by monic Q of degree k: dimension n − k; (u^e − 1)^m in degree ≤ d: d + 1 − em (additive; all places of degree e share a progression). Over ℤ each prime has its own progression, cost N − ⌊N/p⌋.

## ApproximateVanishingIsAlmostDivisibility
- On p's progression D(s_j) = Σ_w C_w w^j, C_w = p-tower sums.
- Separation: distinct roots ω_p(n) ≠ ω_p(m) (n, m ≤ N) are ≥ 4/(Np log p) apart: |log A − log B| ≥ 1/max(A,B) for distinct integers, |1 − e^{iθ}| ≥ 4·dist(θ/2π, ℤ). No Baker bound needed.
- Mean values on a stretch: unimodular points δ-apart ⇒ Σ_{j<J}|Σ_t C_t t^{J₀+j}|² ≥ (J − 2|T|/δ)Σ|C_t|² (diagonal J; off-diagonal geometric sums ≤ 2/δ; Cauchy–Schwarz).
- sum_normSq_towerSums_le (approximate Bézout): |D(s_j)| ≤ ε on J ≥ N²p log p consecutive progression points ⇒ Σ_w |C_w|² ≤ 2ε² (every p-tower sum √2ε-small; D within √2ε in coefficients of multiples of 1 − p^{−s}).

## SmallIntegerAuxiliariesAreDivisible
- IntegerCoeffs a (ℤ[Γ] auxiliaries); tower quotients stay integral. Integer of modulus < 1 is 0.
- dirDeriv_frobPoint_eq_zero_of_small: integer auxiliary with |D| ≤ ε, 2ε² < 1, on N²p log p consecutive points vanishes on the whole progression (approximate vanishing = exact vanishing ⇒ divisible by 1 − p^{−s} in ℤ[Γ]).
- One Euler factor on the progression: D_b^{(i)}(s_j) = −Σ_{l<i} C(i,l)(−log p)^{i−l}D_c^{(l)}(s_j). Chain b = (1−p^{−s})^k b_k: first k derivatives vanish on the progression, k-th = k!(log p)^k D_{b_k}.
- vanishesAlong_of_small (rigidity): |D^{(i)}| ≤ i!(log p)^i ε for i < m on N²p log p consecutive points, 2ε² < 1 ⇒ D vanishes to order m on the whole progression. prod_pow_le_of_small: zero estimate for integer auxiliaries Π p^{m_p} ≤ N. Threshold sharp: auxiliary 1 has |D| = 1 everywhere (ε < 1 necessary). No transcendence input.

## TheTwistTowerCollapsesOverTheIntegers (uses ArithmeticOfSquareRootPrecision TheBatteryOfTheCount)
- Over F_q the twist tower (quadratic twists of 2^j base changes) completes the one-sided count; over ℤ the twist is Liouville (−1)^Ω. twistLevel j n = (−1)^{Ω(n)/2^j}Λ(n) if 2^j | Ω(n) else 0; level 0 = Liouville twin λΛ.
- j ≥ 1: lives on proper prime powers p^k, 2^j | k: |w_j| ≤ Λ − Λ·[prime]; |partial sums| ≤ ψ(x) − θ(x) ≤ 2√x log x; twistLevel_mem_sqrtClass: every level above the first is in the square-root class (invisible to the count). The tower collapses to its first level over ℤ (ℚ_{>0} lacks primes of every degree).

## TwinsAreSeenByEveryLargeSection
- eventually_atomicTest_neg_of_stable_gevrey: a stable form negative on one C² test is negative on some atomic test at every large horizon of a Gevrey schedule (residue classes + shift-stability + zero padding) — not just infinitely often.
- eventually_negative_iff_of_gevrey: a bounded twin |λ| ≤ Λ is negative at every large section iff not WeilPositiveFull.
- liouville_eventually_negative_of_gevrey (unconditional); riemannHypothesis_imp_liouville_separation_of_gevrey: under RH every large section has ζ ≥ 0 on all atomic tests and Liouville < 0 on one.
