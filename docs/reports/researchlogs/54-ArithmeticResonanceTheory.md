# ArithmeticResonanceTheory — facts log

## PrimesObeyNoAffineRecurrence (Mathlib only)
- If residues mod ℓ = p_M follow an injective self-map of ZMod ℓ from M on, then ℓ | p_{M+j} for some j ≥ 1 (permutation of a finite set returns every residue; orderOf σ).
- No eventually increasing prime sequence satisfies p_{n+1} = a p_n + m (a ≥ 1, m ∈ ℤ) eventually: pick ℓ = p_M > a, x ↦ ax + m is a permutation mod ℓ, so ℓ divides a larger member.
- Eventually periodic defect m_n (period d): d-step recurrence is affine with slope a^d and intercept independent of block ⇒ also impossible.

## IntegralityForbidsSuperConformalDistortion
- Convergent integer sequence is eventually constant. a·q not prime for a ≥ 2, q prime.
- Super-conformal ratio: p_{n+1} = a p_n e^{δ_n}, |δ_n| ≤ Kρ^n, aρ < 1 ⇒ p_n ≤ B a^n, integer defect p_{n+1} − a p_n = O((aρ)^n) → 0 ⇒ eventually p_{n+1} = a p_n; with a ≥ 2 not eventually prime.
- Conformal threshold: p_n = C a^n e^{ε_n}, a ≥ 2, C > 0, a^n ε_n → A (any real A) ⇒ defects → C(A − aA), eventually constant ⇒ affine recurrence ⇒ not eventually prime. Second-order remainder a^n(e^ε − 1 − ε) → 0. Margin is from integrality; Beurling systems untouched.

## TheHolderModulusOfAPrimeLengthSystem (uses HTGeometry SymbolicShiftSpace)
- IsCycleFamily(y, L, x, P): P(n+1) = L + P(n), x(n+1) agrees with y for (n+1)L symbols, shift_L x(n+1) agrees with x(n) for P(n) + nL symbols. (u^n v)^∞ is a cycle family of u^∞.
- One-step law for (C, θ)-Hölder roof: |φ^{P(n+1)}(x_{n+1}) − φ^L(y) − φ^{P(n)}(x_n)| ≤ 2C/(1−θ)·(θ^L)^n.
- Cycle law: a = e^{φ^L(y)} integer ≥ 2 and family lengths eventually prime ⇒ a·θ^L ≥ 1.
- IsPrimeLength: every admissible periodic point of least period L has e^{φ^L} prime. Fixed-point law: in a Hölder prime-length system, a fixed point a^∞ with A a a, A a b, A b a (b ≠ a) has θ·e^{φ(a^∞)} ≥ 1 (family (a^n b a)^∞, least period n + 2).

## TheTwoRealizationsOfThePrimes (Mathlib only)
- primeZetaR P(σ) = Σ_p p^{−σ}: strictly decreasing on (1, ∞), continuous on [σ₀, ∞), → +∞ as σ ↓ 1 (Σ 1/p diverges), P(2) ≤ π²/6 − 1 < 1 (injection p ↦ p − 2 into Σ 1/(n+2)²).
- Commutative realization (disjoint loops of length log p): eigenvalues p^{−s}, |·| ≤ 2^{−σ}, < 1 on Re s > 0 (never 1); trace class ⇔ Re s > 1; exp Σ_n tr(L_s^n)/n = ζ(s) on Re s > 1 (Euler product via −log(1 − p^{−s})). Pole of ζ is a nuclearity pole: all eigenvalues ≤ ½ on σ ≥ 1 while trace norm P(σ) → ∞.
- Free realization (full shift on prime alphabet): trace_n = P(σ)^n, zeta = (1 − P(σ))^{−1} (renewal). Spectral pole: unique σ* ∈ (1, 2) with P(σ*) = 1; (1 − P)^{−1} → ∞ as τ ↓ σ*. Free dynamics overcounts (wrong entropy).

## OscillationFailsOnAdditiveRealizations (uses HTGeometry DirichletSimultaneousApproximation)
- phase(t, ℓ) = e^{−itℓ}, unimodular, multiplicative in ℓ. Dirichlet simultaneous approximation: finitely many lengths ⇒ all phases within δ of 1 at arbitrarily large t (explicit Q > (2π² + 2π)/δ). Absolutely convergent Σ a_i(e^{−itℓ_i} − 1) is < ε at arbitrarily large t (finite part + tail).
- RelativeDolgopyat(Z, z): ∃ C, ρ < 1, T, ‖Z_n(t)‖ ≤ Cρ^n z_n for t ≥ T. |Π z_i − 1| ≤ Σ|z_i − 1| for unimodular factors; word sums over n edges within nδΣa of untwisted value.
- No relative Dolgopyat bound for finite additive realizations (finitely many edges, locally constant roof), nor for the free realization (sup_{t ≥ T}|P(σ+it)| = P(σ)). Commutative realization: twisting preserves every eigenvalue modulus. Oscillation needs a non-additive roof.

## TheAmplifierLaw (Mathlib only)
- Almost periodic sums vanishing at infinity are zero: Σ c_i u_i^n → 0 with distinct unimodular u_i ⇒ all c_i = 0 (difference operator b(n+1) − u_j b(n) peels frequencies).
- Rate = depth: |Σ c_i α_i^n| ≤ K R^n eventually (distinct α_i) ⇒ every α_i with c_i ≠ 0 has |α_i| ≤ R (normalize by top modulus M > R; top part → 0).
- Moments lose a root: |a(n)|^{2k} ≤ C(B^{2k}D)^n ⇒ |α_i| ≤ B D^{1/2k}. Family moment bound transfers to each member by positivity.
- Fixed loss D for all k ⇒ |α_i| ≤ B (D^{1/2k} → 1); frequencies above B (poles) must have coefficient 0. Envelope loss D_k = e^{2kλ} gives B e^λ and is attained by single frequency B e^λ: loss exponents are strip widths, tensor powers add nothing.

## OrthogonalityAmplifiersAreTrivial (Mathlib only)
- Family of unimodular twists w_x : Fin r → ℂ, A_x = Σ a_i w_x(i), a_i ≥ 0. IsBrauer(w, k): distinct degree-k monomials (multisets of size k) orthogonal over family.
- Counting: Brauer at level k ⇒ |X| ≥ C(r+k−1, k) (monomial vectors nonzero orthogonal in ℂ^X).
- Moment = diagonal: Σ_x |A_x|^{2k} = |X|Σ_m (N_m a^m)²; Cauchy–Schwarz + multinomial ⇒ (Σ a_i)^{2k} ≤ Σ_x |A_x|^{2k}. Positivity bound never beats trivial bound.
- Rank: C(r+k−1,k)^{1/k} → 1 as k → ∞ at fixed r (≤ (k+r)^r); ≥ r/k always. Fixed rank (curve genus) can have fixed loss; over ℤ rank π(y) is the whole gain. Non-envelope amplifier over ℤ needs an identity, not orthogonality.

## EvenRealizationsHaveNoZeros (uses HTGeometry FiniteDeterminantLogSeries, RHTower ZetaResidueFactorDerivative)
- Entries bounded by a ⇒ n|(A^{k+1})_{ij}| ≤ (na)^{k+1}, |tr A^{k+1}| ≤ (na)^{k+1}; na < 1 ⇒ det(1 − A) = exp(−Σ tr A^k/k) (via Schur-triangulation finiteDet2 identity, Hilbert–Schmidt norm ≤ na).
- graphMatrix M(s)_{ij} = Σ_{e: i→j} c_e e^{−s r_e}; graphZeta = exp Σ tr M^k/k. det(1 − M(s)) entire. Positive lengths ⇒ far right Z(s)·det(1 − M(s)) = 1: even realizations are pole-only (zeros need odd part det(1 − L⁻)/det(1 − L⁺), over F_q = H¹).
- ζ is the dynamical zeta of no finite weighted graph: (s−1)ζ(s)det(1 − M(s)) = s − 1 would extend to ℂ, contradicted by ζ(−2) = 0.

## AHolderRealizationIsAZeroFreeStrip (uses HTGeometry SymbolicRuellePollicott)
- Mixing SFT, Hölder roof φ ≥ r_min > 0, periodic sums summable on σ > 1: Ruelle–Pollicott gives F holomorphic on Re s > 1 − ε with dynamical zeta = 1/F. If ζ = dynamical zeta on Re s > 1 then ζ ≠ 0 on Re s > 1 − ε (s ≠ 1): (s − 1)ζ·F = s − 1 extends by identity theorem. Strip comes from continuation, not oscillation; zeros of ζ are not transfer-operator resonances in such a realization.

## AdditiveRealizationsAreCommutative (Mathlib only)
- Markov shift on any alphabet with locally constant roof r; IsAdditivePrimeLength: every admissible periodic point of least period L has e^{Σ r} prime.
- First-return word at a: starts with a, no other a, closes to a; its periodic point has least period = length. Two different first-return words u, v at a: (uv)^∞ has least period |u| + |v| (a occurs at residues 0 and |u|; smaller period forces u = v).
- Additive rigidity: in an additive prime-length shift each symbol has at most one first-return word (else length of (uv)^∞ = p_u p_v composite). So realization = disjoint loops (commutative), no mixing. Free realization (full shift on primes, roof log p) not prime-length: [2] and [2,3].

## TheArchimedeanPlaceForbidsFiniteVirtualRealizations
- IsExpPoly: Σ c_j e^{−λ_j s}, real λ_j; closed under +, ×, −, finite sums/products; det(1 − M(s)) of a finite weighted graph is one.
- Exponential polynomial vanishing on real progression s₀ + h(k+1), h ≠ 0, is identically zero (group by frequency, distinct real bases e^{−μh}, rate = depth with R = 0).
- ζ is not a finite virtual realization ζ·det(1 − M⁺) = det(1 − M⁻) (M⁺ positive lengths, M⁻ any real lengths): trivial zeros ζ(−2(k+1)) = 0 force D⁻ ≡ 0, then D⁺ = 0 far right, contradicting Z⁺D⁺ = 1. Gamma factor puts zeros on a real progression; a realization of ζ needs infinite-rank odd part.

## OverFiniteFieldsTheOddPartIsSpectral (Mathlib only)
- det(1 − q^{−s}F) = 0 ⇔ q^s eigenvalue of F (zeros = spectrum, no positivity). q^s has period 2πi/log q (zeros on vertical progressions). |q^s| = q^{1/2} ⇒ Re s = ½ (RH = unitarity).

## GeneralizedDirichletSeriesAreDeterminedByTheirValues (Mathlib only)
- Σ_i w_i e^{−σλ_i}, any index, real w, locally finite frequencies ({λ ≤ T} finite), absolutely convergent on σ > σ₀; vanishing on σ > σ₀ ⇒ mass Σ_{λ_i = t} w_i = 0 at every t. Proof: least frequency t₀ with nonzero mass; head = e^{−σt₀}·mass; gap δ above t₀ ⇒ tail O(e^{−σ(t₀+δ)}); σ → ∞. Repeated frequencies allowed.

## ARealizationOfZetaIsPrimeLength
- On real axis, log ζ(σ) has two positive generalized Dirichlet series: orbit side Σ_{(n,x)} n^{−1}e^{−σφ^n(x)}, prime side Σ_{(p,k)} (k+1)^{−1}p^{−(k+1)σ} = Σ_p −log(1 − p^{−σ}). Both locally finite (φ^n ≥ n r_min; (k+1)log p ≥ (k+1)log 2).
- Realization (SFT, φ ≥ r_min > 0, ζ = exp Σ Z_n/n on Re s > 1) ⇒ IsPrimeLength: a periodic point of least period L gives mass ≥ 1 at t = φ^L(x) (L distinct shifts, weight 1/L each); arithmetic side carries t by at most one prime power (unique factorization), mass 1/(k+1) ⇒ k = 0, e^t = p.
- Price of the strip: Hölder realization on mixing SFT ⇒ zero-free strip Re s > 1 − ε AND θ·e^{φ(a^∞)} ≥ 1 at every fixed point that can be left and re-entered.

## TheHolderModulusAlongEveryCycle
- IsReturnWord at a (starts with a, no other a, admissible, closes to a). Cycle point u^∞ admissible with least period |u|. Two different return words u, v at a: every (u^n v)^∞ admissible and primitive with least period n|u| + |v| (a sits at block starts 0, |u|, …, n|u|; smaller period forces |u| = |v| then u = v).
- Cycle law: θ-Hölder prime-length system, return word u at a symbol with a second different return word ⇒ θ^{|u|}·e^{φ^{|u|}(u^∞)} ≥ 1, i.e. θ ≥ p_u^{−1/|u|}. Fixed-point law is |u| = 1. Holds for every Hölder realization of ζ on an SFT (price of the strip along every re-enterable cycle).

## TheMillsBoundary
- |p_n − Ca^n| ≤ B at n, n+1 ⇒ |p_{n+1} − a p_n| ≤ (a+1)B. IsDefectChain: increasing primes with p_{n+1} = a p_n + m_n.
- Necessary: m_n ≠ 0 (a ≥ 2); prime q | a does not divide m_n (unless p_{n+1} = q); odd a ⇒ m_n even; not eventually periodic.
- Congruence forcing: defect a function of residue mod L ⇒ residues follow self-map of ZMod L ⇒ eventually periodic ⇒ impossible. 3 ∤ a with two defect values in distinct nonzero classes mod 3 ⇒ forced ⇒ impossible. a ≡ 1 mod ℓ, defects either d₀ ≡ 0 or ≡ r ≢ 0 ⇒ residue walk x ↦ x + r hits 0 unless defect eventually d₀ ⇒ impossible.
- Decided: no chain with |m| ≤ 2 (a even, 3 ∤ a), |m| ≤ 3 (a odd, 3 ∤ a), |m| ≤ 1 (a odd). ⌊C a^n⌋ not eventually prime for a = 2..6, any real C (defect is a base-a digit in [0, a−1]: a=2 digit 1; a=3 digit 2; a=4 digits 1/3 unipotent mod 3; a=5 digits 2/4 forced mod 3; a=6 digits 1/5 unipotent mod 5). No primes within ½ of Ca^n (C > 0) for a = 2, 4, 5.
