
## 22. Linear twists and the Euler product for degree two and small conductor

Throughout this section `F` belongs to the extended Selberg class `S^♯`, has degree `d_F = 2`, and has
**integer** conductor `q_F = Q`. We use the class `M(d,h)` of Kaczorowski–Perelli: `f ∈ M(d,h)` if `f`
is meromorphic on `C`, holomorphic for `σ < 1`, and for all `A < B` there is `C = C(A,B)` with
`f(σ+it) ≪ |σ|^{d|σ|}(h/(2πe)^d)^{|σ|}|σ|^{C}` as `σ → −∞`, uniformly for `A ≤ t ≤ B`.

Two inputs are quoted. First, their transformation formula for the linear twist
`F(s,α) = Σ a_F(n)e(−nα)n^{−s}`, valid for every `F ∈ S^♯` of degree 2 and every `α > 0`: for each
integer `K > 0` there are polynomials `Q_0 ≡ 1, Q_1, …, Q_K` depending only on the `γ`-factor, with
`deg Q_ν = 2ν`, such that

> `F(s,α) = −i ω_F^*(√Q α)^{2s−1+iθ_F} Σ_{ν=0}^{K} (iQα/2π)^ν Q_ν(s) F̄(s+ν+iθ_F, −1/(Qα)) + H_K(s,α)`,

with `H_K` holomorphic for `−K+1/2 < σ < 2`, `|s| < 2K`, `H_K ≪ (AK)^K`, and
`Q_ν(s) ≪ (A(|s|+1))^{2ν}/ν!` for `1 ≤ ν ≤ min(|s|,K)`. Second, `F ∈ S^♯_d ⟹ F ∈ M(d,q_F)`.

The twist is exactly `1`-periodic in `α`; write `T(α) = α+1` and `W(α) = −1/(Qα)`.

### 22.1 The twist conductor

**Definition.** For `α ∈ Q` with denominator `q` in lowest terms put `h_Q(α) = Q q²/ gcd(q,Q)`.

**Lemma 22.1.** Let `α = A/q`, `A ≠ 0`, `gcd(A,q) = 1`, `g = gcd(q,Q)`. Then `W(α)` has denominator
`q₁ = (Q/g)|A|`, one has `gcd(q₁,Q) = Q/g`, and `h_Q(α) = h_Q(Wα)/(Qα²)`. In particular `h_Q` depends
only on the class of `α` modulo one, as it must.

*Proof.* Put `Q = gm`. Since `gcd(A,q) = 1` we get `gcd(q,QA) = gcd(q,Q) = g`, so `q₁ = m|A|`. Also
`g ∣ q` gives `gcd(A,g) = 1`, whence `gcd(m|A|, gm) = m·gcd(|A|,g) = m = Q/g`. Therefore
`h_Q(Wα) = Q q₁²/(Q/g) = Q²A²/g` and `h_Q(Wα)/(Qα²) = (Q²A²/g)(q²/(QA²)) = Qq²/g = h_Q(α)`. ∎

At `α ≡ 0` this reads `h_Q(0) = Q = q_F`, matching `F ∈ M(2,q_F)`; at `Q = 1` it reads `h_1(A/q) = q²`,
matching the conductor-one case.

### 22.2 The descent

**Lemma 22.2.** Represent each non-zero class in `Q/Z` by `α = A/q` with `gcd(A,q)=1` and `2|A| ≤ q`.
With `α₁ = Wα`, `α₂ = W²α` and `q_i` the corresponding denominators,
```
4 q₂ ≤ Q q .
```
Hence for `Q ≤ 3` the denominator strictly decreases in two steps, and the reduction of any rational
`α` terminates at `0`. For `Q = 4` the same holds when `q` is odd or `4 ∣ q`; the classes with
`q ≡ 2 (mod 4)` reduce to `1/2`, which satisfies `W(1/2) ≡ 1/2`. For `Q ≥ 5` no contraction is
available.

*Proof.* With `g = gcd(q,Q)`, `Q = gm`, Lemma 22.1 gives `q₁ = m|A|`, `gcd(q₁,Q) = m`, hence
`q₂ = (Q/m)|A₁| = g|A₁|`, so `4q₂ = 4g|A₁| ≤ 2g q₁ = 2Q|A| ≤ Qq`. If `q ≡ 2 (mod 4)` and `Q = 4` then
`A` is odd, `g = 2` and `q₁ = 2|A| ≡ 2 (mod 4)`, with `q₁ ≤ q` and equality only for `q = 2`. ∎

The threshold `Q < 4` is exactly the discreteness threshold `√Q < 2` for the group `⟨T,W⟩`, which in
the coordinate `β = √Q α` is the Hecke group `G(√Q) = ⟨β ↦ β+√Q, β ↦ −1/β⟩`; the exceptional class
`1/2` at `Q = 4` is the cusp of `Γ_0(4)` not merged with `∞` by the Fricke involution. The proof above
uses none of this.

### 22.3 The theorem

**Theorem 129.** Let `F ∈ S^♯` be entire, of degree 2 and integer conductor `Q ∈ {1,2,3,4}`, and let
`α = a/q ∈ Q` in lowest terms, with `q ≢ 2 (mod 4)` if `Q = 4`. Then `F(s,α)` is entire and
```
F(s,α) ∈ M(2, Q q²/gcd(q,Q)) .
```

*Proof.* Induction on the number of `W`-steps from `α` to `0`, finite by Lemma 22.2. The base case is
`F(s,0) = F(s) ∈ M(2,Q)` with `h_Q(0) = Q`. For the step, choose the representative with `2|A| ≤ q`;
if `A < 0` replace `F(s,α)` by `conj(F̄(s̄,−α))`, which changes neither entirety nor the class
`M(2,h)`, since the latter is defined by growth on arbitrary horizontal strips. Apply the
transformation formula. Every `F̄(·, Wα)` is entire by the induction hypothesis and `H_K` is
holomorphic for `−K+1/2 < σ < 2`; as `K` is arbitrary, `F(s,α)` is entire. For the growth, fix a strip,
let `σ → −∞`, take `K = [|σ|]+2`. The prefactor contributes `(√Q|α|)^{−2|σ|}` and the inductive bound
contributes `(√{h_Q(Wα)}/(2πe))^{2(|σ|−ν)}|σ|^{2(|σ|−ν)}`; by Lemma 22.1
`√{h_Q(Wα)}/(√Q|α|) = √{h_Q(α)}`, the `ν`-sum converges by `Q_ν(s) ≪ (C|σ|)^{2ν}/ν!`, and the error
`(AK)^K ≪ (A'|σ|)^{|σ|}` is dominated by `|σ|^{2|σ|}`. ∎

The hypothesis that `F` be entire is used only to make the induction hypothesis "entire" propagate.
For `m_F > 0` one needs in addition `(s+ν−1)^{m_F} ∣ Q_ν(s)`, which for `Q = 1` follows from the
coincidence `W(1) ≡ 0`; no substitute is available for `Q > 1`, and the polar case is left open.

**Corollary 130.** Let `F ∈ S` be entire with `d_F = 2` and `q_F = Q ∈ {1,2,3,4}`. Then for every prime
`p` (odd if `Q = 4`)
```
F_p(s) = ∏_{j=1}^{∂_p}(1 − α_j(p)p^{−s})^{−1},  |α_j(p)| ≤ 1,
∂_p ≤ 2 if p ∤ Q,   ∂_p ≤ 1 if p ∣ Q ;
```
in particular `|a_F(p)| ≤ 2`, and `|a_F(p)| ≤ 1` at the primes dividing the conductor.

*Proof.* Theorem 129 with `q = p` gives `F(s,a/p) ∈ M(2,h)` for all `a ≢ 0 (mod p)` with the same
`h = Qp²/gcd(p,Q)`. Every `F ∈ S_2` satisfies `N_F(σ,T) ≪ T^{3/2−σ+ε}` for fixed `σ > 1/2`, hence
`N_F(σ,T) = o(T)`. The implication (i) ⟹ (ii) of Kaczorowski–Perelli's twist criterion then gives the
Euler factor with `∂_p ≤ [log(h/q_F)/log p] = [log(p²/gcd(p,Q))/log p]`. ∎

**Corollary 131.** For such `F`, `Σ_{p≤x}|a_F(p)|²/p ≤ 4 loglog x + O(1)`; in particular the prime
energy `n_F` is finite, with `n_F ≤ 4`. Membership in `S` supplies only `a_F(p) ≪_ε p^{ε}`, which gives
no bound on the energy at all, so this is the finiteness half of Selberg's Conjecture A on a class
where it was not previously available.

### 22.4 Formalisation

The arithmetic core is formalised, unconditionally, in
`formal/GaloisForLFunctions/HTGeometry/TwistConductorDescent.lean`:
`gcd_dualDenom` (Lemma 22.1's gcd identity), `twistConductor_dualDenom` (the exact recursion),
`four_mul_dualDenom_two_le_two_mul` and `four_mul_dualDenom_two_le` (the contraction `4q₂ ≤ Qq`),
`dualDenom_two_lt` (strict descent for `Q ≤ 3`), `dualDenom_two_lt_four_of_odd` (strict descent for
`Q = 4` and odd denominator), and `dualDenom_four_two_one` (the fixed class `1/2` at `Q = 4`).
