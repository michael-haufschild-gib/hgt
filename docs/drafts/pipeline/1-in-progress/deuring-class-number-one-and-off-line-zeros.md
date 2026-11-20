# Deuring's theorem: an off-line zero of ζ bounds the class-number-one imaginary quadratic fields

- **ID:** deuring-class-number-one-and-off-line-zeros
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** user question on Deuring (1933) and the class-number-one problem, 2026-11-20
- **Statement:** If `ζ(ρ) = 0` with `β = Re ρ > 1/2`, then every quadratic field `K` with `disc K < 0` and class number one has `|disc K| ≤ D(ρ) := 4·max(1, A(ρ)/|ζ(2ρ)|)^{2/(2β−1)}`, where `A(ρ) = |C(ρ)||ζ(2ρ−1)| + |ρ| C(β) Z(2β)/2`, `C(s) = √π Γ(s−1/2)/Γ(s)`, `Z(x) = ∑_{n∈ℤ} |n|^{−x}`. Consequently: unboundedly many such fields ⇒ RH.

## Goal
The true direction of Deuring's 1933 theorem, with the genuine `NumberField.classNumber` and an explicit bound. It is an unconditional "X ⇒ RH" reduction. It does not prove RH: by Baker–Heegner–Stark the hypothesis X is false, so the theorem carries no information about RH today; its value is the mechanism (an Epstein zeta function that is a multiple of ζ cannot vanish off the line when its second term is small).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `RHTower/Deuring/`, `lake --old env lean` green

## Approach
Class number one makes the norm form's Epstein zeta function equal to `w ζ(s) L(s)` with `L` holomorphic off `s = 1`; the two-term expansion of the Epstein zeta function is `2ζ(2s) + 2k^{1−2s}C(s)ζ(2s−1) + R` with `k = √|d|/2` and `R = O(k^{−2σ})`. At an off-line zero the first term is a fixed nonzero number and the other two are `O(k^{1−2β})`.

## Paper proof `[PROVED HERE]`

### 1. The model
Let `K` be a quadratic field. `1` is primitive in the lattice `𝓞_K`: if `1 = g·x`, `g ∈ ℤ`, `x ∈ 𝓞_K`, then `g² N(x) = 1`. Write `1 = u e₀ + v e₁` in a ℤ-basis; `gcd(u,v) = 1`, choose `uA + vB = 1` and `ω = −B e₀ + A e₁`. Then `{1, ω}` is a ℤ-basis, `ω² = a + bω` with `a, b ∈ ℤ`, and `𝓞_K ≅ R := ℤ[X]/(X² − bX − a)`. The trace form in this basis has determinant `2(b² + 2a) − b² = b² + 4a =: Δ`, so `disc K = Δ`. In `R`: `N(x + yω) = x² + bxy − ay²`, `4N = (2x + by)² − Δy²`; for `Δ < 0`, `N ≥ 0` with equality only at `0`; `z z̄ = N(z)`; an integer divides `z` iff it divides both coordinates; `z` is a unit iff `N(z) = 1`.

### 2. Representation numbers in a principal order
Assume `Δ < 0` and `R` principal. Let `r(n) = #{z ∈ R : N(z) = n}`. For a prime `p` put `ε_p = −1` if no element has norm `p`; `ε_p = 0` if some `π` of norm `p` is associated to `π̄`; `ε_p = 1` otherwise.

(2.1) If `N(π) = p` then `π` is irreducible (a factorization gives `N(u)N(v) = p`), hence prime. If no element has norm `p`, then `p` is irreducible in `R` (a proper factorization `p = uv` has `N(u)N(v) = p²` with `N(u) ∉ {1, p²}`, so `N(u) = p`), hence prime.

(2.2) If `N(w) = q > 0`, then `z ↦ wz` is a bijection `{N = n} → {N = qn, w | ·}`. With `w = p`: `#{N = pm, p | ·} = r(m/p)` if `p | m` and `0` otherwise.

(2.3) `r(pm) = (1 + ε_p) r(m) − ε_p [p | m] r(m/p)` for `m ≥ 1`. If `N(t) = pm` then `p | t t̄`. Case `ε_p = −1`: `p` is prime and `p̄ = p`, so `p | t`; use (2.2). Otherwise `p = π π̄` with `π` prime, so `π | t` or `π̄ | t`; each set has `r(m)` elements by (2.2). If `π ~ π̄` the two sets coincide. If not, `π | t` and `π̄ | t` force `p = ππ̄ | t`, and inclusion–exclusion with (2.2) gives `2r(m) − [p|m] r(m/p)`.

(2.4) Let `χ` be completely multiplicative with `χ(p) = ε_p` and `g(n) = ∑_{d|n} χ(d)`. Since `div(pm) = div(m) ∪ p·div(m)` with intersection `p·div(m/p)` (if `p | m`), `g` obeys the recursion (2.3). Induction on `n` through its least prime factor gives `r(n) = r(1) g(n)`.

(2.5) For odd `p`, `ε_p = (Δ/p)`. (i) If `N(x + yω) = p` then `p ∤ y` and `(2x + by)² ≡ Δ y² (mod p)`, so `Δ` is a square mod `p`. (ii) If `Δ ≡ c²`, take `2r ≡ b + c`; then `p | r² − br − a = N(ω − r)` while `p` divides neither `ω − r` nor its conjugate, so `p` is not prime and by (2.1) some element has norm `p`. (iii) For `N(π) = p`, `π = x + yω`: `π + π̄ = 2x + by`, so `π | π̄ ⟺ p | (2x + by)² ⟺ p | Δ` (using `4p = (2x+by)² − Δy²`, `p ∤ y`).

### 3. The Dirichlet series
For `Re s > 1`: `∑_{z ≠ 0} N(z)^{−s} = ∑ r(n) n^{−s} = r(1) ζ(s) ∑ χ(n) n^{−s}`. Splitting even and odd `n`, `(1 − ε₂ 2^{−s}) ∑ χ(n) n^{−s} = ∑_{n odd} χ(n) n^{−s}`. For odd `n`, `χ(n) = J(Δ | n)` (Jacobi symbol: both sides are multiplicative and agree on odd primes), and `J(Δ | n)` depends only on `n mod 4|Δ|` (quadratic reciprocity). So `∑_{n odd} χ(n) n^{−s} = ∑ Φ(n mod 4|Δ|) n^{−s}` with `Φ(j) = J(Δ | j)` for odd `j` and `0` for even `j`; by Hurwitz this continues to a function `L_Φ` holomorphic on `ℂ ∖ {1}`.

### 4. The Epstein expansion
With `α = b/2`, `k = √|Δ|/2`: `N(x + yω) = (x + αy)² + (ky)²`.

(4.1) Euler–Maclaurin: if `f, f′ ∈ L¹(ℝ)` then `∑_{n∈ℤ} f(θ + n)` converges absolutely and `|∑ f(θ+n) − ∫f| ≤ ∫|f′|` (on each unit interval `|f(c) − ∫_c^{c+1} f| ≤ ∫_c^{c+1}|f′|`).

(4.2) Row `y ≠ 0`, `T = k|y|`, `θ = αy`, `κ(u) = (T/(u² + T²))^s`: `∑_x N(x+yω)^{−s} = T^{−s} ∑_x κ(θ + x)`, `∫κ = T^{1−s} C(s)`, `|κ′| ≤ (|s|/T)(T/(u²+T²))^σ`, `∫ (T/(u²+T²))^σ = T^{1−σ} C(σ)`. Hence the row equals `T^{1−2s} C(s) + ρ_y(s)`, `|ρ_y(s)| ≤ |s| C(σ) T^{−2σ}`, and `ρ_y` is holomorphic on `σ > 1/2` (locally uniform majorant `(T/(u²+T²))^{σ₁} + (T/(u²+T²))^{σ₂}`).

(4.3) Row `y = 0` is `2ζ(2s)`. Summing over `y` for `Re s > 1`:
`E(s) = 2ζ(2s) + 2k^{1−2s} C(s) ζ(2s−1) + R(s)`, `R = ∑_{y≠0} ρ_y` holomorphic on `σ > 1/2`, `|R(s)| ≤ |s| C(σ) k^{−2σ} Z(2σ)`.

### 5. Conclusion
On `Re s > 1`: `(1 − ε₂2^{−s})(2ζ(2s) + 2k^{1−2s}C(s)ζ(2s−1) + R(s)) = r(1) ζ(s) L_Φ(s)`. Both sides are holomorphic on the connected set `{σ > 1/2, s ≠ 1}`, so the identity holds there. At `ρ` the right side vanishes and `|ε₂ 2^{−ρ}| < 1`, so `2ζ(2ρ) + 2k^{1−2ρ}C(ρ)ζ(2ρ−1) + R(ρ) = 0`. If `k ≥ 1` then `k^{−2β} ≤ k^{1−2β}` and `|ζ(2ρ)| ≤ k^{1−2β} A(ρ)`; `ζ(2ρ) ≠ 0` because `Re 2ρ > 1`. So `k^{2β−1} ≤ A(ρ)/|ζ(2ρ)|` and `|Δ| = 4k² ≤ D(ρ)`. If `k < 1` then `|Δ| < 4 ≤ D(ρ)`. ∎

### Corollary
If RH fails there is a zero with `β > 1/2`, so the discriminants of class-number-one quadratic fields with `disc < 0` are bounded. Contrapositive: unbounded ⇒ RH.

## Not formalized, by decision
- "Finitely many `h = 1` fields ⇒ RH" is not a theorem (it is the converse of the corollary; as an implication from a true statement it is equivalent to RH).
- Baker–Heegner–Stark (exactly nine fields) and the numerical remark about `π√163 ≈ 40.1`.
- Open extension: Mordell–Heilbronn (`h(d) → ∞` if RH fails) needs the same expansion for every reduced form and the full class-group decomposition of `ζ_K`.

## Log
- 2026-11-20 — created in 1-in-progress with the paper proof; Lean formalization started in `formal/GaloisForLFunctions/RHTower/Deuring/`
