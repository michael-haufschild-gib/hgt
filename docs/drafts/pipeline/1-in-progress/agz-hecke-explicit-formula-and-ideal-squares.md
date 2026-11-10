# The explicit formula of a Hecke L-function and the square of a ring through its ideals

- **ID:** agz-hecke-ef
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme step
- **Source:** `docs/reports/review-1011/fable.md` §9.5 question 7, §9.8 step 4; programme card
  `../3-formalized/agz-absolute-geometry-of-spec-z.md`
- **Statement:** for a number field `K`, a modulus `𝔪` and a primitive ray class character `ψ`,
  the zeros of the completed `L(s, ψ)` satisfy Weil's explicit formula
  `Σ_ρ m_ρ H_k(ρ) = [ψ = 1](H_k(0) + H_k(1)) + (1/2π)∫ k̂(r) B_ψ(r) dr
  − Σ_n n^{−1/2}(a_ψ(n) k(log n) + conj a_ψ(n) k(−log n))`,
  `a_ψ(n) = Σ_{N𝔞 = n} Λ_K(𝔞) ψ(𝔞)`, and the square of a ring through its ideals (a class
  character; a ring that is not abelian over `ℚ`, through its Dedekind zeta function) has the
  index law.

## Goal
Question 7 of the `𝔽₁` programme: ideals as degree points, the characters of the class group,
and one ring that is not abelian. The tool that the corpus lacks is the explicit formula of a
Hecke `L`-function. The corpus has the completed functional equation
(`HeckeLFunctions.heckePoleClearedCompletion_reflection`), the Euler product, and the abstract
analytic tools below.

## Gates
- [ ] P1 two lines weigh the zeros of an order-one function (abstract)
- [ ] P2 arithmetic form: pole pair, archimedean factor moved to the critical line, two Dirichlet
      series (abstract, a function and its dual)
- [ ] P3 Hecke inputs: (a) `−L'/L(s, ψ) = Σ a_ψ(n) n^{−s}`; (b) order one of the completed
      function; (c) zeros in the closed strip; (d) the archimedean bracket
- [ ] P4 the explicit formula of `L(s, ψ)`; the zero configuration; temperedness
- [ ] P5 consumers: the pairing of the ideals twisted by a class character; the index law of a
      ring through its Dedekind zeta function; one ring that is not abelian

## Approach

Notation: `H_k(s) = ∫ k(u) e^{(s − 1/2)u} du` (`Zeta23.WeilEF.Hfn`), `ρ_q` the zeros of `E` with
multiplicity (`ZeroCopy (fun z => E (z + 2))`, shifted by `2`).

**P1.** Let `E` be entire with `‖E(s)‖ ≤ exp(C(1 + |s|) log(2 + |s|))`, `E(2) ≠ 0`, all zeros in
`0 ≤ Re s ≤ 1`, `1 < c ≤ 2`, and `H` entire with `|H(σ + it)| ≤ D(1 + t²)^{−2}` on
`−1 ≤ σ ≤ 2`. Then
`Σ_q H(ρ_q) = (1/2π)(∫ H(c + it) E'/E(c + it) dt − ∫ H(1 − c + it) E'/E(1 − c + it) dt)`.

*Proof.* Hadamard (`OrderOneHadamard.exists_expAffine_mul_hadamardProduct`) gives at every
non-zero `s`: `E'/E(s) = a + Σ_q (1/(s − ρ_q) + 1/(ρ_q − 2))`, absolutely convergent, with
`Σ_q |ρ_q − 2|^{−2} < ∞`. For one `q`, `two_line_simple_pole` gives
`∫ H(c + it)/(c + it − ρ_q) − ∫ H(1 − c + it)/(1 − c + it − ρ_q) = 2π H(ρ_q)`, and the two line
integrals of `H` agree (`vertical_line_shift`), so the constants `1/(ρ_q − 2)` and `a` drop out
of the difference of the two lines. Summation over `q` under the integral: on either line
`|s − ρ_q| ≥ c − 1` and `|ρ_q − 2| ≤ |s − ρ_q| + |s − 2|`, hence
`|1/(s − ρ_q) + 1/(ρ_q − 2)| ≤ |s − 2|(1 + |s − 2|/(c − 1)) / |ρ_q − 2|²`, which against the decay
of `H` is integrable in `t` and summable in `q`.

**P2.** Let moreover `E(1 − s) = W Ẽ(s)`, `W ≠ 0`, and on `Re s > 1`
`E'/E = m g₀ + G − Σ a(n) n^{−s}`, `Ẽ'/Ẽ = m g₀ + G − Σ ã(n) n^{−s}`,
`g₀(s) = 1/s + 1/(s − 1)`, `G` holomorphic on `Re s > 0` with `|G(σ + it)| ≤ C log(2 + |t|)` on
`1/2 ≤ σ ≤ 3/2`, both series absolutely convergent at `c`, `1 < c ≤ 3/2`. Then for `k ∈ C_c²`
whose transform decays to fourth order

`Σ_q H_k(ρ_q) = m(H_k(0) + H_k(1)) + (1/2π)∫ k̂(t)(G(1/2 + it) + G(1/2 − it)) dt
− Σ_n n^{−1/2}(a(n) k(log n) + ã(n) k(−log n))`.

*Proof.* `E'/E(1 − s) = −Ẽ'/Ẽ(s)`; substitute `t ↦ −t` on the left line. The pole pair is
`two_line_pair`, the factor `G` is `ThmE.line_shift_generic`, the series are
`hasSum_prime_side_line` for `k` and for `u ↦ k(−u)`.

**P3.** (a) `a_ψ = Σ_{N𝔞 = n} Λ_K(𝔞)ψ(𝔞)`; the convolution identity
`Σ_{𝔟 | 𝔞} Λ_K(𝔟) = log N𝔞` twisted by the multiplicative `ψ` gives
`a_ψ ⍟ c_ψ = log · c_ψ`, hence `L' = −L · Σ a_ψ(n) n^{−s}`. (b) On a vertical strip the
continued Mellin transforms `WeakFEPair.Λ₀` are bounded (the Mellin integral of the norm at the
two edges), the class weights are exponentials, so the pole-cleared completion is `O(|s|²)` on
`−1 ≤ Re s ≤ 2`; right of the strip the Gamma product is bounded by its value on the real axis
and the Dirichlet series is bounded; left of it the functional equation. (c) Euler product right
of `1`, functional equation left of `0`. (d) `E = [s(s − 1)] N^{s/2} Π_v Γ_ℝ(s + κ_v) Γ_ℂ(s)^{r₂} L`,
`Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s + 1)`; `ThmE.archChi_bracket` evaluates each factor on the critical line.

## Log
- 2026-11-10 — created; corpus tools located (Hadamard pairs, two-line pole identity, generic
  line shift, prime side on a line of absolute convergence).
