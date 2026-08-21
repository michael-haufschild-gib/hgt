# Hilbert's irreducibility theorem (ℚ is Hilbertian)

- **ID:** hilbert-irreducibility-theorem
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) — classical; target is an unconditional Lean 4 proof
- **Source:** user goal 2026-08-21; gates the two top-level cards listed in `toplevel-2fp-remaining-ten`
- **Statement:** For `f ∈ ℚ[X][Y]` irreducible with `deg_Y f ≥ 1`, the set of `b ∈ ℚ` with
  `f(b, Y) ∈ ℚ[Y]` irreducible is infinite.

## Goal
Mathlib has **no** Hilbert irreducibility theorem and no notion of Hilbertian field
(`grep -ril "hilbertian"` over the 8264 mathlib files is empty; `Mathlib/FieldTheory/` contains no
`Hilbert` occurrence). The corpus therefore has to own the whole theorem.

## Gates
- [x] 0 → 1  in-progress: route fixed, all analytic inputs located
- [ ] 1 → 2  fully-proven on paper (route below is complete and checked)
- [ ] 2 → 3  formalized: Lean theorem `hilbert_irreducibility`, umbrella-wired, axiom-clean
- [ ] 3 → 4  publication-ready

## Route (frozen)

**Not** the p-adic ramification route recorded in
`memory/hilbert-irreducibility-programme.md`. That route is *provably insufficient*: a single prime
can only kill roots that lie on ramified branches, several primes only force the specialised Galois
group to *meet* the inertia classes (conjugacy ambiguity + Jordan's theorem is not enough), and
`X⁴+1` shows no purely local criterion can ever certify irreducibility (it is reducible over every
`ℚ_p`). HIT needs a global argument. The local half already built
(`HTGeometry/PadicRamifiedSpecialisation.lean`) stays as an independent asset.

The frozen route is the elementary analytic proof of **Coleman–Zwald**,
*Hilbertian fields and Hilbert's irreducibility theorem*, arXiv:1809.10977, Theorem 7 (itself a
cleaned-up Hilbert/Dörge argument). Skeleton, in the exact form to be formalised:

Let `n = deg_Y f ≥ 1`. Pick `s₀ ∈ ℚ` with `a_n(s₀) ≠ 0` and `f(s₀, ·)` separable.

1. **Analytic branches.** On a disc `N ∋ s₀` there are analytic `u₁,…,u_n : N → ℂ` with
   `f(s,Y) = a_n(s)·∏ᵢ (Y − uᵢ(s))` and the `uᵢ(s)` pairwise distinct.
   *Engine: the corpus already owns this* — `U0.HolomorphicIFT.holo_implicit` (analytic implicit
   function theorem) + `HolomorphicIFT.root_complete`; cf. `HTGeometry/BivariateRootCovering.lean`.
2. **Subset coefficients.** For `∅ ≠ S ⊊ Fin n` put `β_S(s) = ∏_{i∈S}(Y − uᵢ(s)) ∈ ℂ[Y]`, with
   analytic coefficient functions `y_{S,k}`.
   *Step 1:* for each `S` some `y_{S,k}` is **not** a rational function over ℚ near `s₀`.
   Proof: if all were, clearing denominators gives `Bhat ∈ ℚ[X][Y]` with `deg_Y Bhat = |S|`,
   `0 < |S| < n`, and `Bhat(s,·) = D(s)·β_S(s,·)` near `s₀`. `f` is irreducible in `ℚ(X)[Y]`
   (Gauss) and `f ∤ Bhat` by degree, so `IsCoprime f Bhat`; Bezout + clearing denominators gives
   `U·f + V·Bhat = C w`, `0 ≠ w ∈ ℚ[X]`. Evaluating at a good `s` near `s₀` makes the monic
   degree-`|S|` polynomial `β_S(s,·)` divide the nonzero constant `w(s)`. Contradiction.
   *Step 2:* if `s ∈ N ∩ ℚ` and `y_{S,k}(s) ∉ ℚ` for the chosen `(S,k)` for every `S`, then
   `f(s,Y)` is irreducible in `ℚ[Y]` (a rational factor would have root set `{uᵢ(s)}_{i∈S}`).
3. **Algebraicity + integrality.** Each `y_{S,k}` is integral over `ℚ[X][1/a_n]` inside the germ
   ring `Filter.Germ (𝓝 s₀) ℂ` (each `uᵢ` is, and `IsIntegral.add/mul` close it up), so there is
   `0 ≠ P ∈ ℚ[X][Y]`, `deg_Y P = m ≥ 1`, with `P(s, y(s)) = 0` near `s₀`.
   Substituting `X ↦ s₀ + 1/T` and clearing (`Polynomial.taylor` + `Polynomial.reflect`) gives
   `0 ≠ P̃ ∈ ℚ[T][Y]` with `P̃(t, δ(t)) = 0`, `δ(t) := y(s₀+1/t)`. Scaling to a monic **integer**
   relation gives `dpoly ∈ ℚ[T]` and monic `Q ∈ ℤ[T][Y]` with `Q(t, z(t)) = 0`,
   `z(t) := dpoly(t)·δ(t)`; hence `t ∈ ℤ` and `δ(t) ∈ ℚ` force `z(t) ∈ ℤ` (rational root theorem).
4. **Trichotomy on `z`.** Write `z(t) = t^L·G(1/t)` with `G` analytic at `0`, `L = deg dpoly`.
   Let `Ḡ(x) := conj (G (conj x))`.
   - **(b)** `G ≠ Ḡ` as germs: `analyticOrderAt (G − Ḡ) 0 = k₀ < ∞` gives
     `Im G(x) ≠ 0` for small real `x > 0`, so `z(t) ∉ ℤ` for all large `t`. Finitely many bad `t`.
   - **(a)** `G = Ḡ` and `G` equals its degree-`≤L` Taylor polynomial `Gpoly`: then `z` is a
     polynomial in `t` of degree `≤ L`. If all its coefficients were rational, `y` would be a
     rational function — excluded by Step 1. So one coefficient is irrational and Lagrange
     interpolation bounds the number of integers `t` with `z(t) ∈ ℚ` by `L`. Finitely many bad `t`.
   - **(c)** `G = Ḡ`, `H := G − Gpoly ≠ 0`: `H(x) = x^K·h(x)`, `h(0) ≠ 0`, `K > L`. With
     `ν := K − L ≥ 1`, `m := L+1`, the recursion `A₀(x) := x^ν h(x)`, `A_{j+1}(x) := −x²A_j'(x)`
     satisfies `z^{(j)}(t) = A_j(1/t)` and `A_j(x) = x^{ν+j}h_j(x)` with
     `h_j(0) = (−1)^j ν(ν+1)⋯(ν+j−1)h(0) ≠ 0`. Hence `0 < |z^{(m)}(t)| < 2|p|/t^q` eventually,
     with `q = ν+m`, `p = h_m(0)`.
     **Gap lemma.** If `t₀<⋯<t_m` are integers `> T` with every `z(tᵢ) ∈ ℤ`, then the integer
     determinant `W_m` (columns `1,t,…,t^{m−1}, z(t)`) is nonzero by the divided-difference mean
     value theorem `W_m/V_m = z^{(m)}(u)/m!`, so `|V_m| ≥ m!·t₀^q/(2|p|)`, and since
     `|V_m| ≤ (t_m−t₀)^{binom(m+1,2)}` we get `t_m − t₀ > α t₀^β`. So any interval
     `[U, U+rm]` with `U` large contains at most `m` integers `t` with `z(t) ∈ ℤ`.
5. **Assembly.** Over the finitely many `(S,k)` pairs, cases (a),(b) exclude finitely many `t`;
   case (c) functions exclude at most `rm` integers from each window `[U, U+rm]` which contains
   `rm+1` integers. So infinitely many integers `t` survive; `b = s₀ + 1/t` are infinitely many
   distinct rationals with `f(b,Y)` irreducible. ∎

## Lean module plan (`HTGeometry/HilbertIrreducibility/`)
| # | module | content | state |
|---|---|---|---|
| 1 | `AnalyticBranches` | analytic root branches + product formula on a disc | |
| 2 | `GermIntegral` | `y` integral over `ℚ[X]` in the germ ring ⇒ `0 ≠ P ∈ ℚ[X][Y]` | |
| 3 | `ReflectSubstitution` | `X ↦ s₀+1/T`; `taylor`/`reflect` evaluation identity | |
| 4 | `MonicIntegerRelation` | monic `Q ∈ ℤ[T][Y]`, `z(t) ∈ ℤ` | |
| 5 | `DividedDifference` | Vandermonde/`W_m/V_m = f^{(m)}(u)/m!` (iterated Rolle) | **DONE** |
| 6 | `RationalInterpolation` | poly with `deg+1` rational values at rationals is rational | **DONE** |
| 7 | `TaylorTail` | `A_j` recursion, order bookkeeping, `thin_or_eventually_poly` (cases a/c) | **DONE** |
| 8 | `ThinSets` | gap-thin sets + the window-packing assembly | **DONE** |
| 9 | `Core` | case (b) + assembly: finitely many non-rational algebraic germs ⇒ infinitely many good `t` | |
| 10 | `SubsetCoefficients` | Step 1 and Step 2 | |
| 11 | `Main` | `hilbert_irreducibility` | |

## Log
- 2026-08-21 — `ThinSets`, `DividedDifference`, `RationalInterpolation`, `TaylorTail` all green
  (`lake env lean`).  `TaylorTail.thin_or_eventually_poly` is the analytic heart: cases (a)/(c).
  Remaining: case (b) (complex→real), the algebraic-relation layer, subset coefficients, main.
- 2026-08-21 — created; mathlib absence verified; p-adic route retired with reason; Coleman–Zwald
  route frozen; corpus analytic engine (`U0.HolomorphicIFT`) located.
