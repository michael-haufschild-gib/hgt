# OWU: the real cut is exactly the even mean-zero deficit

- **ID:** owu-cut-is-even-mean-zero-deficit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU, Need "remove the real cut";
  successor of `3-formalized/owu-odd-spectral-measure-2026-10-16.md`
- **Statement (target):** Let `lam` be odd Weil-positive with odd Nevanlinna data `(ν, c)` of
  `aΨ(½+a)`, `z = a²`. Then for EVERY `C²` compactly supported test `f` (any parity)
  `Re W_lam(f ⋆ f̃) = ∫ Θ_f dν − c|f̂(0)|²`, with
  `Θ_f = [(1+γ²)(|f̂(√γ)|² + |f̂(−√γ)|²)/2 − |f̂(0)|²]/γ` on the critical ordinates and
  `Θ_f = [|f̂(0)|² − (1+γ²) Re(f̂(−i√(−γ)) conj f̂(i√(−γ)))]/(−γ)` on the cut.
  Consequently:
  1. (cut removal) if `W_lam ≥ 0` on all even tests with `f̂(0) = 0`, the cut measure vanishes:
     `ν{ζ ≠ 1, −¼ ≤ γ < 0} = 0`;
  2. (converse) if the cut measure vanishes, `W_lam ≥ 0` on every test with `f̂(0) = 0`;
  3. (extension) if the cut measure vanishes, the Weil function extends holomorphically to
     `Re s > ½`, so by the square-root transfer `λ = Λ` and RH follow from `Ψ ≥ 0` on `(½,∞)`.

## Why this is structural

The odd spectral measure showed that cut mass enters every odd test with the positive weight
`(1+γ²)|f̂(i√(−γ))|²/(−γ)`, so no odd test can remove it. On the even mean-zero tests the same
cut mass enters with the NEGATIVE weight `−(1+γ²)|f̂(i√(−γ))|²/(−γ)`. A two-bump even test
`f_L = b(·−L) − 2b + b(·+L)` has `f̂_L(v) = (2cos(Lv) − 2) b̂(v)` on the critical line (bounded,
with `(1−cos Lv)²/v² ≤ 2L²`) but `f̂_L(ir) = (2cosh(Lr) − 2) b̂(ir)` on the cut (growth `L⁴r⁴`).
So positivity on even mean-zero tests forces the cut to vanish: the Paley–Wiener dichotomy
between the real and imaginary axes amplifies real singularities. This is the Landau mechanism
("real singularities dominate") realised inside the Weil form. The real cut, which the frontier
listed as needing the archimedean term and the prime support, is exactly the even mean-zero
deficit of the weight: `{odd-positive, cut-free} = {Weil-positive on the hyperplane f̂(0) = 0}`.

## Paper proof

1. The spectral formula of the odd card never used oddness except for `H(½) = |f̂(0)|² = 0`;
   for a general test the `c`-term is `c · (1/2π)∫ F/(w−½) = c H(½) = c|f̂(0)|²`.
2. Per-point evaluation as before with `H(½) = |f̂(0)|²`, `H(½ ± i√γ) = |f̂(±√γ)|²`,
   `H(½ ± r) = f̂(∓ir) conj f̂(±ir)`.
3. For `f̂(0) = 0`: `Θ_f ≥ 0` on critical ordinates, at the centre (limit along `bdryPt(1/(n+1))`)
   and at `ζ = 1`; on the cut for even `f`: `Θ_f = −(1+γ²)|f̂(i√(−γ))|²/(−γ) ≤ 0`.
4. Cut removal: with `f_L` as above, `0 ≤ ∫Θ_{f_L} dν ≤ 8L²C_b ν(S¹) − 4(∫b)²(2cosh(Lr₀)−2)² ν(cut_{r₀})`
   where `cut_{r₀} = {ζ ≠ 1, −¼ ≤ γ ≤ −r₀²}` and `C_b = ‖b‖₁² + ‖b''‖₁²`; `2cosh(u) − 2 ≥ u²`
   gives `ν(cut_{r₀}) ≤ 2C_b ν(S¹)/((∫b)² r₀⁴ L²) → 0`. Countable union over `r₀ = 1/k`.
5. Extension: with `ν` supported on `{γ ≥ 0} ∪ {1}`, `g(z) = ∫ (γz−1)/(z+γ) dν + ν{1} z − c` is
   holomorphic on `ℂ ∖ (−∞, 0]` (dominated differentiation), and `Ψ̃(s) = g((s−½)²)/(s−½)` is
   holomorphic on `Re s > ½`, equal to the Weil function on `Re s > 1` by the identity theorem.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [ ] 1 → 2  paper proof above (to be checked against Lean)
- [ ] 2 → 3  Lean

## Conjecture ledger
(empty)

## Log
- 2026-10-16 — created
