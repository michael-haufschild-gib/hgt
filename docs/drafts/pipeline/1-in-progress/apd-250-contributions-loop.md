# APD conjecture loop (250 contributions)

- **ID:** apd-250-contributions-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card)
- **Source:** `formal/GaloisForLFunctions/ArithmeticPositiveDuality/README.md` §8–§10
- **Statement:** Answer the open APD topics with unconditional Lean theorems, one conjecture at a
  time; log every success and failure in `logs/apd-250-2026-10-25.md`.

## Goal
Each item: positive side, spectral side, gap, integer; inserted or intrinsic charge; depth scaling;
battery behaviour (README §10).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  (per conjecture)
- [ ] 2 → 3  (per conjecture)

## Current conjecture
**C1 (topic 6, prescribed successor).** If `φ` is positive definite on `Aff(ℚ)` and
`φ(x ↦ x + b) = 1_ℤ(b)`, then for `u = ±n/d` in lowest terms
`Σ_{b mod (1/d)ℤ} |φ(x ↦ ux + b)|² ≤ 1/(nd)`; equality for the adelic Haar state
`φ_*(ux + b) = (nd)^{−1/2}·1[db ∈ ℤ]`. Corollary: no positive-definite `φ` with successor part
`c·1_ℤ`, `c ≠ 0`, has a dilation part continuous at `1`.

Paper proof. Write `X = d⁻¹Σ_{j<d} π(j/d)ξ`, `Y_b = n⁻¹Σ_{k<n} π(b + k/d)π(u)ξ` in the GNS space.
`φ` is `ℤ`-bi-invariant (three-point Gram), so `φ(u, ·)` is `(ℤ + uℤ) = (1/d)ℤ`-periodic. Gram
entries: `⟨X, X⟩ = 1/d`, `⟨Y_b, Y_{b'}⟩ = n⁻¹[b ≡ b' mod (1/d)ℤ]`, `⟨Y_b, X⟩ = φ(u, b)`. Bessel
(the Gram form with coefficients `1, −n φ(u,b)`) gives `1/d − n Σ|φ(u,b)|² ≥ 0`. Sharpness: the
finite-level model `ℂ^{(1/M)ℤ/Mℤ}` of `L²(𝔸_f)` with `v_g(x) = |a|_f^{1/2} e(bx) 1[ax ∈ ℤ]`;
Gram `= M⁻¹ V V^*`, entries evaluated by a geometric sum over the cyclic group
`a_g⁻¹ℤ ∩ a_h⁻¹ℤ`.

## Log
- 2026-10-25 — created; C1 opened.
