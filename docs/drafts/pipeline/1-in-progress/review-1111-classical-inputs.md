# Classical inputs from review-1111

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, Classical inputs to formalize.
- **Acceptance:** Unconditional proofs on the actual objects, direct Lean checks, umbrella imports.

| Task | Required conclusion | Status |
|---|---|---|
| A115 | Newton polygon of the Carlitz–Goss zeta function from the greedy optimum | **Formalized** for every `q = p^s` and every `z ∈ ℤ_p`: `gossZetaNeg_eq_prod` (`z ∈ ℕ`), `gossZeta_riemannHypothesis` (`z ∉ ℕ`). See `../3-formalized/carlitz-goss-rh-from-greedy-compositions.md`. |
| A26 | Modular Weyl asymptotic `N(Λ) ∼ Λ/12` | open |
| A59 | Primes in short intervals in every reduced residue class | open |
| A120 | Selberg zeta function of a surface with a small eigenvalue: Euler product and functional equation, zero off the line | open |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics | open |
| A33 | Fourier coefficients of the cubic residue at all heights | open |
| A18 | Twisted second moments past the square root | open (below `1/2` formalized: `../3-formalized/twisted-second-moments-below-square-root.md`) |
| A21 | Logarithmic two-point Chowla | open |
