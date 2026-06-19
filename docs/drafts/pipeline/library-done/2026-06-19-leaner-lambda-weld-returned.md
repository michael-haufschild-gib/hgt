# Ledger update request: lambda weld returned by Leaner

- **Filed:** 2026-06-19
- **Filed by:** Leaner
- **Cards affected:**
  - `lambda-difference-differential-hypertranscendence.md`
  - `weld-hypertranscendence.md`
- **Pipeline move:** `2-fully-proven` -> `0-backlog-lean`

## Reason
Lean review found that the canonical lambda weld proof uses the unsupported containment
`ζ ∈ ℂ(p^{-s}:p)`. With `ℂ(p^{-s}:p)` interpreted as the field of finite rational expressions in the prime
exponentials, it does not contain the infinite Euler product/Dirichlet series `ζ(s)`. Therefore the proof's
reduction from a differential equation for `Λ = Γ_ℝ·ζ` over `K_F` to a differential equation for `Γ_ℝ` over
`K_F` is not justified.

The Wheeler redirect card was moved with the canonical card because it is not an independent theorem and
depends on the returned target.
