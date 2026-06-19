# Ledger update request: flow-constraint-asymmetry returned by Leaner

- **Filed:** 2026-06-19
- **Filed by:** Leaner
- **Card affected:** `flow-constraint-asymmetry.md`
- **Pipeline move:** `2-fully-proven` -> `0-backlog-lean`

## Reason
Lean review found that the card's flow-inert consequence is not proved as written. The proof correctly notes
that each individual generator `p^{-s}` is D-finite, so the finite-rational prime-exponential field
`ℂ(s,{p^{-s}})` is differentially algebraic over `ℂ(s)`. But this does not put the infinite Euler
product/Dirichlet series `ζ(s)` in that field, and it does not justify reducing a differential or
difference-differential equation for `Λ=Γ_ℝ·ζ` to one for `Γ_ℝ`.

The constraint-loaded half remains supported by the Lean finite-character facts; the returned issue is the
unstated `ζ`/no-cancellation step in the flow-weld consequence.
