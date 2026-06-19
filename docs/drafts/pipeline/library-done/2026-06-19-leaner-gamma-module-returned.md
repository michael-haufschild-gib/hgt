# Ledger update request: gamma-module-construction returned by Leaner

- **Filed:** 2026-06-19
- **Filed by:** Leaner
- **Card affected:** `gamma-module-construction.md`
- **Pipeline move:** `2-fully-proven` -> `0-backlog-lean`

## Reason
Lean review found a determinant/inverse-determinant error in the ζ-regularized determinant step. Lerch's
formula gives

`ζ_H'(0,a)=log Γ(a)-1/2 log(2π)`,

so the standard ζ-regularized product/determinant is

`exp(-ζ_H'(0,a)) = √(2π)/Γ(a)`.

That is reciprocal to `Γ(a)` up to the constant, not `Γ(a)` itself. The recurrence and logarithmic
connection identities can still be valid subclaims, but the full card is not proved as stated until the
determinant convention/operator and `π^{-s/2}` normalization are repaired.
