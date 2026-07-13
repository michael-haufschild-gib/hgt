# Hypertranscendence: the founding notion of the branch (formal home)

- **ID:** hypertranscendence-founding
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean; built because absent from mathlib AND the tree
- **Statement:** Gives the field's founding notion (Hölder 1887) a formal definition, previously absent:
  - `DifferentiallyAlgebraic f := ∃ n P≠0, ∀z, P(f, f', …, f⁽ⁿ⁾)(z) = 0` (algebraic differential equation: P a nonzero polynomial in the FULL jet (s, f, f', …, f⁽ⁿ⁾) — s is jet variable 0, matching Hölder's classical statement — via MvPolynomial (Fin (n+2)) + iteratedDeriv).
  - `Hypertranscendental f := ¬ DifferentiallyAlgebraic f`.
  - `differentiallyAlgebraic_of_algebraic`: an algebraic function (root of a nonzero univariate P) is differentially algebraic (order-0 relation).
  - `hypertranscendental_imp_transcendental`: hypertranscendental ⟹ transcendental — the "hyper" strictly strengthens "transcendental", justifying the name.
  - `differentiallyAlgebraic_exp`: exp is DA (y'−y=0) — non-vacuity; the class strictly contains the polynomials.
- **Lean:** `GaloisForLFunctions.{DifferentiallyAlgebraic, Hypertranscendental, differentiallyAlgebraic_of_algebraic, hypertranscendental_imp_transcendental, differentiallyAlgebraic_exp}` in `formal/GaloisForLFunctions/HTGeometry/Hypertranscendence.lean`. Axiom-clean.

## What this is
The mission's core object had no formal definition anywhere in the tree (grep-verified) or mathlib. This supplies it and proves the structural fact that anchors the name (hyper ⟹ ordinary transcendence), plus a non-vacuity witness. The frontier statement it sets up — Γ is hypertranscendental (Hölder) — is now expressible: `Hypertranscendental Complex.Gamma`.

## Log
- 2026-07-08 — created (founding notion absent from mathlib/tree; built per standing order).

## Update: general exponential DA + Hurwitz superposition
- `differentiallyAlgebraic_cexp_linear (c)`: every exp(c·s) is DA (y'−c·y=0), generalizing the exp witness; `differentiallyAlgebraic_exp` is now the c=1 corollary.
- (in HurwitzShiftedBridge) `differentiallyAlgebraic_hurwitzMonomial n`: each Hurwitz coefficient exp(−s·log(n+a)) is DA — so ζ(a,·) is an infinite superposition of DA monomials. Whether the sum leaves the DA class (ζ hypertranscendental) is the frontier. Axiom-clean.
