# Arithmetic Bernstein at left exponent one

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/notes.md`, Next-Cycle Conjecture Plan 2.
- **Statement:** Does continuity, all-base torus positivity and `|f(y)| ≤ C exp(-y)` for `y ≤ 0` force exponential convexity?

## Statement audit

`IsAllBaseTorusPositive` is defined using an unconditional `tsum`; no convergence or right-decay assumption occurs in its definition. Existing Bernstein implications separately require right decay. First decide whether the proposed statement survives this distinction.

## Counterexample and positive survivor

Take `f(y)=1+cos(y)/2`. Then `1/2 ≤ f ≤ 3/2`, so the proposed left bound holds.
At `t₁=π/2`, `t₂=3π/2`, coefficients `(1,-1)` give Hankel form `-2`.

For `Uₖ=cosSum θ k`, the recurrence conserves
`Uₖ₊₁²+Uₖ²−2 cos(θ) Uₖ₊₁Uₖ=1`. Hence `Uₖ₊₁²+Uₖ²≥1/2`; the characters cannot tend to zero.
Any amplitude with `|f|≥c>0` therefore makes every nonempty torus series nonsummable
(restrict to one prime-power coordinate). Its totalized sum is zero. Thus, on this whole class,
`IsAllBaseTorusPositive f ↔ ∀ y, 0≤f(y)`.

The stronger damping consequence distinguishes this degeneration from the convergent cone:
`exp(-αy) f(y)` fails torus positivity for every `0<α≤1`. For each `α>1`, sufficiently small
positive cosine perturbations re-enter the cone, by the existing oscillatory dichotomy.

## No-go closure

- **Killing theorem:** `exists_boundary_torusPositive_not_expConvex`.
- **Positive survivor:** `allBaseTorusPositive_iff_nonneg_of_abs_floor` classifies the entire
  nonvanishing class. `exists_oscillation_damping_reentry` exhibits passage out of and back into
  the unrestricted cone; `cosSum_conserved_form` and `cosSum_adjacent_energy` identify the
  exact recurrence obstruction.
- **New insight:** A totalized torus inequality is not a convergence certificate. The omitted
  decay assumption cannot be removed from the positive-kernel damping law.
- **Paper proof:** Complete above, using the already formalized oscillatory Bernstein dichotomy
  for damping and re-entry.
- **Lean:** `ArithmeticInnerFunctionTheory/TorusConvergenceAndBoundary.lean`; final
  `lake --old env lean` audit passed. Main transitive axiom sets are exactly
  `propext`, `Classical.choice`, `Quot.sound`.

The endpoint classification with genuine convergence/right decay remains a distinct open question.
