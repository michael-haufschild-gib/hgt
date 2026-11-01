# Direct arithmetic-coordinate and differential-equation shortcuts

- **Status:** Precise obstructions and positive survivors certified.
  The nonlinear period approach remains open.
- **Scientific status:** Audit of existing formalized mathematics, not new theorems.

## Algebraic prime coordinates

For nonreal `ρ`, three distinct prime powers `p^ρ,q^ρ,r^ρ` cannot all be
algebraic. They therefore cannot supply the algebraic torus point required by
the cited Baker first-jet theorem. This closes its direct application to three
or more prime coordinates at a nonreal zero.

The obstruction is `SixExponentials.not_all_three_prime_cpow_isAlgebraic`.

**Positive survivor:** at an algebraic torus point with algebraic coefficients,
the scalar logarithmic first derivative detects every coordinate partial
derivative simultaneously. Value plus first derivative therefore recover the
entire first-order vanishing condition. This exact first-jet law remains usable
if an arithmetic realization supplies a suitable torus point independently.
Lean: `algebraic_primeLogTrace_firstJets_vanish_iff`; paper and Lean proofs exist,
and its transitive axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`.

## Finite differential equations

Zeta is hypertranscendental over `ℂ(s)⟨Γ⟩`. Adjoining differentially algebraic
coefficients preserves the relevant obstruction when all carriers and derivations
are realized in the same field. Constant periods already belong to `ℂ`.

**Positive survivor:** maximal differential rank. The entire family of reciprocal
integer dilates `1/ζ(ms)`, `m≥2`, remains differentially independent over
`ℂ(s)⟨ζ⟩`, with its analytic coefficient realization proved. Thus a plain finite
polynomial differential relation among integer dilates is unavailable too.

Lean anchors:

- `zeta_hypertranscendentalOver_gammaCoefficientField`;
- `hypertranscendentalOver_iteratedDifferentialAdjoin_iff`;
- `dilatedMoebiusTail_relativeDifferentialIndependent`;
- `LSeries_completeResolutionNormalizedArithmetic`.

## Boundary and validation

No theorem here excludes a mixed relation with additional transcendental variable
periods, a suitable q-difference realization, or special-value period relations.
The canonical Xi–Böttcher coupling and its source trivialization remain missing.
Unmarked Böttcher multiplier groups alone give the same Prüfer group for every
disconnected quadratic basin.

All obstruction and differential-independence declarations, plus the exact Böttcher
image theorem, passed transitive axiom audits: only `propext`, `Classical.choice`,
`Quot.sound`. Their paper arguments and Lean formalizations already exist in the
corpus; no duplicate wrappers were added.
