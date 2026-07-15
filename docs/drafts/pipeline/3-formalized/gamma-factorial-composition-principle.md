# Gamma factorial-composition principle

- **ID:** gamma-factorial-composition-principle
- **Stage:** 3-formalized
- **Type:** STRUCTURE THEOREM · HYPERTRANSCENDENCE DETECTOR
- **Status:** `[PROVEN] [LEAN FORMALIZED]`
- **Statement:** Let `u : ℂ → ℂ` be analytic on the right half-plane.  If its germ at `1` satisfies
  no nonzero polynomial-coefficient algebraic differential equation, then `z ↦ u(Γ(z))` satisfies
  no global algebraic differential equation.  Stronger, no fixed nonzero differential polynomial
  can vanish eventually along every factorial microscope in the left half-plane.  Forward form:
  any such relation for `u ∘ Γ` reflects to one nonzero polynomial jet constraint for `u` on the
  entire right half-plane.

## Goal

Extract the source-specific theorem behind the new `ψ ∘ Γ` result.  The negative-integer poles of
Gamma force the exact factorial scale `sₙ = (-1)^(n+1)/n!`; under this scale, `Γ(-n+sₙx) → -1/x`.
Thus any ADE for `u ∘ Γ` degenerates to a nonzero autonomous ADE for the Möbius pullback
`x ↦ u(-1/x)`.  The natural microscope domain is the entire left half-plane, which the involution
`x ↦ -1/x` maps biholomorphically to the right half-plane.  The Möbius jet map is triangular and
injective, so this gives a local ADE for the outer germ `u` itself.

The claim is a static constraint theorem.  It does not construct a carrier or propagate a flow.

## Gates

- [x] 0 → 1 in-progress: source-pure mechanism and concrete formalized instance identified
- [x] 1 → 2 fully-proven: generic analytic hypotheses and local/global boundary stated without gaps
- [x] 2 → 3 formalized: generic Lean theorem, targeted builds, lint, and axiom audit pass
- [ ] 3 → 4 publication-ready: comparison with Huang--Ng, Steinmetz, coherent families, and
  Poincaré-rescaling methods complete

## Parent boundary

- Highest-weight limits of differential polynomials under affine rescaling are parent mathematics.
- Huang--Ng's composition theorem assumes the hypertranscendental inner function is entire; Gamma is
  meromorphic, and `u ∘ Γ` may have pole clusters accumulating at Gamma poles.
- The new theorem is the exact factorial-pole composition detector on the left/right half-plane
  pair and the reduction from a relation for `u ∘ Γ` to a local relation for the outer germ `u`.
- Huang--Ng explicitly isolate outer-after-inner composition as the harder direction.  Their
  positive theorem assumes that the hypertranscendental inner function is entire; it does not
  include the meromorphic inner function Gamma.
- Searches through the composition, Gamma, digamma, differential-algebra, and recent
  hypertranscendence literature located no statement of this detector or its `ψ ∘ Γ` consequence.

## Formal route

1. `GammaFactorialComposition.lean` defines the right half-plane, the left-half-plane microscope
   domain, and local polynomial jet rigidity at `1`.
2. It proves compact-open convergence of `u(Γ(-n+sₙx))` to `u(-1/x)` on the whole left half-plane,
   eventual holomorphy, and convergence of every jet.
3. It applies the factorial initial-form theorem and the injective triangular Möbius jet pullback to
   prove the full constraint-reflection theorem
   `exists_polynomialJet_relation_on_rightHalfPlane_of_differentiallyAlgebraic_outer_comp_Gamma`
   and its contrapositive `hypertranscendental_outer_comp_Gamma`.
4. `GammaFactorialCompositionLocal.lean` proves the stronger microscope-local reflection and the
   obstruction `no_eventual_differential_relation_outer_comp_Gamma`.
5. The digamma specialization is formalized as
   `hypertranscendental_digamma_comp_Gamma_via_factorialComposition`.

## Log

- 2026-07-15 — extracted from the formally verified factorial blow-up proof for `ψ ∘ Γ`; generic
  statement opened only after the concrete instance and parent collision were understood.
- 2026-07-15 — generalized the limiting domain from a fixed disk to the complete left half-plane;
  formalized the global composition theorem and the eventual-microscope obstruction.  Direct and
  package-scoped module checks pass; the axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
