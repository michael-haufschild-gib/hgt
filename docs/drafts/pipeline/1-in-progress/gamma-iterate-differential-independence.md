# Differential independence of the positive Gamma-iterate tower

- **ID:** `gamma-iterate-differential-independence`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Scientific status:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The countable family

  \[
    \Gamma(z),\Gamma^{\circ2}(z),\Gamma^{\circ3}(z),\ldots
  \]

  is differentially algebraically independent over `ℂ`.

## Goal

Prove that composition depth supplies not merely new algebraic coordinates, but a new differential
transcendence coordinate at every level.  The identity iterate is deliberately excluded: `z' = 1`
makes the depth-zero coordinate differentially algebraic over the constant field.

## Current evidence

- Every positive iterate is individually hypertranscendental in Lean.
- The complete tower including `z` is algebraically independent in Lean.
- The factorial pole microscope lowers every positive depth simultaneously:

  \[
    \Gamma^{\circ(j+1)}\!\left(-n+\frac{(-1)^{n+1}}{n!}x\right)
      \longrightarrow \Gamma^{\circ j}(-1/x).
  \]

- For a joint differential relation, the highest derivative-weight slice therefore descends one
  composition level.  The only new obstruction is the autonomous differential ideal of the
  reciprocal boundary germ `-1/x`.

## Open core: intrinsic pole-germ residue

Write `s_n=(-1)^(n+1)/n!` and

\[
  g_n(x)=\Gamma(-n+s_nx)
        =-\frac{1}{x}\,
          \frac{\Gamma(1+s_nx)}{\prod_{m=1}^n(1-s_nx/m)}.
\]

The reciprocal limit is differentially algebraic, so leading-order descent alone is not
injective.  The exact germ is a deformation whose coefficients contain the harmonic hierarchy
`H_n, H_n^(2), ...`.  The first deformation is an output translation of size `s_n H_n`; it escapes
the reciprocal-affine relation `y y'' - 2(y')^2`.  Translation-invariant projective relations first
detect the next deformation; for example the Schwarzian numerator has a nonzero residue of order
`s_n^2 H_n^2`.

The proof-grade missing theorem is:

> For every nonzero derivative-weight-homogeneous differential polynomial that vanishes on
> `-1/x`, the first nonzero coefficient of its exact Gamma pole-germ expansion is nonzero after
> lexicographic filtration by factorial order and harmonic degree.

Together with the already formalized nonvanishing of the factorial initial form, this would make
depth descent injective and close induction on composition depth.

## Attacks and falsifiers

1. Characterize the homogeneous reciprocal kernel, rather than the unrestricted kernel.  Test
   whether it is generated, in successive invariant layers, by the reciprocal-affine curvature
   `y y''-2(y')^2`, the Schwarzian numerator, and their derivatives.
2. Derive the Gamma pole-germ residues symbolically from the exact product formula.  No numerical
   experiment is evidence for this card.
3. Prove that the residue map is injective on the associated graded kernel.  A nonzero homogeneous
   differential polynomial annihilating every exact residue layer retires this route.
4. Check parent theory on differential ideals of reciprocal/projective jets and singular
   perturbations.  A published general theorem implying the statement retires novelty, not truth.
5. Do not replace this core with separate hypertranscendence, finite algebraic independence, or a
   conditional wrapper: none proves joint differential independence.

## Significance gate

If true, this produces a countably infinite differential transcendence basis from one classical
hypertranscendental function by self-composition and identifies simple-pole deformation depth as
the mechanism.  The claim is potentially field-defining, but it is not promoted until the residue
injectivity theorem is complete and an independent priority audit finds no antecedent.

## Gates

- [x] 0 → 1 in-progress: precise positive-depth statement, exact leading obstruction, attack, and
  falsifier isolated
- [ ] 1 → 2 fully-proven: pole-germ residue injectivity and induction complete on paper
- [ ] 2 → 3 formalized: unconditional joint theorem in Lean, targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: specialist priority review and standalone paper complete

## Log

- 2026-07-15 — opened after formalization of algebraic independence of the complete Gamma-iterate
  tower.  The algebraic descent is injective; the differential route is isolated to the
  reciprocal-boundary associated-graded kernel.
