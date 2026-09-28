# HB literal retarded compact weak realization

- **ID:** hb-retarded-compact-weak-realization
- **Stage:** 3-formalized
- **Type:** BRIDGE
- **Source:** HB literal cyclic Peierls realization; B1 on `hb-source-pole-frequency-defect-cochain.md`

## Exact statement

Let `U(t,x,X,k) = originalPotential q branch a (t+x) (t-x) X k`.  For every
smooth compact test `F` whose topological support is contained in

`W = { ((t,x),z) | 0 < t+x and x < 0 }`,

the literal retarded field obeys

`∫ U * weakWaveTest(F) = ∫ exp(-k) * timeOriginalForcing(t,x,[X,exp k]) * F`.

Consequently `originalPotential - correctedFutureField` is weakly homogeneous
on this exact compact physical-wedge test class.

## Dependency-closed paper proof

1. On `W`, put `p=t+x`, `r=t-x`.  Then `0<p<r`; hence
   `originalPotential_smooth` applies and `originalPotential_wave` gives

   `4 ∂r∂p U - angularLaplacian(U)/cosh(x)^2 = timeOriginalForcing(t,x)`.

2. The affine change has

   `∂t² - ∂x² = 4 ∂p∂r`.

   Smoothness commutes the two null derivatives, so the displayed literal
   equation is exactly the pointwise event-wave equation on `W`.

3. Let `K` be a closed coordinate box with `tsupport F` in its interior and
   `K ⊂ W`; such a box exists by compactness of `tsupport F` and openness of
   `W`.  All derivatives of `F` vanish near every face of `K`.  Twice applying
   ordinary integration by parts in `t` and `x` transfers `eventWave` from
   `F` to `U`, with no boundary term.

4. In `(X,k)`, the literal angular operator is

   `angularLaplacian(U) = exp(2k) * ∂X²U + ∂k²U - ∂kU`.

   Two `X` integrations by parts and two/one `k` integrations by parts yield

   `∫ exp(-k) * angularLaplacian(U) * F = ∫ U * angularTestAction(F)`.

   This is exactly the three displayed terms in `weakWaveTest`; it retains the
   hyperbolic area factor and introduces no source replacement.

5. Multiply the pointwise equation by `exp(-k)F`, integrate over `K`, and use
   steps 3--4.  Since every integrand is continuous with compact support,
   all integrals are absolutely defined and extending from `K` to all target
   space changes neither side.  This proves the stated retarded weak identity.

6. `complete_original_weak_wave` gives the identical right side for
   `correctedFutureField` on the larger `x<0` test class.  Subtraction proves
   weak homogeneity of their literal difference on `W`.

## Consequence for the full route

`source pole → explicit wave cochain → [this bridge] homogeneous causal
difference → cutoff-face transgression → mixedField two-leg action → cyclic
Peierls extinction → RH`.

This bridge does not claim a noncompact Green identity, a vanishing cutoff
face, or a Peierls-current extinction.  A nonzero cutoff face still kills the
literal distributional/action realization; a zero face is the required
identification with the retained `mixedField` action boundary.

## Lean status

`HTGeometry.ComplexWaveGreenIdentity` now source-checks the reusable complex
compact Green primitives for one and two coordinate derivatives.  Remaining
formal work is purely the target-coordinate/weighted-angular assembly above,
followed by the noncompact cutoff-face theorem; neither has been claimed.

## Formalized (2026-09-27)

`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRetardedCompactWeakRealization.lean`
(namespace `RHTower.D4BMRetardedCompactWeakRealization`):

- `eventPotential q br a ((t,x),z) = originalPotential q br a (t+x) (t-x) z.re z.im`,
  `physicalWedge = {0 < t+x, x < 0}`;
- `eventPotential_weak_wave`: for every smooth compactly supported `F` with
  `tsupport F ⊆ physicalWedge`, `∫ U · weakWaveTest F = ∫ e^{-k} · timeOriginalForcing(t,x,[X,e^k]) · F`;
- `eventPotential_sub_correctedFutureField_weak`: `∫ (U - correctedFutureField) · weakWaveTest F = 0`
  on the same test class;
- supporting theorems: `weakFieldOperator_eventPotential` (pointwise equation on the wedge from
  `originalPotential_wave`, the null chart and symmetry of second derivatives),
  `integral_mul_weakWaveTest` (compact transposition for every smooth field),
  `integral_angularTestAction_mul` (hyperbolic angular transposition), `exists_contDiff_cutoff`
  (smooth cutoff equal to one near a compact set), `weakWaveTest_eq_zero_of_notMem`,
  `weakFieldOperator_congr`.

The field is only smooth on the wedge; the proof multiplies it by a smooth cutoff equal to one near
`tsupport F` instead of the coordinate-box argument of step 3.  Axioms
`[propext, Classical.choice, Quot.sound]`.
