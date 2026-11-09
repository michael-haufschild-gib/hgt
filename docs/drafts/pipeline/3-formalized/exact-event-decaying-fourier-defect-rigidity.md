# Integrable Euler–FE defects force the rational primes

- **ID:** exact-event-decaying-fourier-defect-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** obstacles-summary §3 (B122), §2.5 (B84), §2.10 (M1–M2).
- **Programmes:** ExactEventTheory and EulerFETransportTheory.

## Statement and scope

Every countable Beurling system in the corpus's Hamburger strip class with an integrable
uncompleted Riemann FE defect has exactly the rational primes, with their usual norms.
The analytic class requires the inverse-3/2 moment; continuity of E on the closed strip
[1/2,3/2]; holomorphy inside; `‖E(s)‖ ≤ C/(1+Im(s)²)`; the prescribed right-boundary
identity for Γℝζ_B and critical-line defect identity; and a measurable, polynomially
bounded defect g. There is no smallness condition on `∫‖g‖`, lattice premise, nonempty
prime-label premise, or assumed recurrence.

The conclusion includes β = 1/2, equality of the generalized-integer measure with the
ordinary positive-integer counting measure, exactly one generalized integer of each
positive integer norm, ζ_B = ζ on Re s > 1, and a norm-preserving bijection of prime
labels with the rational primes.

Every nonclassical system satisfying the remaining analytic conditions therefore has
extended defect cost `∫⁻ ‖g(t)‖ₑ = ∞`. In particular, the nonclassical finite-layer cost
`D_layer` is infinite in this class. This does not exclude an exceptional layer of ζ
or establish AAL.

## Proof

1. Mellin inversion gives the defective theta law. On the positive real axis both
   Laplace series are real; the integrable defect has zero radial residue. Taking
   imaginary parts proves that β is real.
2. The defect Laplace transform J has continuous boundary values away from zero,
   bounded by `3‖g‖₁ |y|⁻¹ᐟ²/(2π)`. The boundary is locally integrable and decays at infinity.
3. Pair with tents `T_h(x)=max(0,1−|x|/h)`. For y > h, half the atomic tent mass equals
   `P_h(y)+E_h(y)`, where

       P_h(y) = hβ + h Σ_x sinc²(πh‖x‖) cos(2π‖x‖y).

   The inverse-square moment makes P_h an absolutely convergent almost-periodic series;
   E_h tends to zero under distant translation. Two widths have common distant returns.
4. Every atom has mass at least one. Outer half-mass below 1/4 forces the inner
   half-width mass to vanish. Common returns and decay transfer this implication to
   the recurrent parts: `P_h(y)<1/4 ⇒ P_{h/2}(y)=0`.
5. For 0 < y < 1, small tents lie in the empty unit gap. Their unnormalized errors
   tend to zero, so the threshold kills the inner normalized averages. Their limit
   is Re J(iy), which must vanish. Conjugation gives the negative unit gap.
6. Pair at the origin with the unit tent. Dominated convergence uses the integrable
   square-root majorant. The defect, Poisson and polar contributions vanish, giving
   `Σ_x sinc²(π‖x‖)=0`. Positivity forces every norm to be a natural number.
7. An empty prime-label system has only its unit atom. Integer support would force
   2β = 1, while its finite exponential sum has zero Abel residue and forces β = 0.
8. For nonempty systems, integer support identifies the Abel cosine means at zero
   and one. The unit atom fixes 2β = 1. Unit-density rigidity fills the integer lattice
   with unit masses; multiplicative factorization identifies the prime labels.

## Lean declarations

Shared analytic modules in `ExactEventTheory`:

- `IntegrableDefectsHaveDecayingBoundary.lean`: boundary values, local integrability,
  decay, and passage under compact continuous tests.
- `TentPairingsOfIntegrableDefects.lean`: `tent_boundary_identity_of_theta_defect`,
  `tendsto_tentBoundaryError_atTop`.
- `TentRecurrenceOfIntegrableDefects.lean`: `exists_common_tent_returns`,
  `recurrent_threshold_of_decaying_errors`, `beurling_tentRecurrentPart_half_eq_zero`.
- `IntegrableDefectsVanishInTheUnitGap.lean`:
  `beurling_defectBoundary_re_eq_zero_on_unit_gap`, `defectBoundary_re_even_of_theta_defect`.
- `IntegerSupportForcesExactArithmetic.lean`: pole pinning and integer-support rigidity.

Classification modules in `EulerFETransportTheory`:

- `IntegrableDefectsForceIntegerSupport.lean`: `beurling_integral_sinc_sq_eq_zero`,
  `beurling_intNorm_nat_of_integrable_theta_defect`.
- `IntegrableFunctionalEquationsDetermineThePrimes.lean`:
  `measure_pole_real_of_integrable_theta_defect`,
  `beurling_labels_nonempty_of_integrable_theta_defect`,
  `beurlingSystem_rigidity_of_integrable_defect`,
  `nonclassical_beurling_defect_cost_eq_top`.

The boundary, tent, recurrence, unit-gap, integer-support and classification modules pass
direct `lake --old env lean` checks. The terminal classification/cost theorems have exactly
the transitive axioms `propext`, `Classical.choice`, and `Quot.sound`.
