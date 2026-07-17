# Gamma normalization horizons and radial quantifier exchange

- **ID:** `gamma-normalization-horizon-phase-transition`
- **Stage:** 3-formalized
- **Type:** EXACT NORMALIZATION-HORIZON MODEL / POSITIVE SUCCESSOR TO SOURCE BLINDNESS
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [STRUCTURALLY NEW TO THE PROGRAM]`
  `[PARENT BOHR--MOLLERUP / VARIATIONAL CONE THEORY]`
  `[NOT YET STANDALONE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/GammaNormalizationHorizon.lean`
- **Parent:**
  `../../1-in-progress/hypertranscendental-conservativity-spectrum.md`

## The no-go and its positive successor

The Gamma source equation and a pointing do not select Gamma.  In logarithmic gauge coordinates,
every other positive source solution has the form

```text
log F = log Gamma + h,
```

with `h` one-periodic and pointed.  Any construction derived only from the forgotten source remains
blind to this residual gauge.

The positive successor is a transverse, nonlinear, cofinal selector.  Write

```text
b(x) = Re psi'(x).
```

For `B>0`, define the normalization horizon `N_B` to be the pointed twice-differentiable
one-periodic gauges satisfying

```text
b(x) + h''(x) >= 0,        0 < x <= B.                    (1)
```

The field `B |-> N_B` is antitone.

## Exact phase transition

Lean proves all of the following.

1. The background curvature obeys

   ```text
   1/x^2 <= b(x),          x>0,
   b(x+n) -> 0.                                             (2)
   ```

2. Every finite positive horizon contains a nonzero pointed analytic periodic gauge.  An explicit
   witness is

   ```text
   h_B(x) = [1 / (2 B^2 (2 pi)^2)] [1-cos(2 pi x)].         (3)
   ```

3. More strongly, every pointed twice-differentiable periodic direction whose curvature is bounded
   on `(0,B]` is absorbed by `N_B` after a sufficiently small positive rescaling.

4. A gauge lying in every positive horizon is zero:

   ```text
   (forall B>0, h in N_B)  iff  h=0.                        (4)
   ```

5. Define horizon-dependent radial admissibility and uniform cofinal radial admissibility by

   ```text
   FinRad(h) := forall B>0, exists epsilon_B>0,
                  epsilon_B h in N_B;

   CofRad(h) := exists epsilon>0, forall B>0,
                  epsilon h in N_B.                         (5)
   ```

   Then every nonzero regular locally curvature-bounded periodic gauge satisfies

   ```text
   FinRad(h) and not CofRad(h).                              (6)
   ```

   Moreover `CofRad(h) iff h=0` for every gauge direction.

The source blindness no-go therefore has a strong positive theorem: Gamma is not selected at any
finite horizon, but it is selected by the complete cofinal incidence.  The missing information is
not a finite datum concealed in the source.  It is the failure to uniformize a family of admissible
rescalings at the vanishing-curvature boundary.

## Mechanism

If `h''(x_0)<0`, periodicity repeats the same negative value at `x_0+n`, while `(2)` makes the
positive background tend to zero.  Hence global nonnegativity in `(1)` forces `h''>=0`.  The gauge
is convex and periodic, therefore constant; pointing makes it zero.

At a fixed finite horizon the situation is opposite.  The lower bound in `(2)` leaves positive
slack, so any bounded-curvature direction survives after shrinking its amplitude.  The exchange

```text
forall B exists epsilon_B    versus    exists epsilon forall B               (7)
```

is therefore genuinely false.

## Novelty and anti-theatre gate

Bohr--Mollerup uniqueness, eventual log-convex uniqueness for Gamma-type functional equations,
higher-order convexity characterizations, tangent-cone nonregularity, and failures of uniform
constraint qualification are established parent theories.  The curvature proof of `(4)` is an
elementary reformulation of that world.  The exact package `(1)`--`(7)` was not found in the audited
literature, but it does not clear the significance gate as a standalone Gamma theorem.

The candidate-new scientific claim is instead the cross-family statement that the obstruction
object for constrained HT sources is the **normalization-horizon uniformization defect**, and that
spectral, positivity, continuation, monodromy, and boundary failures are conservative realizations
of that same defect.  That claim remains in progress and requires at least one non-Gamma comparison
theorem.

## Lean declarations

- `vanishing_background_periodic_nonneg_of_pos`
- `convex_periodic_eq_const`
- `vanishing_background_periodic_curvature_rigidity_of_pos`
- `tendsto_realTrigamma_add_nat`
- `one_div_sq_le_realTrigamma`
- `gammaLocalGauge_strictly_admissible`
- `gamma_periodic_curvature_rigidity`
- `gammaCurvatureHorizon_antitone`
- `gammaCurvatureHorizon_nontrivial`
- `gammaCurvatureHorizon_absorbs_bounded_direction`
- `gammaCurvatureHorizon_cofinal_iff`
- `gammaCofinalRadial_iff`
- `gammaRadial_quantifier_exchange_defect`

## Verification

- exact targeted module build passed;
- direct Lean verification of the touched module passed;
- no full build and no numerical computation was used.
