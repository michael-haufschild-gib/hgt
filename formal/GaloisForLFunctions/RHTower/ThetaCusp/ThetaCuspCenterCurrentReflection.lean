import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairKernelOrderDerivative
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflection

/-!
# Reflection law for the theta centre current

The linear centre weight `u` is odd, so for an even `f` the reflection `u ↦ -u` sends the
exponential rate `c` to `-c` and flips the sign:

```text
∫ u e^(c u) f u du = - ∫ u e^(-c u) f u du .
```

Applied to `f u = Φ(u+t) Φ(u-t)` with the complete theta source, which is even, this says the
centre-weighted current at `σ` is minus the one at `1 - σ`.  Consequently the `sinh`-weighted
Hedenmalm current is **twice** the single-exponent current, not a genuine difference: for the
complete source the `σ ↔ 1-σ` antisymmetrisation is automatic, and the gate is a single-exponent
positivity statement.

The atom-level currents behave differently, because the individual atoms `Φ_n` are not even; their
`σ ↔ 1-σ` antisymmetry is a statement about the sum, i.e. the theta functional equation.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- **Reflection law for a centre-weighted exponential moment of an even function.**  The linear
centre weight is odd, so reflecting `u` flips both the weight and the exponential rate. -/
theorem integral_center_exp_eq_neg_of_even {f : ℝ → ℝ} (hf : ∀ u : ℝ, f (-u) = f u) (c : ℝ) :
    (∫ u : ℝ, u * Real.exp (c * u) * f u) =
      -∫ u : ℝ, u * Real.exp (-(c * u)) * f u := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => u * Real.exp (c * u) * f u) (-1)
  simp only [abs_inv, abs_neg, abs_one, inv_one, one_smul] at h
  rw [← h, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (-1 * u) * Real.exp (c * (-1 * u)) * f (-1 * u) =
    -(u * Real.exp (-(c * u)) * f u)
  rw [show (-1 : ℝ) * u = -u by ring, hf u, show c * -u = -(c * u) by ring]
  ring

/-- **The theta centre current is odd under `σ ↔ 1 − σ`.**  Because the completed theta source is
even, the centre-weighted current at `σ` is minus the one at `1 − σ`, for every `t`. -/
theorem integral_center_mul_exp_mul_thetaCuspFullSource_reflect (σ t : ℝ) :
    (∫ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))) =
      -∫ u : ℝ, u * Real.exp ((2 * (1 - σ) - 1) * u) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) := by
  have hf : ∀ u : ℝ, thetaCuspFullSource (-u + t) * thetaCuspFullSource (-u - t) =
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) := by
    intro u
    have h1 : thetaCuspFullSource (-u + t) = thetaCuspFullSource (u - t) := by
      rw [← thetaCuspFullSource_neg (u - t)]
      congr 1
      ring
    have h2 : thetaCuspFullSource (-u - t) = thetaCuspFullSource (u + t) := by
      rw [← thetaCuspFullSource_neg (u + t)]
      congr 1
      ring
    rw [h1, h2]
    ring
  have h := integral_center_exp_eq_neg_of_even (f := fun u : ℝ =>
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) hf (2 * σ - 1)
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show u * Real.exp (-((2 * σ - 1) * u)) *
      (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) =
    u * Real.exp ((2 * (1 - σ) - 1) * u) *
      (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))
  rw [show -((2 * σ - 1) * u) = (2 * (1 - σ) - 1) * u by ring]

/-- **The antisymmetrised theta orientation current is twice the single-exponent current.**  The
`sinh` weight does not produce a genuine `σ ↔ 1−σ` difference for the complete source: evenness
makes the two halves equal up to sign, so the Hedenmalm gate is a single-exponent positivity
statement after all. -/
theorem integral_center_sinh_mul_thetaCuspFullSource_eq_two_mul {σ t : ℝ}
    (h1 : Integrable (fun u : ℝ => u * Real.exp ((2 * σ - 1) * u) *
      (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))))
    (h2 : Integrable (fun u : ℝ => u * Real.exp ((2 * (1 - σ) - 1) * u) *
      (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)))) :
    (∫ u : ℝ, u * (Real.exp ((2 * σ - 1) * u) - Real.exp ((2 * (1 - σ) - 1) * u)) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))) =
      2 * ∫ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) := by
  have hsplit : (∫ u : ℝ, u * (Real.exp ((2 * σ - 1) * u) -
        Real.exp ((2 * (1 - σ) - 1) * u)) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))) =
      (∫ u : ℝ, u * Real.exp ((2 * σ - 1) * u) *
          (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))) -
        ∫ u : ℝ, u * Real.exp ((2 * (1 - σ) - 1) * u) *
          (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) := by
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show u * (Real.exp ((2 * σ - 1) * u) - Real.exp ((2 * (1 - σ) - 1) * u)) *
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) =
      u * Real.exp ((2 * σ - 1) * u) *
          (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)) -
        u * Real.exp ((2 * (1 - σ) - 1) * u) *
          (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t))
    ring
  rw [hsplit, integral_center_mul_exp_mul_thetaCuspFullSource_reflect σ t]
  ring

end

end RHTower
