import GaloisForLFunctions.RHTower.ProlateL2Regularity
import GaloisForLFunctions.RHTower.BandVariational

/-!
# From the band operator to the band double integral

The band operator lives on `L²[-1,1]`, while the trial computations live in interval integrals over
`[-1,1]`.  This module is the dictionary between them for continuous test functions:

```text
⟪B_c (psi|), (psi|)⟫ = ∫∫ sinc_c(x-y) psi(x) psi(y),      ‖(psi|)‖² = ∫ psi²,
```

where `(psi|)` is the `L²` class of the restriction of `psi` to the band.  Combined with the
variational bound, every continuous test function therefore produces an upper bound for the band
leakage `1 - ‖B_c‖` in purely function-level terms.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

open _root_.RHTower

/-- The restriction of a continuous function on the line to the band. -/
def restrictUnit (Φ : ℝ → ℝ) (hΦ : Continuous Φ) : C(ClosedInterval (-1 : ℝ) 1, ℝ) :=
  ContinuousMap.restrict _ ⟨Φ, hΦ⟩

/-- The `L²` class of a continuous test function on the band. -/
def bandClass (Φ : ℝ → ℝ) (hΦ : Continuous Φ) : RealIntervalL2 (-1 : ℝ) 1 :=
  ContinuousMap.toLp 2 volume ℝ (restrictUnit Φ hΦ)

theorem coeFn_bandClass (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) : ClosedInterval (-1 : ℝ) 1 → ℝ)
      =ᵐ[volume] fun x => Φ (x : ℝ) := by
  have h := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval (-1 : ℝ) 1))) (restrictUnit Φ hΦ)
  exact h

/-- **The band quadratic form in interval integrals.** -/
theorem inner_bandOperatorL2_bandClass (c : ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    (inner ℝ (bandOperatorL2 c (bandClass Φ hΦ)) (bandClass Φ hΦ) : ℝ)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (Φ x * Φ y) := by
  have hcoe := coeFn_bandClass Φ hΦ
  rw [bandOperatorL2, inner_continuousKernelOperator_eq]
  -- replace the class by the function, inside and out
  have hinner : ∀ x : ClosedInterval (-1 : ℝ) 1,
      (∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelContinuous c (x, y) *
          (((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) x : ℝ) *
            ((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) y : ℝ)) ∂volume)
      = ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c (x : ℝ) (y : ℝ) *
          (((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) x : ℝ) * Φ (y : ℝ)) ∂volume := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with y hy
    rw [hy]
    rfl
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have houter : (∫ x : ClosedInterval (-1 : ℝ) 1, ∫ y : ClosedInterval (-1 : ℝ) 1,
      sincKernelSmooth c (x : ℝ) (y : ℝ) *
        (((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) x : ℝ) * Φ (y : ℝ)) ∂volume ∂volume)
      = ∫ x : ClosedInterval (-1 : ℝ) 1, ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c (x : ℝ) (y : ℝ) * (Φ (x : ℝ) * Φ (y : ℝ)) ∂volume ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hx]
  rw [houter]
  -- convert both subtype integrals to interval integrals
  have hy : ∀ x : ℝ, (∫ y : ClosedInterval (-1 : ℝ) 1,
      sincKernelSmooth c x (y : ℝ) * (Φ x * Φ (y : ℝ)) ∂volume)
      = ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (Φ x * Φ y) := fun x =>
    integral_subtype_unit (fun y => sincKernelSmooth c x y * (Φ x * Φ y))
  have hstep : (∫ x : ClosedInterval (-1 : ℝ) 1, ∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c (x : ℝ) (y : ℝ) * (Φ (x : ℝ) * Φ (y : ℝ)) ∂volume ∂volume)
      = ∫ x : ClosedInterval (-1 : ℝ) 1,
          (fun t : ℝ => ∫ y in (-1 : ℝ)..1, sincKernelSmooth c t y * (Φ t * Φ y)) (x : ℝ)
            ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hy (x : ℝ)
  rw [hstep]
  exact integral_subtype_unit
    (fun t => ∫ y in (-1 : ℝ)..1, sincKernelSmooth c t y * (Φ t * Φ y))

/-- **The band energy in interval integrals.** -/
theorem norm_sq_bandClass (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ‖bandClass Φ hΦ‖ ^ 2 = ∫ x in (-1 : ℝ)..1, Φ x ^ 2 := by
  have hcoe := coeFn_bandClass Φ hΦ
  rw [norm_sq_eq_integral]
  have hcongr : (∫ x : ClosedInterval (-1 : ℝ) 1,
      ((bandClass Φ hΦ : RealIntervalL2 (-1 : ℝ) 1) x : ℝ) ^ 2 ∂volume)
      = ∫ x : ClosedInterval (-1 : ℝ) 1, Φ (x : ℝ) ^ 2 ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
  rw [hcongr]
  exact integral_subtype_unit (fun x => Φ x ^ 2)

/-- **The function-level variational bound for the band leakage.**  Every continuous test function with
positive energy bounds `1 - ‖B_c‖` by its normalized band deficit. -/
theorem one_sub_norm_bandOperatorL2_le (c : ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (hne : bandClass Φ hΦ ≠ 0) :
    1 - ‖bandOperatorL2 c‖
      ≤ ((∫ x in (-1 : ℝ)..1, Φ x ^ 2)
          - ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * (Φ x * Φ y))
        / ∫ x in (-1 : ℝ)..1, Φ x ^ 2 := by
  have h := one_sub_norm_le_rayleigh_deficit (bandOperatorL2 c) hne
  rwa [norm_sq_bandClass Φ hΦ, inner_bandOperatorL2_bandClass c Φ hΦ] at h

end GaloisForLFunctions.RHTower

end
