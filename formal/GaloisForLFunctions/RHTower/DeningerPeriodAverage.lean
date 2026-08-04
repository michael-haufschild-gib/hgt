import GaloisForLFunctions.RHTower.DeningerPoincareOneForm
import GaloisForLFunctions.RHTower.DeningerExpCover

/-!
# Averaging over a period

The average of a directional derivative along the period of a periodic map vanishes: the integrand
is the derivative in the segment parameter of the map along that period, and the endpoints agree.
This is the mechanism that removes the derivative terms from the Cartan formula when a closed
constant form is written as the derivative of a periodic form.

* `deningerPeriodCurve_hasDerivAt` : the derivative of the map along a period direction.
* `deningerPeriodAverage_deriv_eq_zero` : the average of the directional derivative vanishes.
-/

namespace RHTower

open Complex

section PeriodAverage

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The curve traversing one period in a coordinate direction. -/
noncomputable def deningerPeriodCurve (w : Fin r → ℂ) (j : Fin r) (s : ℝ) : Fin r → ℂ :=
  w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)

theorem deningerPeriodCurve_zero (w : Fin r → ℂ) (j : Fin r) :
    deningerPeriodCurve w j 0 = w := by
  show w + (((0 : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) •
    (Pi.single j (1 : ℂ) : Fin r → ℂ) = w
  norm_num

theorem deningerPeriodCurve_one (w : Fin r → ℂ) (j : Fin r) :
    deningerPeriodCurve w j 1 =
      w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
  show w + (((1 : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) •
    (Pi.single j (1 : ℂ) : Fin r → ℂ) = _
  norm_num

/-- **The period curve is differentiable** with constant derivative the period vector. -/
theorem deningerPeriodCurve_hasDerivAt (w : Fin r → ℂ) (j : Fin r) (s : ℝ) :
    HasDerivAt (deningerPeriodCurve w j)
      ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) s := by
  have h1 := deningerRealCast_hasDerivAt s
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * (2 * Real.pi * Complex.I))
      (2 * Real.pi * Complex.I) s := by
    have h := h1.mul_const (2 * Real.pi * Complex.I)
    rw [one_mul] at h
    exact h
  have h3 := h2.smul_const (Pi.single j (1 : ℂ) : Fin r → ℂ)
  exact h3.const_add w

/-- **The average of a directional derivative along a period vanishes.** -/
theorem deningerPeriodAverage_deriv_eq_zero {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    (hcont : Continuous (fderiv ℂ β)) (j : Fin r)
    (hper : ∀ w : Fin r → ℂ,
      β (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = β w)
    (w : Fin r → ℂ) :
    ∫ s in (0 : ℝ)..1, (fderiv ℂ β (deningerPeriodCurve w j s))
      ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = 0 := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => β (deningerPeriodCurve w j t))
      ((fderiv ℂ β (deningerPeriodCurve w j s))
        ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))) s := by
    intro s
    have hfd := (hdiff (deningerPeriodCurve w j s)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt s (deningerPeriodCurve_hasDerivAt w j s)
  have hcurvecont : Continuous (deningerPeriodCurve w j) := by
    show Continuous fun s : ℝ => w + ((s : ℂ) * (2 * Real.pi * Complex.I)) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hintegrand : Continuous fun s : ℝ => (fderiv ℂ β (deningerPeriodCurve w j s))
      ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) :=
    (ContinuousLinearMap.apply ℂ X
      ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))).continuous.comp
      (hcont.comp hcurvecont)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hintegrand.intervalIntegrable 0 1)]
  rw [deningerPeriodCurve_zero, deningerPeriodCurve_one, hper w, sub_self]

end PeriodAverage

end RHTower

namespace RHTower

section ConstantExact

variable {r : ℕ}

/-- A functional vanishing on the coordinate vectors vanishes. -/
theorem deningerFunctional_eq_zero_of_single {α : (Fin r → ℂ) →L[ℂ] ℂ}
    (h : ∀ j : Fin r, α (Pi.single j (1 : ℂ) : Fin r → ℂ) = 0) : α = 0 := by
  classical
  refine ContinuousLinearMap.ext fun u => ?_
  have hbasis : ∀ j : Fin r,
      (fun l => if j = l then (1 : ℂ) else 0) = (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j
    funext l
    rw [Pi.single_apply]
    by_cases hl : j = l
    · rw [if_pos hl, if_pos hl.symm]
    · rw [if_neg hl, if_neg (Ne.symm hl)]
  conv_lhs => rw [show u = ∑ j, u j • (fun l => if j = l then (1 : ℂ) else 0) from pi_eq_sum_univ u]
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, hbasis j, h j, smul_zero]

/-- **A constant one-form that is the derivative of a periodic function vanishes.**  This is the
base case of the separation of the generators in cohomology: on the covering space the classes of
the generators are constant forms, and a constant form killed by a periodic primitive is zero. -/
theorem deningerConstant_functional_eq_zero {β : (Fin r → ℂ) → ℂ} {α : (Fin r → ℂ) →L[ℂ] ℂ}
    (hderiv : ∀ w : Fin r → ℂ, HasFDerivAt β α w)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      β (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = β w) :
    α = 0 := by
  have hfd : fderiv ℂ β = fun _ => α := by
    funext w
    exact (hderiv w).fderiv
  have hdiff : Differentiable ℂ β := fun w => (hderiv w).differentiableAt
  have hcont : Continuous (fderiv ℂ β) := by
    rw [hfd]
    exact continuous_const
  refine deningerFunctional_eq_zero_of_single fun j => ?_
  have hzero := deningerPeriodAverage_deriv_eq_zero hdiff hcont j (hper j) (0 : Fin r → ℂ)
  rw [hfd] at hzero
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hzero
  have hsmul : α ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
      (2 * Real.pi * Complex.I) * α (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    rw [map_smul, smul_eq_mul]
  rw [hsmul] at hzero
  have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h htwopi
  · exact h

end ConstantExact

end RHTower
