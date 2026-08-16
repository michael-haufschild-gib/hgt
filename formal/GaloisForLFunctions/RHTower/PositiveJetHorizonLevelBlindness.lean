import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Constant level shifts are invisible to positive-jet data

Subtracting a constant from the completed `ξ` changes no positive derivative, no functional-equation
parity, no Schwarz reality, and no order-one growth envelope — yet it moves the zero divisor.

Taking the constant `ξ(2)` gives an entire function with the same positive jets as `ξ`, the same
reflection `s ↦ 1 - s` symmetry, the same Schwarz reality and the same growth envelope, whose zero
at `s = 2` lies off the critical line.  So positive-jet horizon data, the functional equation,
reality and order-one growth together cannot mark the RH zero level.
-/

noncomputable section

namespace RHTower

open Complex

/-- The completed `ξ` with a constant level shift. -/
def xiLevelShift (a : ℂ) (s : ℂ) : ℂ := xi s - a

theorem xiLevelShift_differentiable (a : ℂ) : Differentiable ℂ (xiLevelShift a) := by
  unfold xiLevelShift
  exact xi_differentiable.sub_const a

/-- **Functional equation.**  A constant shift preserves the reflection symmetry. -/
theorem xiLevelShift_one_sub (a s : ℂ) : xiLevelShift a (1 - s) = xiLevelShift a s := by
  unfold xiLevelShift
  rw [xi_one_sub]

/-- **Schwarz reality.**  A real constant shift preserves the Schwarz reflection. -/
theorem xiLevelShift_conj {a : ℂ} (ha : (starRingEnd ℂ) a = a) (s : ℂ) :
    xiLevelShift a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiLevelShift a s) := by
  unfold xiLevelShift
  rw [xi_conj, map_sub, ha]

/-- The first derivative is unchanged. -/
theorem deriv_xiLevelShift (a : ℂ) : deriv (xiLevelShift a) = deriv xi := by
  funext s
  unfold xiLevelShift
  exact deriv_sub_const a

/-- **Positive-jet blindness.**  Every derivative of positive order is unchanged. -/
theorem iteratedDeriv_xiLevelShift (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    iteratedDeriv k (xiLevelShift a) = iteratedDeriv k xi := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_xiLevelShift]

/-- **Growth envelope.**  A constant shift preserves the order-one growth envelope of `ξ`. -/
theorem xiLevelShift_growth (a : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖xiLevelShift a s‖ ≤ (1 + ‖a‖) * Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hbound⟩ := xi_growth_order_le_one
  refine ⟨C, hC, fun s => ?_⟩
  have hexp : (1 : ℝ) ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    refine Real.one_le_exp ?_
    have h1 : (0 : ℝ) ≤ 1 + ‖s‖ := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (2 + ‖s‖) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
      linarith
    positivity
  have hsub : ‖xiLevelShift a s‖ ≤ ‖xi s‖ + ‖a‖ := by
    unfold xiLevelShift
    exact norm_sub_le _ _
  have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  nlinarith [hbound s, hexp, hna, hsub]

/-- The shift by `ξ(2)` vanishes at `s = 2`. -/
theorem xiLevelShift_xiTwo_two : xiLevelShift (xi 2) 2 = 0 := by
  unfold xiLevelShift
  ring

/-- `ξ(2)` is real. -/
theorem xi_two_conj : (starRingEnd ℂ) (xi 2) = xi 2 := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    apply Complex.ext <;> simp
  have h := xi_conj 2
  rw [h2] at h
  exact h.symm

theorem re_two_ne_half : ((2 : ℂ)).re ≠ 1 / 2 := by
  norm_num

/-- **Level blindness of the positive-jet horizon.**  The function `ξ - ξ(2)` is entire, satisfies
the completed functional equation, is Schwarz real, has the order-one growth envelope of `ξ`, has
exactly the same derivatives of every positive order — and has a zero off the critical line. -/
theorem xi_levelShift_countermodel :
    Differentiable ℂ (xiLevelShift (xi 2)) ∧
      (∀ s : ℂ, xiLevelShift (xi 2) (1 - s) = xiLevelShift (xi 2) s) ∧
      (∀ s : ℂ, xiLevelShift (xi 2) ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (xiLevelShift (xi 2) s)) ∧
      (∀ k : ℕ, 1 ≤ k → iteratedDeriv k (xiLevelShift (xi 2)) = iteratedDeriv k xi) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
        ‖xiLevelShift (xi 2) s‖ ≤
          (1 + ‖xi 2‖) * Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) ∧
      xiLevelShift (xi 2) 2 = 0 ∧ ((2 : ℂ)).re ≠ 1 / 2 :=
  ⟨xiLevelShift_differentiable _, xiLevelShift_one_sub _,
    xiLevelShift_conj xi_two_conj, fun _ hk => iteratedDeriv_xiLevelShift _ hk,
    xiLevelShift_growth _, xiLevelShift_xiTwo_two, re_two_ne_half⟩

end RHTower
