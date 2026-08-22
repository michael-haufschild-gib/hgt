import GaloisForLFunctions.HTGeometry.BuresWasserstein.GeometricMeanLipschitz
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinDerivOperator
import GaloisForLFunctions.HTGeometry.CFCSqrtLipschitz
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldHilbertSchmidt

/-!
# The derivative of the Wasserstein field is Lipschitz

The Lyapunov coefficient of the derivative is exactly the conjugated geometric mean:
`√(a^{-1/2} X⁻¹ a^{-1/2}) = a^{-1/2}(a # X⁻¹)a^{-1/2}`, because the Riccati equation makes the
square of the right-hand side equal to `a^{-1/2}X⁻¹a^{-1/2}`.  Hence the Lipschitz estimate for
the geometric mean transfers directly to the Lyapunov coefficient, and the Sylvester perturbation
bound turns that into a Lipschitz estimate for the derivative itself.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The Lyapunov coefficient of the derivative is the conjugated geometric mean.** -/
theorem cfcSqrt_conjMap_rpow_neg_half {a b : A} (ha : IsStrictlyPositive a) :
    CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) b)
      = a ^ (-(1/2) : ℝ) * gm a b * a ^ (-(1/2) : ℝ) := by
  rw [gm_eq_sqrt, conjMap_apply']
  have hL : (a ^ (-(1/2) : ℝ) : A) * (a ^ (1/2 : ℝ)) = 1 := rpow_neg_half_mul_rpow_half ha
  have hR : (a ^ (1/2 : ℝ) : A) * (a ^ (-(1/2) : ℝ)) = 1 := rpow_half_mul_rpow_neg_half ha
  calc CFC.sqrt ((a ^ (-(1/2) : ℝ) : A) * b * a ^ (-(1/2) : ℝ))
      = 1 * CFC.sqrt ((a ^ (-(1/2) : ℝ) : A) * b * a ^ (-(1/2) : ℝ)) * 1 := by
        rw [one_mul, mul_one]
    _ = ((a ^ (-(1/2) : ℝ) : A) * (a ^ (1/2 : ℝ)))
          * CFC.sqrt ((a ^ (-(1/2) : ℝ) : A) * b * a ^ (-(1/2) : ℝ))
          * ((a ^ (1/2 : ℝ) : A) * (a ^ (-(1/2) : ℝ))) := by rw [hL, hR]
    _ = (a ^ (-(1/2) : ℝ) : A)
          * ((a ^ (1/2 : ℝ) : A)
            * CFC.sqrt ((a ^ (-(1/2) : ℝ) : A) * b * a ^ (-(1/2) : ℝ))
            * (a ^ (1/2 : ℝ))) * (a ^ (-(1/2) : ℝ)) := by noncomm_ring

/-- The Lyapunov coefficient of the derivative is Lipschitz in the base point. -/
theorem norm_cfcSqrt_conjMap_sub_le {a b c : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) (hc : IsStrictlyPositive c) {α γ M : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hM : 0 < M)
    (haα : α • (1 : A) ≤ a) (haM : a ≤ M • (1 : A))
    (hgb : γ • (1 : A) ≤ gm a b) (hgc : γ • (1 : A) ≤ gm a c) :
    (2 * (γ * M⁻¹))
        * ‖CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) b)
          - CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) c)‖
      ≤ α⁻¹ * ‖b - c‖ := by
  have h := norm_gm_sub_le ha hb hc hγ hM haM hgb hgc
  have hid : CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) b)
      - CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) c)
      = (a ^ (-(1/2) : ℝ) : A) * (gm a b - gm a c) * a ^ (-(1/2) : ℝ) := by
    rw [cfcSqrt_conjMap_rpow_neg_half ha, cfcSqrt_conjMap_rpow_neg_half ha]
    noncomm_ring
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  rw [hid]
  refine h.trans ?_
  have hd : ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖
      ≤ (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖) * ‖b - c‖ := by
    calc ‖(a ^ (-(1/2) : ℝ) : A) * (b - c) * a ^ (-(1/2) : ℝ)‖
        ≤ ‖(a ^ (-(1/2) : ℝ) : A) * (b - c)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖ := norm_mul_le _ _
      _ ≤ (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖b - c‖) * ‖(a ^ (-(1/2) : ℝ) : A)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = (‖(a ^ (-(1/2) : ℝ) : A)‖ * ‖(a ^ (-(1/2) : ℝ) : A)‖) * ‖b - c‖ := by ring
  refine hd.trans ?_
  exact mul_le_mul_of_nonneg_right hN2 (norm_nonneg _)

/-! ### The Lipschitz estimate for the derivative -/

section HilbertSchmidt

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- The Lipschitz constant of the derivative of the Wasserstein field on `[α·1, β·1]`. -/
noncomputable def derivLipConst (α β : ℝ) : ℝ :=
  β * (β / 2) * (2 * (α⁻¹ ^ 4) + β ^ 2 * α⁻¹ ^ 6 / (2 * Real.sqrt (α * β⁻¹)))

/-- Difference of two conjugated inverses. -/
lemma norm_ringInverse_sub_le_of_Icc {X Y : E →L[ℂ] E} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) {α : ℝ} (hα : 0 < α)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hYα : α • (1 : E →L[ℂ] E) ≤ Y) :
    ‖(X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖X - Y‖ := by
  have hXn : ‖(X⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hYn : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  have hid : (X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ = X⁻¹ʳ * (Y - X) * Y⁻¹ʳ := by
    have h1 : (X⁻¹ʳ : E →L[ℂ] E) * (Y - X) * Y⁻¹ʳ
        = X⁻¹ʳ * (Y * Y⁻¹ʳ) - (X⁻¹ʳ * X) * Y⁻¹ʳ := by noncomm_ring
    rw [h1, Ring.mul_inverse_cancel _ hY.isUnit, Ring.inverse_mul_cancel _ hX.isUnit,
      mul_one, one_mul]
  rw [hid]
  have hYX : ‖Y - X‖ = ‖X - Y‖ := by rw [← norm_neg (X - Y), neg_sub]
  calc ‖(X⁻¹ʳ : E →L[ℂ] E) * (Y - X) * Y⁻¹ʳ‖
      ≤ ‖(X⁻¹ʳ : E →L[ℂ] E) * (Y - X)‖ * ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ := norm_mul_le _ _
    _ ≤ (‖(X⁻¹ʳ : E →L[ℂ] E)‖ * ‖Y - X‖) * ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (α⁻¹ * ‖X - Y‖) * α⁻¹ := by
        rw [hYX]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hXn (norm_nonneg _)) hYn
          (norm_nonneg _) (by positivity)
    _ = (α⁻¹ * α⁻¹) * ‖X - Y‖ := by ring

/-- Hilbert–Schmidt difference of two inverses. -/
lemma hsNorm_ringInverse_sub_le_of_Icc {X Y : E →L[ℂ] E} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) {α : ℝ} (hα : 0 < α)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hYα : α • (1 : E →L[ℂ] E) ≤ Y)
    (hPHS : IsHilbertSchmidt (X - Y)) :
    hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm (X - Y) := by
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hXn : ‖(X⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hYn : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  have hid : (Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ = Y⁻¹ʳ * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ := by
    have h1 : (Y⁻¹ʳ : E →L[ℂ] E) * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ
        = Y⁻¹ʳ * (X * X⁻¹ʳ) - (Y⁻¹ʳ * Y) * X⁻¹ʳ := by noncomm_ring
    rw [h1, Ring.mul_inverse_cancel _ hX.isUnit, Ring.inverse_mul_cancel _ hY.isUnit,
      mul_one, one_mul]
  rw [hid]
  refine (hsNorm_sandwich_le (S := (Y⁻¹ʳ : E →L[ℂ] E)) (T := (X⁻¹ʳ : E →L[ℂ] E)) hPHS).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul hYn hXn (norm_nonneg _) hαinv.le)
    (hsNorm_nonneg _)

/-- Difference of two symmetric sandwiches by inverses, in the Hilbert–Schmidt norm. -/
lemma hsNorm_conj_ringInverse_sub_le {X Y P : E →L[ℂ] E} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) (hP : IsHilbertSchmidt P) {α : ℝ} (hα : 0 < α)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hYα : α • (1 : E →L[ℂ] E) ≤ Y) :
    hsNorm ((X⁻¹ʳ : E →L[ℂ] E) * P * X⁻¹ʳ - Y⁻¹ʳ * P * Y⁻¹ʳ)
      ≤ (2 * (α⁻¹ * α⁻¹ * α⁻¹)) * (‖X - Y‖ * hsNorm P) := by
  have hXn : ‖(X⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hYn : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  have hdiff := norm_ringInverse_sub_le_of_Icc hX hY hα hXα hYα
  have hid : (X⁻¹ʳ : E →L[ℂ] E) * P * X⁻¹ʳ - Y⁻¹ʳ * P * Y⁻¹ʳ
      = ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ) * P * X⁻¹ʳ
        + Y⁻¹ʳ * P * ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ) := by noncomm_ring
  have h1 : IsHilbertSchmidt
      (((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ) * P * X⁻¹ʳ) := (hP.comp_left _).comp_right _
  have h2 : IsHilbertSchmidt
      ((Y⁻¹ʳ : E →L[ℂ] E) * P * ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ)) := (hP.comp_left _).comp_right _
  have hb1 : hsNorm (((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ) * P * X⁻¹ʳ)
      ≤ ‖(X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ‖ * ‖(X⁻¹ʳ : E →L[ℂ] E)‖ * hsNorm P := by
    exact hsNorm_sandwich_le (S := ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ))
      (T := (X⁻¹ʳ : E →L[ℂ] E)) hP
  have hb2 : hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) * P * ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ))
      ≤ ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ * ‖(X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ‖ * hsNorm P := by
    exact hsNorm_sandwich_le (S := (Y⁻¹ʳ : E →L[ℂ] E))
      (T := ((X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ)) hP
  rw [hid]
  refine (hsNorm_add_le h1 h2).trans ?_
  have hαnn : (0 : ℝ) ≤ α⁻¹ := (inv_pos.mpr hα).le
  have hnn := hsNorm_nonneg P
  have hd1 : ‖(X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ‖ * ‖(X⁻¹ʳ : E →L[ℂ] E)‖ * hsNorm P
      ≤ ((α⁻¹ * α⁻¹) * ‖X - Y‖) * α⁻¹ * hsNorm P := by gcongr
  have hd2 : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ * ‖(X⁻¹ʳ : E →L[ℂ] E) - Y⁻¹ʳ‖ * hsNorm P
      ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * ‖X - Y‖) * hsNorm P := by gcongr
  nlinarith [norm_nonneg (X - Y), hnn, hαnn]

/-- **The derivative of the Wasserstein field is Lipschitz in the base point**, one term. -/
theorem hsNorm_deriv_term_diff_le {a X Y P : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hPsa : IsSelfAdjoint P) (hP : IsHilbertSchmidt P)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haβ : a ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    {u v : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : (↑u : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj))
    (hv : (↑v : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm (conjMap (a ^ (1/2 : ℝ)) ((↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
        - conjMap (a ^ (1/2 : ℝ)) ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap (a ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ))))
      ≤ derivLipConst α β * (‖X - Y‖ * hsNorm P) := by
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨w, hwdef, hwpos⟩ : ∃ w : ℝ, w = Real.sqrt (α * β⁻¹) ∧ 0 < w := ⟨_, rfl, hγ⟩
  obtain ⟨qX, hqXdef⟩ : ∃ z : E →L[ℂ] E,
      z = conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨qY, hqYdef⟩ : ∃ z : E →L[ℂ] E,
      z = conjMap (a ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨wX, hwXdef⟩ : ∃ z : E →L[ℂ] E,
      z = CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨wY, hwYdef⟩ : ∃ z : E →L[ℂ] E,
      z = CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) Y⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨yX, hyXdef⟩ : ∃ z : E →L[ℂ] E,
      z = (↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) qX := ⟨_, rfl⟩
  obtain ⟨yY, hyYdef⟩ : ∃ z : E →L[ℂ] E,
      z = (↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) qY := ⟨_, rfl⟩
  rw [← hqXdef, ← hqYdef, ← hyXdef, ← hyYdef]
  have hqXsa : IsSelfAdjoint qX := by
    rw [hqXdef]
    exact isSelfAdjoint_conjMap (isSelfAdjoint_rpow a _)
      (hPsa.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hqYsa : IsSelfAdjoint qY := by
    rw [hqYdef]
    exact isSelfAdjoint_conjMap (isSelfAdjoint_rpow a _)
      (hPsa.conjugate_self hY.ringInverse.isSelfAdjoint)
  have hlX : wX * yX + yX * wX = qX := by
    rw [hwXdef, hyXdef]; exact lyapunov_twisted_unit_inv hu hqXsa
  have hlY : wY * yY + yY * wY = qY := by
    rw [hwYdef, hyYdef]; exact lyapunov_twisted_unit_inv hv hqYsa
  have hyXHS : IsHilbertSchmidt yX := by
    rw [hyXdef, hqXdef]; exact isHilbertSchmidt_gmInvDerivSolution ha hX hP hPsa hu
  have hyYHS : IsHilbertSchmidt yY := by
    rw [hyYdef, hqYdef]; exact isHilbertSchmidt_gmInvDerivSolution ha hY hP hPsa hv
  have hwXsa : IsSelfAdjoint wX := by
    rw [hwXdef]; exact (CFC.sqrt_nonneg _).isSelfAdjoint
  have hwYsa : IsSelfAdjoint wY := by
    rw [hwYdef]; exact (CFC.sqrt_nonneg _).isSelfAdjoint
  have hwXlb : β⁻¹ • (1 : E →L[ℂ] E) ≤ wX := by
    rw [hwXdef]; exact smul_one_le_cfcSqrt_conjMap ha hX hβ haβ hXβ
  have hwYlb : β⁻¹ • (1 : E →L[ℂ] E) ≤ wY := by
    rw [hwYdef]; exact smul_one_le_cfcSqrt_conjMap ha hY hβ haβ hYβ
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  have hYn : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  -- (a) the right-hand sides
  have hqdiff : hsNorm (qX - qY) ≤ (2 * α⁻¹ ^ 4) * (‖X - Y‖ * hsNorm P) := by
    have hid : qX - qY
        = conjMap (a ^ (-(1/2) : ℝ))
          ((X⁻¹ʳ : E →L[ℂ] E) * P * X⁻¹ʳ - Y⁻¹ʳ * P * Y⁻¹ʳ) := by
      rw [hqXdef, hqYdef, map_sub]
    rw [hid]
    refine (hsNorm_conjMap_le ((hP.comp_left _).comp_right _ |>.sub
      ((hP.comp_left _).comp_right _))).trans ?_
    refine le_trans (mul_le_mul hN2 (hsNorm_conj_ringInverse_sub_le hX hY hP hα hXα hYα)
      (hsNorm_nonneg _) hαinv.le) (le_of_eq ?_)
    ring
  -- (b) the coefficients
  have hgX : w • (1 : E →L[ℂ] E) ≤ gm a X⁻¹ʳ := by
    rw [hwdef]
    exact smul_one_le_gm ha hX.ringInverse hα hβinv haα
      (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ)
  have hgY : w • (1 : E →L[ℂ] E) ≤ gm a Y⁻¹ʳ := by
    rw [hwdef]
    exact smul_one_le_gm ha hY.ringInverse hα hβinv haα
      (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
  have hwdiff : (2 * (w * β⁻¹)) * ‖wX - wY‖ ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * ‖X - Y‖) := by
    rw [hwXdef, hwYdef, hwdef]
    refine (norm_cfcSqrt_conjMap_sub_le ha hX.ringInverse hY.ringInverse hα hγ hβ
      haα haβ (hwdef ▸ hgX) (hwdef ▸ hgY)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (norm_ringInverse_sub_le_of_Icc hX hY hα hXα hYα) hαinv.le
  have hb2 : ‖wX - wY‖ ≤ (β * α⁻¹ ^ 3 / (2 * w)) * ‖X - Y‖ := by
    have hid : ‖wX - wY‖ = (β / (2 * w)) * ((2 * (w * β⁻¹)) * ‖wX - wY‖) := by
      field_simp
    rw [hid]
    refine le_trans (mul_le_mul_of_nonneg_left hwdiff
      (by positivity : (0:ℝ) ≤ β / (2 * w))) (le_of_eq ?_)
    field_simp
  -- (c) the size of the second solution
  have hqYb : hsNorm qY ≤ (α⁻¹ ^ 3) * hsNorm P := by
    rw [hqYdef]
    refine (hsNorm_conjMap_le ((hP.comp_left _).comp_right _)).trans ?_
    have hinner : hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) * P * Y⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm P := by
      refine (hsNorm_sandwich_le (S := (Y⁻¹ʳ : E →L[ℂ] E)) (T := (Y⁻¹ʳ : E →L[ℂ] E)) hP).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hYn hYn (norm_nonneg _) hαinv.le) (hsNorm_nonneg _)
    refine le_trans (mul_le_mul hN2 hinner (hsNorm_nonneg _) hαinv.le) (le_of_eq ?_)
    ring
  have hyYb : (2 * β⁻¹) * hsNorm yY ≤ hsNorm qY :=
    hsNorm_le_of_lyapunov hwYsa hyYHS hβinv hwYlb hlY
  have hynn : (0 : ℝ) ≤ hsNorm yY := hsNorm_nonneg _
  have hb3 : hsNorm yY ≤ (β / 2 * α⁻¹ ^ 3) * hsNorm P := by
    have h := hyYb.trans hqYb
    have hid : hsNorm yY = (β / 2) * ((2 * β⁻¹) * hsNorm yY) := by field_simp
    rw [hid]
    refine le_trans (mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ β / 2))
      (le_of_eq ?_)
    ring
  -- the Sylvester perturbation
  have hsyl := hsNorm_sylvester_sub_le hwXsa hwXsa hyXHS hyYHS hβinv hβinv hwXlb hwXlb hlX hlY
  have hprod : (‖wX - wY‖ + ‖wX - wY‖) * hsNorm yY
      ≤ (β ^ 2 * α⁻¹ ^ 6 / (2 * w)) * (‖X - Y‖ * hsNorm P) := by
    have hle : ‖wX - wY‖ + ‖wX - wY‖ ≤ 2 * ((β * α⁻¹ ^ 3 / (2 * w)) * ‖X - Y‖) := by
      linarith [hb2]
    refine le_trans (mul_le_mul hle hb3 hynn (by positivity)) (le_of_eq ?_)
    field_simp
  have hkey : (β⁻¹ + β⁻¹) * hsNorm (yX - yY)
      ≤ (2 * (α⁻¹ ^ 4) + β ^ 2 * α⁻¹ ^ 6 / (2 * w)) * (‖X - Y‖ * hsNorm P) := by
    refine hsyl.trans ?_
    linarith [hqdiff, hprod]
  have hfinal : hsNorm (yX - yY)
      ≤ (β / 2) * ((2 * (α⁻¹ ^ 4) + β ^ 2 * α⁻¹ ^ 6 / (2 * w)) * (‖X - Y‖ * hsNorm P)) := by
    have hid : hsNorm (yX - yY) = (β / 2) * ((β⁻¹ + β⁻¹) * hsNorm (yX - yY)) := by
      field_simp
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  -- outer conjugation
  have hP2 : ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ ≤ β :=
    norm_rpow_half_sq_le ha.nonneg hβ.le haβ
  have houter : hsNorm (conjMap (a ^ (1/2 : ℝ)) yX - conjMap (a ^ (1/2 : ℝ)) yY)
      ≤ β * hsNorm (yX - yY) := by
    rw [← map_sub]
    refine (hsNorm_conjMap_le (hyXHS.sub hyYHS)).trans ?_
    exact mul_le_mul_of_nonneg_right hP2 (hsNorm_nonneg _)
  refine houter.trans ?_
  unfold derivLipConst
  rw [← hwdef]
  refine le_trans (mul_le_mul_of_nonneg_left hfinal hβ.le) (le_of_eq ?_)
  ring

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- **The derivative of the Wasserstein vector field is Lipschitz in the base point.** -/
theorem hsNorm_wassDerivFun_diff_le {X Y P : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hPsa : IsSelfAdjoint P) (hP : IsHilbertSchmidt P)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    {u v : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj))
    (hv : ∀ i ∈ s, (↑(v i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm (wassDerivFun s w Av X u P - wassDerivFun s w Av Y v P)
      ≤ derivLipConst α β * (‖X - Y‖ * hsNorm P) := by
  have hid : wassDerivFun s w Av X u P - wassDerivFun s w Av Y v P
      = ∑ i ∈ s, w i • (conjMap ((Av i) ^ (1/2 : ℝ))
          ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
            (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
        - conjMap ((Av i) ^ (1/2 : ℝ))
          ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
            (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ)))) := by
    unfold wassDerivFun
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
  rw [hid]
  have hHS : ∀ i ∈ s, IsHilbertSchmidt (w i • (conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
    - conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ))))) := fun i hi =>
    IsHilbertSchmidt.real_smul
      ((isHilbertSchmidt_gmInvDeriv (hA i hi) hX hP hPsa (hu i hi)).sub
        (isHilbertSchmidt_gmInvDeriv (hA i hi) hY hP hPsa (hv i hi))) _
  refine (hsNorm_sum_le hHS).trans ?_
  have hterm : ∀ i ∈ s, hsNorm (w i • (conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
    - conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ)))))
      ≤ w i * (derivLipConst α β * (‖X - Y‖ * hsNorm P)) := by
    intro i hi
    rw [hsNorm_real_smul, abs_of_nonneg (hw i hi)]
    exact mul_le_mul_of_nonneg_left
      (hsNorm_deriv_term_diff_le hα hβ (hA i hi) hX hY hPsa hP (hAα i hi) (hAβ i hi)
        hXα hXβ hYα hYβ (hu i hi) (hv i hi)) (hw i hi)
  calc ∑ i ∈ s, hsNorm (w i • (conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ)))
      - conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * P * Y⁻¹ʳ)))))
      ≤ ∑ i ∈ s, w i * (derivLipConst α β * (‖X - Y‖ * hsNorm P)) := Finset.sum_le_sum hterm
    _ = derivLipConst α β * (‖X - Y‖ * hsNorm P) := by
        rw [← Finset.sum_mul, hwsum, one_mul]

end HilbertSchmidt

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
