import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldHilbertSchmidt

/-!
# Subtangentiality of the Wasserstein vector field to a Loewner interval

The Loewner bounds `√α X^{-1/2} - 1 ≤ -Φ(X) ≤ √β X^{-1/2} - 1` on the interval `[α·1, β·1]`
reduce the flow invariance of that interval under `u' = -Φ(u)` to a scalar statement: for
`0 < λ ≤ 2α` and `t ∈ [α, β]`,

`t + λ(√α t^{-1/2} - 1) ≥ α`   and   `t + λ(√β t^{-1/2} - 1) ≤ β`,

both of which follow from the factorisations
`t + λ√α t^{-1/2} - (α+λ) = (√t - √α)(t + √α√t - λ)/√t` and
`β + λ - t - λ√β t^{-1/2} = (β - t)(1 - λ/(√t(√β+√t)))`.
The continuous functional calculus turns them into the operator inequalities, giving the
subtangential condition `X + λ(-Φ(X)) ∈ [α·1, β·1]`.
-/

open scoped NNReal Ring BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### The scalar inequalities -/

/-- `t + λ√α t^{-1/2} ≥ α + λ` for `t ≥ α` and `0 < λ ≤ 2α`. -/
lemma add_smul_inv_sqrt_lower {α lam t : ℝ} (hα : 0 < α) (_hlam : 0 < lam)
    (hlam2 : lam ≤ 2 * α) (ht : α ≤ t) :
    α + lam ≤ t + lam * Real.sqrt α * (Real.sqrt t)⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le hα ht
  have ha : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hau : Real.sqrt α ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hasq : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have husq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  rw [← sub_nonneg]
  have key : t + lam * Real.sqrt α * (Real.sqrt t)⁻¹ - (α + lam)
      = (Real.sqrt t - Real.sqrt α)
        * (Real.sqrt t * Real.sqrt t + Real.sqrt α * Real.sqrt t - lam) / Real.sqrt t := by
    rw [eq_div_iff (ne_of_gt hu)]
    field_simp
    nlinarith [hasq, husq]
  rw [key]
  refine div_nonneg (mul_nonneg (by linarith) ?_) hu.le
  nlinarith [hasq, husq, hau]

/-- `t + λ√β t^{-1/2} ≤ β + λ` for `α ≤ t ≤ β` and `0 < λ ≤ 2α`. -/
lemma add_smul_inv_sqrt_upper {α β lam t : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (_hlam : 0 < lam)
    (hlam2 : lam ≤ 2 * α) (ht : α ≤ t) (htβ : t ≤ β) :
    t + lam * Real.sqrt β * (Real.sqrt t)⁻¹ ≤ β + lam := by
  have ht0 : 0 < t := lt_of_lt_of_le hα ht
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have ha : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hau : Real.sqrt α ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have hub : Real.sqrt t ≤ Real.sqrt β := Real.sqrt_le_sqrt htβ
  have hab : Real.sqrt α ≤ Real.sqrt β := Real.sqrt_le_sqrt hαβ
  have hasq : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have husq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hbsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  rw [← sub_nonneg]
  have key : β + lam - (t + lam * Real.sqrt β * (Real.sqrt t)⁻¹)
      = (Real.sqrt β - Real.sqrt t)
        * (Real.sqrt t * Real.sqrt β + Real.sqrt t * Real.sqrt t - lam) / Real.sqrt t := by
    rw [eq_div_iff (ne_of_gt hu)]
    field_simp
    nlinarith [hasq, husq, hbsq]
  rw [key]
  refine div_nonneg (mul_nonneg (by linarith) ?_) hu.le
  nlinarith [hasq, husq, hbsq, hau, hab]

/-! ### The operator inequalities -/

/-- The continuous functional calculus form of the lower scalar bound. -/
theorem smul_one_le_add_smul_rpow_neg_half {X : A} (hX : IsStrictlyPositive X) {α lam : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hlam2 : lam ≤ 2 * α) (hXα : α • (1 : A) ≤ X) :
    (α + lam) • (1 : A) ≤ X + (lam * Real.sqrt α) • (X ^ (-(1/2) : ℝ)) := by
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspecα : ∀ x ∈ spectrum ℝ X, α ≤ x := by
    rw [← algebraMap_le_iff_le_spectrum (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXα
  have hne : ∀ x ∈ spectrum ℝ X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le hα (hspecα x hx)))
  have hfg : ∀ x ∈ spectrum ℝ X,
      α + lam ≤ x + lam * Real.sqrt α * (Real.sqrt x)⁻¹ := fun x hx =>
    add_smul_inv_sqrt_lower hα hlam hlam2 (hspecα x hx)
  have hcont1 : ContinuousOn (fun _ : ℝ => α + lam) (spectrum ℝ X) := by fun_prop
  have hcont2 : ContinuousOn (fun x : ℝ => x + lam * Real.sqrt α * (Real.sqrt x)⁻¹)
      (spectrum ℝ X) := by
    refine ContinuousOn.add continuousOn_id ?_
    refine ContinuousOn.mul continuousOn_const ?_
    exact ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
  have hmono := cfc_mono (R := ℝ) (a := X) hfg hcont1 hcont2
  have hL : cfc (fun _ : ℝ => α + lam) X = (α + lam) • (1 : A) := by
    rw [cfc_const _ X, Algebra.algebraMap_eq_smul_one]
  have hsq : cfc Real.sqrt X = CFC.sqrt X := by
    rw [CFC.sqrt_eq_real_sqrt X hX.nonneg, cfcₙ_eq_cfc]
  have hR : cfc (fun x : ℝ => x + lam * Real.sqrt α * (Real.sqrt x)⁻¹) X
      = X + (lam * Real.sqrt α) • (X ^ (-(1/2) : ℝ)) := by
    have hcinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ X) :=
      ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
    have hcmul : ContinuousOn (fun x : ℝ => lam * Real.sqrt α * (Real.sqrt x)⁻¹)
        (spectrum ℝ X) := ContinuousOn.mul continuousOn_const hcinv
    rw [cfc_add X (fun x : ℝ => x) (fun x : ℝ => lam * Real.sqrt α * (Real.sqrt x)⁻¹)
        continuousOn_id hcmul,
      cfc_id' ℝ X, cfc_const_mul (lam * Real.sqrt α) (fun x : ℝ => (Real.sqrt x)⁻¹) X hcinv,
      cfc_inv Real.sqrt X hne, hsq, CFC.sqrt_eq_rpow, ringInverse_rpow_half hX]
  rwa [hL, hR] at hmono

/-- The continuous functional calculus form of the upper scalar bound. -/
theorem add_smul_rpow_neg_half_le_smul_one {X : A} (hX : IsStrictlyPositive X) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam) (hlam2 : lam ≤ 2 * α)
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A)) :
    X + (lam * Real.sqrt β) • (X ^ (-(1/2) : ℝ)) ≤ (β + lam) • (1 : A) := by
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspecα : ∀ x ∈ spectrum ℝ X, α ≤ x := by
    rw [← algebraMap_le_iff_le_spectrum (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXα
  have hspecβ : ∀ x ∈ spectrum ℝ X, x ≤ β := by
    rw [← le_algebraMap_iff_spectrum_le (a := X) hXsa, Algebra.algebraMap_eq_smul_one]
    exact hXβ
  have hne : ∀ x ∈ spectrum ℝ X, Real.sqrt x ≠ 0 := fun x hx =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le hα (hspecα x hx)))
  have hfg : ∀ x ∈ spectrum ℝ X,
      x + lam * Real.sqrt β * (Real.sqrt x)⁻¹ ≤ β + lam := fun x hx =>
    add_smul_inv_sqrt_upper hα hαβ hlam hlam2 (hspecα x hx) (hspecβ x hx)
  have hcont2 : ContinuousOn (fun _ : ℝ => β + lam) (spectrum ℝ X) := by fun_prop
  have hcont1 : ContinuousOn (fun x : ℝ => x + lam * Real.sqrt β * (Real.sqrt x)⁻¹)
      (spectrum ℝ X) := by
    refine ContinuousOn.add continuousOn_id ?_
    refine ContinuousOn.mul continuousOn_const ?_
    exact ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
  have hmono := cfc_mono (R := ℝ) (a := X) hfg hcont1 hcont2
  have hR : cfc (fun _ : ℝ => β + lam) X = (β + lam) • (1 : A) := by
    rw [cfc_const _ X, Algebra.algebraMap_eq_smul_one]
  have hsq : cfc Real.sqrt X = CFC.sqrt X := by
    rw [CFC.sqrt_eq_real_sqrt X hX.nonneg, cfcₙ_eq_cfc]
  have hL : cfc (fun x : ℝ => x + lam * Real.sqrt β * (Real.sqrt x)⁻¹) X
      = X + (lam * Real.sqrt β) • (X ^ (-(1/2) : ℝ)) := by
    have hcinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ X) :=
      ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) hne
    have hcmul : ContinuousOn (fun x : ℝ => lam * Real.sqrt β * (Real.sqrt x)⁻¹)
        (spectrum ℝ X) := ContinuousOn.mul continuousOn_const hcinv
    rw [cfc_add X (fun x : ℝ => x) (fun x : ℝ => lam * Real.sqrt β * (Real.sqrt x)⁻¹)
        continuousOn_id hcmul,
      cfc_id' ℝ X, cfc_const_mul (lam * Real.sqrt β) (fun x : ℝ => (Real.sqrt x)⁻¹) X hcinv,
      cfc_inv Real.sqrt X hne, hsq, CFC.sqrt_eq_rpow, ringInverse_rpow_half hX]
  rwa [hL, hR] at hmono

/-! ### Loewner bounds for the field and the subtangential condition -/

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- Two-sided Loewner bounds for `-Φ` on the interval `[α·1, β·1]`. -/
theorem neg_wassField_Icc {X : A} (hX : IsStrictlyPositive X) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1 ≤ -wassField s w Av X ∧
      -wassField s w Av X ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1 := by
  have hid : -wassField s w Av X = ∑ i ∈ s, w i • (gm (Av i) X⁻¹ʳ - 1) := by
    unfold wassField
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, ← smul_neg]
    congr 1
    abel
  have hkey : ∀ i ∈ s, Real.sqrt α • X ^ (-(1/2) : ℝ) ≤ gm (Av i) X⁻¹ʳ ∧
      gm (Av i) X⁻¹ʳ ≤ Real.sqrt β • X ^ (-(1/2) : ℝ) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← gm_smul_one_ringInverse hα hX]
      exact gm_mono_left (IsStrictlyPositive.smul hα isStrictlyPositive_one) (hA i hi)
        hX.ringInverse (hAα i hi)
    · rw [← gm_smul_one_ringInverse hβ hX]
      exact gm_mono_left (hA i hi) (IsStrictlyPositive.smul hβ isStrictlyPositive_one)
        hX.ringInverse (hAβ i hi)
  constructor
  · rw [hid, show Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1
      = ∑ i ∈ s, w i • (Real.sqrt α • X ^ (-(1/2) : ℝ) - 1) by
        rw [← Finset.sum_smul, hwsum, one_smul]]
    exact Finset.sum_le_sum fun i hi =>
      smul_le_smul_of_nonneg_left (sub_le_sub_right (hkey i hi).1 1) (hw i hi)
  · rw [hid, show Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1
      = ∑ i ∈ s, w i • (Real.sqrt β • X ^ (-(1/2) : ℝ) - 1) by
        rw [← Finset.sum_smul, hwsum, one_smul]]
    exact Finset.sum_le_sum fun i hi =>
      smul_le_smul_of_nonneg_left (sub_le_sub_right (hkey i hi).2 1) (hw i hi)

/-- **Lemma 4.7 (Kim–Mer–Pálfia), subtangential condition.**  For every `X` in the Loewner
interval `[α·1, β·1]` and every step `0 < λ ≤ 2α`, the explicit step `X + λ(-Φ(X))` stays in the
interval.  This is the subtangentiality that makes `[α·1, β·1]` invariant under `u' = -Φ(u)`. -/
theorem sub_smul_wassField_mem_Icc {X : A} (hX : IsStrictlyPositive X) {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam) (hlam2 : lam ≤ 2 * α)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    (hXα : α • (1 : A) ≤ X) (hXβ : X ≤ β • (1 : A)) :
    α • (1 : A) ≤ X - lam • wassField s w Av X ∧
      X - lam • wassField s w Av X ≤ β • (1 : A) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  obtain ⟨hlow, hupp⟩ := neg_wassField_Icc hX hα hβ hw hwsum hA hAα hAβ
  have hstep : X - lam • wassField s w Av X = X + lam • (-wassField s w Av X) := by
    rw [smul_neg]; abel
  constructor
  · have h1 : X + lam • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        ≤ X + lam • (-wassField s w Av X) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hlow hlam.le) X
    refine le_trans ?_ (hstep ▸ h1)
    have h2 := smul_one_le_add_smul_rpow_neg_half hX hα hlam hlam2 hXα
    have h3 : X + lam • (Real.sqrt α • (X ^ (-(1/2) : ℝ)) - 1)
        = (X + (lam * Real.sqrt α) • (X ^ (-(1/2) : ℝ))) - lam • (1 : A) := by
      rw [smul_sub, smul_smul]; abel
    rw [h3]
    have h4 : (α : ℝ) • (1 : A) = (α + lam) • (1 : A) - lam • (1 : A) := by
      rw [← sub_smul]; congr 1; ring
    rw [h4]
    exact sub_le_sub_right h2 _
  · have h1 : X + lam • (-wassField s w Av X)
        ≤ X + lam • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1) :=
      add_le_add_right (smul_le_smul_of_nonneg_left hupp hlam.le) X
    refine le_trans (hstep ▸ h1) ?_
    have h2 := add_smul_rpow_neg_half_le_smul_one hX hα hαβ hlam hlam2 hXα hXβ
    have h3 : X + lam • (Real.sqrt β • (X ^ (-(1/2) : ℝ)) - 1)
        = (X + (lam * Real.sqrt β) • (X ^ (-(1/2) : ℝ))) - lam • (1 : A) := by
      rw [smul_sub, smul_smul]; abel
    rw [h3]
    have h4 : (β : ℝ) • (1 : A) = (β + lam) • (1 : A) - lam • (1 : A) := by
      rw [← sub_smul]; congr 1; ring
    rw [h4]
    exact sub_le_sub_right h2 _

/-! ### Boundedness and global Lipschitz continuity in the operator norm -/

/-- The inverse is Lipschitz on a Loewner interval, in the operator norm. -/
lemma norm_ringInverse_sub_le_of_smul_one_le {X Y : A} (hX : IsStrictlyPositive X)
    (hY : IsStrictlyPositive Y) {α : ℝ} (hα : 0 < α)
    (hXα : α • (1 : A) ≤ X) (hYα : α • (1 : A) ≤ Y) :
    ‖(X⁻¹ʳ : A) - Y⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖X - Y‖ := by
  have hXn : ‖(X⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hYn : ‖(Y⁻¹ʳ : A)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  have hid : (X⁻¹ʳ : A) - Y⁻¹ʳ = X⁻¹ʳ * (Y - X) * Y⁻¹ʳ := by
    have h1 : (X⁻¹ʳ : A) * (Y - X) * Y⁻¹ʳ
        = X⁻¹ʳ * (Y * Y⁻¹ʳ) - (X⁻¹ʳ * X) * Y⁻¹ʳ := by noncomm_ring
    rw [h1, Ring.mul_inverse_cancel _ hY.isUnit, Ring.inverse_mul_cancel _ hX.isUnit,
      mul_one, one_mul]
  rw [hid]
  have hYX : ‖Y - X‖ = ‖X - Y‖ := by rw [← norm_neg (X - Y), neg_sub]
  calc ‖(X⁻¹ʳ : A) * (Y - X) * Y⁻¹ʳ‖ ≤ ‖(X⁻¹ʳ : A) * (Y - X)‖ * ‖(Y⁻¹ʳ : A)‖ := norm_mul_le _ _
    _ ≤ (‖(X⁻¹ʳ : A)‖ * ‖Y - X‖) * ‖(Y⁻¹ʳ : A)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (α⁻¹ * ‖X - Y‖) * α⁻¹ := by
        rw [hYX]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hXn (norm_nonneg _)) hYn (norm_nonneg _)
          (by positivity)
    _ = (α⁻¹ * α⁻¹) * ‖X - Y‖ := by ring

/-- The upper Loewner bound for `X^{-1/2}` on a Loewner interval. -/
lemma rpow_neg_half_le_smul_one {X : A} (hX : IsStrictlyPositive X) {α : ℝ} (hα : 0 < α)
    (hXα : α • (1 : A) ≤ X) :
    X ^ (-(1/2) : ℝ) ≤ (Real.sqrt α⁻¹) • (1 : A) := by
  have hinv : (X⁻¹ʳ : A) ≤ α⁻¹ • (1 : A) := ringInverse_le_of_smul_one_le hα hXα
  have hsq := CFC.sqrt_le_sqrt _ _ hinv
  rw [cfcSqrt_smul (inv_pos.mpr hα).le (isStrictlyPositive_one (A := A)).nonneg,
    CFC.sqrt_one] at hsq
  rw [show (X ^ (-(1/2) : ℝ) : A) = CFC.sqrt (X⁻¹ʳ) by
    rw [CFC.sqrt_eq_rpow, rpow_half_ringInverse hX]]
  exact hsq

/-- **Lemma 4.6 (Kim–Mer–Pálfia).**  On the Loewner interval `[α·1, β·1]` the Wasserstein vector
field is bounded and globally Lipschitz in the operator norm. -/
theorem exists_bound_lipschitz_wassField {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A)) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
      (∀ X : A, IsStrictlyPositive X → α • (1 : A) ≤ X → X ≤ β • (1 : A) →
        ‖wassField s w Av X‖ ≤ B) ∧
      (∀ X Y : A, IsStrictlyPositive X → IsStrictlyPositive Y →
        α • (1 : A) ≤ X → X ≤ β • (1 : A) → α • (1 : A) ≤ Y → Y ≤ β • (1 : A) →
        ‖wassField s w Av X - wassField s w Av Y‖ ≤ L * ‖X - Y‖) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨1 + Real.sqrt β * Real.sqrt α⁻¹,
    β * α⁻¹ * (α⁻¹ * α⁻¹) / (2 * (Real.sqrt (α * β⁻¹) * β⁻¹)), by positivity, by positivity,
    ?_, ?_⟩
  · -- boundedness
    intro X hX hXα hXβ
    have hgm : ∀ i ∈ s, ‖gm (Av i) X⁻¹ʳ‖ ≤ Real.sqrt β * Real.sqrt α⁻¹ := by
      intro i hi
      have hup : gm (Av i) X⁻¹ʳ ≤ Real.sqrt β • (X ^ (-(1/2) : ℝ)) := by
        rw [← gm_smul_one_ringInverse hβ hX]
        exact gm_mono_left (hA i hi) (IsStrictlyPositive.smul hβ isStrictlyPositive_one)
          hX.ringInverse (hAβ i hi)
      have hup2 : Real.sqrt β • (X ^ (-(1/2) : ℝ))
          ≤ (Real.sqrt β * Real.sqrt α⁻¹) • (1 : A) := by
        have h := smul_le_smul_of_nonneg_left (rpow_neg_half_le_smul_one hX hα hXα)
          (Real.sqrt_nonneg β)
        rwa [smul_smul] at h
      exact norm_le_of_le_smul_one (gm_nonneg (Av i) X⁻¹ʳ)
        (r := Real.sqrt β * Real.sqrt α⁻¹) (by positivity) (hup.trans hup2)
    unfold wassField
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ s, ‖w i • ((1 : A) - gmInvMap (Av i) X)‖
        ≤ w i * (1 + Real.sqrt β * Real.sqrt α⁻¹) := by
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
      rw [gmInvMap_eq_gm hX]
      refine (norm_sub_le _ _).trans ?_
      have hone : ‖(1 : A)‖ ≤ 1 :=
        norm_le_of_le_smul_one zero_le_one zero_le_one (by rw [one_smul])
      exact add_le_add hone (hgm i hi)
    calc ∑ i ∈ s, ‖w i • ((1 : A) - gmInvMap (Av i) X)‖
        ≤ ∑ i ∈ s, w i * (1 + Real.sqrt β * Real.sqrt α⁻¹) := Finset.sum_le_sum hterm
      _ = 1 + Real.sqrt β * Real.sqrt α⁻¹ := by rw [← Finset.sum_mul, hwsum, one_mul]
  · -- Lipschitz continuity
    intro X Y hX hY hXα hXβ hYα hYβ
    have hinvn : ‖(Y⁻¹ʳ : A) - X⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖X - Y‖ := by
      have h := norm_ringInverse_sub_le_of_smul_one_le hY hX hα hYα hXα
      rwa [show ‖Y - X‖ = ‖X - Y‖ by rw [← norm_neg (X - Y), neg_sub]] at h
    have hid : wassField s w Av X - wassField s w Av Y
        = ∑ i ∈ s, w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ) := by
      unfold wassField
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hY, ← smul_sub]
      congr 1
      abel
    have hgY : ∀ i ∈ s, (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm (Av i) Y⁻¹ʳ := fun i hi =>
      smul_one_le_gm (hA i hi) hY.ringInverse hα hβinv (hAα i hi)
        (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
    have hgX : ∀ i ∈ s, (Real.sqrt (α * β⁻¹)) • (1 : A) ≤ gm (Av i) X⁻¹ʳ := fun i hi =>
      smul_one_le_gm (hA i hi) hX.ringInverse hα hβinv (hAα i hi)
        (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ)
    have hterm : ∀ i ∈ s, ‖w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)‖
        ≤ w i * ((β * α⁻¹ * (α⁻¹ * α⁻¹) / (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))) * ‖X - Y‖) := by
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
      have hgmi := norm_gm_sub_le_of_Icc (hA i hi) hY.ringInverse hX.ringInverse hα hγ hβ
        (hAα i hi) (hAβ i hi) (hgY i hi) (hgX i hi)
      have hstep : (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))
          * ‖gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ‖
          ≤ (β * α⁻¹) * ((α⁻¹ * α⁻¹) * ‖X - Y‖) :=
        hgmi.trans (mul_le_mul_of_nonneg_left hinvn (by positivity))
      rw [← le_div_iff₀' (by positivity : (0:ℝ) < 2 * (Real.sqrt (α * β⁻¹) * β⁻¹))] at hstep
      refine hstep.trans (le_of_eq ?_)
      field_simp
    rw [hid]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ s, ‖w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)‖
        ≤ ∑ i ∈ s, w i * ((β * α⁻¹ * (α⁻¹ * α⁻¹)
            / (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))) * ‖X - Y‖) := Finset.sum_le_sum hterm
      _ = (β * α⁻¹ * (α⁻¹ * α⁻¹) / (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))) * ‖X - Y‖ := by
          rw [← Finset.sum_mul, hwsum, one_mul]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
