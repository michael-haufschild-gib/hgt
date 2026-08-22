import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinStrongMonotone

/-!
# The explicit gradient step for the Wasserstein equation

The Wasserstein vector field is Lipschitz and locally strongly monotone on a Loewner interval, so
the explicit step `X ↦ X - t Φ(X)` contracts:

`‖(X - tΦ(X)) - (Y - tΦ(Y))‖²_HS ≤ (1 - 2tκ' + t²L²) ‖X - Y‖²_HS`,

with `κ' = κ - C‖X - Y‖` the local monotonicity modulus and `L` the Lipschitz constant.  The step
never uses the inverse of the derivative, so the whole continuation is explicit.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- The Lipschitz constant of the Wasserstein vector field on `[α·1, β·1]`. -/
noncomputable def wassLipConst (α β : ℝ) : ℝ :=
  β ^ 2 * α⁻¹ ^ 3 / (2 * Real.sqrt (α * β⁻¹))

lemma wassLipConst_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 ≤ wassLipConst α β := by
  unfold wassLipConst
  have : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The Wasserstein vector field is Lipschitz on a Loewner interval.** -/
theorem hsNorm_wassField_sub_le {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) :
    hsNorm (wassField s w Av X - wassField s w Av Y)
      ≤ wassLipConst α β * hsNorm (X - Y) := by
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hinvHS : IsHilbertSchmidt ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) :=
    isHilbertSchmidt_ringInverse_sub hY hX hPHS
  have hinvn : hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm (X - Y) :=
    hsNorm_ringInverse_sub_le_of_Icc hX hY hα hXα hYα hPHS
  have hid : wassField s w Av X - wassField s w Av Y
      = ∑ i ∈ s, w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ) := by
    unfold wassField
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hY, ← smul_sub]
    congr 1
    abel
  have hgY : ∀ i ∈ s, (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm (Av i) Y⁻¹ʳ := fun i hi =>
    smul_one_le_gm (hA i hi) hY.ringInverse hα hβinv (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
  have hgX : ∀ i ∈ s, (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm (Av i) X⁻¹ʳ := fun i hi =>
    smul_one_le_gm (hA i hi) hX.ringInverse hα hβinv (hAα i hi)
      (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ)
  have hHS : ∀ i ∈ s, IsHilbertSchmidt (w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)) := fun i hi =>
    IsHilbertSchmidt.real_smul
      (isHilbertSchmidt_gm_sub (hA i hi) hY.ringInverse hX.ringInverse hγ hβ (hAβ i hi)
        (hgY i hi) (hgX i hi) hinvHS) _
  have hterm : ∀ i ∈ s, hsNorm (w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ))
      ≤ w i * (wassLipConst α β * hsNorm (X - Y)) := by
    intro i hi
    rw [hsNorm_real_smul, abs_of_nonneg (hw i hi)]
    refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
    have hgm := hsNorm_gm_sub_le_of_Icc (hA i hi) hY.ringInverse hX.ringInverse hα hγ hβ
      (hAα i hi) (hAβ i hi) (hgY i hi) (hgX i hi) hinvHS
    have hstep : (2 * (Real.sqrt (α * β⁻¹) * β⁻¹))
        * hsNorm (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
        ≤ (β * α⁻¹) * ((α⁻¹ * α⁻¹) * hsNorm (X - Y)) :=
      hgm.trans (mul_le_mul_of_nonneg_left hinvn (by positivity))
    have hid2 : hsNorm (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
        = (β / (2 * Real.sqrt (α * β⁻¹)))
          * ((2 * (Real.sqrt (α * β⁻¹) * β⁻¹))
            * hsNorm (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)) := by
      field_simp
    rw [hid2]
    refine le_trans (mul_le_mul_of_nonneg_left hstep
      (by positivity : (0:ℝ) ≤ β / (2 * Real.sqrt (α * β⁻¹)))) (le_of_eq ?_)
    unfold wassLipConst
    field_simp
  rw [hid]
  refine (hsNorm_sum_le hHS).trans ?_
  calc ∑ i ∈ s, hsNorm (w i • (gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ))
      ≤ ∑ i ∈ s, w i * (wassLipConst α β * hsNorm (X - Y)) := Finset.sum_le_sum hterm
    _ = wassLipConst α β * hsNorm (X - Y) := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- **The explicit gradient step contracts.** -/
theorem hsNormSq_gradientStep_sub_le {X Y : E →L[ℂ] E} {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 ≤ t)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) (hPsa : IsSelfAdjoint (X - Y))
    {v : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hv : ∀ i ∈ s, (↑(v i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNormSq ((X - t • wassField s w Av X) - (Y - t • wassField s w Av Y))
      ≤ (1 - 2 * t * (α * α / (2 * (β * (β * β))) - secondOrderConst α β * ‖X - Y‖)
          + t ^ 2 * (wassLipConst α β) ^ 2) * hsNormSq (X - Y) := by
  obtain ⟨D, hDdef⟩ : ∃ z : E →L[ℂ] E,
      z = wassField s w Av X - wassField s w Av Y := ⟨_, rfl⟩
  have hDHS : IsHilbertSchmidt D := by
    rw [hDdef]; exact isHilbertSchmidt_wassField_sub hα hβ hA hX hY hAα hAβ hXβ hYβ hPHS
  have hZ : (X - t • wassField s w Av X) - (Y - t • wassField s w Av Y)
      = (X - Y) - t • D := by rw [hDdef, smul_sub]; abel
  rw [hZ]
  have hsq : hsNormSq (t • D) = t ^ 2 * hsNormSq D := by
    have h1 : hsNormSq (t • D) = (hsNorm (t • D)) ^ 2 := (sq_hsNorm _).symm
    rw [h1, hsNorm_real_smul, mul_pow, sq_abs, sq_hsNorm]
  have hexp : hsNormSq ((X - Y) - t • D)
      = hsNormSq (X - Y) - 2 * (t * RCLike.re (hsInner D (X - Y))) + t ^ 2 * hsNormSq D := by
    rw [hsNormSq_sub hPHS (hDHS.real_smul t), hsq, hsInner_real_smul_right]
    congr 2
    have hconj : RCLike.re (hsInner (X - Y) D) = RCLike.re (hsInner D (X - Y)) := by
      rw [hsInner_conj_symm (X - Y) D, RCLike.conj_re]
    simp [hconj]
  rw [hexp]
  have hmono : (α * α / (2 * (β * (β * β))) - secondOrderConst α β * ‖X - Y‖)
      * hsNormSq (X - Y) ≤ RCLike.re (hsInner D (X - Y)) := by
    rw [hDdef]
    exact re_hsInner_wassField_sub_lower hα hβ hw hwsum hA hX hY hAα hAβ hXα hXβ hYα hYβ
      hPHS hPsa hv
  have hlip : hsNormSq D ≤ (wassLipConst α β) ^ 2 * hsNormSq (X - Y) := by
    have h := hsNorm_wassField_sub_le hα hβ hw hwsum hA hX hY hAα hAβ hXα hXβ hYα hYβ hPHS
    rw [hDdef]
    have h2 : (hsNorm (wassField s w Av X - wassField s w Av Y)) ^ 2
        ≤ (wassLipConst α β * hsNorm (X - Y)) ^ 2 :=
      pow_le_pow_left₀ (hsNorm_nonneg _) h 2
    rw [sq_hsNorm, mul_pow, sq_hsNorm] at h2
    exact h2
  nlinarith [hmono, hlip, ht, sq_nonneg t, hsNormSq_nonneg (X - Y)]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
