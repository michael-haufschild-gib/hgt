import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourFixedGlobal

open MeasureTheory Set Matrix
namespace RHTower
noncomputable section

private theorem strictEven
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ((thetaCuspCenterMixedSignedHankel a 7).submatrix
      (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))
      (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))).PosDef := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let K : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun r =>
    if 0 < r then thetaCuspCenterCorrectedEvenFour a 1000000000000 r else 0
  have hEntry : ∀ i j, Integrable (fun r => K r i j) μ := by
    intro i j
    apply (integrableOn_thetaCuspCenterCorrectedEvenFour ha0.le ha 1000000000000 i j).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    simp [K, hr]
  have hKpos : ∀ r, 0 < r → (K r).PosDef := by
    intro r hr
    simpa only [K, if_pos hr] using
      thetaCuspCenterCorrectedEvenFour_posDef_of_source ha0 (by positivity) hr
        (thetaCuspNativeEvenFourFixed_posDef (by linarith : 0 ≤ r / 2))
  have hK : ∀ r, (K r).PosSemidef := by
    intro r
    by_cases hr : 0 < r
    · exact (hKpos r hr).posSemidef
    · simpa only [K, if_neg hr] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4) (Fin 4) ℝ).PosSemidef)
  have hMass : μ (Ioo (1 : ℝ) 2) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo (1 : ℝ) 2 ⊆ Ioi 0 from
        fun r hr => lt_trans (by norm_num : (0 : ℝ) < 1) hr.1), Real.volume_Ioo]
    norm_num
  have hSeparate : ∀ v : Fin 4 → ℝ, v ≠ 0 →
      0 < μ (Function.support (HTGeometry.integralMatrixKernelQuadratic K v)) := by
    intro v hv
    have hSub : Ioo (1 : ℝ) 2 ⊆
        Function.support (HTGeometry.integralMatrixKernelQuadratic K v) := by
      intro r hr
      have hrpos : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1) hr.1
      change star v ⬝ᵥ (K r *ᵥ v) ≠ 0
      exact (hKpos r hrpos).dotProduct_mulVec_pos hv |>.ne'
    have hmono := measure_mono (μ := μ) hSub
    rw [hMass] at hmono
    exact lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hmono
  have hIntegral := HTGeometry.integralMatrixKernel_posDef_of_support μ K hEntry hK hSeparate
  have hBlock : HTGeometry.integralMatrixKernel μ K =
      (thetaCuspCenterMixedSignedHankel a 7).submatrix
        (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))
        (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7)) := by
    ext i j
    have hEntryEq : (∫ r : ℝ in Ioi 0, K r i j) =
        ∫ r : ℝ in Ioi 0,
          thetaCuspCenterCorrectedEvenFour a 1000000000000 r i j := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      change 0 < r at hr
      simp [K, hr]
    change (∫ r : ℝ in Ioi 0, K r i j) =
      thetaCuspCenterMixedSignedJet a (2 * i.val + 2 * j.val)
    rw [hEntryEq, integral_thetaCuspCenterCorrectedEvenFour ha0.le ha]
    rw [show 2 * i.val + 2 * j.val = 2 * (i.val + j.val) by omega,
      thetaCuspCenterMixedSignedJet_even]
  rw [hBlock] at hIntegral
  exact hIntegral

theorem thetaCuspCenterMixedSignedHankel_seven_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 7).PosDef := by
  let e : Fin 4 → Fin 7 := fun i => ⟨2 * i.val, by omega⟩
  let o : Fin 3 → Fin 7 := fun i => ⟨2 * i.val + 1, by omega⟩
  let o6 : Fin 3 → Fin 6 := fun i => ⟨2 * i.val + 1, by omega⟩
  have hEven : ((thetaCuspCenterMixedSignedHankel a 7).submatrix e e).PosDef :=
    strictEven ha0 ha
  have ho6inj : Function.Injective o6 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only [o6] at h
    omega
  have hOdd6 : ((thetaCuspCenterMixedSignedHankel a 6).submatrix o6 o6).PosDef :=
    (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha).submatrix ho6inj
  have hOddEq : (thetaCuspCenterMixedSignedHankel a 7).submatrix o o =
      (thetaCuspCenterMixedSignedHankel a 6).submatrix o6 o6 := by
    ext i j
    rfl
  have hOdd : ((thetaCuspCenterMixedSignedHankel a 7).submatrix o o).PosDef := by
    rw [hOddEq]
    exact hOdd6
  have hHerm : (thetaCuspCenterMixedSignedHankel a 7).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
  have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
  have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
  have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
  have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
  have ho5 := thetaCuspCenterMixedSignedJet_odd a 5
  norm_num at ho0 ho1 ho2 ho3 ho4 ho5
  have hSplit (v : Fin 7 → ℝ) :
      star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a 7 *ᵥ v) =
        star (v ∘ e) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 7).submatrix e e *ᵥ (v ∘ e)) +
        star (v ∘ o) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 7).submatrix o o *ᵥ (v ∘ o)) := by
    simp [dotProduct, mulVec, Fin.sum_univ_succ,
      thetaCuspCenterMixedSignedHankel, e, o, ho0, ho1, ho2, ho3, ho4, ho5] <;> ring
  have hCover (v : Fin 7 → ℝ) (he : v ∘ e = 0) (ho : v ∘ o = 0) : v = 0 := by
    funext i
    fin_cases i
    · simpa [e, Function.comp_def] using congrFun he (0 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (0 : Fin 3)
    · simpa [e, Function.comp_def] using congrFun he (1 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (1 : Fin 3)
    · simpa [e, Function.comp_def] using congrFun he (2 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (2 : Fin 3)
    · simpa [e, Function.comp_def] using congrFun he (3 : Fin 4)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro v hv
  rw [hSplit]
  by_cases he : v ∘ e = 0
  · have ho : v ∘ o ≠ 0 := by
      intro hz
      exact hv (hCover v he hz)
    exact add_pos_of_nonneg_of_pos
      (hEven.posSemidef.dotProduct_mulVec_nonneg (v ∘ e))
      (hOdd.dotProduct_mulVec_pos ho)
  · exact add_pos_of_pos_of_nonneg
      (hEven.dotProduct_mulVec_pos he)
      (hOdd.posSemidef.dotProduct_mulVec_nonneg (v ∘ o))

end
end RHTower
