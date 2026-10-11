import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalOnset
import GaloisForLFunctions.RHTower.XiCosineShiftUniformLosslessHeights

/-!
# Sharp defect transport at every large height

**Theorem** (`eventually_windowDefectCount_le_transport`). For every depth `0 < h ≤ ½` and all
large `T`, the following holds. The non-real zeros of `cos(hD)Ξ` with real part in `[T, 2T]`
(counted with multiplicity) number at most `2·#{ρ : ξ(ρ) = 0, Re ρ ≥ ½ + h, T/2 ≤ Im ρ ≤ 3T} + 2`.

This is the frontier-map item "the non-real zeros of `cos(hD)Ξ` up to `T` number
`≤ 4N(½+h, T) + O(log T)`", in sharp form. The error is the constant `2`, not `O(log T)`.

**Proof.**
* The heights in `[20, V]` that lie in the shadow `[γ − |β − ½|, γ + |β − ½|]` of some off-line
  zero have measure at most `2·offLineMoment(V + 1)` (`volume_shadowBad_le`).
* Selberg's bound `offLineMoment V ≤ 67V/1000` makes this less than `T/2` for `V = 3T`.
* So `[T/2, T]` and `[2T, 3T]` contain shadow-free heights that also avoid the finitely many real
  zeros of `cos(hD)Ξ` and the ordinates of critical zeros
  (`exists_shadowFree_admissible_height`).
* Between such heights, apply the window transport law (`windowDefectCount_le_transport`).
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **The shadows of the off-line zeros have small measure.** -/
theorem volume_shadowBad_le (V : ℝ) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ v : ℂ, XiC v = 0 ∧ v.im ≠ 0 ∧ (t - v.re) ^ 2 ≤ v.im ^ 2}
      ≤ ENNReal.ofReal (2 * offLineMoment (V + 1)) := by
  classical
  set F := boxFinsetLe (V + 1) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ ∃ v : ℂ, XiC v = 0 ∧ v.im ≠ 0 ∧
      (t - v.re) ^ 2 ≤ v.im ^ 2} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, v, hv, hvim, hshadow⟩
    have hvhalf := abs_im_lt_half_of_XiC_eq_zero hv
    have hclose : |t - v.re| ≤ |v.im| := by
      have := sq_le_sq.mp hshadow; simpa using this
    set ρ : ℂ := 1 / 2 + v * I with hρ
    have hρ0 : xi ρ = 0 := by rw [← hv, XiC]
    have hρre : ρ.re = 1 / 2 - v.im := by simp [hρ]; ring
    have hρim : ρ.im = v.re := by simp [hρ]
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |v.im| ∧ w.im = v.re := by
      rcases lt_or_gt_of_ne hvim with hneg | hpos
      · exact ⟨ρ, hρ0, by rw [hρre, abs_of_neg hneg]; ring, hρim⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ0, map_zero], ?_, ?_⟩
        · simp [hρ, abs_of_pos hpos]; ring
        · simp [hρ]
    have hvpos : 0 < |v.im| := abs_pos.mpr hvim
    have hwmem : w ∈ F := by
      rw [hF, mem_boxFinsetLe]
      refine ⟨by rw [hwre]; linarith, xi_zero_re_lt_one hw, ?_, ?_, hw⟩
      · rw [hwim]; linarith [(abs_le.mp hclose).1, (abs_le.mp hclose).2, ht.1]
      · rw [hwim]; linarith [(abs_le.mp hclose).1, (abs_le.mp hclose).2, ht.2]
    refine Set.mem_iUnion₂.mpr ⟨w, hwmem, ?_, ?_⟩
    · rw [hwre, hwim]; linarith [(abs_le.mp hclose).1]
    · rw [hwre, hwim]; linarith [(abs_le.mp hclose).2]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    obtain ⟨hw1, -, -, -, hw0⟩ := hw
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hw0
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    have := hw.1
    have : (0 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  rfl

/-- The real zeros of `Ξ` and of `cos(hD)Ξ` in a bounded interval are finite. -/
theorem finite_real_zeros_cosProducer (h a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ cosProducer h t = 0}.Finite := by
  have hfin := finite_zeros_cosProducer_closedBall h (((a + b) / 2 : ℝ) : ℂ) ((b - a) / 2 + 1)
  refine (hfin.preimage (fun x _ y _ hxy => Complex.ofReal_inj.mp hxy)).subset ?_
  rintro t ⟨ht, h0⟩
  refine ⟨(dist_center_lt_of_window (z := (t : ℂ)) (by simpa using ht) (by simp)).le, h0⟩

/-- **Admissible heights exist.** If the shadows in `[20, V]` have measure less than `L`, then
every interval `[α, α + L] ⊆ [20, V]` contains a shadow-free height `t` with
`cos(hD)Ξ(t) ≠ 0`. -/
theorem exists_shadowFree_admissible_height {h V α L : ℝ} (hα : 20 ≤ α) (hαV : α + L ≤ V)
    (hsmall : 2 * offLineMoment (V + 1) < L) :
    ∃ t ∈ Icc α (α + L), (∀ v, XiC v = 0 → v.im ^ 2 < (t - v.re) ^ 2) ∧ cosProducer h t ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set bad := {t : ℝ | t ∈ Icc 20 V ∧ ∃ v : ℂ, XiC v = 0 ∧ v.im ≠ 0 ∧
    (t - v.re) ^ 2 ≤ v.im ^ 2} with hbad
  set Z0 := {t : ℝ | t ∈ Icc α (α + L) ∧ XiC t = 0} with hZ0
  set Zh := {t : ℝ | t ∈ Icc α (α + L) ∧ cosProducer h t = 0} with hZh
  have hZ0fin : Z0.Finite := by
    refine (finite_real_zeros_cosProducer 0 α (α + L)).subset ?_
    rintro t ⟨ht, h0⟩; exact ⟨ht, by rw [cosProducer_zero]; exact h0⟩
  have hZhfin : Zh.Finite := finite_real_zeros_cosProducer h α (α + L)
  have hcover : Icc α (α + L) ⊆ bad ∪ Z0 ∪ Zh := by
    intro t ht
    by_cases hA : cosProducer h t = 0
    · exact Or.inr ⟨ht, hA⟩
    have hnfree : ¬ ∀ v, XiC v = 0 → v.im ^ 2 < (t - v.re) ^ 2 := fun hfree => hA (hcon t ht hfree)
    push Not at hnfree
    obtain ⟨v, hv, hvle⟩ := hnfree
    by_cases hvim : v.im = 0
    · refine Or.inl (Or.inr ⟨ht, ?_⟩)
      have hsq : (t - v.re) ^ 2 ≤ 0 := by rw [hvim] at hvle; simpa using hvle
      have htv : t = v.re := by nlinarith [sq_nonneg (t - v.re)]
      have hve : v = ((t : ℝ) : ℂ) := Complex.ext (by simp [htv]) (by simp [hvim])
      rw [← hve]; exact hv
    · exact Or.inl (Or.inl ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, v, hv, hvim, hvle⟩)
  have hvol := measure_mono (μ := volume) hcover
  have hZ0 : volume Z0 = 0 := hZ0fin.measure_zero _
  have hZh : volume Zh = 0 := hZhfin.measure_zero _
  have hle : volume (bad ∪ Z0 ∪ Zh) ≤ ENNReal.ofReal (2 * offLineMoment (V + 1)) := by
    calc volume (bad ∪ Z0 ∪ Zh) ≤ volume (bad ∪ Z0) + volume Zh := measure_union_le _ _
      _ ≤ volume bad + volume Z0 + volume Zh := by gcongr; exact measure_union_le _ _
      _ = volume bad := by rw [hZ0, hZh, add_zero, add_zero]
      _ ≤ _ := volume_shadowBad_le V
  have hL0 : 0 < L := lt_of_le_of_lt (by
    have : 0 ≤ offLineMoment (V + 1) := Finset.sum_nonneg fun w hw => offLineMoment_term_nonneg hw
    linarith) hsmall
  rw [Real.volume_Icc, show α + L - α = L by ring] at hvol
  have := (hvol.trans hle)
  rw [ENNReal.ofReal_le_ofReal_iff (by
    have : 0 ≤ offLineMoment (V + 1) := Finset.sum_nonneg fun w hw => offLineMoment_term_nonneg hw
    linarith)] at this
  linarith

/-- The defect count is monotone in the window. -/
theorem windowDefectCount_mono {T₁ T₂ T₁' T₂' h : ℝ} (h1 : T₁ ≤ T₁') (h2 : T₂' ≤ T₂) :
    windowDefectCount T₁' T₂' h ≤ windowDefectCount T₁ T₂ h := by
  unfold windowDefectCount
  refine Finset.sum_le_sum_of_subset fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz ⊢
  obtain ⟨hre, him, h0⟩ := hz
  exact ⟨⟨h1.trans hre.1, hre.2.trans h2⟩, him, h0⟩

/-- **Sharp defect transport at every large height.** -/
theorem eventually_windowDefectCount_le_transport {h : ℝ} (hh : 0 < h) :
    ∀ᶠ T in atTop, windowDefectCount T (2 * T) h ≤
      2 * ∑ w ∈ (boxFinsetLe (3 * T)).filter (fun w => 1 / 2 + h ≤ w.re ∧ T / 2 ≤ w.im),
        (analyticOrderAt xi w).toNat + 2 := by
  classical
  have hsel := ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  have hshift : Tendsto (fun T : ℝ => 3 * T + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hshift.eventually hsel, eventually_ge_atTop (40 : ℝ)] with T hT hT40
  have hsmall : 2 * offLineMoment (3 * T + 1) < T / 2 := by linarith
  -- admissible window ends
  obtain ⟨T₁, hT₁I, hg₁, hA₁⟩ := exists_shadowFree_admissible_height (h := h) (V := 3 * T)
    (α := T / 2) (L := T / 2) (by linarith) (by linarith) hsmall
  obtain ⟨T₂, hT₂I, hg₂, hA₂⟩ := exists_shadowFree_admissible_height (h := h) (V := 3 * T)
    (α := 2 * T) (L := T / 2) (by linarith) (by linarith) hsmall
  have hreA : ∀ x : ℝ, cosProducer h x ≠ 0 → (xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).re ≠ 0 := by
    intro x hx hre
    apply hx
    rw [cosProducer_ofReal]
    have e : (1 / 2 : ℂ) + h + x * I = ((1 / 2 + h : ℝ) : ℂ) + x * I := by push_cast; ring
    rw [e, hre]; simp
  have hT12 : T₁ < T₂ := by linarith [hT₁I.2, hT₂I.1]
  obtain ⟨Zξ, hZξ, hD⟩ := windowDefectCount_le_transport hh hT12 hg₁ hg₂ (hreA T₁ hA₁)
    (hreA T₂ hA₂)
  have hmono := windowDefectCount_mono (h := h) (T₁ := T₁) (T₂ := T₂) (T₁' := T) (T₂' := 2 * T)
    (by linarith [hT₁I.2]) hT₂I.1
  have hsub : Zξ ⊆ (boxFinsetLe (3 * T)).filter (fun w => 1 / 2 + h ≤ w.re ∧ T / 2 ≤ w.im) := by
    intro w hw
    obtain ⟨hR, h0, hre⟩ := (hZξ w).mp hw
    obtain ⟨-, him⟩ := mem_reProdIm.mp hR
    rw [Finset.mem_filter, mem_boxFinsetLe]
    refine ⟨⟨by linarith, xi_zero_re_lt_one h0, by linarith [him.1, hT₁I.1],
      by linarith [him.2, hT₂I.2], h0⟩, hre, by linarith [him.1, hT₁I.1]⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => (analyticOrderAt xi w).toNat) hsub
  omega

end

end RHTower
