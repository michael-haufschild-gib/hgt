import GaloisForLFunctions.RHTower.XiCosineShiftDefectTransportAllHeights
import GaloisForLFunctions.RHTower.SelbergNearLineZeroDensity
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# The PTR producer at the critical scale

**Theorem** (`exists_criticalScale_windowDefectCount_le`). There are `A, K > 0` with the following
property. For every `a ≥ 1` and all large `U`, the non-real zeros of `cos(hD)Ξ` at depth
`h = 2a/log U` with real part in `[U/3, 2U/5]` number at most
`(log U/(π a)) · (U/8 · selbergNearLineRate A a + K log U) + 2`.

The rate decays like `1/a` (`selbergNearLineRate_le_div`), and `[U/3, 2U/5]` carries
`≍ U log U` zeros. So at the critical depth `2a/log U` the PTR producer is lossless on all but an
`O(1/a²)` proportion of its spectrum, unconditionally.

**Proof.** Selberg's near-line density (`exists_selberg_nearLine_zeroDensity`) counts the zeros of
`ζ` with `Re ρ ≥ ½ + 2a/log U` in a window `[T₁, T₂] ⊂ (U/4, U/2)`. Inside that window choose
shadow-free admissible heights `S₁ ≤ U/3`, `S₂ ≥ 2U/5`. They exist because the shadows cover at
most `2·offLineMoment ≤ 0.067U` of `[20, U/2]` (`exists_shadowFree_admissible_height`). The sharp
transport law (`windowDefectCount_le_transport`) gives at most twice those zeros, plus `2`. In the
strip `ξ` and `ζ` have equal orders.

So the PTR producer's "nonlocal port" at the critical scale is the mollifier: its defect count is
governed by the mollified mean square that drives Selberg's density estimate.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **The PTR producer at the critical scale.** -/
theorem exists_criticalScale_windowDefectCount_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ a : ℝ, 1 ≤ a → ∀ᶠ U in atTop,
      (windowDefectCount (U / 3) (2 * U / 5) (2 * a / Real.log U) : ℝ) ≤
        Real.log U / (Real.pi * a) * (U / 8 * selbergNearLineRate A a + K * Real.log U) + 2 := by
  classical
  obtain ⟨A, K, hA, hK, hsel⟩ := exists_selberg_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, fun a ha => ?_⟩
  have hmom := ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper
  have hshift : Tendsto (fun U : ℝ => U / 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_id.atTop_div_const (by norm_num))
  filter_upwards [hsel a ha, hshift.eventually hmom, eventually_ge_atTop (Real.exp (2 * a)),
    eventually_ge_atTop (1000 : ℝ)] with U hU hmU hUexp hU1000
  obtain ⟨T₁, hT₁, T₂, hT₂, hZsel⟩ := hU
  have hlogU : 2 * a ≤ Real.log U := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hUexp
  have hlogpos : 0 < Real.log U := by linarith
  set h : ℝ := 2 * a / Real.log U with hhdef
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hlogpos]; exact hlogU
  -- admissible shadow-free heights inside Selberg's window
  set L : ℝ := U / 12 - 1 with hL
  have hsmall : 2 * offLineMoment (U / 2 + 1) < L := by rw [hL]; linarith
  obtain ⟨S₁, hS₁I, hg₁, hA₁⟩ := exists_shadowFree_admissible_height (h := h) (V := U / 2)
    (α := T₁) (L := L) (by linarith [hT₁.1]) (by linarith [hT₁.2]) hsmall
  obtain ⟨S₂, hS₂I, hg₂, hA₂⟩ := exists_shadowFree_admissible_height (h := h) (V := U / 2)
    (α := T₂ - L) (L := L) (by linarith [hT₂.1]) (by linarith [hT₂.2]) hsmall
  have hreA : ∀ x : ℝ, cosProducer h x ≠ 0 → (xi (((1 / 2 + h : ℝ) : ℂ) + x * I)).re ≠ 0 := by
    intro x hx hre
    apply hx
    rw [cosProducer_ofReal]
    have e : (1 / 2 : ℂ) + h + x * I = ((1 / 2 + h : ℝ) : ℂ) + x * I := by push_cast; ring
    rw [e, hre]; simp
  have hS12 : S₁ < S₂ := by linarith [hS₁I.2, hS₂I.1, hT₁.2, hT₂.1]
  obtain ⟨Zξ, hZξ, hD⟩ := windowDefectCount_le_transport hh hS12 hg₁ hg₂ (hreA S₁ hA₁)
    (hreA S₂ hA₂)
  have hmono := windowDefectCount_mono (h := h) (T₁ := S₁) (T₂ := S₂) (T₁' := U / 3)
    (T₂' := 2 * U / 5) (by linarith [hS₁I.2, hT₁.2]) (by linarith [hS₂I.1, hT₂.1])
  -- the zeros of `ζ` in Selberg's box
  have hfinZ : {z : ℂ | z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0}.Finite := by
    have hxi : AnalyticOnNhd ℂ xi univ := xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hfin := entire_zeros_closedRectangle_finite hxi ⟨2, xi_ne_zero_of_one_le (by simp)⟩
      (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((15 / 2 : ℝ) : ℂ) + T₂ * I)
    refine hfin.subset ?_
    rintro z ⟨hzR, hz0⟩
    refine ⟨by simpa using hzR, ?_⟩
    have hre := (mem_reProdIm.mp hzR).1
    have him := (mem_reProdIm.mp hzR).2
    rw [uIcc_of_le (by norm_num)] at hre
    rw [uIcc_of_le (by linarith [hT₁.2, hT₂.1])] at him
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at him; simp at him; linarith [him.1, hT₁.1]
    exact (xi_eq_zero_iff (by linarith [hre.1]) hz1).mpr hz0
  set Z := hfinZ.toFinset with hZ
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0 := fun z => by rw [hZ, Set.Finite.mem_toFinset]; rfl
  have hsel' := hZsel Z hZmem
  -- `Zξ` sits inside the filtered box, with equal orders
  have hsub : Zξ ⊆ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re) := by
    intro w hw
    obtain ⟨hR, h0, hre⟩ := (hZξ w).mp hw
    obtain ⟨hreI, himI⟩ := mem_reProdIm.mp hR
    rw [Finset.mem_filter, hZmem]
    have hlt1 := xi_zero_re_lt_one h0
    have hw1 : w ≠ 1 := by intro h1; rw [h1] at hlt1; simp at hlt1
    refine ⟨⟨?_, (xi_eq_zero_iff (by linarith [hreI.1]) hw1).mp h0⟩, hre⟩
    rw [mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le (by linarith [hT₁.2, hT₂.1])]
    exact ⟨⟨by linarith [hreI.1], by linarith⟩, ⟨by linarith [himI.1, hS₁I.1],
      by linarith [himI.2, hS₂I.2]⟩⟩
  have hordeq : ∑ w ∈ Zξ, (analyticOrderAt xi w).toNat =
      ∑ w ∈ Zξ, (analyticOrderAt riemannZeta w).toNat := by
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hR, h0, hre⟩ := (hZξ w).mp hw
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
      ⟨by linarith [(mem_reProdIm.mp hR).1.1], xi_zero_re_lt_one h0⟩]
  have hsum_le : (∑ w ∈ Zξ, (analyticOrderAt xi w).toNat : ℝ) ≤
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    have := Finset.sum_le_sum_of_subset (f := fun w => (analyticOrderAt riemannZeta w).toNat) hsub
    rw [← hordeq] at this
    exact_mod_cast this
  -- assemble
  have hrate := selbergNearLineRate_nonneg hA.le a
  have hpa : 0 < Real.pi * a := by positivity
  have hT21 : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hselN : ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
      Real.log U / (2 * Real.pi * a) * ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 2 * Real.pi * (a / Real.log U) *
        ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
        (T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U := by
      have h2 := hsel'
      rw [← mul_assoc] at h2
      exact h2
    have e : 2 * Real.pi * (a / Real.log U) = 2 * Real.pi * a / Real.log U := by ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hlogpos] at this
    linarith
  have hD' : (windowDefectCount S₁ S₂ h : ℝ) ≤
      2 * (∑ w ∈ Zξ, (analyticOrderAt xi w).toNat : ℝ) + 2 := by exact_mod_cast hD
  have hmono' : (windowDefectCount (U / 3) (2 * U / 5) h : ℝ) ≤ windowDefectCount S₁ S₂ h := by
    exact_mod_cast hmono
  have hfin : Real.log U / (2 * Real.pi * a) *
        ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U) * 2 ≤
      Real.log U / (Real.pi * a) * (U / 8 * selbergNearLineRate A a + K * Real.log U) := by
    have e : Real.log U / (2 * Real.pi * a) * 2 = Real.log U / (Real.pi * a) := by
      field_simp
    have hmon : (T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U ≤
        U / 8 * selbergNearLineRate A a + K * Real.log U := by nlinarith
    calc Real.log U / (2 * Real.pi * a) *
          ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U) * 2
        = Real.log U / (Real.pi * a) *
          ((T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmon (by positivity)
  linarith

end

end RHTower
