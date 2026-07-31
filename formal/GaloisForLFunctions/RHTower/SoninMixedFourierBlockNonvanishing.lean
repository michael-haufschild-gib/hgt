import GaloisForLFunctions.RHTower.SoninMixedPhysicalBlockNonvanishing

/-!
# The Fourier polarized block of the coupling does not vanish either

The argument for the physically polarized block runs verbatim with the two polarizations exchanged.
A compactly supported vector whose Fourier transform vanishes on a nondegenerate shell is zero — here
no involution is needed, the one-interval uncertainty theorem applies directly — and the dilation
sum is injective on a physical annulus by the same band-shrinking iteration, run with the expanding
dilation instead of the contracting one.

Both halves of the mixed coupling are therefore nonzero, not merely their sum.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory ContinuousLinearMap

/-! ### The physical annulus is nontrivial -/

/-- **A nondegenerate physical annulus is a nonzero operator.** -/
theorem evenIndicatorCutoff_sub_ne_zero {b c : ℝ} (hb : 0 < b) (hbc : b < c) :
    evenIndicatorCutoff c - evenIndicatorCutoff b ≠ 0 := by
  intro hzero
  have hwnorm : ‖evenShellVectorEven b c hbc 0‖ = 1 :=
    (evenShellVectorEven_orthonormal b c hb hbc).norm_eq_one 0
  have happ := DFunLike.congr_fun hzero (evenShellVectorEven b c hbc 0)
  rw [sub_apply, zero_apply, sub_eq_zero,
    evenIndicatorCutoff_evenShellVectorEven_of_le b c c hbc le_rfl 0,
    evenIndicatorCutoff_evenShellVectorEven_eq_zero b c b hbc le_rfl 0] at happ
  rw [happ, norm_zero] at hwnorm
  exact zero_ne_one hwnorm

/-! ### Compactly supported vectors cannot have a vanishing Fourier shell -/

/-- **A compactly supported vector whose Fourier transform dies on a shell is zero.** -/
theorem eq_zero_of_evenIndicatorCutoff_eq_self_of_fourierShell_apply_eq_zero
    {t a b : ℝ} {v : evenSubspace} (ha : 0 ≤ a) (hab : a < b)
    (hA : evenIndicatorCutoff t v = v)
    (hshell : (evenFourierCutoff b - evenFourierCutoff a) v = 0) :
    v = 0 := by
  set f : SoninL2 := (v : SoninL2) with hfdef
  have hfA :
      indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) f = f := by
    have h := congrArg (fun z : evenSubspace => (z : SoninL2)) hA
    simpa using h
  have hsupp : ∀ᵐ x ∂volume, x ∉ Set.Icc (-t) t → (f : ℝ → ℂ) x = 0 := by
    filter_upwards [indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) f]
      with x hx hout
    rw [hfA] at hx
    simpa [centralInterval, hout] using hx
  have hshellL2 :
      fourierCutoff (centralInterval b) (measurableSet_centralInterval b) f -
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a) f = 0 := by
    have h := congrArg (fun z : evenSubspace => (z : SoninL2)) hshell
    simpa using h
  have hFeq :
      indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) (fourierUnitary f) =
        indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
          (fourierUnitary f) := by
    have h := sub_eq_zero.mp hshellL2
    simp only [fourierCutoff_apply] at h
    exact fourierUnitary.symm.injective h
  have hFzero : ∀ᵐ w ∂volume, w ∈ Set.Ioo a b →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) w = 0 := by
    filter_upwards [indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b)
        (fourierUnitary f),
      indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
        (fourierUnitary f)] with x hb' ha' hmem
    have hxb : x ∈ centralInterval b := ⟨by linarith [hmem.1, hmem.2], hmem.2.le⟩
    have hxa : x ∉ centralInterval a := fun hc => absurd hc.2 (not_le.mpr hmem.1)
    have hx := congrFun (congrArg (fun z : SoninL2 => (z : ℝ → ℂ)) hFeq) x
    rw [hb', ha', Set.indicator_of_mem hxb, Set.indicator_of_notMem hxa] at hx
    exact hx
  have hfzero : f = 0 :=
    l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo f hsupp hab hFzero
  have hcoe : (v : SoninL2) = ((0 : evenSubspace) : SoninL2) := by
    simpa [hfdef] using hfzero
  exact Subtype.ext hcoe

/-! ### Injectivity of the dilation sum on a physical annulus -/

/-- A vector killed by the dilation sum is a `(-1)`-eigenvector of the square dilation. -/
theorem evenDilationCLM_sq_apply_eq_neg_of_evenDilationSum_apply_eq_zero
    {r : ℝ} (hr : 1 < r) (hs : 0 < r ^ 2) {v : evenSubspace}
    (hD : evenDilationSum r hr v = 0) :
    evenDilationCLM (r ^ 2) hs v = -v := by
  have hsinv : (0 : ℝ) < (r ^ 2)⁻¹ := inv_pos.mpr hs
  have hinv := evenDilationCLM_inv_sq_apply_eq_neg_of_evenDilationSum_apply_eq_zero hr hsinv hD
  have h := DFunLike.congr_fun (evenDilationCLM_mul (r ^ 2) ((r ^ 2)⁻¹) hs hsinv) v
  rw [mul_apply_eq_comp, hinv, map_neg,
    DFunLike.congr_fun (evenDilationCLM_congr (mul_pos hs hsinv)
      (mul_inv_cancel₀ hs.ne')) v] at h
  have hone : evenDilationCLM (1 : ℝ) (mul_inv_cancel₀ hs.ne' ▸ mul_pos hs hsinv) =
      (1 : evenSubspace →L[ℂ] evenSubspace) := evenDilationCLM_one
  rw [hone] at h
  have h' : -evenDilationCLM (r ^ 2) hs v = v := h
  linear_combination (norm := module) -h'

/-- **Injectivity of the dilation sum on a physical annulus.** -/
theorem eq_zero_of_evenDilationSum_apply_eq_zero_of_physicalAnnulus
    {b c r : ℝ} (hb : 0 < b) (hr : 1 < r) {v : evenSubspace}
    (hD : evenDilationSum r hr v = 0)
    (hcv : evenIndicatorCutoff c v = v)
    (hbv : evenIndicatorCutoff b v = 0) :
    v = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hr2 : (1 : ℝ) < r ^ 2 := by nlinarith
  have hsq : (0 : ℝ) < r ^ 2 := by positivity
  have hspos : (0 : ℝ) < (r ^ 2)⁻¹ := inv_pos.mpr hsq
  set s : ℝ := (r ^ 2)⁻¹ with hsdef
  have hs0 : 0 < s := hspos
  have hs1 : s < 1 := by
    rw [hsdef]
    exact inv_lt_one_of_one_lt₀ hr2
  have hUs : evenDilationCLM (r ^ 2) hsq v = -v :=
    evenDilationCLM_sq_apply_eq_neg_of_evenDilationSum_apply_eq_zero hr hsq hD
  have hiter : ∀ n : ℕ, evenIndicatorCutoff (s ^ n * c) v = v := by
    intro n
    induction n with
    | zero => simpa using hcv
    | succ n ih =>
      have hcov := evenIndicatorCutoff_mul_evenDilationCLM (s * (s ^ n * c)) (r ^ 2) hsq
      rw [show r ^ 2 * (s * (s ^ n * c)) = s ^ n * c by
        rw [hsdef]; exact mul_inv_cancel_left₀ hsq.ne' _] at hcov
      have happ := DFunLike.congr_fun hcov v
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ih, hUs, map_neg] at happ
      rw [show s ^ (n + 1) * c = s * (s ^ n * c) by ring]
      exact neg_injective happ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s ^ n * c ≤ b := by
    rcases le_or_gt c 0 with hc | hc
    · exact ⟨0, by simpa using hc.trans hb.le⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hb hc) hs1
      exact ⟨n, ((lt_div_iff₀ hc).mp hn).le⟩
  have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le_rev (s ^ n * c) b hn) v
  rw [mul_apply_eq_comp, hiter n, hbv] at hnest
  exact hnest.symm

/-! ### The image of the Fourier block is compactly supported -/

/-- Dilating a physical annulus at `c` keeps it supported inside radius `r c`. -/
theorem evenIndicatorCutoff_mul_evenDilationSum_mul_evenIndicatorCutoff
    {c r : ℝ} (hc : 0 ≤ c) (hr : 1 < r) :
    evenIndicatorCutoff (r * c) * (evenDilationSum r hr * evenIndicatorCutoff c) =
      evenDilationSum r hr * evenIndicatorCutoff c := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hcov1 : evenIndicatorCutoff (r * c) * evenDilationCLM r hr0 =
      evenDilationCLM r hr0 * evenIndicatorCutoff (r * (r * c)) :=
    evenIndicatorCutoff_mul_evenDilationCLM (r * c) r hr0
  have hcov2 : evenIndicatorCutoff (r * c) * evenDilationCLM r⁻¹ hrinv =
      evenDilationCLM r⁻¹ hrinv * evenIndicatorCutoff c := by
    rw [evenIndicatorCutoff_mul_evenDilationCLM (r * c) r⁻¹ hrinv,
      show r⁻¹ * (r * c) = c from inv_mul_cancel_left₀ hr0.ne' c]
  have hrr : (1 : ℝ) ≤ r * r := by nlinarith
  have hcc : c ≤ r * (r * c) := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hrr)]
  have hnest1 : evenIndicatorCutoff (r * (r * c)) * evenIndicatorCutoff c =
      evenIndicatorCutoff c :=
    evenIndicatorCutoff_mul_of_le_rev c (r * (r * c)) hcc
  have hnest2 : evenIndicatorCutoff c * evenIndicatorCutoff c = evenIndicatorCutoff c :=
    evenIndicatorCutoff_mul_of_le c c le_rfl
  calc evenIndicatorCutoff (r * c) * (evenDilationSum r hr * evenIndicatorCutoff c)
      = evenIndicatorCutoff (r * c) * evenDilationCLM r hr0 * evenIndicatorCutoff c +
          evenIndicatorCutoff (r * c) * evenDilationCLM r⁻¹ hrinv * evenIndicatorCutoff c := by
        rw [evenDilationSum_eq]; noncomm_ring
    _ = evenDilationCLM r hr0 *
            (evenIndicatorCutoff (r * (r * c)) * evenIndicatorCutoff c) +
          evenDilationCLM r⁻¹ hrinv * (evenIndicatorCutoff c * evenIndicatorCutoff c) := by
        rw [hcov1, hcov2]; noncomm_ring
    _ = evenDilationCLM r hr0 * evenIndicatorCutoff c +
          evenDilationCLM r⁻¹ hrinv * evenIndicatorCutoff c := by rw [hnest1, hnest2]
    _ = evenDilationSum r hr * evenIndicatorCutoff c := by
        rw [evenDilationSum_eq]; noncomm_ring

/-! ### Nonvanishing -/

/-- **The Fourier polarized block of the aperture coupling is nonzero.** -/
theorem soninMixedFourierBlock_ne_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hr : 1 < r) :
    soninMixedFourierBlock a b c r hr ≠ 0 := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  intro hzero
  have hshellzero : evenIndicatorCutoff c - evenIndicatorCutoff b = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hidem :
        evenIndicatorCutoff c * (evenIndicatorCutoff c - evenIndicatorCutoff b) =
          evenIndicatorCutoff c - evenIndicatorCutoff b := by
      rw [mul_sub, evenIndicatorCutoff_mul_of_le c c le_rfl,
        evenIndicatorCutoff_mul_of_le_rev b c hbc.le]
    have hkill :
        evenIndicatorCutoff b * (evenIndicatorCutoff c - evenIndicatorCutoff b) = 0 := by
      rw [mul_sub, evenIndicatorCutoff_mul_of_le b c hbc.le,
        evenIndicatorCutoff_mul_of_le b b le_rfl, sub_self]
    set v : evenSubspace := (evenIndicatorCutoff c - evenIndicatorCutoff b) w with hv
    have hcv : evenIndicatorCutoff c v = v := by
      have h := DFunLike.congr_fun hidem w
      rw [mul_apply_eq_comp] at h
      exact h
    have hbv : evenIndicatorCutoff b v = 0 := by
      have h := DFunLike.congr_fun hkill w
      rw [mul_apply_eq_comp, zero_apply] at h
      exact h
    have hDzero : evenDilationSum r hr v = 0 := by
      have hAy :
          evenIndicatorCutoff (r * c) (evenDilationSum r hr v) = evenDilationSum r hr v := by
        have hband := evenIndicatorCutoff_mul_evenDilationSum_mul_evenIndicatorCutoff hc.le hr
        have h := DFunLike.congr_fun hband v
        rw [mul_apply_eq_comp, mul_apply_eq_comp, hcv] at h
        exact h
      have hshell :
          (evenFourierCutoff b - evenFourierCutoff a) (evenDilationSum r hr v) = 0 := by
        have h := DFunLike.congr_fun hzero w
        unfold soninMixedFourierBlock at h
        rw [zero_apply, mul_apply_eq_comp, mul_apply_eq_comp] at h
        exact h
      exact eq_zero_of_evenIndicatorCutoff_eq_self_of_fourierShell_apply_eq_zero ha.le hab hAy
        hshell
    have := eq_zero_of_evenDilationSum_apply_eq_zero_of_physicalAnnulus hb hr hDzero hcv hbv
    simpa [hv] using this
  exact evenIndicatorCutoff_sub_ne_zero hb hbc hshellzero

/-- **Both polarized halves of the mixed coupling are nonzero.** -/
theorem soninMixedBlocks_ne_zero
    {a b c r : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hr : 1 < r) :
    soninMixedPhysicalBlock a b c r hr ≠ 0 ∧ soninMixedFourierBlock a b c r hr ≠ 0 :=
  ⟨soninMixedPhysicalBlock_ne_zero ha hab hbc hr,
    soninMixedFourierBlock_ne_zero ha hab hbc hr⟩

end RHTower
