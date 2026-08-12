import GaloisForLFunctions.RHTower.Sieve.RouteTZetaInverseBound
import GaloisForLFunctions.RHTower.Sieve.PerronSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox
import GaloisForLFunctions.RHTower.Sieve.InvZetaEdgeBounds

/-!
# Route-T Perron rectangle for Möbius sums

The high edges use the Route-T reciprocal theorem.  One compact box of fixed height handles the
remaining bounded ordinates.  The left shift is the minimum of half the compact-box thickness and
one twentieth of the Route-T `Delta` at the truncation height, so the full rectangle is zero-free
without retaining any classical `log⁻⁹` width.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

def routeTContourShift (A δ T : ℝ) : ℝ :=
  min (routeTInverseDelta A T / 20) (δ / 2)

def routeTContourLeft (A δ T : ℝ) : ℝ :=
  1 - routeTContourShift A δ T

def routeTContourRight (A T : ℝ) : ℝ :=
  1 + routeTInverseDelta A T

def routeTContourEdgeBound (A T : ℝ) : ℝ :=
  Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight T) ^ 2)

def routeTContourRightBound (A T : ℝ) : ℝ :=
  Real.exp (22 / 4) * (1 + 1 / routeTInverseDelta A T)

theorem routeTContourShift_pos {A δ T : ℝ} (hδ : 0 < δ) :
    0 < routeTContourShift A δ T := by
  unfold routeTContourShift
  exact lt_min (div_pos (routeTInverseDelta_pos A T) (by norm_num))
    (div_pos hδ (by norm_num))

theorem routeTContourShift_le_delta_twentieth (A δ T : ℝ) :
    routeTContourShift A δ T ≤ routeTInverseDelta A T / 20 := by
  unfold routeTContourShift
  exact min_le_left _ _

theorem routeTContourShift_le_box_half (A δ T : ℝ) :
    routeTContourShift A δ T ≤ δ / 2 := by
  unfold routeTContourShift
  exact min_le_right _ _

theorem routeTContourLeft_pos {A δ T : ℝ} :
    0 < routeTContourLeft A δ T := by
  have hshift := routeTContourShift_le_delta_twentieth A δ T
  have hD := routeTInverseDelta_le_sixteenth A T
  unfold routeTContourLeft
  linarith

theorem routeTContourLeft_le_one {A δ T : ℝ} (hδ : 0 < δ) :
    routeTContourLeft A δ T ≤ 1 := by
  unfold routeTContourLeft
  linarith [routeTContourShift_pos (A := A) (T := T) hδ]

theorem routeTContourRight_gt_one (A T : ℝ) :
    1 < routeTContourRight A T := by
  unfold routeTContourRight
  linarith [routeTInverseDelta_pos A T]

theorem routeTContourLeft_le_right {A δ T : ℝ} (hδ : 0 < δ) :
    routeTContourLeft A δ T ≤ routeTContourRight A T := by
  have hleft := routeTContourLeft_le_one (A := A) (T := T) hδ
  have hright := routeTContourRight_gt_one A T
  linarith

/-- Compact reciprocal bound through any fixed ordinate height. -/
theorem exists_bound_invZeta_fixed_box {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ B → ‖invZeta s‖ ≤ M := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect hB
  set c : ℝ := 1 - δ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hc2 : c ≤ 2 := by linarith
  have hrect : Set.uIcc c 2 ×ℂ Set.uIcc (-B) B =
      Set.Icc c 2 ×ℂ Set.Icc (-B) B := by
    rw [Set.uIcc_of_le hc2, Set.uIcc_of_le (by linarith : -B ≤ B)]
  have hdiff : DifferentiableOn ℂ invZeta (Set.Icc c 2 ×ℂ Set.Icc (-B) B) := by
    rw [← hrect]
    exact differentiableOn_invZeta_rect (hzf c 2 (by rw [hcdef]) hc1 (by norm_num))
  have hK : IsCompact (Set.Icc c 2 ×ℂ Set.Icc (-B) B) :=
    isCompact_reProdIm_Icc _ _ _ _
  have hne : (Set.Icc c 2 ×ℂ Set.Icc (-B) B).Nonempty := by
    refine ⟨1, ?_, ?_⟩
    · exact ⟨by simpa using hc1, by norm_num⟩
    · constructor <;> simp [hB]
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hdiff.continuousOn.norm)
  refine ⟨δ, hδ, ‖invZeta z‖, norm_nonneg _, fun s hlo hhi him => ?_⟩
  exact hmax (show s ∈ Set.Icc c 2 ×ℂ Set.Icc (-B) B from
    ⟨⟨hlo, hhi⟩, (abs_le.1 him).1, (abs_le.1 him).2⟩)

private theorem routeTInverseDelta_mono_upto
    {A y T : ℝ} (hy : 100001 ≤ |y|) (hyT : |y| ≤ T) :
    routeTInverseDelta A T ≤ routeTInverseDelta A |y| := by
  unfold routeTInverseDelta routeTInverseHeight
  exact routeTZeroFreeDelta_antitone
    (by
      have hpi := Real.pi_lt_d2
      linarith : 8 * Real.pi + 1 ≤ |y| + 1)
    (by linarith : |y| + 1 ≤ T + 1)

private theorem routeTZeroFreeBudget_mono_upto
    {A y T : ℝ} (hy : 100001 ≤ |y|) (hyT : |y| ≤ T) :
    routeTZeroFreeBudget A (routeTInverseHeight |y|) ≤
      routeTZeroFreeBudget A (routeTInverseHeight T) := by
  unfold routeTInverseHeight
  exact routeTZeroFreeBudget_mono
    (by
      have hpi := Real.pi_lt_d2
      linarith : 8 * Real.pi + 1 ≤ |y| + 1)
    (by linarith : |y| + 1 ≤ T + 1)

set_option maxHeartbeats 800000 in
/-- **Route-T contour rectangle is zero-free.** -/
theorem routeT_contour_zero_free
    {A δ T : ℝ}
    (hA : ∀ x : ℝ, 1 < x → x ≤ 2 →
      (-deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ)).re ≤ 1 / (x - 1) + A)
    (hδ : 0 < δ)
    (hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ routeTInverseBaseHeight → s ≠ 1 → riemannZeta s ≠ 0)
    (hT : routeTInverseBaseHeight ≤ T) :
    ∀ s ∈ Set.uIcc (routeTContourLeft A δ T) (routeTContourRight A T) ×ℂ
        Set.uIcc (-T) T,
      s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  have hleftRight := routeTContourLeft_le_right (A := A) (T := T) hδ
  have hT0 : 0 ≤ T := (by
    have hbase := routeTInverseBaseHeight_ge
    linarith)
  rw [Complex.mem_reProdIm, Set.uIcc_of_le hleftRight,
    Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
  have himT : |s.im| ≤ T := abs_le.2 hs.2
  by_cases hlow : |s.im| ≤ routeTInverseBaseHeight
  · rcases le_or_gt s.re 1 with hre | hre
    · apply hbox s
      · have hshift := routeTContourShift_le_box_half A δ T
        have hreLeft := hs.1.1
        unfold routeTContourLeft at hreLeft
        linarith
      · exact hre
      · exact hlow
      · exact hs1
    · exact riemannZeta_ne_zero_of_one_le_re hre.le
  · have himBase : routeTInverseBaseHeight ≤ |s.im| := le_of_lt (lt_of_not_ge hlow)
    have him100 : 100001 ≤ |s.im| := routeTInverseBaseHeight_ge.trans himBase
    have hlarge : routeTBandDepthRootThreshold ^ 10 ≤
        routeTBinaryHeight (|s.im| - 1) :=
      routeTInverseBaseDepth.trans
        (routeTBinaryHeight_mono (by linarith : routeTInverseBaseHeight - 1 ≤ |s.im| - 1))
    rcases le_or_gt s.re 1 with hre | hre
    · have hD := routeTInverseDelta_mono_upto (A := A) him100 himT
      have hDpoint : routeTInverseDelta A |s.im| ≤ routeTZeroFreeDelta A |s.im| := by
        unfold routeTInverseDelta routeTInverseHeight
        exact routeTZeroFreeDelta_antitone
          (by
            have hpi := Real.pi_lt_d2
            linarith : 8 * Real.pi + 1 ≤ |s.im|)
          (by linarith : |s.im| ≤ |s.im| + 1)
      have hshift := routeTContourShift_le_delta_twentieth A δ T
      have hnear : 1 - routeTZeroFreeWidth A |s.im| < s.re := by
        have hDpos := routeTZeroFreeDelta_pos A |s.im|
        have hwidth : routeTZeroFreeWidth A |s.im| = routeTZeroFreeDelta A |s.im| / 10 := by
          rfl
        rw [hwidth]
        have hreLeft := hs.1.1
        unfold routeTContourLeft at hreLeft
        linarith
      have hlargePoint : routeTBandDepthRootThreshold ^ 10 ≤
          routeTBinaryHeight |s.im| :=
        hlarge.trans (routeTBinaryHeight_mono (by linarith : |s.im| - 1 ≤ |s.im|))
      rcases le_or_gt 0 s.im with him | him
      · have habs : |s.im| = s.im := abs_of_nonneg him
        rw [habs] at him100 hlargePoint hnear
        have hz := riemannZeta_ne_zero_routeT_region
          (β := s.re) (γ := s.im) hA (by linarith) hlargePoint hre hnear
        have hsdecomp : ((s.re : ℝ) : ℂ) + (s.im : ℂ) * Complex.I = s :=
          Complex.re_add_im s
        rw [hsdecomp] at hz
        exact hz
      · have habs : |s.im| = -s.im := abs_of_neg him
        rw [habs] at him100 hlargePoint hnear
        have hz := riemannZeta_ne_zero_routeT_region
          (β := s.re) (γ := -s.im) hA (by linarith) hlargePoint hre hnear
        have hzneg := riemannZeta_ne_zero_neg_im hz
        have hsdecomp :
            ((s.re : ℝ) : ℂ) + ((-(-s.im) : ℝ) : ℂ) * Complex.I = s := by
          rw [neg_neg]
          exact Complex.re_add_im s
        rw [hsdecomp] at hzneg
        exact hzneg
    · exact riemannZeta_ne_zero_of_one_le_re hre.le

/-- High ordinate reciprocal bound uniform over the Route-T contour width. -/
theorem norm_inv_riemannZeta_le_routeT_contour
    {A δ T x y : ℝ}
    (hA : ∀ u : ℝ, 1 < u → u ≤ 2 →
      (-deriv riemannZeta (u : ℂ) / riemannZeta (u : ℂ)).re ≤ 1 / (u - 1) + A)
    (hy : routeTInverseBaseHeight ≤ |y|)
    (hyT : |y| ≤ T)
    (hxlo : routeTContourLeft A δ T ≤ x)
    (hxhi : x ≤ routeTContourRight A T) :
    ‖(riemannZeta ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹‖ ≤ routeTContourEdgeBound A T := by
  have hy100 : 100001 ≤ |y| := routeTInverseBaseHeight_ge.trans hy
  have hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (|y| - 1) :=
    routeTInverseBaseDepth.trans
      (routeTBinaryHeight_mono (by linarith : routeTInverseBaseHeight - 1 ≤ |y| - 1))
  have hD := routeTInverseDelta_mono_upto (A := A) hy100 hyT
  have hshift := routeTContourShift_le_delta_twentieth A δ T
  have hσlo : 1 - routeTInverseDelta A |y| / 20 ≤ x := by
    unfold routeTContourLeft at hxlo
    linarith
  have hσhi : x ≤ 1 + routeTInverseDelta A |y| := by
    unfold routeTContourRight at hxhi
    linarith
  have hraw := norm_inv_riemannZeta_le_routeT_abs hA hy100 hlarge hσlo hσhi
  have hQ := routeTZeroFreeBudget_mono_upto (A := A) hy100 hyT
  have hQ0 := routeTZeroFreeBudget_pos A (routeTInverseHeight |y|)
  have hQsq : routeTZeroFreeBudget A (routeTInverseHeight |y|) ^ 2 ≤
      routeTZeroFreeBudget A (routeTInverseHeight T) ^ 2 :=
    pow_le_pow_left₀ hQ0.le hQ 2
  have hexp :
      Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight |y|) ^ 2) ≤
        routeTContourEdgeBound A T := by
    unfold routeTContourEdgeBound
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hQsq (by norm_num))
  exact hraw.trans hexp

end

end RHTower.Sieve
