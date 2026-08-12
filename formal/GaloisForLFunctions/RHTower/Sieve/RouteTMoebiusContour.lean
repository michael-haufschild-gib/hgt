import GaloisForLFunctions.RHTower.Sieve.RouteTZetaInverseBound
import GaloisForLFunctions.RHTower.Sieve.PerronSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox
import GaloisForLFunctions.RHTower.Sieve.InvZetaEdgeBounds
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistSharpSubstitution

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
        have hzneg :
            riemannZeta (((s.re : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) ≠ 0 := by
          intro hzero
          apply hz
          have hc :
              (((s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * Complex.I) =
                (starRingEnd ℂ) (((s.re : ℝ) : ℂ) + (s.im : ℂ) * Complex.I) := by
            apply Complex.ext <;> simp
          rw [hc, riemannZeta_conj, hzero, map_zero]
        have hsdecomp :
            ((s.re : ℝ) : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
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

set_option maxHeartbeats 1200000 in
/-- **Route-T four-edge Perron bound for smoothed Möbius sums.**  No classical `log⁻⁹` width
remains in the rectangle. -/
theorem exists_norm_tsum_moebius_smoothWeight_le_routeT :
    ∃ (A C C' M δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
      ∀ N H T : ℝ, 0 < N → 0 < H → routeTInverseBaseHeight ≤ T →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (routeTContourRightBound A T *
              (C / H ^ 2 * (N + H + 1) ^ 2 *
                (N + H + 1) ^ routeTContourRight A T)) / T
          + routeTContourEdgeBound A T *
              (C' / H ^ 1 * (N + H + 1) ^ 1 *
                (N + H + 1) ^ routeTContourRight A T) /
              T ^ (0 + 1) * (routeTContourRight A T - routeTContourLeft A δ T)
          + routeTContourEdgeBound A T *
              (C' / H ^ 1 * (N + H + 1) ^ 1 *
                (N + H + 1) ^ routeTContourRight A T) /
              T ^ (0 + 1) * (routeTContourRight A T - routeTContourLeft A δ T)
          + max M (routeTContourEdgeBound A T) *
              (2 * ((N + H) ^ routeTContourLeft A δ T /
                    routeTContourLeft A δ T)
                + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 *
                    (N + H + 1) ^ routeTContourLeft A δ T)) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdec0⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨δz, hδz, hzfbox⟩ := exists_zero_free_box routeTInverseBaseHeight
  obtain ⟨δm, hδm, M, hM, hbdbox⟩ :=
    exists_bound_invZeta_fixed_box (by
      have hbase := routeTInverseBaseHeight_ge
      linarith : 0 ≤ routeTInverseBaseHeight)
  let δ := min δz δm
  have hδ : 0 < δ := lt_min hδz hδm
  refine ⟨A, C, C', M, δ, hC, hC', hM, hδ, ?_⟩
  intro N H T hN hH hT
  let c := routeTContourLeft A δ T
  let d := routeTContourRight A T
  let Md := routeTContourRightBound A T
  let Mh := routeTContourEdgeBound A T
  let Mc := max M Mh
  have hTpos : 0 < T := by
    have hbase := routeTInverseBaseHeight_ge
    linarith
  have hT1 : 1 ≤ T := by linarith [routeTInverseBaseHeight_ge]
  have hc0 : 0 < c := by simpa only [c] using routeTContourLeft_pos (A := A) (δ := δ) (T := T)
  have hc1 : c ≤ 1 := by simpa only [c] using routeTContourLeft_le_one (A := A) (T := T) hδ
  have hd1 : 1 < d := by simpa only [d] using routeTContourRight_gt_one A T
  have hcd : c ≤ d := by simpa only [c, d] using routeTContourLeft_le_right (A := A) (T := T) hδ
  have hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ routeTInverseBaseHeight → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hslo hshi him hs1
    apply hzfbox s
    · have hδle : δ ≤ δz := min_le_left _ _
      linarith
    · exact hshi
    · exact him
    · exact hs1
  have hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T,
      s ≠ 1 → riemannZeta s ≠ 0 := by
    simpa only [c, d] using routeT_contour_zero_free hA hδ hbox hT
  have hMd : 0 ≤ Md := by
    dsimp only [Md, routeTContourRightBound]
    have hD := routeTInverseDelta_pos A T
    exact mul_nonneg (Real.exp_nonneg _) (by
      have hinv : 0 < 1 / routeTInverseDelta A T := one_div_pos.mpr hD
      linarith)
  have hMh : 0 ≤ Mh := by
    dsimp only [Mh, routeTContourEdgeBound]
    exact Real.exp_nonneg _
  have hMc : 0 ≤ Mc := by
    dsimp only [Mc]
    exact le_max_of_le_left hM
  have hFd : ∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Md := by
    intro y
    have hright := norm_invZeta_right_le (d := d) (y := y) hd1
    have heq : Real.exp (22 / 4) * (1 + 1 / (d - 1)) = Md := by
      dsimp only [d, Md, routeTContourRight, routeTContourRightBound]
      congr 2
      ring_nf
    exact hright.trans_eq heq
  have hFt : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh := by
    intro x hx
    have hne : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    rw [norm_invZeta_eq hne]
    exact norm_inv_riemannZeta_le_routeT_contour hA
      (by rw [abs_of_pos hTpos]; exact hT)
      (by rw [abs_of_pos hTpos]) hx.1.le hx.2
  have hFb : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh := by
    intro x hx
    have hne : ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    rw [norm_invZeta_eq hne]
    exact norm_inv_riemannZeta_le_routeT_contour hA
      (by rw [abs_neg, abs_of_pos hTpos]; exact hT)
      (by rw [abs_neg, abs_of_pos hTpos]) hx.1.le hx.2
  have hFc : ∀ y ∈ Set.Icc (-T) T,
      ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Mc := by
    intro y hy
    have hyT : |y| ≤ T := abs_le.2 hy
    by_cases hylow : |y| ≤ routeTInverseBaseHeight
    · have hδle : δ ≤ δm := min_le_right _ _
      have hcbox : 1 - δm ≤ c := by
        have hshift := routeTContourShift_le_box_half A δ T
        dsimp only [c, routeTContourLeft]
        linarith
      have hlow := hbdbox ((c : ℂ) + (y : ℝ) * Complex.I)
        (by simpa using hcbox) (by simp; linarith) (by simpa using hylow)
      exact hlow.trans (le_max_left _ _)
    · have hybase : routeTInverseBaseHeight ≤ |y| := le_of_lt (lt_of_not_ge hylow)
      have hne : ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        simp at him
        subst y
        simp at hylow
        have hbase := routeTInverseBaseHeight_ge
        linarith
      rw [norm_invZeta_eq hne]
      have hhigh := norm_inv_riemannZeta_le_routeT_contour hA hybase hyT
        (le_refl c) hcd
      exact hhigh.trans (le_max_right _ _)
  have hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-T) T) :=
    continuousOn_invZeta_left_line hc1 hd1.le hzf
  exact norm_tsum_moebius_smoothWeight_le_sharp hN hH 0 hd1 hc0 hcd hT1
    hMd hMh hMc hzf hFd hFt hFb hFc hFccont
    (fun s hs hsd => hdec1 N H hN hH d s hs hsd)
    (fun s hs hsd => hdec0 N H hN hH d s hs hsd)
    (fun s hs hsc => hdec1 N H hN hH c s hs hsc)

private theorem routeT_twist_abs_bounds
    {τ U y : ℝ}
    (hsep : routeTInverseBaseHeight + U ≤ |τ|)
    (hy : |y| ≤ U) :
    routeTInverseBaseHeight ≤ |y + τ| ∧ |y + τ| ≤ |τ| + U := by
  have hrev : |τ| ≤ |y + τ| + |y| := by
    calc
      |τ| = |(y + τ) + (-y)| := by ring_nf
      _ ≤ |y + τ| + |-y| := abs_add_le _ _
      _ = |y + τ| + |y| := by rw [abs_neg]
  have hupp : |y + τ| ≤ |τ| + U := by
    calc
      |y + τ| ≤ |y| + |τ| := abs_add_le _ _
      _ ≤ U + |τ| := add_le_add hy le_rfl
      _ = |τ| + U := by ring
  constructor
  · linarith
  · exact hupp

set_option maxHeartbeats 1200000 in
/-- **Route-T four-edge Perron bound for twisted smoothed Möbius sums.**  If the contour
half-height stays below the twist by the fixed Route-T base height, every shifted edge lies in the
quantitative high-ordinate region.  Thus the same Route-T reciprocal bound controls all three
non-right edges, with no compact reciprocal constant. -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT :
    ∃ (A C C' δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < δ ∧
      ∀ N H τ U : ℝ, 0 < N → 0 < H → 1 ≤ U →
      routeTInverseBaseHeight + U ≤ |τ| →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (routeTContourRightBound A (|τ| + U) *
              (C / H ^ 2 * (N + H + 1) ^ 2 *
                (N + H + 1) ^ routeTContourRight A (|τ| + U))) / U
          + routeTContourEdgeBound A (|τ| + U) *
              (C' / H ^ 1 * (N + H + 1) ^ 1 *
                (N + H + 1) ^ routeTContourRight A (|τ| + U)) /
              U ^ (0 + 1) *
                (routeTContourRight A (|τ| + U) -
                  routeTContourLeft A δ (|τ| + U))
          + routeTContourEdgeBound A (|τ| + U) *
              (C' / H ^ 1 * (N + H + 1) ^ 1 *
                (N + H + 1) ^ routeTContourRight A (|τ| + U)) /
              U ^ (0 + 1) *
                (routeTContourRight A (|τ| + U) -
                  routeTContourLeft A δ (|τ| + U))
          + routeTContourEdgeBound A (|τ| + U) *
              (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
                    routeTContourLeft A δ (|τ| + U))
                + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 *
                    (N + H + 1) ^ routeTContourLeft A δ (|τ| + U)) ) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdec0⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨δ, hδ, hzfbox⟩ := exists_zero_free_box routeTInverseBaseHeight
  refine ⟨A, C, C', δ, hC, hC', hδ, ?_⟩
  intro N H τ U hN hH hU hsep
  let S : ℝ := |τ| + U
  let c : ℝ := routeTContourLeft A δ S
  let d : ℝ := routeTContourRight A S
  let Md : ℝ := routeTContourRightBound A S
  let Mh : ℝ := routeTContourEdgeBound A S
  have hU0 : 0 ≤ U := by linarith
  have hS : routeTInverseBaseHeight ≤ S := by
    dsimp only [S]
    linarith [abs_nonneg τ]
  have hc0 : 0 < c := by
    simpa only [c] using routeTContourLeft_pos (A := A) (δ := δ) (T := S)
  have hc1 : c ≤ 1 := by
    simpa only [c] using routeTContourLeft_le_one (A := A) (T := S) hδ
  have hd1 : 1 < d := by
    simpa only [d] using routeTContourRight_gt_one A S
  have hcd : c ≤ d := by
    simpa only [c, d] using routeTContourLeft_le_right (A := A) (T := S) hδ
  have hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ routeTInverseBaseHeight → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hslo hshi him hs1
    exact hzfbox s hslo hshi him hs1
  have hzfS : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-S) S,
      s ≠ 1 → riemannZeta s ≠ 0 := by
    simpa only [c, d] using routeT_contour_zero_free hA hδ hbox hS
  have hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + U)) (|τ| + U),
      s ≠ 1 → riemannZeta s ≠ 0 := by
    simpa only [S] using hzfS
  have hMd : 0 ≤ Md := by
    dsimp only [Md, routeTContourRightBound]
    have hD := routeTInverseDelta_pos A S
    exact mul_nonneg (Real.exp_nonneg _) (by
      have hinv : 0 < 1 / routeTInverseDelta A S := one_div_pos.mpr hD
      linarith)
  have hMh : 0 ≤ Mh := by
    dsimp only [Mh, routeTContourEdgeBound]
    exact Real.exp_nonneg _
  have hFd : ∀ y : ℝ,
      ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md := by
    intro y
    have harg :
        ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
          (d : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hright := norm_invZeta_right_le (d := d) (y := y + τ) hd1
    have heq : Real.exp (22 / 4) * (1 + 1 / (d - 1)) = Md := by
      dsimp only [d, Md, routeTContourRight, routeTContourRightBound]
      congr 2
      ring_nf
    exact hright.trans_eq heq
  have htop := routeT_twist_abs_bounds hsep
    (show |U| ≤ U by rw [abs_of_nonneg hU0])
  have hbot := routeT_twist_abs_bounds hsep
    (show |-U| ≤ U by rw [abs_neg, abs_of_nonneg hU0])
  have hFt : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh := by
    intro x hx
    have harg :
        ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
          (x : ℂ) + ((U + τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hne : ((x : ℂ) + ((U + τ : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      rw [him, abs_zero] at htop
      linarith [routeTInverseBaseHeight_ge]
    rw [norm_invZeta_eq hne]
    exact norm_inv_riemannZeta_le_routeT_contour hA htop.1
      (by simpa only [S] using htop.2) hx.1.le hx.2
  have hFb : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh := by
    intro x hx
    have harg :
        ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
          (x : ℂ) + (((-U) + τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hne : ((x : ℂ) + (((-U) + τ : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      rw [him, abs_zero] at hbot
      linarith [routeTInverseBaseHeight_ge]
    rw [norm_invZeta_eq hne]
    exact norm_inv_riemannZeta_le_routeT_contour hA hbot.1
      (by simpa only [S] using hbot.2) hx.1.le hx.2
  have hFc : ∀ y ∈ Set.Icc (-U) U,
      ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh := by
    intro y hy
    have hyabs : |y| ≤ U := abs_le.2 hy
    have hyshift := routeT_twist_abs_bounds hsep hyabs
    have harg :
        ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
          (c : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hne : ((c : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I) ≠ 1 := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      rw [him, abs_zero] at hyshift
      linarith [routeTInverseBaseHeight_ge]
    rw [norm_invZeta_eq hne]
    exact norm_inv_riemannZeta_le_routeT_contour hA hyshift.1
      (by simpa only [S] using hyshift.2) (le_refl c) hcd
  have hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-U) U) :=
    continuousOn_invZetaTwist_left_line τ hU0 hc1 hd1.le hzf
  exact norm_tsum_moebiusTwist_smoothWeight_le_sharp hN hH 0 τ hd1 hc0 hcd hU
    hMd hMh hMh hzf hFd hFt hFb hFc hFccont
    (fun s hs hsd => hdec1 N H hN hH d s hs hsd)
    (fun s hs hsd => hdec0 N H hN hH d s hs hsd)
    (fun s hs hsc => hdec1 N H hN hH c s hs hsc)

end

end RHTower.Sieve
