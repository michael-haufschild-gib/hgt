import GaloisForLFunctions.ArithmeticDiscreteness.TheDepthOfAnFEPairIsReadOnTheLine
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubWeylZetaProfiles
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine

/-! # Sub-Weyl flatness of functional-equation pairs

The sub-Weyl strip profile and the functional equation bound zeta on a fixed
small disc crossing the critical line. Two reflected zeros then force a
quadratic central value with height cost `|γ|^(33/200+ε)`.
-/

noncomputable section
open Complex Metric

namespace GaloisForLFunctions.ArithmeticDiscreteness

private theorem norm_zeta_real_add_im_abs (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ =
      ‖riemannZeta ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht]
    have he : (σ : ℂ) + (t : ℂ) * I =
        starRingEnd ℂ ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
      push_cast
      ring
    rw [he, riemannZeta_conj, Complex.norm_conj]

/-- Reflection extends the sub-Weyl bound to a narrow two-sided strip. -/
private theorem exists_subWeyl_narrow_strip_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ 0 < C ∧
      ∀ σ t : ℝ, |σ - 1 / 2| ≤ r → 8 ≤ |t| →
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          C * |t| ^ (33 / 200 + ε) := by
  let r : ℝ := min (ε / 4) (1 / 100)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r ≤ 1 / 100 := min_le_right _ _
  have hrε : r ≤ ε / 4 := min_le_left _ _
  obtain ⟨A, hA, ha⟩ :=
    ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_le_subWeyl_profile_one hr
      (by linarith only [hr1])
  obtain ⟨K, hK, hk⟩ := RHTower.exists_norm_zetaChi_moving_left_line_le_rpow
    (d₀ := r) hr.le (by linarith only [hr1])
  have hright : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + r → 8 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ A * |t| ^ (33 / 200 + r) := by
    intro σ t hσ0 hσ1 ht
    rw [norm_zeta_real_add_im_abs]
    refine (ha σ |t| hσ0 (by linarith only [hσ1, hr1]) ht).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith only [ht])
        (by linarith only [hσ0])) hA.le
  refine ⟨r, (K + 1) * A, hr, hr1, by positivity, ?_⟩
  intro σ t hσ ht
  have ht0 : 0 < |t| := by linarith only [ht]
  have ht1 : 1 ≤ |t| := by linarith only [ht]
  have hσlo := (abs_le.mp hσ).1
  have hσhi := (abs_le.mp hσ).2
  by_cases hrightσ : 1 / 2 ≤ σ
  · calc
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          A * |t| ^ (33 / 200 + r) := hright σ t hrightσ (by linarith) ht
      _ ≤ A * |t| ^ (33 / 200 + ε) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hrε, hε])) hA.le
      _ ≤ ((K + 1) * A) * |t| ^ (33 / 200 + ε) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hK, hA]) (by positivity)
  · have hleftσ : σ ≤ 1 / 2 := le_of_not_ge hrightσ
    have hσpos : 0 < σ := by linarith only [hσlo, hr1]
    have hz0 : (σ : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro he
      have he' := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_re] at he'
      linarith only [he', hσpos]
    have hz1 : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro he
      have he' := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, one_re] at he'
      linarith only [he', hleftσ]
    have hg : Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp only [sub_re, one_re, add_re, ofReal_re, mul_re, I_re, ofReal_im,
        I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hleftσ]
    have hχ := hk (1 / 2 - σ) (by linarith only [hleftσ])
      (by linarith only [hσlo]) t
    rw [show (1 / 2 : ℝ) - (1 / 2 - σ) = σ by ring,
      max_eq_right ht1] at hχ
    have href := hright (1 - σ) (-t) (by linarith only [hleftσ])
      (by linarith only [hσlo]) (by simpa only [abs_neg] using ht)
    have he : (1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I) =
        ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    rw [RHTower.zeta_eq_zetaChi_mul hz0 hz1 hg, norm_mul, he]
    simp only [abs_neg] at href
    calc
      _ ≤ (K * |t| ^ (1 / 2 - σ)) * (A * |t| ^ (33 / 200 + r)) :=
        mul_le_mul hχ href (norm_nonneg _) (by positivity)
      _ = (K * A) * |t| ^ (1 / 2 - σ + (33 / 200 + r)) := by
        rw [Real.rpow_add ht0 (1 / 2 - σ) (33 / 200 + r)]; ring
      _ ≤ (K * A) * |t| ^ (33 / 200 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1
          (by linarith only [hσlo, hrε, hε])) (mul_nonneg hK hA.le)
      _ ≤ ((K + 1) * A) * |t| ^ (33 / 200 + ε) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hA]) (by positivity)

/-- A fixed disc has a sub-Weyl envelope; its radius depends only on ε. -/
private theorem exists_subWeyl_line_disc_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ 1 / 4 ∧ 0 < C ∧
      ∀ γ : ℝ, 9 ≤ |γ| →
        ∀ z ∈ closedBall ((1 / 2 : ℂ) + γ * I) (2 * R),
          ‖riemannZeta z‖ ≤ C * |γ| ^ (33 / 200 + ε) := by
  obtain ⟨r, A, hr, hr1, hA, ha⟩ := exists_subWeyl_narrow_strip_bound hε
  refine ⟨r / 2, A * (2 : ℝ) ^ (33 / 200 + ε), by positivity,
    by linarith only [hr1], by positivity, ?_⟩
  intro γ hγ z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (abs_re_le_norm _).trans hz
  have him := (abs_im_le_norm _).trans hz
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, sub_im, add_im, mul_im, add_zero] at hre him
  norm_num at hre him
  have ht8 : 8 ≤ |z.im| := by
    have h := abs_sub_abs_le_abs_sub γ z.im
    rw [abs_sub_comm] at h
    linarith only [h, him, hγ, hr1]
  have htγ : |z.im| ≤ 2 * |γ| := by
    have h := abs_sub_abs_le_abs_sub z.im γ
    linarith only [h, him, hγ, hr1]
  have hbound := ha z.re z.im (by linarith only [hre]) ht8
  rw [re_add_im] at hbound
  calc
    ‖riemannZeta z‖ ≤ A * |z.im| ^ (33 / 200 + ε) := hbound
    _ ≤ A * (2 * |γ|) ^ (33 / 200 + ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) htγ
        (by linarith only [hε])) hA.le
    _ = (A * (2 : ℝ) ^ (33 / 200 + ε)) * |γ| ^ (33 / 200 + ε) := by
      rw [Real.mul_rpow (by norm_num) (abs_nonneg γ)]
      ring

private theorem line_disc_avoids_pole {γ R : ℝ} (hγ : 9 ≤ |γ|) (hR : R ≤ 1 / 4) :
    closedBall ((1 / 2 : ℂ) + γ * I) (2 * R) ⊆ {s : ℂ | s ≠ 1} := by
  intro z hz he
  rw [mem_closedBall, dist_eq_norm] at hz
  have him := (abs_im_le_norm (z - ((1 / 2 : ℂ) + γ * I))).trans hz
  rw [he] at him
  norm_num at him
  linarith only [him, hγ, hR]

/-- Every strip zero forces a quadratically small central value, with
sub-Weyl height cost and no restriction on its depth. -/
theorem exists_norm_zeta_center_le_subWeyl_depth_sq {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 → 9 ≤ |ρ.im| →
      ‖riemannZeta ((1 / 2 : ℂ) + ρ.im * I)‖ ≤
        C * |ρ.im| ^ (33 / 200 + ε) * (ρ.re - 1 / 2) ^ 2 := by
  obtain ⟨R, A, hR, hR1, hA, ha⟩ := exists_subWeyl_line_disc_bound hε
  refine ⟨64 * A / R ^ 2, by positivity, ?_⟩
  intro ρ hρ h0 h1 hγ
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hbound := ha ρ.im hγ
  by_cases hδ : |ρ.re - 1 / 2| ≤ R / 8
  · let c : ℂ := (1 / 2 : ℂ) + ρ.im * I
    let h : ℂ := ((ρ.re - 1 / 2 : ℝ) : ℂ)
    have hplus : c + h = ρ := by apply Complex.ext <;> simp [c, h]
    have hminus : c - h = 1 - (starRingEnd ℂ) ρ := by
      apply Complex.ext <;> simp [c, h]; ring
    have hpartner : riemannZeta (c - h) = 0 := by
      rw [hminus, show (1 : ℂ) - (starRingEnd ℂ) ρ =
        (starRingEnd ℂ) (1 - ρ) by simp,
        riemannZeta_conj, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ h0 h1,
        map_zero]
    have hf : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
      fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
    have hhn : ‖h‖ = |ρ.re - 1 / 2| := by
      rw [show h = ((ρ.re - 1 / 2 : ℝ) : ℂ) from rfl, norm_real, Real.norm_eq_abs]
    have key := norm_le_of_two_symmetric_zeros isOpen_ne hf hR
      (line_disc_avoids_pole hγ hR1) hbound (by rw [hhn]; exact hδ)
      hpartner (by rw [hplus]; exact hρ)
    rw [hhn, sq_abs] at key
    calc
      ‖riemannZeta c‖ ≤ 24 * (A * |ρ.im| ^ (33 / 200 + ε)) / R ^ 2 *
          (ρ.re - 1 / 2) ^ 2 := key
      _ ≤ 64 * (A * |ρ.im| ^ (33 / 200 + ε)) / R ^ 2 *
          (ρ.re - 1 / 2) ^ 2 := by gcongr; norm_num
      _ = _ := by ring
  · have hquad : R ^ 2 ≤ 64 * (ρ.re - 1 / 2) ^ 2 := by
      have hδ' : R / 8 < |ρ.re - 1 / 2| := lt_of_not_ge hδ
      have hs := sq_nonneg (|ρ.re - 1 / 2| - R / 8)
      nlinarith only [hδ', hR, sq_abs (ρ.re - 1 / 2), hs]
    calc
      ‖riemannZeta ((1 / 2 : ℂ) + ρ.im * I)‖ ≤
          A * |ρ.im| ^ (33 / 200 + ε) :=
        hbound _ (mem_closedBall_self (by positivity))
      _ ≤ 64 * A * |ρ.im| ^ (33 / 200 + ε) * (ρ.re - 1 / 2) ^ 2 / R ^ 2 := by
        apply (le_div_iff₀ hR2).2
        have hm := mul_le_mul_of_nonneg_left hquad
          (show 0 ≤ A * |ρ.im| ^ (33 / 200 + ε) by positivity)
        nlinarith only [hm]
      _ = _ := by ring

/-- The central value measures FE-pair depth at the sub-Weyl scale. -/
theorem exists_subWeyl_depth_ge_sqrt_center {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 → 9 ≤ |ρ.im| →
      Real.sqrt (‖riemannZeta ((1 / 2 : ℂ) + ρ.im * I)‖ /
        (C * |ρ.im| ^ (33 / 200 + ε))) ≤ |ρ.re - 1 / 2| := by
  obtain ⟨C, hC, hc⟩ := exists_norm_zeta_center_le_subWeyl_depth_sq hε
  refine ⟨C, hC, fun ρ hρ h0 h1 hγ => ?_⟩
  have hpos : 0 < C * |ρ.im| ^ (33 / 200 + ε) :=
    mul_pos hC (Real.rpow_pos_of_pos (by linarith only [hγ]) _)
  rw [← Real.sqrt_sq (abs_nonneg (ρ.re - 1 / 2)), sq_abs]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hpos]
  simpa only [mul_comm ((ρ.re - 1 / 2) ^ 2)] using hc ρ hρ h0 h1 hγ

/-- A shallow off-line FE pair flattens a whole interval at sub-Weyl cost. -/
theorem exists_norm_zeta_interval_le_subWeyl_depth_sq {ε : ℝ} (hε : 0 < ε) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 → 9 ≤ |ρ.im| →
      ∀ η u : ℝ, |ρ.re - 1 / 2| ≤ η → η ≤ r → |u| ≤ η →
      ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im + u) * I)‖ ≤
        C * |ρ.im| ^ (33 / 200 + ε) * η ^ 2 := by
  obtain ⟨R, A, hR, hR1, hA, ha⟩ := exists_subWeyl_line_disc_bound hε
  refine ⟨R / 8, 64 * A / R ^ 2, by positivity, by positivity, ?_⟩
  intro ρ hρ h0 h1 hoff hγ η u hδη hη hu
  let c : ℂ := (1 / 2 : ℂ) + ρ.im * I
  let h : ℂ := ((ρ.re - 1 / 2 : ℝ) : ℂ)
  let M : ℝ := A * |ρ.im| ^ (33 / 200 + ε)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hδη
  have hhn : ‖h‖ = |ρ.re - 1 / 2| := by
    rw [show h = ((ρ.re - 1 / 2 : ℝ) : ℂ) from rfl, norm_real, Real.norm_eq_abs]
  have hplus : c + h = ρ := by apply Complex.ext <;> simp [c, h]
  have hminus : c - h = 1 - (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [c, h]; ring
  have hpartner : riemannZeta (c - h) = 0 := by
    rw [hminus, show (1 : ℂ) - (starRingEnd ℂ) ρ =
      (starRingEnd ℂ) (1 - ρ) by simp,
      riemannZeta_conj, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ h0 h1,
      map_zero]
  have hball : closedBall (c - h) R ⊆ closedBall c (2 * R) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    calc
      ‖z - c‖ = ‖(z - (c - h)) - h‖ := by ring_nf
      _ ≤ ‖z - (c - h)‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 2 * R := by rw [hhn]; linarith only [hz, hδη, hη, hR]
  have hsub : closedBall (c - h) R ⊆ {s : ℂ | s ≠ 1} :=
    hball.trans (line_disc_avoids_pole hγ hR1)
  have hf : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hbound : ∀ z ∈ closedBall (c - h) R, ‖riemannZeta z‖ ≤ M :=
    fun z hz => ha ρ.im hγ z (hball hz)
  have hpair : ‖(c + h) - (c - h)‖ = 2 * |ρ.re - 1 / 2| := by
    rw [show (c + h) - (c - h) = 2 * h by ring, norm_mul, hhn]; norm_num
  have hδ0 : 0 < 2 * |ρ.re - 1 / 2| :=
    mul_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hoff))
  have hder : ‖deriv riemannZeta (c - h)‖ ≤ 8 * M / R ^ 2 * (2 * η) := by
    have hd := norm_deriv_mul_le_of_two_zeros isOpen_ne hf hR hsub hbound
      (by rw [hpair]; linarith only [hδη, hη]) hpartner (by rw [hplus]; exact hρ)
    rw [hpair] at hd
    have hd' : ‖deriv riemannZeta (c - h)‖ ≤
        8 * M / R ^ 2 * (2 * |ρ.re - 1 / 2|) := by
      have hm : ‖deriv riemannZeta (c - h)‖ * (2 * |ρ.re - 1 / 2|) ≤
          (8 * M / R ^ 2 * (2 * |ρ.re - 1 / 2|)) * (2 * |ρ.re - 1 / 2|) := by
        calc
          _ ≤ 8 * M / R ^ 2 * (2 * |ρ.re - 1 / 2|) ^ 2 := hd
          _ = _ := by ring
      exact le_of_mul_le_mul_right hm hδ0
    exact hd'.trans (mul_le_mul_of_nonneg_left (by linarith only [hδη]) (by positivity))
  let b : ℂ := c + (u : ℂ) * I
  have hbeq : (1 / 2 : ℂ) + (ρ.im + u) * I = b := by
    dsimp only [b, c]; ring
  have hba : ‖b - (c - h)‖ ≤ 2 * η := by
    rw [show b - (c - h) = h + (u : ℂ) * I by dsimp only [b]; ring]
    calc
      ‖h + (u : ℂ) * I‖ ≤ ‖h‖ + ‖(u : ℂ) * I‖ := norm_add_le _ _
      _ = |ρ.re - 1 / 2| + |u| := by
        rw [hhn, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      _ ≤ 2 * η := by linarith only [hδη, hu]
  have htay := norm_sub_taylor_le isOpen_ne hf hR hsub hbound
    (b := b) (by linarith only [hba, hη])
  rw [hpartner, sub_zero] at htay
  rw [hbeq]
  calc
    ‖riemannZeta b‖ = ‖(riemannZeta b - deriv riemannZeta (c - h) * (b - (c - h))) +
        deriv riemannZeta (c - h) * (b - (c - h))‖ := by ring_nf
    _ ≤ ‖riemannZeta b - deriv riemannZeta (c - h) * (b - (c - h))‖ +
        ‖deriv riemannZeta (c - h)‖ * ‖b - (c - h)‖ := by
      rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 8 * M / R ^ 2 * (2 * η) ^ 2 + (8 * M / R ^ 2 * (2 * η)) * (2 * η) := by
      refine add_le_add (htay.trans ?_) (mul_le_mul hder hba (norm_nonneg _) (by positivity))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hba 2) (by positivity)
    _ = _ := by dsimp only [M]; ring

end GaloisForLFunctions.ArithmeticDiscreteness

#print axioms GaloisForLFunctions.ArithmeticDiscreteness.exists_norm_zeta_center_le_subWeyl_depth_sq
#print axioms GaloisForLFunctions.ArithmeticDiscreteness.exists_subWeyl_depth_ge_sqrt_center

#print axioms GaloisForLFunctions.ArithmeticDiscreteness.exists_norm_zeta_interval_le_subWeyl_depth_sq
