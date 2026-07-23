import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Reflected digamma anomaly orientation universality

The reflected archimedean anomaly is not only real exactly on the critical line.  At every
positive height its imaginary part is strictly decreasing across the open strip, is odd under
reflection about `1/2`, and carries the exact orientation of the two half-strips.
-/

namespace ReflectedDigammaAnomaly

open Set

noncomputable section

/-- Reflection about the critical line reverses the imaginary anomaly. -/
theorem anomaly_one_sub_im (sigma t : ℝ) :
    (anomaly (1 - sigma) t).im = -(anomaly sigma t).im := by
  rw [anomaly_im_eq_sub, anomaly_im_eq_sub]
  ring_nf

/-- At every positive height, the imaginary reflected anomaly is strictly decreasing across the
open critical strip. -/
theorem anomaly_im_strictAntiOn {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun sigma : ℝ => (anomaly sigma t).im) (Set.Ioo 0 1) := by
  intro sigma hsigma tau htau hst
  change (anomaly tau t).im < (anomaly sigma t).im
  rw [anomaly_im_eq_sub, anomaly_im_eq_sub]
  have hdirect :
      verticalDigammaIm tau t < verticalDigammaIm sigma t :=
    verticalDigammaIm_strictAnti hsigma.1.le hst ht
  have hreflected :
      verticalDigammaIm (1 - sigma) t < verticalDigammaIm (1 - tau) t :=
    verticalDigammaIm_strictAnti (by linarith [htau.2]) (by linarith) ht
  linarith

/-- The positive half of the exact reflected-anomaly orientation law. -/
theorem anomaly_im_pos_iff {sigma t : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (ht : 0 < t) :
    0 < (anomaly sigma t).im ↔ sigma < 1 / 2 := by
  constructor
  · intro hpos
    by_contra hnot
    have hhalf : (1 / 2 : ℝ) ≤ sigma := le_of_not_gt hnot
    rcases hhalf.eq_or_lt with heq | hlt
    · subst sigma
      norm_num [anomaly_im_eq_sub] at hpos
    · have hstrict :=
        anomaly_im_strictAntiOn ht
          (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by norm_num)
          ⟨hsigma, hsigma1⟩ hlt
      have hcenter : (anomaly (1 / 2 : ℝ) t).im = 0 :=
        (anomaly_im_eq_zero_iff (by norm_num) (by norm_num) ht).2 rfl
      linarith
  · intro hlt
    have hstrict :=
      anomaly_im_strictAntiOn ht
        ⟨hsigma, hsigma1⟩
        (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by norm_num) hlt
    have hcenter : (anomaly (1 / 2 : ℝ) t).im = 0 :=
      (anomaly_im_eq_zero_iff (by norm_num) (by norm_num) ht).2 rfl
    linarith

/-- The negative half of the exact reflected-anomaly orientation law. -/
theorem anomaly_im_neg_iff {sigma t : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (ht : 0 < t) :
    (anomaly sigma t).im < 0 ↔ 1 / 2 < sigma := by
  constructor
  · intro hneg
    by_contra hnot
    have hhalf : sigma ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
    rcases hhalf.eq_or_lt with heq | hlt
    · subst sigma
      norm_num [anomaly_im_eq_sub] at hneg
    · exact (not_lt_of_ge (anomaly_im_pos_iff hsigma hsigma1 ht |>.2 hlt).le) hneg
  · intro hlt
    have hstrict :=
      anomaly_im_strictAntiOn ht
        (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by norm_num)
        ⟨hsigma, hsigma1⟩ hlt
    have hcenter : (anomaly (1 / 2 : ℝ) t).im = 0 :=
      (anomaly_im_eq_zero_iff (by norm_num) (by norm_num) ht).2 rfl
    linarith

/-- **Reflected digamma anomaly orientation universality law.**  The critical line is the unique
zero, and the imaginary anomaly gives the exact oriented side of every point in the open strip. -/
theorem reflectedDigammaAnomaly_orientationUniversality
    {sigma t : ℝ} (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (ht : 0 < t) :
    ((anomaly (1 - sigma) t).im = -(anomaly sigma t).im) ∧
      (0 < (anomaly sigma t).im ↔ sigma < 1 / 2) ∧
      ((anomaly sigma t).im = 0 ↔ sigma = 1 / 2) ∧
      ((anomaly sigma t).im < 0 ↔ 1 / 2 < sigma) :=
  ⟨anomaly_one_sub_im sigma t,
    anomaly_im_pos_iff hsigma hsigma1 ht,
    anomaly_im_eq_zero_iff hsigma hsigma1 ht,
    anomaly_im_neg_iff hsigma hsigma1 ht⟩

end

end ReflectedDigammaAnomaly
