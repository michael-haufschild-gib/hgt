import GaloisForLFunctions.HTGeometry.ExpLocalInverse

/-!
# Stable logarithms of interpolation weights

The Lagrange weights at zero can be exponentially large. Their logarithmic
changes involve only reciprocal node separations. Factoring each weight
before taking logarithms keeps every branch near one.
-/

open Complex Finset Metric

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lagrange interpolation weight for evaluation at zero. -/
def zeroInterpolationWeight (z : ι → ℂ) (j : ι) : ℂ :=
  ∏ k ∈ univ.erase j, (-z k) / (z j - z k)

/-- A logarithmic change of weights, with each factor normalized at the reference nodes. -/
def interpolationLogCorrection (b z : ι → ℂ) (j : ι) : ℂ :=
  ∑ k ∈ univ.erase j,
    (Complex.log (z k / b k) - Complex.log ((z j - z k) / (b j - b k)))

/-- Exponentiating the factorwise logarithms gives the exact change of interpolation weights. -/
theorem zeroInterpolationWeight_eq_mul_exp {b z : ι → ℂ}
    (hb : ∀ k, b k ≠ 0) (hz : ∀ k, z k ≠ 0)
    (hbi : Function.Injective b) (hzi : Function.Injective z) (j : ι) :
    zeroInterpolationWeight z j =
      zeroInterpolationWeight b j * Complex.exp (interpolationLogCorrection b z j) := by
  unfold zeroInterpolationWeight interpolationLogCorrection
  rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
  have hbd : b j - b k ≠ 0 := sub_ne_zero.mpr (hbi.ne hjk)
  have hzd : z j - z k ≠ 0 := sub_ne_zero.mpr (hzi.ne hjk)
  rw [Complex.exp_sub, Complex.exp_log (div_ne_zero (hz k) (hb k)),
    Complex.exp_log (div_ne_zero hzd hbd)]
  field_simp [hb k, hbd, hzd] <;> ring

private theorem normalized_node_mem_ball {a b : ℂ} {s r : ℝ}
    (hs : 0 < s) (hb : s ≤ ‖b‖) (hr : 4 * r ≤ s) (ha : ‖a - b‖ ≤ r) :
    a / b ∈ ball (1 : ℂ) (1 / 2) := by
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hs.trans_le hb)
  rw [mem_ball, dist_eq_norm, show a / b - 1 = (a - b) / b by field_simp, norm_div]
  apply (div_lt_iff₀ (hs.trans_le hb)).mpr
  linarith only [ha, hr, hb, hs]

private theorem log_ratio_difference_le {a c b : ℂ} {s D : ℝ}
    (hs : 0 < s) (hb : s ≤ ‖b‖) (hD : 0 ≤ D)
    (ha : a / b ∈ ball (1 : ℂ) (1 / 2))
    (hc : c / b ∈ ball (1 : ℂ) (1 / 2)) (hac : ‖a - c‖ ≤ D) :
    ‖Complex.log (a / b) - Complex.log (c / b)‖ ≤ 2 * D / s := by
  have hh := HTGeometry.lipschitzOnWith_log_ball_one.dist_le_mul _ ha _ hc
  simp only [dist_eq_norm, NNReal.coe_ofNat, ← sub_div, norm_div] at hh
  calc
    _ ≤ 2 * (‖a - c‖ / ‖b‖) := hh
    _ ≤ 2 * (D / s) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div₀ hD hac hs hb
    _ = _ := by ring

/-- The normalized numerator and denominator factors stay in a single logarithm chart. -/
theorem interpolation_factors_mem_ball {b z : ι → ℂ} {s r : ℝ}
    (hs : 0 < s) (hr : 0 ≤ r) (hsmall : 8 * r ≤ s)
    (hb : ∀ j, s ≤ ‖b j‖) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖)
    (hz : ∀ j, ‖z j - b j‖ ≤ r) :
    (∀ j, z j / b j ∈ ball (1 : ℂ) (1 / 2)) ∧
      ∀ j k, j ≠ k → (z j - z k) / (b j - b k) ∈ ball (1 : ℂ) (1 / 2) := by
  constructor
  · intro j
    exact normalized_node_mem_ball hs (hb j) (by linarith only [hr, hsmall]) (hz j)
  · intro j k hjk
    apply normalized_node_mem_ball hs (hsep j k hjk) (r := 2 * r)
      (by linarith only [hsmall])
    calc
      _ = ‖(z j - b j) - (z k - b k)‖ := by congr 1; ring
      _ ≤ ‖z j - b j‖ + ‖z k - b k‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith only [hz j, hz k]

/-- The logarithmic change is Lipschitz with a polynomial, rather than exponential, constant. -/
theorem norm_interpolationLogCorrection_sub_le {b z w : ι → ℂ} {s r D : ℝ}
    (hs : 0 < s) (hr : 0 ≤ r) (hsmall : 8 * r ≤ s)
    (hb : ∀ j, s ≤ ‖b j‖) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖)
    (hz : ∀ j, ‖z j - b j‖ ≤ r) (hw : ∀ j, ‖w j - b j‖ ≤ r)
    (hD : 0 ≤ D) (hzw : ∀ j, ‖z j - w j‖ ≤ D) (j : ι) :
    ‖interpolationLogCorrection b z j - interpolationLogCorrection b w j‖ ≤
      (Fintype.card ι : ℝ) * (6 * D / s) := by
  obtain ⟨hzn, hzd⟩ := interpolation_factors_mem_ball hs hr hsmall hb hsep hz
  obtain ⟨hwn, hwd⟩ := interpolation_factors_mem_ball hs hr hsmall hb hsep hw
  unfold interpolationLogCorrection
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ univ.erase j,
        ‖(Complex.log (z k / b k) - Complex.log ((z j - z k) / (b j - b k))) -
          (Complex.log (w k / b k) - Complex.log ((w j - w k) / (b j - b k)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ univ.erase j, 6 * D / s := by
      apply Finset.sum_le_sum
      intro k hk
      have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
      have hn := log_ratio_difference_le hs (hb k) hD (hzn k) (hwn k) (hzw k)
      have hdiff : ‖(z j - z k) - (w j - w k)‖ ≤ 2 * D := by
        calc
          _ = ‖(z j - w j) - (z k - w k)‖ := by congr 1; ring
          _ ≤ ‖z j - w j‖ + ‖z k - w k‖ := norm_sub_le _ _
          _ ≤ 2 * D := by linarith only [hzw j, hzw k]
      have hd := log_ratio_difference_le hs (hsep j k hjk) (by positivity : 0 ≤ 2 * D)
        (hzd j k hjk) (hwd j k hjk) hdiff
      rw [show (Complex.log (z k / b k) - Complex.log ((z j - z k) / (b j - b k))) -
          (Complex.log (w k / b k) - Complex.log ((w j - w k) / (b j - b k))) =
          (Complex.log (z k / b k) - Complex.log (w k / b k)) -
          (Complex.log ((z j - z k) / (b j - b k)) -
            Complex.log ((w j - w k) / (b j - b k))) by ring]
      exact (norm_sub_le _ _).trans (by linarith only [hn, hd])
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_le_card (Finset.erase_subset j univ))

/-- The logarithmic change vanishes at the reference configuration. -/
theorem interpolationLogCorrection_self {b : ι → ℂ}
    (hb : ∀ j, b j ≠ 0) (hsep : Function.Injective b) (j : ι) :
    interpolationLogCorrection b b j = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
  simp only [div_self (hb k), div_self (sub_ne_zero.mpr (hsep.ne hjk)),
    Complex.log_one, sub_self]

/-- The size of the logarithmic change depends only on node separation and displacement. -/
theorem norm_interpolationLogCorrection_le {b z : ι → ℂ} {s r : ℝ}
    (hs : 0 < s) (hr : 0 ≤ r) (hsmall : 8 * r ≤ s)
    (hb : ∀ j, s ≤ ‖b j‖) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖)
    (hz : ∀ j, ‖z j - b j‖ ≤ r) (j : ι) :
    ‖interpolationLogCorrection b z j‖ ≤ (Fintype.card ι : ℝ) * (6 * r / s) := by
  have hbn : ∀ j, b j ≠ 0 := fun j => norm_pos_iff.mp (hs.trans_le (hb j))
  have hinj : Function.Injective b := by
    intro j k he
    by_contra hjk
    have hh := hsep j k hjk
    rw [he, sub_self, norm_zero] at hh
    exact (not_le_of_gt hs) hh
  have hh := norm_interpolationLogCorrection_sub_le hs hr hsmall hb hsep hz
    (fun _ => by simpa only [sub_self, norm_zero] using hr) hr hz j
  simpa only [interpolationLogCorrection_self hbn hinj, sub_zero] using hh

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
