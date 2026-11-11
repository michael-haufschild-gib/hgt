import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheInterpolationWeightsCanBeExponentialCoefficients
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.HighFrequencyBinomialPolynomials

/-!
# Nearby logarithms of imaginary-grid interpolation weights

A phase shift of at most `2π/T` chooses the logarithm nearest a prescribed
imaginary node. Factorwise norm bounds control its real displacement.
This supplies the logarithmic data of the simultaneous node calibration.
-/

open Complex Finset Metric Set

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Every nonzero coefficient has a logarithm close to any prescribed imaginary frequency. -/
theorem exists_scaled_log_near_imaginary {c b : ℂ} (hc : c ≠ 0) (hb : b.re = 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ a : ℂ, Complex.exp a = c ∧
      ‖a / (T : ℂ) - b‖ ≤ (|Real.log ‖c‖| + 2 * Real.pi) / T := by
  let η : ℝ := phaseShift b.im c.arg 0 T
  have hη0 : 0 < η := by simpa only [Nat.cast_zero, mul_zero, zero_div] using phaseShift_gt b.im c.arg 0 hT
  have hη : η ≤ 2 * Real.pi / T := by
    simpa only [Nat.cast_zero, zero_add, mul_one] using phaseShift_le b.im c.arg 0 hT
  let a : ℂ := (Real.log ‖c‖ : ℂ) + (((b.im + η) * T : ℝ) : ℂ) * I
  have hb' : b = (b.im : ℂ) * I := by
    apply Complex.ext <;> simp [hb]
  have hlog : (Real.log ‖c‖ : ℂ) + (c.arg : ℂ) * I = Complex.log c := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  refine ⟨a, ?_, ?_⟩
  · dsimp only [a]
    rw [Complex.exp_add, cexp_add_phaseShift_mul_T b.im c.arg 0 hT,
      ← Complex.exp_add, hlog, Complex.exp_log hc]
  · have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hid : a / (T : ℂ) - b = ((Real.log ‖c‖ / T : ℝ) : ℂ) + (η : ℂ) * I := by
      dsimp only [a]
      rw [hb']
      push_cast
      field_simp [hTne] <;> ring
    rw [hid]
    calc
      _ ≤ ‖((Real.log ‖c‖ / T : ℝ) : ℂ)‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
      _ = |Real.log ‖c‖| / T + η := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hT,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0, Complex.norm_I, mul_one]
      _ ≤ |Real.log ‖c‖| / T + 2 * Real.pi / T := add_le_add_left hη _
      _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct nonzero nodes have nonzero interpolation weights at zero. -/
theorem zeroInterpolationWeight_ne_zero {b : ι → ℂ}
    (hb : ∀ j, b j ≠ 0) (hbi : Function.Injective b) (j : ι) :
    zeroInterpolationWeight b j ≠ 0 := by
  unfold zeroInterpolationWeight
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
  exact div_ne_zero (neg_ne_zero.mpr (hb k)) (sub_ne_zero.mpr (hbi.ne hjk))

private theorem abs_log_le_of_between {s B x : ℝ} (hs : 0 < s)
    (hx : s ≤ x) (hB : x ≤ B) :
    |Real.log x| ≤ |Real.log s| + |Real.log B| := by
  have hlo := Real.log_le_log hs hx
  have hhi := Real.log_le_log (hs.trans_le hx) hB
  rw [abs_le]
  constructor
  · linarith only [hlo, neg_abs_le (Real.log s), abs_nonneg (Real.log B)]
  · linarith only [hhi, le_abs_self (Real.log B), abs_nonneg (Real.log s)]

/-- A coarse logarithmic weight bound grows linearly with node count. -/
theorem abs_log_norm_zeroInterpolationWeight_le {b : ι → ℂ} {s B : ℝ}
    (hs : 0 < s) (hB : 0 < B) (hb : ∀ j, s ≤ ‖b j‖)
    (hupper : ∀ j, ‖b j‖ ≤ B) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖) (j : ι) :
    |Real.log ‖zeroInterpolationWeight b j‖| ≤
      2 * (Fintype.card ι : ℝ) * (|Real.log s| + |Real.log (2 * B)|) := by
  have hbn : ∀ k, b k ≠ 0 := fun k => norm_pos_iff.mp (hs.trans_le (hb k))
  have hdn : ∀ k ∈ univ.erase j, b j - b k ≠ 0 := by
    intro k hk
    exact norm_pos_iff.mp (hs.trans_le (hsep j k (Finset.mem_erase.mp hk).1.symm))
  have hfac : ∀ k ∈ univ.erase j, ‖(-b k) / (b j - b k)‖ ≠ 0 := by
    intro k hk
    exact norm_ne_zero_iff.mpr (div_ne_zero (neg_ne_zero.mpr (hbn k)) (hdn k hk))
  unfold zeroInterpolationWeight
  rw [norm_prod, Real.log_prod hfac]
  calc
    _ ≤ ∑ k ∈ univ.erase j, |Real.log ‖(-b k) / (b j - b k)‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ univ.erase j, 2 * (|Real.log s| + |Real.log (2 * B)|) := by
      apply Finset.sum_le_sum
      intro k hk
      have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
      have hn := abs_log_le_of_between hs (hb k) ((hupper k).trans (by linarith only [hB]))
      have hd := abs_log_le_of_between hs (hsep j k hjk)
        ((norm_sub_le (b j) (b k)).trans (by linarith only [hupper j, hupper k]))
      rw [norm_div, norm_neg, Real.log_div (norm_ne_zero_iff.mpr (hbn k))
        (norm_ne_zero_iff.mpr (hdn k hk))]
      exact (abs_sub _ _).trans (by linarith only [hn, hd])
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hh : ((univ.erase j).card : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Finset.card_le_card (Finset.erase_subset j univ))
      nlinarith only [hh, abs_nonneg (Real.log s), abs_nonneg (Real.log (2 * B))]

/-- Explicit size and separation bounds suffice for exact exponential calibration of imaginary nodes. -/
theorem exists_self_consistent_nodes_near_imaginary_grid {b : ι → ℂ} {s r T B : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hT : 0 < T) (hB : 0 < B) (hsmall : 8 * r ≤ s)
    (hb : ∀ j, s ≤ ‖b j‖) (hupper : ∀ j, ‖b j‖ ≤ B)
    (him : ∀ j, (b j).re = 0) (hsep : ∀ j k, j ≠ k → s ≤ ‖b j - b k‖)
    (hcontract : 12 * (Fintype.card ι : ℝ) ≤ s * T)
    (hsize : 2 * (2 * (Fintype.card ι : ℝ) * (|Real.log s| + |Real.log (2 * B)|) +
      2 * Real.pi) ≤ r * T) :
    ∃ z : ι → ℂ, (∀ j, ‖z j - b j‖ ≤ r) ∧ Function.Injective z ∧
      (∀ j, z j ≠ 0) ∧ ∀ j, Complex.exp ((T : ℂ) * z j) = zeroInterpolationWeight z j := by
  have hbn : ∀ j, b j ≠ 0 := fun j => norm_pos_iff.mp (hs.trans_le (hb j))
  have hbi : Function.Injective b := by
    intro j k he
    by_contra hjk
    have hh := hsep j k hjk
    rw [he, sub_self, norm_zero] at hh
    exact (not_le_of_gt hs) hh
  choose a hae han using fun j => exists_scaled_log_near_imaginary
    (zeroInterpolationWeight_ne_zero hbn hbi j) (him j) hT
  apply exists_self_consistent_interpolation_nodes hs hr hT hsmall hb hsep hcontract hae
  intro j
  refine (han j).trans ?_
  apply (div_le_iff₀ hT).mpr
  have hh := abs_log_norm_zeroInterpolationWeight_le hs hB hb hupper hsep j
  linarith only [hh, hsize]

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
