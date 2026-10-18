import GaloisForLFunctions.RHTower.DQPTEulerMaclaurinPartialSum

/-!
# Euler–Maclaurin summation for complex derivative towers

Complexification of the existing arbitrary-order real formula. The remainder
estimate keeps the integral of the highest derivative, so it can be applied to
complex powers on intervals whose length grows with the vertical height.
-/

open Complex Filter Topology Set MeasureTheory
open RHTower.DQPT

noncomputable section

namespace RHTower

def ComplexDerivTower (F : ℕ → ℝ → ℂ) (s : Set ℝ) : Prop :=
  ∀ j : ℕ, ∀ x ∈ s, HasDerivAt (F j) (F (j + 1) x) x

theorem ComplexDerivTower.continuousOn {F : ℕ → ℝ → ℂ} {s : Set ℝ}
    (hF : ComplexDerivTower F s) (j : ℕ) : ContinuousOn (F j) s :=
  fun x hx => (hF j x hx).continuousAt.continuousWithinAt

theorem ComplexDerivTower.mono {F : ℕ → ℝ → ℂ} {s t : Set ℝ}
    (hF : ComplexDerivTower F s) (hts : t ⊆ s) : ComplexDerivTower F t :=
  fun j x hx => hF j x (hts hx)

theorem ComplexDerivTower.re {F : ℕ → ℝ → ℂ} {s : Set ℝ}
    (hF : ComplexDerivTower F s) : DqptDerivTower (fun j x => (F j x).re) s := by
  intro j x hx
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hF j x hx)

theorem ComplexDerivTower.im {F : ℕ → ℝ → ℂ} {s : Set ℝ}
    (hF : ComplexDerivTower F s) : DqptDerivTower (fun j x => (F j x).im) s := by
  intro j x hx
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hF j x hx)

def complexEMCell (F : ℕ → ℝ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ∫ x in t..(t + 1), (bernoulliFun k (x - t) / (k.factorial : ℝ) : ℝ) * F k x

theorem intervalIntegrable_complexEMCell {F : ℕ → ℝ → ℂ} {t : ℝ}
    (hF : ComplexDerivTower F (Icc t (t + 1))) (k : ℕ) :
    IntervalIntegrable
      (fun x => (bernoulliFun k (x - t) / (k.factorial : ℝ) : ℝ) * F k x)
      volume t (t + 1) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : t ≤ t + 1)]
  exact (by fun_prop : ContinuousOn
    (fun x : ℝ => ((bernoulliFun k (x - t) / (k.factorial : ℝ) : ℝ) : ℂ))
    (Icc t (t + 1))).mul (hF.continuousOn k)

theorem complexEMCell_re {F : ℕ → ℝ → ℂ} {t : ℝ}
    (hF : ComplexDerivTower F (Icc t (t + 1))) (k : ℕ) :
    (complexEMCell F k t).re = dqptEMJ (fun j x => (F j x).re) k t := by
  have h := Complex.reCLM.intervalIntegral_comp_comm (intervalIntegrable_complexEMCell hF k)
  simpa only [Complex.reCLM_apply, complexEMCell, dqptEMJ, Complex.re_ofReal_mul] using h.symm

theorem complexEMCell_im {F : ℕ → ℝ → ℂ} {t : ℝ}
    (hF : ComplexDerivTower F (Icc t (t + 1))) (k : ℕ) :
    (complexEMCell F k t).im = dqptEMJ (fun j x => (F j x).im) k t := by
  have h := Complex.imCLM.intervalIntegral_comp_comm (intervalIntegrable_complexEMCell hF k)
  simpa only [Complex.imCLM_apply, complexEMCell, dqptEMJ, Complex.im_ofReal_mul] using h.symm

/-- Arbitrary even-order Euler–Maclaurin, with complex values and a cell-integral
remainder. No estimate or asymptotic is assumed. -/
theorem complex_euler_maclaurin {F : ℕ → ℝ → ℂ} {a : ℝ} (m N : ℕ)
    (hF : ComplexDerivTower F (Icc a (a + N))) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n) =
      (∫ x in a..(a + (N : ℝ)), F 0 x) + (F 0 a + F 0 (a + N)) / 2 +
        ∑ r ∈ Finset.range (m + 1),
          (((bernoulli (2 * r + 2) : ℚ) : ℝ) /
            (((2 * r + 2).factorial : ℕ) : ℝ) : ℝ) *
              (F (2 * r + 1) (a + N) - F (2 * r + 1) a) -
        ∑ n ∈ Finset.range N, complexEMCell F (2 * m + 2) (a + n) := by
  have hi : IntervalIntegrable (F 0) volume a (a + N) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))]
    exact hF.continuousOn 0
  have hcell (n : ℕ) (hn : n ∈ Finset.range N) :
      ComplexDerivTower F (Icc (a + n) (a + n + 1)) := by
    apply hF.mono
    apply Icc_subset_Icc
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
      linarith
  apply Complex.ext
  · have h := dqpt_euler_maclaurin m N hF.re
    have hir : (∫ x in a..(a + N), (F 0 x).re) =
        (∫ x in a..(a + N), F 0 x).re := Complex.reCLM.intervalIntegral_comp_comm hi
    rw [hir] at h
    simpa only [Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.div_ofNat_re,
      Complex.re_ofReal_mul, Finset.sum_congr rfl (fun n hn =>
        complexEMCell_re (hcell n hn) (2 * m + 2))] using h
  · have h := dqpt_euler_maclaurin m N hF.im
    have hii : (∫ x in a..(a + N), (F 0 x).im) =
        (∫ x in a..(a + N), F 0 x).im := Complex.imCLM.intervalIntegral_comp_comm hi
    rw [hii] at h
    simpa only [Complex.im_sum, Complex.add_im, Complex.sub_im, Complex.div_ofNat_im,
      Complex.im_ofReal_mul, Finset.sum_congr rfl (fun n hn =>
        complexEMCell_im (hcell n hn) (2 * m + 2))] using h

/-- The complex remainder is bounded directly in norm, without losing a factor
through separate estimates for its real and imaginary parts. -/
theorem norm_complexEMCell_le {F : ℕ → ℝ → ℂ} {t : ℝ}
    (hF : ComplexDerivTower F (Icc t (t + 1))) {k : ℕ} (hk : k ≠ 0) :
    ‖complexEMCell F (2 * k) t‖ ≤
      |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
        ∫ x in t..(t + 1), ‖F (2 * k) x‖ := by
  have hle : t ≤ t + 1 := by linarith
  have hf : 0 < (((2 * k).factorial : ℕ) : ℝ) := by positivity
  have hnorm : IntervalIntegrable
      (fun x => ‖(bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ) : ℝ) *
        F (2 * k) x‖) volume t (t + 1) := (intervalIntegrable_complexEMCell hF _).norm
  have hbound : IntervalIntegrable
      (fun x => |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
        ‖F (2 * k) x‖) volume t (t + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact continuousOn_const.mul (hF.continuousOn _).norm
  calc
    ‖complexEMCell F (2 * k) t‖ ≤
        ∫ x in t..(t + 1),
          ‖(bernoulliFun (2 * k) (x - t) / (((2 * k).factorial : ℕ) : ℝ) : ℝ) *
            F (2 * k) x‖ := intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ x in t..(t + 1),
        |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
          ‖F (2 * k) x‖ := by
      apply intervalIntegral.integral_mono_on hle hnorm hbound
      intro x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hf]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (dqpt_abs_bernoulliFun_le hk ⟨by linarith [hx.1], by linarith [hx.2]⟩) hf.le)
        (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Summing the cell estimates keeps the integral over the whole interval. -/
theorem norm_sum_complexEMCell_le {F : ℕ → ℝ → ℂ} {a : ℝ} (N : ℕ)
    (hF : ComplexDerivTower F (Icc a (a + N))) {k : ℕ} (hk : k ≠ 0) :
    ‖∑ n ∈ Finset.range N, complexEMCell F (2 * k) (a + n)‖ ≤
      |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
        ∫ x in a..(a + N), ‖F (2 * k) x‖ := by
  have hcell (n : ℕ) (hn : n < N) :
      ComplexDerivTower F (Icc (a + n) (a + n + 1)) := by
    apply hF.mono
    apply Icc_subset_Icc
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
      linarith
  have hadj : (∑ n ∈ Finset.range N,
      ∫ x in (a + n)..(a + (n + 1 : ℕ)), ‖F (2 * k) x‖) =
      ∫ x in a..(a + N), ‖F (2 * k) x‖ := by
    simpa using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : ℕ => a + n) (n := N) (fun n hn => by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by push_cast; linarith : a + (n : ℝ) ≤ a + (n + 1 : ℕ))]
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          ((hcell n hn).continuousOn (2 * k)).norm)
  calc
    ‖∑ n ∈ Finset.range N, complexEMCell F (2 * k) (a + n)‖ ≤
        ∑ n ∈ Finset.range N,
          |((bernoulli (2 * k) : ℚ) : ℝ)| / (((2 * k).factorial : ℕ) : ℝ) *
            ∫ x in (a + n)..(a + (n + 1 : ℕ)), ‖F (2 * k) x‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        norm_complexEMCell_le (hcell n (Finset.mem_range.mp hn)) hk
    _ = _ := by rw [← Finset.mul_sum, hadj]

end RHTower
