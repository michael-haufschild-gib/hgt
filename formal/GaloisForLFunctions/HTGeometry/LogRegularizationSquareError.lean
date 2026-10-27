import GaloisForLFunctions.HTGeometry.LogWeightedGeometricSum

/-!
# Quantitative logarithmic regularization

Splitting the amplitude at `exp(-K/4)` bounds the regularization error by
an exponentially small constant plus `8/K` times the squared logarithm.
A second estimate absorbs any multiplicative cutoff control into an
exponential regulator, without a bound on that control's growth.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Adding a positive squared-amplitude regulator raises the logarithmic potential. -/
lemma half_log_regularization_nonneg {x η : ℝ} (hx : 0 < x) (hη : 0 < η) :
    0 ≤ (1 / 2 : ℝ) * Real.log (x ^ 2 + η) - Real.log x := by
  have h := Real.log_le_log (sq_pos_of_pos hx) (le_add_of_nonneg_right hη.le)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- A scalar error bound separating the regular and small-amplitude regions. -/
lemma half_log_regularization_le_log_square {x K : ℝ} (hx : 0 < x) (hK : 4 ≤ K) :
    |(1 / 2 : ℝ) * Real.log (x ^ 2 + Real.exp (-K)) - Real.log x| ≤
      (1 / 2 : ℝ) * Real.exp (-K / 2) + (8 / K) * Real.log x ^ 2 := by
  have hK0 : 0 < K := by linarith only [hK]
  have hη := Real.exp_pos (-K)
  rw [abs_of_nonneg (half_log_regularization_nonneg hx hη)]
  by_cases hlarge : Real.exp (-K / 4) ≤ x
  · have hratio : Real.exp (-K) / x ^ 2 ≤ Real.exp (-K / 2) := by
      apply (div_le_iff₀ (sq_pos_of_pos hx)).2
      have hsq := pow_le_pow_left₀ (Real.exp_pos (-K / 4)).le hlarge 2
      have hp := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (-K / 2)).le
      have he : Real.exp (-K / 2) * Real.exp (-K / 4) ^ 2 = Real.exp (-K) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rwa [he] at hp
    have hquot : 1 + Real.exp (-K) / x ^ 2 = (x ^ 2 + Real.exp (-K)) / x ^ 2 := by
      field_simp
    have hid : (1 / 2 : ℝ) * Real.log (x ^ 2 + Real.exp (-K)) - Real.log x =
        (1 / 2 : ℝ) * Real.log (1 + Real.exp (-K) / x ^ 2) := by
      rw [hquot, Real.log_div (by positivity) (pow_ne_zero 2 hx.ne'), Real.log_pow]
      ring
    rw [hid]
    have hlog := Real.log_le_sub_one_of_pos
      (by positivity : 0 < 1 + Real.exp (-K) / x ^ 2)
    have hnonneg : 0 ≤ (8 / K) * Real.log x ^ 2 := by positivity
    linarith only [hlog, hratio, hnonneg]
  · have hxsmall : x ≤ Real.exp (-K / 4) := (lt_of_not_ge hlarge).le
    have hlog := Real.log_le_log hx hxsmall
    rw [Real.log_exp] at hlog
    have hneglog : 1 ≤ -Real.log x := by linarith only [hlog, hK]
    have hx1 : x ≤ 1 := hxsmall.trans (by
      apply Real.exp_le_one_iff.mpr
      linarith only [hK])
    have hη1 : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hK])
    have hsum : x ^ 2 + Real.exp (-K) ≤ 2 := by
      have hsq := pow_le_pow_left₀ hx.le hx1 2
      norm_num only [one_pow] at hsq
      linarith only [hsq, hη1]
    have hlogsum := Real.log_le_sub_one_of_pos (by positivity : 0 < x ^ 2 + Real.exp (-K))
    have hfirst : (1 / 2 : ℝ) * Real.log (x ^ 2 + Real.exp (-K)) - Real.log x ≤
        2 * (-Real.log x) := by linarith only [hlogsum, hsum, hneglog]
    have hlog0 : 0 ≤ -Real.log x := le_trans (by norm_num) hneglog
    have hquad : K * (-Real.log x) ≤ 4 * Real.log x ^ 2 := by
      have hp := mul_nonneg hlog0 (show 0 ≤ -Real.log x - K / 4 by linarith only [hlog])
      nlinarith only [hp]
    have hsecond : 2 * (-Real.log x) ≤ (8 / K) * Real.log x ^ 2 := by
      calc
        2 * (-Real.log x) ≤ (8 * Real.log x ^ 2) / K :=
          (le_div_iff₀ hK0).2 (by nlinarith only [hquad])
        _ = _ := by ring
    exact hfirst.trans (hsecond.trans (le_add_of_nonneg_left (by positivity)))


/-- Exponential regularization absorbs every control factor at least one. -/
lemma mul_exp_neg_exp_mul_half_le_exp_neg {x M : ℝ} (hx : 16 ≤ x) (hM : 1 ≤ M) :
    M * Real.exp (-(Real.exp x * M) / 2) ≤ Real.exp (-x) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hhalf : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.exp_pos (x / 2))
    rw [Real.log_exp] at h
    linarith only [h]
  have hsquare := pow_le_pow_left₀ (div_nonneg hx0 (by norm_num)) hhalf 2
  have he : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hsquare
  have hax : 4 * x ≤ Real.exp x := by
    have hp := mul_nonneg hx0 (sub_nonneg.mpr hx)
    nlinarith only [hsquare, hp]
  have ha4 : 4 ≤ Real.exp x := by linarith only [hax, hx]
  have hMexp : M ≤ Real.exp M := by
    have h := Real.log_le_sub_one_of_pos (Real.exp_pos M)
    rw [Real.log_exp] at h
    linarith only [h]
  calc
    M * Real.exp (-(Real.exp x * M) / 2) ≤
        Real.exp M * Real.exp (-(Real.exp x * M) / 2) :=
      mul_le_mul_of_nonneg_right hMexp (Real.exp_pos _).le
    _ = Real.exp (M - Real.exp x * M / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.exp x / 4) := by
      apply Real.exp_le_exp.mpr
      have hp := mul_nonneg (sub_nonneg.mpr hM)
        (show 0 ≤ Real.exp x / 2 - 1 by linarith only [ha4])
      nlinarith only [hp, ha4]
    _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith only [hax])

end GaloisForLFunctions.HTGeometry
