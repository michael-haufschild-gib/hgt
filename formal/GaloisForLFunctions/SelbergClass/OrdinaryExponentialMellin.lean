import GaloisForLFunctions.SelbergClass.OrdinaryExponentialSeries
import GaloisForLFunctions.SelbergClass.OrdinaryMellinContourBounds

/-!
# Mellin inversion of the ordinary exponential series

On the line at two, absolute Dirichlet convergence justifies interchanging the
coefficient sum and the Mellin integral. Each term is the inverse transform of Gamma.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private def ordinaryExponentialMellinTerm (F : ExtendedSelbergClass) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else F.coeff n * (n : ℂ) ^ (-(2 + (t : ℂ) * I)) *
    (x : ℂ) ^ (-(2 + (t : ℂ) * I)) * Complex.Gamma (2 + (t : ℂ) * I)

private theorem norm_ordinaryExponentialMellinTerm (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖ordinaryExponentialMellinTerm F x n t‖ =
      ‖LSeries.term F.coeff (2 : ℂ) n‖ *
        (x ^ (-2 : ℝ) * ‖Complex.Gamma (2 + (t : ℂ) * I)‖) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ordinaryExponentialMellinTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ordinaryExponentialMellinTerm, if_neg hn.ne', norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hn, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    LSeries.norm_term_eq, if_neg hn.ne']
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.ofNat_re]
  rw [Real.rpow_neg hnR.le]
  ring

private theorem integrable_ordinaryExponentialMellinTerm (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) (n : ℕ) : Integrable (ordinaryExponentialMellinTerm F x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have heq : ordinaryExponentialMellinTerm F x 0 = fun _ => 0 := by
      funext t; simp [ordinaryExponentialMellinTerm]
    rw [heq]
    exact integrable_zero _ _ _
  have hΓ : Continuous fun t : ℝ => Complex.Gamma (2 + (t : ℂ) * I) :=
    continuous_Gamma_line_of_pos (by norm_num : (0 : ℝ) < 2)
  have hcont : Continuous (ordinaryExponentialMellinTerm F x n) := by
    have heq : ordinaryExponentialMellinTerm F x n = fun t : ℝ =>
        F.coeff n * (n : ℂ) ^ (-(2 + (t : ℂ) * I)) *
          (x : ℂ) ^ (-(2 + (t : ℂ) * I)) * Complex.Gamma (2 + (t : ℂ) * I) := by
      funext t; rw [ordinaryExponentialMellinTerm, if_neg hn.ne']
    rw [heq]
    refine ((continuous_const.mul ?_).mul ?_).mul hΓ
    · exact continuous_const.cpow (by fun_prop) fun _ => Or.inl (by exact_mod_cast hn)
    · exact continuous_const.cpow (by fun_prop) fun _ => Or.inl (by simpa using hx)
  have hΓint := (gamma_verticalIntegrable_of_pos (c := 2) (by norm_num)).norm
  apply Integrable.mono' (hΓint.const_mul (‖LSeries.term F.coeff (2 : ℂ) n‖ * x ^ (-2 : ℝ)))
    hcont.aestronglyMeasurable
  filter_upwards with t
  rw [norm_ordinaryExponentialMellinTerm F hx]
  exact le_of_eq (by ring)

private theorem ordinaryExponentialTerm_eq_mellin (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ordinaryExponentialTerm F (x : ℂ) n =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, ordinaryExponentialMellinTerm F x n t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ordinaryExponentialTerm, ordinaryExponentialMellinTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv := complexMellinInvLine_Gamma_ofReal (c := 2) (by norm_num) (mul_pos hx hnR)
  rw [ordinaryExponentialTerm, show -(n : ℂ) * (x : ℂ) = -((x * n : ℝ) : ℂ) by
    push_cast; ring, ← hinv, complexMellinInvLine]
  calc F.coeff n * ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
      ((x * n : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) * Complex.Gamma (2 + (t : ℂ) * I))
      = (1 / (2 * Real.pi) : ℝ) • (F.coeff n * ∫ t : ℝ,
          ((x * n : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) * Complex.Gamma (2 + (t : ℂ) * I)) := by
          simp only [Complex.real_smul]
          ring
    _ = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        F.coeff n * (((x * n : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) *
          Complex.Gamma (2 + (t : ℂ) * I)) := by rw [integral_const_mul]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have hsplit := ofReal_mul_rpow_cpow_neg hx hn 1 (2 + (t : ℂ) * I)
      simp only [one_div_one, Real.rpow_one, Complex.ofReal_one, div_one] at hsplit
      rw [ordinaryExponentialMellinTerm, if_neg hn.ne', hsplit]
      ring

/-- The ordinary exponential series is the Mellin integral on the line at two. -/
theorem ordinaryExponentialSeries_eq_mellin (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) :
    ordinaryExponentialSeries F (x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I) := by
  have hint := integrable_ordinaryExponentialMellinTerm F hx
  have hsumint : Summable (fun n : ℕ => ∫ t : ℝ, ‖ordinaryExponentialMellinTerm F x n t‖) := by
    simp_rw [norm_ordinaryExponentialMellinTerm F hx, integral_const_mul]
    exact (F.lSeriesSummable (2 : ℂ) (by norm_num)).norm.mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hint hsumint
  rw [ordinaryExponentialSeries]
  simp_rw [ordinaryExponentialTerm_eq_mellin F hx]
  rw [tsum_const_smul'', hswap]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have hterm : ∀ n : ℕ, ordinaryExponentialMellinTerm F x n t =
      ((x : ℂ) ^ (-(2 + (t : ℂ) * I)) * Complex.Gamma (2 + (t : ℂ) * I)) *
        LSeries.term F.coeff (2 + (t : ℂ) * I) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ordinaryExponentialMellinTerm]
    rw [ordinaryExponentialMellinTerm, if_neg hn.ne', LSeries.term_of_ne_zero hn.ne',
      Complex.cpow_neg, div_eq_mul_inv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hval := F.lSeries_eq_value (2 + (t : ℂ) * I) (by norm_num)
  change _ * LSeries F.coeff (2 + (t : ℂ) * I) = _
  rw [hval, ordinaryMellinIntegrand, zero_add]
  ring

end GaloisForLFunctions.SelbergClass
