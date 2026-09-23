import GaloisForLFunctions.RHTower.ZetaChiVerticalGrowth
import GaloisForLFunctions.HTGeometry.DigammaPositiveStripLinearBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative

/-!
# Logarithmic derivative on the reflected AFE left edge

For `-3/4 ≤ sigma ≤ -1/2`, one digamma argument of `chi'/chi` is shifted
once by recurrence into a fixed positive strip.  The reciprocal correction is
uniform because the original argument stays a fixed distance from zero.
-/

noncomputable section

open Complex

namespace RHTower

/-- Uniform linear envelope for `chi'/chi` throughout the reflected AFE edge
strip. -/
theorem exists_norm_logDeriv_zetaChi_left_edge_strip_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ sigma : ℝ, -3 / 4 ≤ sigma → sigma ≤ -1 / 2 →
      ∀ t : ℝ,
        ‖logDeriv zetaChi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
          D * (1 + |t|) := by
  obtain ⟨K, hK, hstrip⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_positive_strip_le
      (show (0 : ℝ) < 5 / 8 by norm_num)
      (show (5 / 8 : ℝ) ≤ 7 / 8 by norm_num)
  let D : ℝ := K + 2 + |Real.log Real.pi|
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun sigma hsigmaLow hsigmaHigh t => ?_⟩
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * I
  let a : ℂ := z / 2
  let b : ℂ := (1 - z) / 2
  have hzre : z.re = sigma := by simp [z]
  have h1zre : (1 - z).re = 1 - sigma := by simp [z]
  have haRe : a.re = sigma / 2 := by simp [a, z]
  have hbRe : b.re = (1 - sigma) / 2 := by simp [b, z]
  have ha1arg : a + 1 =
      ((sigma / 2 + 1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [a, z]
    · simp [a, z]
  have hbarg : b =
      (((1 - sigma) / 2 : ℝ) : ℂ) + (((-t) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [b, z]
    · simp [b, z]
  have haPole : ∀ m : ℕ, a ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    rw [haRe] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases m with _ | m
    · norm_num at hre
      linarith
    · have hm1 : (1 : ℕ) ≤ Nat.succ m :=
        Nat.succ_le_succ (Nat.zero_le m)
      norm_num at hre
      exact (not_lt_of_ge hsigmaLow) (by
        have hm1R : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by exact_mod_cast hm1
        linarith)
  have ha0 : a ≠ 0 := by
    intro haZero
    have hre := congrArg Complex.re haZero
    rw [haRe] at hre
    simp at hre
    linarith
  have haNorm : (1 / 4 : ℝ) ≤ ‖a‖ := by
    calc
      (1 / 4 : ℝ) ≤ |a.re| := by
        rw [haRe, abs_of_nonpos (by linarith)]
        linarith
      _ ≤ ‖a‖ := Complex.abs_re_le_norm a
  have haInv : ‖a⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) haNorm
    norm_num at hi ⊢
    exact hi
  have ha1 := hstrip (sigma / 2 + 1) (by linarith) (by linarith) (t / 2)
  have hbBound := hstrip ((1 - sigma) / 2) (by linarith) (by linarith) ((-t) / 2)
  have htHalf : 1 + |t / 2| ≤ 1 + |t| := by
    rw [abs_div]
    norm_num
  have htNegHalf : 1 + |(-t) / 2| ≤ 1 + |t| := by
    simpa only [neg_div, abs_neg] using htHalf
  have ha1' : ‖Complex.digamma (a + 1)‖ ≤ K * (1 + |t|) := by
    rw [ha1arg]
    exact ha1.trans (mul_le_mul_of_nonneg_left htHalf hK)
  have hb' : ‖Complex.digamma b‖ ≤ K * (1 + |t|) := by
    rw [hbarg]
    exact hbBound.trans (mul_le_mul_of_nonneg_left htNegHalf hK)
  have hrec := Complex.digamma_apply_add_one a haPole
  have haPsi : ‖Complex.digamma a‖ ≤ K * (1 + |t|) + 4 := by
    have heq : Complex.digamma a = Complex.digamma (a + 1) - a⁻¹ := by
      rw [hrec]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add ha1' haInv)
  have h1z0 : 0 < (1 - z).re := by rw [h1zre]; linarith
  rw [show ((sigma : ℂ) + (t : ℂ) * I) = z by rfl,
    logDeriv_zetaChi_off_poles
      haPole
      (div_two_ne_neg_nat_of_re_pos h1z0)]
  change ‖-(Complex.digamma a / 2) - Complex.digamma b / 2 +
      (Real.log Real.pi : ℂ)‖ ≤ _
  have hq : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc
    ‖-(Complex.digamma a / 2) - Complex.digamma b / 2 +
        (Real.log Real.pi : ℂ)‖
      ≤ ‖Complex.digamma a‖ / 2 + ‖Complex.digamma b‖ / 2 +
          |Real.log Real.pi| := by
        calc
          _ ≤ ‖-(Complex.digamma a / 2) - Complex.digamma b / 2‖ +
              ‖(Real.log Real.pi : ℂ)‖ := norm_add_le _ _
          _ ≤ (‖-(Complex.digamma a / 2)‖ +
                ‖Complex.digamma b / 2‖) +
              ‖(Real.log Real.pi : ℂ)‖ := by gcongr; exact norm_sub_le _ _
          _ = _ := by
            rw [norm_div, norm_neg, norm_div, Complex.norm_real,
              Real.norm_eq_abs]
            norm_num
    _ ≤ (K * (1 + |t|) + 4) / 2 +
          (K * (1 + |t|)) / 2 + |Real.log Real.pi| := by gcongr
    _ = K * (1 + |t|) + 2 + |Real.log Real.pi| := by ring
    _ ≤ (K + 2 + |Real.log Real.pi|) * (1 + |t|) := by
      nlinarith [mul_nonneg (show 0 ≤ 2 + |Real.log Real.pi| by positivity)
        (abs_nonneg t)]
    _ = D * (1 + |t|) := by rfl

/-- Cubic polynomial envelope for the derivative of `chi` on each fixed
vertical line of the reflected edge strip. -/
theorem exists_norm_deriv_zetaChi_vertical_left_edge_le
    {sigma : ℝ} (hsigmaLow : -3 / 4 ≤ sigma)
    (hsigmaHigh : sigma ≤ -1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv zetaChi ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ (3 : ℕ) := by
  obtain ⟨D, hD, hlogDeriv⟩ :=
    exists_norm_logDeriv_zetaChi_left_edge_strip_le
  obtain ⟨K, hK, hchi⟩ := exists_bound_norm_zetaChi_vertical
    (show sigma ≠ 0 by linarith) (by linarith) (by linarith)
  let C : ℝ := D * K
  refine ⟨C, mul_nonneg hD hK, fun t => ?_⟩
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have hGamma : Gammaℝ z ≠ 0 := by
    dsimp only [z]
    exact Gammaℝ_vertical_ne_zero (by linarith) (by linarith)
  have hGammaOne : Gammaℝ (1 - z) ≠ 0 := by
    dsimp only [z]
    exact Gammaℝ_one_sub_vertical_ne_zero (by linarith)
  have hchi0 : zetaChi z ≠ 0 := by
    unfold zetaChi
    exact div_ne_zero hGammaOne hGamma
  have hderiv : deriv zetaChi z = logDeriv zetaChi z * zetaChi z := by
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hchi0).symm
  have hq : 0 ≤ 1 + |t| := by positivity
  rw [show ((sigma : ℂ) + (t : ℂ) * I) = z by rfl, hderiv, norm_mul]
  calc
    ‖logDeriv zetaChi z‖ * ‖zetaChi z‖
      ≤ (D * (1 + |t|)) * (K * (1 + |t|) ^ (2 : ℕ)) := by
        apply mul_le_mul
        · simpa only [z] using hlogDeriv sigma hsigmaLow hsigmaHigh t
        · simpa only [z] using hchi t
        · exact norm_nonneg _
        · positivity
    _ = C * (1 + |t|) ^ (3 : ℕ) := by
      dsimp only [C]
      ring

end RHTower
