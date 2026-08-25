import GaloisForLFunctions.RHTower.ZetaChiLineSharp
import GaloisForLFunctions.RHTower.ArchLadderRegular
import GaloisForLFunctions.HTGeometry.DigammaPositiveStripLinearBound
import GaloisForLFunctions.HTGeometry.DigammaBounds
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative

/-!
# Global bounds for `χ` and `χ'` on a fixed deep negative line

The line `Re s = -7/2` is the fixed `χ`-line produced by moving the
reflected smooth-AFE contour to `Re w = -(4-d)`.  Fixing this line removes
all dependence of the archimedean constants on the displacement `d`.
-/

noncomputable section

open Complex Set

namespace RHTower

private theorem neg_seven_halves_half_ne_neg_nat (t : ℝ) (m : ℕ) :
    ((((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    Complex.neg_re, Complex.natCast_re] at hre
  norm_num at hre
  have hm : m ≤ 1 ∨ 2 ≤ m := by omega
  rcases hm with hm | hm
  · have hm' : (m : ℝ) ≤ 1 := by exact_mod_cast hm
    linarith
  · have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

private theorem one_sub_neg_seven_halves_half_ne_neg_nat (t : ℝ) (m : ℕ) :
    ((1 - (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) / 2) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.div_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  norm_num at hre
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem continuous_zetaChi_neg_seven_halves :
    Continuous (fun t : ℝ =>
      zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℂ := ((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m
    simpa only [z] using neg_seven_halves_half_ne_neg_nat t m
  have h1z : ∀ m : ℕ, (1 - z) / 2 ≠ -(m : ℂ) := by
    intro m
    simpa only [z] using one_sub_neg_seven_halves_half_ne_neg_nat t m
  have hpath : ContinuousAt
      (fun u : ℝ => (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by fun_prop
  have hpathOne : ContinuousAt
      (fun u : ℝ => 1 - (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by fun_prop
  have hnum : ContinuousAt
      (fun u : ℝ => Complex.Gammaℝ
        (1 - (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I))) t :=
    by
      have hc := ContinuousAt.comp
        (f := fun u : ℝ => 1 - (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
        (g := Complex.Gammaℝ)
        (analyticAt_Gammaℝ_off_poles h1z).continuousAt hpathOne
      simpa only [Function.comp_def] using hc
  have hden : ContinuousAt
      (fun u : ℝ => Complex.Gammaℝ
        (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t :=
    by
      have hc := ContinuousAt.comp
        (f := fun u : ℝ => (((-7 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
        (g := Complex.Gammaℝ)
        (analyticAt_Gammaℝ_off_poles hz).continuousAt hpath
      simpa only [Function.comp_def] using hc
  have hden0 : Complex.Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_off_poles hz
  unfold zetaChi
  exact hnum.div hden (by simpa only [z] using hden0)

/-- Sharp global polynomial envelope for `χ` on `Re s = -7/2`. -/
theorem exists_norm_zetaChi_neg_seven_halves_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ 4 := by
  obtain ⟨C₁, hC₁, hlarge⟩ :=
    exists_norm_zetaChi_line_le (show (-7 / 2 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
      continuous_zetaChi_neg_seven_halves.continuousOn
  let C : ℝ := C₁ + max B 0
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun t => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow : (1 : ℝ) ≤ (1 + |t|) ^ 4 := one_le_pow₀ hbase
  rcases le_total 2 |t| with ht | ht
  · have h := hlarge t ht
    norm_num [Real.rpow_natCast] at h
    have hp : |t| ^ 4 ≤ (1 + |t|) ^ 4 := by
      gcongr
      linarith
    calc
      ‖zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
          ≤ C₁ * |t| ^ 4 := by convert h using 1; norm_num
      _ ≤ C₁ * (1 + |t|) ^ 4 :=
        mul_le_mul_of_nonneg_left hp hC₁.le
      _ ≤ C * (1 + |t|) ^ 4 := by
        apply mul_le_mul_of_nonneg_right
        · dsimp only [C]
          exact le_add_of_nonneg_right (le_max_right B 0)
        · positivity
  · have htmem : t ∈ Set.Icc (-2 : ℝ) 2 := by
      rw [Set.mem_Icc, ← abs_le]
      exact ht
    calc
      ‖zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
          ≤ B := hB t htmem
      _ ≤ max B 0 := le_max_left _ _
      _ ≤ C := by dsimp only [C]; linarith [hC₁]
      _ = C * 1 := by ring
      _ ≤ C * (1 + |t|) ^ 4 :=
        mul_le_mul_of_nonneg_left hpow hC.le

/-- Global linear envelope for `χ'/χ` on `Re s = -7/2`. -/
theorem exists_norm_logDeriv_zetaChi_neg_seven_halves_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ,
      ‖logDeriv zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        D * (1 + |t|) := by
  obtain ⟨K, hK, hstrip⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_positive_strip_le
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) ≤ 9 / 4 by norm_num)
  let D : ℝ := K + 3 + |Real.log Real.pi|
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun t => ?_⟩
  let z : ℂ := ((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  let a : ℂ := z / 2
  let b : ℂ := (1 - z) / 2
  have haPole : ∀ m : ℕ, a ≠ -(m : ℂ) := by
    intro m
    simpa only [a, z] using neg_seven_halves_half_ne_neg_nat t m
  have hbPole : ∀ m : ℕ, b ≠ -(m : ℂ) := by
    intro m
    simpa only [b, z] using one_sub_neg_seven_halves_half_ne_neg_nat t m
  have haRe : a.re = -7 / 4 := by simp [a, z]; norm_num
  have haOneRe : (a + 1).re = -3 / 4 := by simp [a, z]; norm_num
  have haTwoArg : a + 2 =
      ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [a, z]
      ring
    · simp [a, z]
  have hbArg : b =
      ((9 / 4 : ℝ) : ℂ) + (((-t) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [b, z]
      ring
    · simp [b, z]
  have haNorm : (1 : ℝ) ≤ ‖a‖ := by
    calc
      (1 : ℝ) ≤ |a.re| := by rw [haRe]; norm_num
      _ ≤ ‖a‖ := Complex.abs_re_le_norm a
  have haInv : ‖a⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hi := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) haNorm
    norm_num at hi ⊢
    exact hi
  have haOneNorm : (3 / 4 : ℝ) ≤ ‖a + 1‖ := by
    calc
      (3 / 4 : ℝ) ≤ |(a + 1).re| := by rw [haOneRe]; norm_num
      _ ≤ ‖a + 1‖ := Complex.abs_re_le_norm (a + 1)
  have haOneInv : ‖(a + 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hi := one_div_le_one_div_of_le
      (show (0 : ℝ) < 3 / 4 by norm_num) haOneNorm
    simpa only [one_div] using
      hi.trans (show (1 / (3 / 4) : ℝ) ≤ 2 by norm_num)
  have htHalf : 1 + |t / 2| ≤ 1 + |t| := by
    rw [abs_div]
    norm_num
  have htNegHalf : 1 + |(-t) / 2| ≤ 1 + |t| := by
    simpa only [neg_div, abs_neg] using htHalf
  have haTwo := hstrip (1 / 4) (by norm_num) (by norm_num) (t / 2)
  have hb := hstrip (9 / 4) (by norm_num) (by norm_num) ((-t) / 2)
  have haTwo' : ‖Complex.digamma (a + 2)‖ ≤ K * (1 + |t|) := by
    rw [haTwoArg]
    exact haTwo.trans (mul_le_mul_of_nonneg_left htHalf hK)
  have hb' : ‖Complex.digamma b‖ ≤ K * (1 + |t|) := by
    rw [hbArg]
    exact hb.trans (mul_le_mul_of_nonneg_left htNegHalf hK)
  have hrec := digamma_apply_add_nat a haPole 2
  have haEq : Complex.digamma a =
      Complex.digamma (a + 2) - a⁻¹ - (a + 1)⁻¹ := by
    norm_num [Finset.sum_range_succ] at hrec
    calc
      Complex.digamma a =
          (Complex.digamma a + (a⁻¹ + (a + 1)⁻¹)) -
            (a⁻¹ + (a + 1)⁻¹) := by ring
      _ = Complex.digamma (a + 2) - (a⁻¹ + (a + 1)⁻¹) := by rw [← hrec]
      _ = Complex.digamma (a + 2) - a⁻¹ - (a + 1)⁻¹ := by ring
  have ha' : ‖Complex.digamma a‖ ≤ K * (1 + |t|) + 3 := by
    rw [haEq]
    calc
      ‖Complex.digamma (a + 2) - a⁻¹ - (a + 1)⁻¹‖
          ≤ ‖Complex.digamma (a + 2) - a⁻¹‖ + ‖(a + 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ (‖Complex.digamma (a + 2)‖ + ‖a⁻¹‖) + ‖(a + 1)⁻¹‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (K * (1 + |t|) + 1) + 2 :=
        add_le_add (add_le_add haTwo' haInv) haOneInv
      _ = K * (1 + |t|) + 3 := by ring
  rw [show (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = z by rfl,
    logDeriv_zetaChi_off_poles haPole hbPole]
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
              ‖(Real.log Real.pi : ℂ)‖ := by
                gcongr
                exact norm_sub_le _ _
          _ = _ := by
            rw [norm_div, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs]
            norm_num
    _ ≤ (K * (1 + |t|) + 3) / 2 +
          (K * (1 + |t|)) / 2 + |Real.log Real.pi| := by gcongr
    _ = K * (1 + |t|) + 3 / 2 + |Real.log Real.pi| := by ring
    _ ≤ (K + 3 + |Real.log Real.pi|) * (1 + |t|) := by
      nlinarith [mul_nonneg (show 0 ≤ 3 + |Real.log Real.pi| by positivity)
        (abs_nonneg t)]
    _ = D * (1 + |t|) := by rfl

/-- Global polynomial envelope for `χ'` on `Re s = -7/2`. -/
theorem exists_norm_deriv_zetaChi_neg_seven_halves_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖deriv zetaChi (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * (1 + |t|) ^ 5 := by
  obtain ⟨D, hD, hlog⟩ :=
    exists_norm_logDeriv_zetaChi_neg_seven_halves_le
  obtain ⟨K, hK, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_le
  let C : ℝ := D * K
  refine ⟨C, mul_nonneg hD hK.le, fun t => ?_⟩
  let z : ℂ := ((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m
    simpa only [z] using neg_seven_halves_half_ne_neg_nat t m
  have h1z : ∀ m : ℕ, (1 - z) / 2 ≠ -(m : ℂ) := by
    intro m
    simpa only [z] using one_sub_neg_seven_halves_half_ne_neg_nat t m
  have hchi0 : zetaChi z ≠ 0 := by
    unfold zetaChi
    exact div_ne_zero (Gammaℝ_ne_zero_off_poles h1z)
      (Gammaℝ_ne_zero_off_poles hz)
  have hderiv : deriv zetaChi z = logDeriv zetaChi z * zetaChi z := by
    rw [logDeriv_apply]
    exact (div_mul_cancel₀ _ hchi0).symm
  rw [show (((-7 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = z by rfl,
    hderiv, norm_mul]
  calc
    ‖logDeriv zetaChi z‖ * ‖zetaChi z‖
      ≤ (D * (1 + |t|)) * (K * (1 + |t|) ^ 4) := by
        apply mul_le_mul
        · simpa only [z] using hlog t
        · simpa only [z] using hchi t
        · exact norm_nonneg _
        · positivity
    _ = C * (1 + |t|) ^ 5 := by
      dsimp only [C]
      ring

end RHTower
