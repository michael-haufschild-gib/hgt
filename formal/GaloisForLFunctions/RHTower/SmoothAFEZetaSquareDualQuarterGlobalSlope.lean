import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualQuarterHeightDerivative

noncomputable section

open Complex Set

namespace RHTower

theorem positive_vertical_ne_neg_nat {sigma t : ℝ} (hsigma : 0 < sigma) :
    ∀ m : ℕ, ((sigma : ℂ) + (t : ℂ) * I) ≠ -(m : ℂ) := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- A linear envelope uniform over every positive eighth argument in the
negative-quarter chi slope. -/
theorem exists_norm_digamma_positive_eighth_strip_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (sigma t : ℝ),
      1 / 8 ≤ sigma → sigma ≤ 3 / 8 →
      ‖Complex.digamma ((sigma : ℂ) + (t : ℂ) * I)‖ ≤
        K * (1 + |t|) := by
  obtain ⟨C, hC, hsector⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_halfShift_le
  let K : ℝ := 4 * C + 8
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro sigma t hsigmaLow hsigmaHigh
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigmaLow
  let a : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have hrec := Complex.digamma_apply_add_one a
    (positive_vertical_ne_neg_nat hsigmaPos)
  have haone : a + 1 = ((sigma + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
    dsimp only [a]
    push_cast
    ring
  have hbase :
      ‖Complex.digamma (((sigma + 1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        4 * C * (1 + |t|) := by
    let z : ℂ := ((2 * (sigma + 1) - 1 : ℝ) : ℂ) +
      ((2 * t : ℝ) : ℂ) * I
    have hzmem : z ∈ GaloisForLFunctions.HTGeometry.digammaWatsonSector := by
      change -(‖z‖ / 2) ≤ z.re
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      have hzre : z.re = 2 * (sigma + 1) - 1 := by simp [z]
      rw [hzre]
      linarith
    have harg : (1 + z) / 2 =
        ((sigma + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      dsimp only [z]
      push_cast
      ring
    have hznorm : ‖z‖ ≤ (2 * (sigma + 1) - 1) + 2 * |t| := by
      have hre0 : 0 ≤ 2 * (sigma + 1) - 1 := by linarith
      have hreal : ‖(((2 * (sigma + 1) - 1 : ℝ) : ℂ))‖ =
          2 * (sigma + 1) - 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0]
      have himag : ‖(((2 * t : ℝ) : ℂ) * I)‖ = 2 * |t| := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_mul]
        norm_num
      calc
        ‖z‖ ≤ ‖(((2 * (sigma + 1) - 1 : ℝ) : ℂ))‖ +
            ‖(((2 * t : ℝ) : ℂ) * I)‖ := by
              dsimp only [z]
              exact norm_add_le _ _
        _ = (2 * (sigma + 1) - 1) + 2 * |t| := by rw [hreal, himag]
    have hlinear : 1 + ‖z‖ ≤ 4 * (1 + |t|) := by
      nlinarith [hznorm, abs_nonneg t]
    rw [← harg]
    refine (hsector z hzmem).trans ?_
    calc
      C * (1 + ‖z‖) ≤ C * (4 * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left hlinear hC
      _ = 4 * C * (1 + |t|) := by ring
  have hainv : ‖a⁻¹‖ ≤ 8 := by
    have hare : |a.re| = sigma := by
      dsimp only [a]
      simp [abs_of_pos hsigmaPos]
    have hnorm : (1 : ℝ) / 8 ≤ ‖a‖ := by
      calc
        (1 : ℝ) / 8 ≤ sigma := hsigmaLow
        _ = |a.re| := hare.symm
        _ ≤ ‖a‖ := Complex.abs_re_le_norm a
    rw [norm_inv]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 8) hnorm
    norm_num at hi ⊢
    exact hi
  have hsplit : Complex.digamma a = Complex.digamma (a + 1) - a⁻¹ := by
    rw [hrec]
    ring
  change ‖Complex.digamma a‖ ≤ K * (1 + |t|)
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [haone]
  dsimp only [K]
  calc
    ‖Complex.digamma (((sigma + 1 : ℝ) : ℂ) + (t : ℂ) * I)‖ + ‖a⁻¹‖
        ≤ 4 * C * (1 + |t|) + 8 := add_le_add hbase hainv
    _ ≤ (4 * C + 8) * (1 + |t|) := by
      nlinarith [mul_nonneg hC (by positivity : 0 ≤ 1 + |t|), abs_nonneg t]

/-- The negative-quarter chi logarithmic slope has a global polynomial
envelope. Central cancellation will later replace it by `O(1/tau)` where
`2|v| ≤ tau`; this theorem controls the Gaussian tail. -/
theorem exists_norm_logDeriv_zetaChi_quarter_shift_sub_line_le_global :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ tau v : ℝ,
      ‖logDeriv zetaChi
          (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤
      D * (1 + |tau|) * (1 + |v|) := by
  obtain ⟨K, hK, hfamily⟩ := exists_norm_digamma_positive_eighth_strip_le
  let D : ℝ := 2 * K
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro tau v
  let z : ℂ := linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have hzpos : 0 < z.re := by dsimp only [z]; simp [linePt]; norm_num
  have h1zpos : 0 < (1 - z).re := by
    dsimp only [z]
    simp [linePt]
    norm_num
  have hspos : 0 < (linePt tau).re := by rw [linePt_re]; norm_num
  have h1spos : 0 < (1 - linePt tau).re := by
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  rw [show linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I) = z by rfl,
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hzpos)
      (div_two_ne_neg_nat_of_re_pos h1zpos),
    logDeriv_zetaChi_off_poles
      (div_two_ne_neg_nat_of_re_pos hspos)
      (div_two_ne_neg_nat_of_re_pos h1spos)]
  let A : ℂ := Complex.digamma (z / 2)
  let B : ℂ := Complex.digamma (linePt tau / 2)
  let C : ℂ := Complex.digamma ((1 - z) / 2)
  let E : ℂ := Complex.digamma ((1 - linePt tau) / 2)
  have hAarg : z / 2 =
      ((3 / 8 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
    dsimp only [z]
    apply Complex.ext <;> simp [linePt] <;> ring
  have hBarg : linePt tau / 2 =
      ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [linePt] <;> ring
  have hCarg : (1 - z) / 2 =
      ((1 / 8 : ℝ) : ℂ) + (((-(tau - v)) / 2 : ℝ) : ℂ) * I := by
    dsimp only [z]
    apply Complex.ext <;> simp [linePt] <;> ring
  have hEarg : (1 - linePt tau) / 2 =
      ((1 / 4 : ℝ) : ℂ) + (((-tau) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [linePt] <;> ring
  have hA : ‖A‖ ≤ K * (1 + |(tau - v) / 2|) := by
    dsimp only [A]
    rw [hAarg]
    exact hfamily (3 / 8) ((tau - v) / 2) (by norm_num) (by norm_num)
  have hB : ‖B‖ ≤ K * (1 + |tau / 2|) := by
    dsimp only [B]
    rw [hBarg]
    exact hfamily (1 / 4) (tau / 2) (by norm_num) (by norm_num)
  have hC : ‖C‖ ≤ K * (1 + |(-(tau - v)) / 2|) := by
    dsimp only [C]
    rw [hCarg]
    exact hfamily (1 / 8) (-(tau - v) / 2) (by norm_num) (by norm_num)
  have hE : ‖E‖ ≤ K * (1 + |(-tau) / 2|) := by
    dsimp only [E]
    rw [hEarg]
    exact hfamily (1 / 4) ((-tau) / 2) (by norm_num) (by norm_num)
  have hheight :
      (1 + |(tau - v) / 2|) + (1 + |tau / 2|) ≤
        2 + |tau| + |v| := by
    have htv := abs_sub tau v
    rw [abs_div, abs_div]
    norm_num
    nlinarith [abs_nonneg v]
  have hheightNeg :
      (1 + |(-(tau - v)) / 2|) + (1 + |(-tau) / 2|) ≤
        2 + |tau| + |v| := by
    rw [show (-(tau - v)) / 2 = -((tau - v) / 2) by ring,
      abs_neg, show (-tau) / 2 = -(tau / 2) by ring, abs_neg]
    exact hheight
  have hAB : ‖A - B‖ ≤ K * (2 + |tau| + |v|) := by
    calc
      ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(tau - v) / 2|) + K * (1 + |tau / 2|) :=
        add_le_add hA hB
      _ = K * ((1 + |(tau - v) / 2|) + (1 + |tau / 2|)) := by ring
      _ ≤ K * (2 + |tau| + |v|) := mul_le_mul_of_nonneg_left hheight hK
  have hCE : ‖C - E‖ ≤ K * (2 + |tau| + |v|) := by
    calc
      ‖C - E‖ ≤ ‖C‖ + ‖E‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(-(tau - v)) / 2|) + K * (1 + |(-tau) / 2|) :=
        add_le_add hC hE
      _ = K * ((1 + |(-(tau - v)) / 2|) + (1 + |(-tau) / 2|)) := by ring
      _ ≤ K * (2 + |tau| + |v|) := mul_le_mul_of_nonneg_left hheightNeg hK
  have hprod : 2 + |tau| + |v| ≤
      2 * (1 + |tau|) * (1 + |v|) := by
    nlinarith [abs_nonneg tau, abs_nonneg v,
      mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
  calc
    ‖-(Complex.digamma (z / 2) / 2) -
          Complex.digamma ((1 - z) / 2) / 2 +
          (Real.log Real.pi : ℂ) -
        (-(Complex.digamma (linePt tau / 2) / 2) -
          Complex.digamma ((1 - linePt tau) / 2) / 2 +
          (Real.log Real.pi : ℂ))‖ =
        ‖-(A - B) / 2 - (C - E) / 2‖ := by
      congr 1
      dsimp only [A, B, C, E]
      ring
    ‖-(A - B) / 2 - (C - E) / 2‖
        ≤ ‖-(A - B) / 2‖ + ‖(C - E) / 2‖ := norm_sub_le _ _
    _ = ‖A - B‖ / 2 + ‖C - E‖ / 2 := by
      rw [norm_div, norm_neg, norm_div]
      norm_num
    _ ≤ (K * (2 + |tau| + |v|)) / 2 +
          (K * (2 + |tau| + |v|)) / 2 := by gcongr
    _ = K * (2 + |tau| + |v|) := by ring
    _ ≤ K * (2 * (1 + |tau|) * (1 + |v|)) :=
      mul_le_mul_of_nonneg_left hprod hK
    _ = D * (1 + |tau|) * (1 + |v|) := by dsimp only [D]; ring

end RHTower
