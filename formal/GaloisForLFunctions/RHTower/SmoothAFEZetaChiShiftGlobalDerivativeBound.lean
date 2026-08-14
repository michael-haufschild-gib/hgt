import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftVariationBound
import GaloisForLFunctions.HTGeometry.DigammaSectorBounds

/-!
# Global polynomial envelope for the zeta-AFE chi-shift derivative

The central conductor window has relative speed `O((1+|v|)/tau)`.  Differentiating the exact dual
weight also requires an integrable envelope outside that window.  Sector bounds for the digamma,
together with one recurrence at the quarter arguments, give a global polynomial envelope.  The
Gaussian Mellin kernel can absorb this envelope.
-/

noncomputable section

open Complex Set

namespace RHTower

theorem quarter_vertical_ne_neg_nat {sigma t : ℝ}
    (hsigma : sigma = -1 / 4 ∨ sigma = 1 / 4) :
    ∀ m : ℕ, ((sigma : ℂ) + (t : ℂ) * I) ≠ -(m : ℂ) := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  rcases hsigma with rfl | rfl
  · cases m with
    | zero => norm_num at hre
    | succ m =>
        have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        norm_num at hre
        linarith
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hre
    linarith

private theorem norm_inv_quarter_vertical_le_four {sigma t : ℝ}
    (hsigma : sigma = -1 / 4 ∨ sigma = 1 / 4) :
    ‖(((sigma : ℂ) + (t : ℂ) * I)⁻¹)‖ ≤ 4 := by
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * I
  have hzre : |z.re| = 1 / 4 := by
    dsimp only [z]
    rcases hsigma with rfl | rfl <;> norm_num
  have hnorm : (1 : ℝ) / 4 ≤ ‖z‖ := by
    rw [← hzre]
    exact Complex.abs_re_le_norm z
  rw [norm_inv]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hnorm
  norm_num at hi ⊢
  exact hi

/-- One linear envelope covers every quarter argument occurring in the exact chi logarithmic
derivative. -/
theorem exists_norm_digamma_quarter_family_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (sigma t : ℝ),
      (sigma = -1 / 4 ∨ sigma = 1 / 4 ∨ sigma = 3 / 4) →
      ‖Complex.digamma ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ K * (1 + |t|) := by
  obtain ⟨C, hC, hsector⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_halfShift_le
  let K : ℝ := 3 * C + 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro sigma t hsigma
  have hsectorBound : ∀ rho : ℝ, 1 / 2 ≤ rho → rho ≤ 5 / 4 →
      ‖Complex.digamma ((rho : ℂ) + (t : ℂ) * I)‖ ≤
        3 * C * (1 + |t|) := by
    intro rho hrho hrhole
    let z : ℂ := ((2 * rho - 1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I
    have hzmem : z ∈ GaloisForLFunctions.HTGeometry.digammaWatsonSector := by
      change -(‖z‖ / 2) ≤ z.re
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      have hzre : z.re = 2 * rho - 1 := by simp [z]
      rw [hzre]
      linarith
    have harg : (1 + z) / 2 = (rho : ℂ) + (t : ℂ) * I := by
      dsimp only [z]
      push_cast
      ring
    have hznorm : ‖z‖ ≤ (2 * rho - 1) + 2 * |t| := by
      have hre0 : 0 ≤ 2 * rho - 1 := by linarith
      have hreal : ‖(((2 * rho - 1 : ℝ) : ℂ))‖ = 2 * rho - 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0]
      have himag : ‖(((2 * t : ℝ) : ℂ) * I)‖ = 2 * |t| := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        norm_num
      calc
        ‖z‖ ≤ ‖(((2 * rho - 1 : ℝ) : ℂ))‖ +
            ‖(((2 * t : ℝ) : ℂ) * I)‖ := by
              dsimp only [z]
              exact norm_add_le _ _
        _ = (2 * rho - 1) + 2 * |t| := by rw [hreal, himag]
    have hlinear : 1 + ‖z‖ ≤ 3 * (1 + |t|) := by
      nlinarith [hznorm, abs_nonneg t]
    rw [← harg]
    refine (hsector z hzmem).trans ?_
    calc
      C * (1 + ‖z‖) ≤ C * (3 * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left hlinear hC
      _ = 3 * C * (1 + |t|) := by ring
  rcases hsigma with rfl | rfl | rfl
  · let a : ℂ := ((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I
    have hrec := Complex.digamma_apply_add_one a
      (quarter_vertical_ne_neg_nat (Or.inl rfl))
    have haone : a + 1 = ((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I := by
      dsimp only [a]
      push_cast
      ring
    have hinv := norm_inv_quarter_vertical_le_four (t := t) (Or.inl rfl)
    have hsplit : Complex.digamma a = Complex.digamma (a + 1) - a⁻¹ := by
      rw [hrec]
      ring
    change ‖Complex.digamma a‖ ≤ K * (1 + |t|)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    rw [haone]
    have hbase := hsectorBound (3 / 4) (by norm_num) (by norm_num)
    dsimp only [K]
    calc
      ‖Complex.digamma (((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ + ‖a⁻¹‖
          ≤ 3 * C * (1 + |t|) + 4 := add_le_add hbase hinv
      _ ≤ (3 * C + 4) * (1 + |t|) := by
        nlinarith [mul_nonneg hC (by positivity : 0 ≤ 1 + |t|), abs_nonneg t]
  · let a : ℂ := ((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I
    have hrec := Complex.digamma_apply_add_one a
      (quarter_vertical_ne_neg_nat (Or.inr rfl))
    have haone : a + 1 = ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I := by
      dsimp only [a]
      push_cast
      ring
    have hinv := norm_inv_quarter_vertical_le_four (t := t) (Or.inr rfl)
    have hsplit : Complex.digamma a = Complex.digamma (a + 1) - a⁻¹ := by
      rw [hrec]
      ring
    change ‖Complex.digamma a‖ ≤ K * (1 + |t|)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    rw [haone]
    have hbase := hsectorBound (5 / 4) (by norm_num) (by norm_num)
    dsimp only [K]
    calc
      ‖Complex.digamma (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ + ‖a⁻¹‖
          ≤ 3 * C * (1 + |t|) + 4 := add_le_add hbase hinv
      _ ≤ (3 * C + 4) * (1 + |t|) := by
        nlinarith [mul_nonneg hC (by positivity : 0 ≤ 1 + |t|), abs_nonneg t]
  · have hbase := hsectorBound (3 / 4) (by norm_num) (by norm_num)
    dsimp only [K]
    exact hbase.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- The exact chi logarithmic slope has a global polynomial envelope.  Unlike the central estimate,
this theorem makes no relation between `tau` and `v`; it is intended for Gaussian domination. -/
theorem exists_norm_logDeriv_zetaChi_shift_sub_line_le_global :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ tau v : ℝ,
      ‖logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤
      D * (1 + |tau|) * (1 + |v|) := by
  obtain ⟨K, hK, hfamily⟩ := exists_norm_digamma_quarter_family_le
  let D : ℝ := 2 * K
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro tau v
  rw [logDeriv_zetaChi_shift_sub_line_eq_digamma_increments]
  let A : ℂ := Complex.digamma
    ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2)
  let B : ℂ := Complex.digamma (linePt tau / 2)
  let C : ℂ := Complex.digamma
    ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2)
  let E : ℂ := Complex.digamma ((1 - linePt tau) / 2)
  have hAarg :
      (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
        ((-1 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [linePt]
    · norm_num [linePt]
  have hBarg : linePt tau / 2 =
      ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [linePt]
    · norm_num [linePt]
  have hCarg :
      (1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
        ((3 / 4 : ℝ) : ℂ) + (((-(tau - v)) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [linePt]
    · norm_num [linePt]
  have hEarg : (1 - linePt tau) / 2 =
      ((1 / 4 : ℝ) : ℂ) + (((-tau) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [linePt]
    · norm_num [linePt]
  have hA : ‖A‖ ≤ K * (1 + |(tau - v) / 2|) := by
    dsimp only [A]
    rw [hAarg]
    exact hfamily (-1 / 4) ((tau - v) / 2) (Or.inl rfl)
  have hB : ‖B‖ ≤ K * (1 + |tau / 2|) := by
    dsimp only [B]
    rw [hBarg]
    exact hfamily (1 / 4) (tau / 2) (Or.inr (Or.inl rfl))
  have hC : ‖C‖ ≤ K * (1 + |(-(tau - v)) / 2|) := by
    dsimp only [C]
    rw [hCarg]
    exact hfamily (3 / 4) (-(tau - v) / 2) (Or.inr (Or.inr rfl))
  have hE : ‖E‖ ≤ K * (1 + |(-tau) / 2|) := by
    dsimp only [E]
    rw [hEarg]
    exact hfamily (1 / 4) ((-tau) / 2) (Or.inr (Or.inl rfl))
  have hheight :
      (1 + |(tau - v) / 2|) + (1 + |tau / 2|) ≤
        2 + |tau| + |v| := by
    have htv := abs_sub tau v
    have htvhalf : |(tau - v) / 2| = |tau - v| / 2 := by
      rw [abs_div]
      norm_num
    have htauhalf : |tau / 2| = |tau| / 2 := by
      rw [abs_div]
      norm_num
    rw [htvhalf, htauhalf]
    calc
      1 + |tau - v| / 2 + (1 + |tau| / 2)
          = 2 + |tau - v| / 2 + |tau| / 2 := by ring
      _ ≤ 2 + (|tau| + |v|) / 2 + |tau| / 2 := by gcongr
      _ ≤ 2 + |tau| + |v| := by linarith [abs_nonneg v]
  have hheightNeg :
      (1 + |(-(tau - v)) / 2|) + (1 + |(-tau) / 2|) ≤
        2 + |tau| + |v| := by
    have hfirst : |(-(tau - v)) / 2| = |(tau - v) / 2| := by
      rw [show (-(tau - v)) / 2 = -((tau - v) / 2) by ring, abs_neg]
    have hsecond : |(-tau) / 2| = |tau / 2| := by
      rw [show (-tau) / 2 = -(tau / 2) by ring, abs_neg]
    rw [hfirst, hsecond]
    exact hheight
  have hAB : ‖A - B‖ ≤ K * (2 + |tau| + |v|) := by
    calc
      ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(tau - v) / 2|) + K * (1 + |tau / 2|) := add_le_add hA hB
      _ = K * ((1 + |(tau - v) / 2|) + (1 + |tau / 2|)) := by ring
      _ ≤ K * (2 + |tau| + |v|) := mul_le_mul_of_nonneg_left hheight hK
  have hCE : ‖C - E‖ ≤ K * (2 + |tau| + |v|) := by
    calc
      ‖C - E‖ ≤ ‖C‖ + ‖E‖ := norm_sub_le _ _
      _ ≤ K * (1 + |(-(tau - v)) / 2|) + K * (1 + |(-tau) / 2|) :=
        add_le_add hC hE
      _ = K * ((1 + |(-(tau - v)) / 2|) + (1 + |(-tau) / 2|)) := by ring
      _ ≤ K * (2 + |tau| + |v|) := mul_le_mul_of_nonneg_left hheightNeg hK
  have hprod : 2 + |tau| + |v| ≤ 2 * (1 + |tau|) * (1 + |v|) := by
    nlinarith [abs_nonneg tau, abs_nonneg v,
      mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
  change ‖-(A - B) / 2 - (C - E) / 2‖ ≤ _
  calc
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

/-- Global derivative envelope for the exact chi shift ratio.  Its quadratic polynomial in `v` is
integrable against the Gaussian AFE kernel. -/
theorem exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ tau v : ℝ,
      ‖deriv
          (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
            (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau‖ ≤
        D * (1 + |tau|) ^ 2 * (1 + |v|) ^ 2 := by
  obtain ⟨D, hD, hslope⟩ :=
    exists_norm_logDeriv_zetaChi_shift_sub_line_le_global
  refine ⟨D, hD, ?_⟩
  intro tau v
  rw [(hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line tau v).deriv]
  rw [norm_mul, norm_mul, norm_I, one_mul]
  have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
  calc
    ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
        ‖logDeriv zetaChi (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
          logDeriv zetaChi (linePt tau)‖
      ≤ ((1 + |tau|) * (1 + |v|)) *
          ‖logDeriv zetaChi (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
            logDeriv zetaChi (linePt tau)‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ ≤ ((1 + |tau|) * (1 + |v|)) *
          (D * (1 + |tau|) * (1 + |v|)) :=
        mul_le_mul_of_nonneg_left (hslope tau v) (by positivity)
    _ = D * (1 + |tau|) ^ 2 * (1 + |v|) ^ 2 := by ring

end RHTower
