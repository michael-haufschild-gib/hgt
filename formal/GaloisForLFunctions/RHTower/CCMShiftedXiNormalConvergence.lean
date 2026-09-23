import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation

/-!
# Normal convergence of the Xi-cancelled shifted-zeta carrier

The completed Xi factor supplies the nonflat source datum missing from a bare
moment or formal-asymptotic carrier.  After it cancels each shifted zeta pole,
the resulting rectangular family converges locally normally on `Re s > 1`.
-/

open Complex Filter Function

namespace RHTower

noncomputable section

/-- The coefficient-weighted Xi-cancelled summand. -/
def xiRectangularCancelledTerm (L : ℝ) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  xiRectangularRightCoefficient L q * xiShiftedZetaCancelledTerm q s

/-- The completed, pole-cancelled rectangular shifted-zeta carrier. -/
def xiRectangularCancelledSeries (L : ℝ) (s : ℂ) : ℂ :=
  ∑' q : XiRightZeroCopy, xiRectangularCancelledTerm L q s

lemma sqrt_le_two_mul_sqrt_rectangular {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≤ 4 * x) :
    Real.sqrt y ≤ 2 * Real.sqrt x := by
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hsx_sq : (Real.sqrt x) ^ (2 : ℕ) = x := Real.sq_sqrt hx
  have hsy_sq : (Real.sqrt y) ^ (2 : ℕ) = y := Real.sq_sqrt hy
  nlinarith

lemma inv_sq_mul_sqrt_rectangular {x : ℝ} (hx : 0 < x) :
    (1 / x ^ (2 : ℕ)) * Real.sqrt x = 1 / (x * Real.sqrt x) := by
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrt_sq : (Real.sqrt x) ^ (2 : ℕ) = x := Real.sq_sqrt hx.le
  field_simp
  nlinarith

/-- Only finitely many rectangular zero copies have spectral point of norm below a given bound. -/
private theorem eventually_cofinite_le_norm_xiSpectralPoint (S : ℝ) (hS : 0 < S) :
    ∀ᶠ q : XiRightZeroCopy in Filter.cofinite, S ≤ ‖xiSpectralPoint q.1‖ := by
  have hbase : Summable (fun q : XiRightZeroCopy =>
      1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) :=
    xiSpectralPoint_inv_sq_summable.subtype _
  have htend := hbase.tendsto_cofinite_zero
  have hlt : ∀ᶠ q : XiRightZeroCopy in Filter.cofinite,
      1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) < 1 / S ^ (2 : ℕ) :=
    htend.eventually_lt_const (by positivity)
  filter_upwards [hlt] with q hq
  have hqpos : 0 < ‖xiSpectralPoint q.1‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
  have hsq : S ^ (2 : ℕ) < ‖xiSpectralPoint q.1‖ ^ (2 : ℕ) :=
    lt_of_one_div_lt_one_div (pow_pos hqpos 2) hq
  exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)

/-- **Uniform tail estimate for one shifted rectangular zeta term.**  For `s` in a ball of radius
`R₀` and a zero copy whose spectral point satisfies `2(R₀+2) ≤ ‖γ‖`, the point `s` is not the shifted
pole and the coefficient times the shifted zeta value is at most `10 C₀ ‖γ‖^{-3/2}`.  The separation
puts `s - γ` at distance at least one from the zeta pole, and `‖s - γ‖ + 2 ≤ 4‖γ‖` turns the
square-root growth bound into `2√‖γ‖`. -/
private theorem norm_xiRectangularRightCoefficient_mul_riemannZeta_le
    (L : ℝ) {R0 : ℝ} {q : XiRightZeroCopy} {s : ℂ} (hsre : 1 < s.re)
    (hsNorm : ‖s‖ ≤ R0)
    (hqLarge : 2 * (R0 + 2) ≤ ‖xiSpectralPoint q.1‖) :
    s ≠ xiRightShiftedPole q ∧
      ‖xiRectangularRightCoefficient L q‖ *
          ‖riemannZeta (s - xiRightCenteredZero q)‖ ≤
        (10 * (1 + Real.exp (|L| / 2)) ^ (2 : ℕ)) *
          (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) := by
  have hR0nonneg : 0 ≤ R0 := (norm_nonneg s).trans hsNorm
  set C0 : ℝ := (1 + Real.exp (|L| / 2)) ^ (2 : ℕ) with hC0
  set w : ℂ := xiRightCenteredZero q with hw
  have hwNorm : ‖w‖ = ‖xiSpectralPoint q.1‖ := by
    simp [hw, xiRightCenteredZero]
  have hwLarge : 2 * (R0 + 2) ≤ ‖w‖ := by rw [hwNorm]; exact hqLarge
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr (xiRightCenteredZero_ne_zero q)
  have hshiftRe : 1 / 2 ≤ (s - w).re := by
    rw [Complex.sub_re]
    have hwre := abs_xiRightCenteredZero_re_lt_half q
    rw [hw]
    linarith [(abs_lt.mp hwre).1, (abs_lt.mp hwre).2]
  have hsOneNorm : ‖s - 1‖ ≤ R0 + 1 := by
    calc
      ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by norm_num
      _ ≤ R0 + 1 := by linarith
  have hsep : 1 ≤ ‖(s - w) - 1‖ := by
    have hrev : ‖w‖ - ‖s - 1‖ ≤ ‖w - (s - 1)‖ := norm_sub_norm_le _ _
    have hcoord : ‖w - (s - 1)‖ = ‖(s - w) - 1‖ := by
      rw [show w - (s - 1) = -((s - w) - 1) by ring, norm_neg]
    rw [hcoord] at hrev
    linarith
  have hnotPole : s ≠ xiRightShiftedPole q := by
    intro heq
    have hzero : (s - w) - 1 = 0 := by
      rw [heq, xiRightShiftedPole, hw]
      ring
    rw [hzero, norm_zero] at hsep
    norm_num at hsep
  refine ⟨hnotPole, ?_⟩
  have hzeta := norm_riemannZeta_le_sqrt_norm_add_two_half
    hshiftRe (by norm_num : (0 : ℝ) < 1) hsep
  have harg : ‖s - w‖ + 2 ≤ 4 * ‖w‖ := by
    have hsub : ‖s - w‖ ≤ ‖s‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have hsqrt : Real.sqrt (‖s - w‖ + 2) ≤ 2 * Real.sqrt ‖w‖ :=
    sqrt_le_two_mul_sqrt_rectangular (norm_nonneg w) (by positivity) harg
  have hzeta' : ‖riemannZeta (s - w)‖ ≤ 10 * Real.sqrt ‖w‖ := by
    calc
      ‖riemannZeta (s - w)‖ ≤
          (2 + 1 / (1 : ℝ) + 2) * Real.sqrt (‖s - w‖ + 2) := hzeta
      _ ≤ 5 * (2 * Real.sqrt ‖w‖) := by
        norm_num only [div_one, OfNat.ofNat]
        gcongr
      _ = 10 * Real.sqrt ‖w‖ := by ring
  have hcoeff := norm_xiRectangularRightCoefficient_le L q
  calc
    ‖xiRectangularRightCoefficient L q‖ * ‖riemannZeta (s - w)‖ ≤
        (C0 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) * (10 * Real.sqrt ‖w‖) := by
          gcongr
    _ = (10 * C0) *
        ((1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) * Real.sqrt ‖xiSpectralPoint q.1‖) := by
      rw [hwNorm]
      ring
    _ = (10 * C0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) := by
      rw [inv_sq_mul_sqrt_rectangular
        (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1))]

/-- The cancelled rectangular carrier converges locally normally on the
connected half-plane `Re s > 1`. -/
theorem summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne :
    SummableLocallyUniformlyOn
      (fun q : XiRightZeroCopy => xiRectangularCancelledTerm L q)
      {s : ℂ | 1 < s.re} := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (xi_differentiable.continuous.comp
      (continuous_id.sub continuous_const)).continuousOn
  let C0 : ℝ := (1 + Real.exp (|L| / 2)) ^ (2 : ℕ)
  let R0 : ℝ := max R 0
  let M0 : ℝ := max M 0
  have hthree : Summable (fun q : XiRightZeroCopy =>
      1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) :=
    xiSpectralPoint_inv_three_halves_summable.subtype _
  refine ⟨fun q : XiRightZeroCopy =>
      (10 * C0 * M0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)),
    hthree.mul_left (10 * C0 * M0), ?_⟩
  filter_upwards [eventually_cofinite_le_norm_xiSpectralPoint (2 * (R0 + 2))
    (by dsimp only [R0]; positivity)] with q hqLarge
  intro s hs
  have hsright : 1 < s.re := hKsub hs
  have hsNorm : ‖s‖ ≤ R0 := (hR s hs).trans (le_max_left _ _)
  have hxiNorm : ‖xi (s - 1 / 2)‖ ≤ M0 := (hM s hs).trans (le_max_left _ _)
  obtain ⟨hnotPole, hbound⟩ :=
    norm_xiRectangularRightCoefficient_mul_riemannZeta_le L hsright hsNorm hqLarge
  rw [xiRectangularCancelledTerm, xiShiftedZetaCancelledTerm,
    Function.update_of_ne hnotPole, norm_mul, norm_mul]
  calc
    ‖xiRectangularRightCoefficient L q‖ *
        (‖xi (s - 1 / 2)‖ * ‖riemannZeta (s - xiRightCenteredZero q)‖) =
      (‖xiRectangularRightCoefficient L q‖ *
        ‖riemannZeta (s - xiRightCenteredZero q)‖) * ‖xi (s - 1 / 2)‖ := by ring
    _ ≤ ((10 * C0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖))) * M0 :=
      mul_le_mul hbound hxiNorm (norm_nonneg _) (by dsimp only [C0]; positivity)
    _ = (10 * C0 * M0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) := by ring

/-- The locally normal cancelled carrier is holomorphic on `Re s > 1`. -/
theorem differentiableOn_xiRectangularCancelledSeries_rightOne (L : ℝ) :
    DifferentiableOn ℂ (xiRectangularCancelledSeries L) {s : ℂ | 1 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne
  intro q s hs
  exact (differentiable_xiShiftedZetaCancelledTerm q s).const_mul
    (xiRectangularRightCoefficient L q)

/-- Absolute summability of the raw shifted-zeta carrier at every point to
the right of a common transverse bound. -/
theorem xiRectangularShiftedZetaSeries_summable_of_re_gt_transverse
    (L : ℝ) {delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    Summable (fun q : XiRightZeroCopy =>
      xiRectangularRightCoefficient L q *
        riemannZeta (s - xiRightCenteredZero q)) := by
  let eps : ℝ := s.re - (1 + delta)
  have heps : 0 < eps := by dsimp only [eps]; linarith
  apply Summable.of_norm_bounded
    ((xiRectangularRightCoefficient_summable L).norm.mul_right (1 + 1 / eps))
  intro q
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply norm_riemannZeta_le heps
  rw [Complex.sub_re]
  have := hupper q
  dsimp only [eps]
  linarith

/-- Even before pole cancellation, the rectangular shifted-zeta terms are
locally normally summable as a family of values on `Re s > 1`.  The finitely
many possible poles on a compact set are irrelevant to convergence; they are
excluded separately when holomorphy is required. -/
theorem summableLocallyUniformlyOn_xiRectangularRawShiftedTerm_rightOne
    (L : ℝ) :
    SummableLocallyUniformlyOn
      (fun q : XiRightZeroCopy => fun s : ℂ =>
        xiRectangularRightCoefficient L q *
          riemannZeta (s - xiRightCenteredZero q))
      {s : ℂ | 1 < s.re} := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let C0 : ℝ := (1 + Real.exp (|L| / 2)) ^ (2 : ℕ)
  let R0 : ℝ := max R 0
  have hthree : Summable (fun q : XiRightZeroCopy =>
      1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) :=
    xiSpectralPoint_inv_three_halves_summable.subtype _
  refine ⟨fun q : XiRightZeroCopy =>
      (10 * C0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)),
    hthree.mul_left (10 * C0), ?_⟩
  filter_upwards [eventually_cofinite_le_norm_xiSpectralPoint (2 * (R0 + 2))
    (by dsimp only [R0]; positivity)] with q hqLarge
  intro s hs
  have hsright : 1 < s.re := hKsub hs
  have hsNorm : ‖s‖ ≤ R0 := (hR s hs).trans (le_max_left _ _)
  rw [norm_mul]
  exact (norm_xiRectangularRightCoefficient_mul_riemannZeta_le L hsright hsNorm hqLarge).2

/-- On the common right half-plane, the locally normal cancelled carrier is
exactly the completed Xi factor times the raw shifted-zeta carrier. -/
theorem xiRectangularCancelledSeries_eq_xi_mul_shiftedZeta
    (L : ℝ) {delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    xiRectangularCancelledSeries L s =
      xi (s - 1 / 2) * xiRectangularShiftedZetaSeries L s := by
  have hsum := xiRectangularShiftedZetaSeries_summable_of_re_gt_transverse
    L hupper hs
  rw [xiRectangularCancelledSeries, xiRectangularShiftedZetaSeries,
    ← tsum_mul_left]
  apply tsum_congr
  intro q
  have hne : s ≠ xiRightShiftedPole q := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [xiRightShiftedPole, Complex.add_re] at hre
    have := hupper q
    simp only [Complex.one_re] at hre
    linarith
  rw [xiRectangularCancelledTerm, xiShiftedZetaCancelledTerm,
    Function.update_of_ne hne]
  ring

end

end RHTower
