import GaloisForLFunctions.RHTower.XiWardFiveShiftWeilKreinLanding

/-!
# A legal windowed five-shift Weil--Krein charge

Raw prime exponential tests detect horizontal displacement through their Hermitian reflection
difference, but are not square-summable on the Xi divisor.  Multiplying every one of the five
modes by the same rectangular two-edge window repairs summability without losing prime labels or
multiplicity.

The window produces one extra term, `4 * Im(H)^2`, in every reflection-difference square.  The
five-shift coefficient sum annihilates that term exactly.  Hence the windowed negative Krein
combination is the old strictly off-line separator multiplied by the window norm square.  At
half aperture a positive-width window never vanishes off the critical line, so the resulting
global charge is nonnegative, absolutely summable, and zero exactly when RH holds.

The corresponding holomorphic Weil-pair combination is also absolutely summable, but is
identically zero: every prime mode collapses to the same squared window and the same coefficient
sum annihilates it.  Thus regularization does not solve the source problem.  It isolates the exact
remaining producer as a Hermitian/source identification; that identification is itself equivalent
to RH.

No RH premise, numerical computation, or new axiom is used.
-/

open Complex

namespace RHTower

noncomputable section

private theorem rectangularTwoEdgeTransform_half_ne_zero_of_re_pos
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hwre : 0 < w.re) :
    rectangularTwoEdgeTransform L (L / 2) w ≠ 0 := by
  have hw : w ≠ 0 := by
    intro h
    subst w
    norm_num at hwre
  rw [rectangularTwoEdgeTransform_eq hw]
  apply mul_ne_zero (rectangularWindowAmplitude_ne_zero hL hwre)
  have heq :
      Complex.exp (((L / 2 : ℝ) : ℂ) * w) +
          Complex.exp (-((((L / 2 : ℝ) : ℂ) - (L : ℂ))) * w) =
        2 * Complex.exp (((L / 2 : ℝ) : ℂ) * w) := by
    rw [show -((((L / 2 : ℝ) : ℂ) - (L : ℂ))) * w =
        (((L / 2 : ℝ) : ℂ) * w) by push_cast; ring]
    ring
  rw [heq]
  exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

private theorem rectangularTwoEdgeTransform_half_ne_zero
    {L : ℝ} (hL : 0 < L) {w : ℂ} (hwre : w.re ≠ 0) :
    rectangularTwoEdgeTransform L (L / 2) w ≠ 0 := by
  rcases lt_or_gt_of_ne hwre with hneg | hpos
  · intro hzero
    have hnre : 0 < (-w).re := by simpa using neg_pos.mpr hneg
    exact rectangularTwoEdgeTransform_half_ne_zero_of_re_pos hL hnre
      ((rectangularTwoEdgeTransform_even L (L / 2) w).trans hzero)
  · exact rectangularTwoEdgeTransform_half_ne_zero_of_re_pos hL hpos

/-- At half aperture, one positive rectangular window retains every off-line Xi copy. -/
theorem xiRectangularTwoEdgeTransform_half_ne_zero_of_offline
    {L : ℝ} (hL : 0 < L) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiRectangularTwoEdgeTransform L (L / 2) (xiSpectralPoint q) ≠ 0 := by
  apply rectangularTwoEdgeTransform_half_ne_zero hL
  rw [I_mul_xiSpectralPoint]
  simp only [Complex.sub_re]
  norm_num
  exact sub_ne_zero.mpr hoff

/-- Product of a square-summable rectangular window and one labeled prime exponential mode. -/
def xiWindowedPrimeTest (L a p : ℝ) (z : ℂ) : ℂ :=
  xiRectangularTwoEdgeTransform L a z * xiWeilPrimeTest p z

/-- Windowing makes every fixed prime mode square-summable on the multiplicity-exact Xi divisor. -/
theorem xiWindowedPrimeTest_squareSummable
    (L a : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    XiWeilSquareSummable (xiWindowedPrimeTest L a p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hH := xiRectangularTwoEdgeTransform_squareSummable L a
  rw [XiWeilSquareSummable] at hH ⊢
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    (hH.mul_left ((p ^ (1 / 2 : ℝ)) ^ 2))
  have hprime : ‖xiWeilPrimeTest p (xiSpectralPoint q)‖ ≤ p ^ (1 / 2 : ℝ) := by
    rw [xiWeilPrimeTest_spectralPoint hp0, norm_burnolPrimeCharacter hp0]
    apply Real.rpow_le_rpow_of_exponent_le hp
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  rw [xiWindowedPrimeTest, norm_mul, mul_pow]
  have hsquare : ‖xiWeilPrimeTest p (xiSpectralPoint q)‖ ^ 2 ≤
      (p ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hprime 2
  nlinarith [sq_nonneg (‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)‖)]

private theorem norm_sq_windowed_pair_sub
    (h x y : ℂ) (hxy : x * (starRingEnd ℂ) y = 1) :
    ‖h * x - (starRingEnd ℂ) h * y‖ ^ 2 =
      ‖h‖ ^ 2 * ‖x - y‖ ^ 2 + 4 * h.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_sub, Complex.normSq_sub]
  rw [Complex.normSq_mul, Complex.normSq_mul]
  have hnormConj : Complex.normSq ((starRingEnd ℂ) h) = Complex.normSq h := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.conj_re, Complex.conj_im]
    ring
  have hxyre : (x * (starRingEnd ℂ) y).re = 1 := by rw [hxy]; norm_num
  have hcross :
      ((h * x) * (starRingEnd ℂ) ((starRingEnd ℂ) h * y)).re =
        (h * h).re := by
    rw [map_mul, Complex.conj_conj]
    rw [show (h * x) * (h * (starRingEnd ℂ) y) =
        (h * h) * (x * (starRingEnd ℂ) y) by ring, hxy, mul_one]
  rw [hnormConj, hcross, hxyre]
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re]
  ring

private theorem xiWeilPrimeTest_mul_conj_lineConj
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    xiWeilPrimeTest p (xiSpectralPoint q) *
        (starRingEnd ℂ)
          (xiWeilPrimeTest p (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) = 1 := by
  rw [xiWeilPrimeTest_spectralPoint hp, xiWeilPrimeTest_spectralPoint hp,
    GaloisForLFunctions.RHTower.xiZeroCopyLineConj_support]
  rw [conj_burnolPrimeCharacter_one_sub_conj hp]
  exact burnolPrimeCharacter_mul_one_sub hp _

/-- Windowing adds the same phase correction to every prime-mode reflection difference. -/
theorem norm_sq_xiWindowedPrimeTest_pairDif
    (L a : ℝ) {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    ‖xiWeilPairDif (xiWindowedPrimeTest L a p) q‖ ^ 2 =
      ‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)‖ ^ 2 *
          ‖xiWeilPairDif (xiWeilPrimeTest p) q‖ ^ 2 +
        4 * (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q)).im ^ 2 := by
  rw [xiWeilPairDif, xiWeilPairDif, xiWindowedPrimeTest, xiWindowedPrimeTest,
    xiRectangularTwoEdgeTransform_lineConj]
  exact norm_sq_windowed_pair_sub _ _ _
    (xiWeilPrimeTest_mul_conj_lineConj hp q)

/-- The holomorphic Weil pair remains prime-blind after windowing: it sees only window square. -/
theorem xiWeilPairTerm_xiWindowedPrimeTest
    (L a : ℝ) {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    xiWeilPairTerm (xiWindowedPrimeTest L a p) q =
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
  rw [xiWeilPairTerm, xiWindowedPrimeTest, xiWeilSharp]
  change (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) *
      xiWeilPrimeTest p (xiSpectralPoint q)) *
    (starRingEnd ℂ)
      (xiRectangularTwoEdgeTransform L a ((starRingEnd ℂ) (xiSpectralPoint q)) *
        xiWeilPrimeTest p ((starRingEnd ℂ) (xiSpectralPoint q))) = _
  rw [← xiSpectralPoint_lineConj]
  rw [map_mul, xiRectangularTwoEdgeTransform_lineConj, Complex.conj_conj]
  rw [show
      (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) *
          xiWeilPrimeTest p (xiSpectralPoint q)) *
        (xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) *
          (starRingEnd ℂ)
            (xiWeilPrimeTest p
              (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))) =
        xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 *
          (xiWeilPrimeTest p (xiSpectralPoint q) *
            (starRingEnd ℂ)
              (xiWeilPrimeTest p
                (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))) by ring,
    xiWeilPrimeTest_mul_conj_lineConj hp, mul_one]

/-- Five-shift negative Krein combination built from legal windowed prime tests. -/
def fiveShiftEulerGammaWindowedKreinDefectCombination
    (L a r : ℝ) (q0 : XiZeroCopy) : ℝ :=
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  t * q * u * ‖xiWeilPairDif (xiWindowedPrimeTest L a (Real.exp r)) q0‖ ^ 2 -
    (t * q + t * u + q * u + t * q * u) *
      ‖xiWeilPairDif (xiWindowedPrimeTest L a (Real.exp (2 * r))) q0‖ ^ 2 +
    (t + q + u + t * q + t * u + q * u) *
      ‖xiWeilPairDif (xiWindowedPrimeTest L a (Real.exp (3 * r))) q0‖ ^ 2 -
    (1 + t + q + u) *
      ‖xiWeilPairDif (xiWindowedPrimeTest L a (Real.exp (4 * r))) q0‖ ^ 2 +
    ‖xiWeilPairDif (xiWindowedPrimeTest L a (Real.exp (5 * r))) q0‖ ^ 2

/-- Coefficient-faithful holomorphic counterpart of the windowed Krein combination. -/
def fiveShiftEulerGammaWindowedWeilPairCombination
    (L a r : ℝ) (q0 : XiZeroCopy) : ℂ :=
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  t * q * u * xiWeilPairTerm (xiWindowedPrimeTest L a (Real.exp r)) q0 -
    (t * q + t * u + q * u + t * q * u) *
      xiWeilPairTerm (xiWindowedPrimeTest L a (Real.exp (2 * r))) q0 +
    (t + q + u + t * q + t * u + q * u) *
      xiWeilPairTerm (xiWindowedPrimeTest L a (Real.exp (3 * r))) q0 -
    (1 + t + q + u) *
      xiWeilPairTerm (xiWindowedPrimeTest L a (Real.exp (4 * r))) q0 +
    xiWeilPairTerm (xiWindowedPrimeTest L a (Real.exp (5 * r))) q0

/-- Exact source blindness: every pointwise windowed five-shift holomorphic combination is zero. -/
theorem fiveShiftEulerGammaWindowedWeilPairCombination_eq_zero
    (L a r : ℝ) (q0 : XiZeroCopy) :
    fiveShiftEulerGammaWindowedWeilPairCombination L a r q0 = 0 := by
  rw [fiveShiftEulerGammaWindowedWeilPairCombination,
    xiWeilPairTerm_xiWindowedPrimeTest L a (Real.exp_pos r),
    xiWeilPairTerm_xiWindowedPrimeTest L a (Real.exp_pos (2 * r)),
    xiWeilPairTerm_xiWindowedPrimeTest L a (Real.exp_pos (3 * r)),
    xiWeilPairTerm_xiWindowedPrimeTest L a (Real.exp_pos (4 * r)),
    xiWeilPairTerm_xiWindowedPrimeTest L a (Real.exp_pos (5 * r))]
  push_cast
  ring

/-- The identically-zero holomorphic source combination is nevertheless a legal absolute sum. -/
theorem fiveShiftEulerGammaWindowedWeilPairCombination_summable
    (L a : ℝ) {r : ℝ} (hr : 0 < r) :
    Summable (fiveShiftEulerGammaWindowedWeilPairCombination L a r) := by
  have hsq (k : ℕ) (hk : 1 ≤ k) :
      XiWeilSquareSummable
        (xiWindowedPrimeTest L a (Real.exp (k * r))) := by
    apply xiWindowedPrimeTest_squareSummable
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg (by positivity) hr.le
  have h1 := xiWeilPairTerm_summable (hsq 1 (by norm_num))
  have h2 := xiWeilPairTerm_summable (hsq 2 (by norm_num))
  have h3 := xiWeilPairTerm_summable (hsq 3 (by norm_num))
  have h4 := xiWeilPairTerm_summable (hsq 4 (by norm_num))
  have h5 := xiWeilPairTerm_summable (hsq 5 (by norm_num))
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  have hsum := ((((h1.mul_left ((t * q * u : ℝ) : ℂ)).sub
      (h2.mul_left (((t * q + t * u + q * u + t * q * u : ℝ)) : ℂ))).add
      (h3.mul_left (((t + q + u + t * q + t * u + q * u : ℝ)) : ℂ))).sub
      (h4.mul_left (((1 + t + q + u : ℝ)) : ℂ))).add h5
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at hsum
  exact hsum.congr fun b => by
    simp only [fiveShiftEulerGammaWindowedWeilPairCombination, q, t, u]
    push_cast
    ring

/-- Global absolutely summable holomorphic source selected by the five coefficients. -/
def fiveShiftEulerGammaWindowedGlobalWeilSource (L a r : ℝ) : ℂ :=
  ∑' q0 : XiZeroCopy,
    fiveShiftEulerGammaWindowedWeilPairCombination L a r q0

/-- The legal global holomorphic source is identically zero for every window and scale. -/
theorem fiveShiftEulerGammaWindowedGlobalWeilSource_eq_zero
    (L a r : ℝ) :
    fiveShiftEulerGammaWindowedGlobalWeilSource L a r = 0 := by
  rw [fiveShiftEulerGammaWindowedGlobalWeilSource]
  calc
    (∑' q0 : XiZeroCopy,
        fiveShiftEulerGammaWindowedWeilPairCombination L a r q0) =
        ∑' _q0 : XiZeroCopy, 0 :=
      tsum_congr (fiveShiftEulerGammaWindowedWeilPairCombination_eq_zero L a r)
    _ = 0 := tsum_zero

/-- Five-shift cancellation removes the common window phase correction exactly. -/
theorem fiveShiftEulerGammaWindowedKreinDefectCombination_eq
    (L a r : ℝ) (q0 : XiZeroCopy) :
    fiveShiftEulerGammaWindowedKreinDefectCombination L a r q0 =
      ‖xiRectangularTwoEdgeTransform L a (xiSpectralPoint q0)‖ ^ 2 *
        fiveShiftEulerGammaKreinDefectCombination r q0 := by
  have h1 := norm_sq_xiWindowedPrimeTest_pairDif (L := L) (a := a)
    (p := Real.exp r) (Real.exp_pos r) q0
  have h2 := norm_sq_xiWindowedPrimeTest_pairDif (L := L) (a := a)
    (p := Real.exp (2 * r)) (Real.exp_pos (2 * r)) q0
  have h3 := norm_sq_xiWindowedPrimeTest_pairDif (L := L) (a := a)
    (p := Real.exp (3 * r)) (Real.exp_pos (3 * r)) q0
  have h4 := norm_sq_xiWindowedPrimeTest_pairDif (L := L) (a := a)
    (p := Real.exp (4 * r)) (Real.exp_pos (4 * r)) q0
  have h5 := norm_sq_xiWindowedPrimeTest_pairDif (L := L) (a := a)
    (p := Real.exp (5 * r)) (Real.exp_pos (5 * r)) q0
  rw [fiveShiftEulerGammaWindowedKreinDefectCombination,
    fiveShiftEulerGammaKreinDefectCombination, h1, h2, h3, h4, h5]
  ring

/-- Strict positivity of the paired five-shift feature on the right half of the critical strip. -/
theorem fiveShiftEulerGammaPairedFeature_pos
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    0 < fiveShiftEulerGammaPairedFeature r a := by
  have h1 : 0 < 1 - Real.exp (-2 * a * r) := by
    rw [sub_pos, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have h2 : 0 < Real.exp (-2 * a * r) - Real.exp (-2 * r) := by
    rw [sub_pos]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have h3 :
      0 < Real.exp (-2 * a * r) - Real.exp (-(21 / 10 : ℝ) * r) := by
    rw [sub_pos]
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact lt_of_lt_of_le (mul_pos (mul_pos (sq_pos_of_pos h1) h2) h3)
    (fiveShiftEulerGammaPairedFeature_lower hr ha0 ha)

theorem fiveShiftEulerGammaPairedFeature_neg (r a : ℝ) :
    fiveShiftEulerGammaPairedFeature r (-a) =
      fiveShiftEulerGammaPairedFeature r a := by
  rw [fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaPairedFeature]
  ring_nf

/-- Strict positivity of the paired feature at either off-line orientation. -/
theorem fiveShiftEulerGammaPairedFeature_pos_of_ne_zero
    {r a : ℝ} (hr : 0 < r) (ha0 : a ≠ 0) (ha : |a| ≤ 1 / 2) :
    0 < fiveShiftEulerGammaPairedFeature r a := by
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  · rw [← fiveShiftEulerGammaPairedFeature_neg r a]
    apply fiveShiftEulerGammaPairedFeature_pos hr (neg_pos.mpr hneg)
    simpa [abs_of_neg hneg] using ha
  · exact fiveShiftEulerGammaPairedFeature_pos hr hpos
      (by simpa [abs_of_pos hpos] using ha)

/-- Every off-line multiplicity copy contributes strictly positive legal windowed charge. -/
theorem fiveShiftEulerGammaWindowedKreinDefectCombination_pos_of_offline
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (q0 : XiZeroCopy)
    (hoff : (q0.1 : ℂ).re ≠ 1 / 2) :
    0 < fiveShiftEulerGammaWindowedKreinDefectCombination L (L / 2) r q0 := by
  rw [fiveShiftEulerGammaWindowedKreinDefectCombination_eq]
  rw [fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature hr]
  have hstrip := xi_divisor_support_re_mem_open_unit q0.1
  have hfeature :
      0 < fiveShiftEulerGammaPairedFeature r ((q0.1 : ℂ).re - 1 / 2) := by
    apply fiveShiftEulerGammaPairedFeature_pos_of_ne_zero hr
    · exact sub_ne_zero.mpr hoff
    · rw [abs_le]
      constructor <;> linarith
  exact mul_pos (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr
      (xiRectangularTwoEdgeTransform_half_ne_zero_of_offline hL q0 hoff))) hfeature

/-- Every multiplicity copy contributes nonnegative legal windowed charge. -/
theorem fiveShiftEulerGammaWindowedKreinDefectCombination_nonneg
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (q0 : XiZeroCopy) :
    0 ≤ fiveShiftEulerGammaWindowedKreinDefectCombination L (L / 2) r q0 := by
  by_cases hoff : (q0.1 : ℂ).re = 1 / 2
  · rw [fiveShiftEulerGammaWindowedKreinDefectCombination_eq,
      fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature hr]
    simp [hoff, fiveShiftEulerGammaPairedFeature,
      fiveShiftEulerGammaFeature_zero]
  · exact (fiveShiftEulerGammaWindowedKreinDefectCombination_pos_of_offline
      hL hr q0 hoff).le

/-- The full multiplicity-exact windowed negative Krein sector is absolutely summable. -/
theorem fiveShiftEulerGammaWindowedKreinDefectCombination_summable
    (L a : ℝ) {r : ℝ} (hr : 0 < r) :
    Summable (fiveShiftEulerGammaWindowedKreinDefectCombination L a r) := by
  have hsq (k : ℕ) (hk : 1 ≤ k) :
      XiWeilSquareSummable
        (xiWindowedPrimeTest L a (Real.exp (k * r))) := by
    apply xiWindowedPrimeTest_squareSummable
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg (by positivity) hr.le
  have h1 := xiWeilPairDif_squareSummable (hsq 1 (by norm_num))
  have h2 := xiWeilPairDif_squareSummable (hsq 2 (by norm_num))
  have h3 := xiWeilPairDif_squareSummable (hsq 3 (by norm_num))
  have h4 := xiWeilPairDif_squareSummable (hsq 4 (by norm_num))
  have h5 := xiWeilPairDif_squareSummable (hsq 5 (by norm_num))
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  have hsum := ((((h1.mul_left (t * q * u)).sub
      (h2.mul_left (t * q + t * u + q * u + t * q * u))).add
      (h3.mul_left (t + q + u + t * q + t * u + q * u))).sub
      (h4.mul_left (1 + t + q + u))).add h5
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at hsum
  exact hsum.congr fun b => by
    simp only [fiveShiftEulerGammaWindowedKreinDefectCombination, q, t, u]

/-- Global nonnegative windowed five-shift charge. -/
def fiveShiftEulerGammaWindowedGlobalKreinCharge (L r : ℝ) : ℝ :=
  ∑' q0 : XiZeroCopy,
    fiveShiftEulerGammaWindowedKreinDefectCombination L (L / 2) r q0

/-- One off-line copy forces the full global charge to be strictly positive. -/
theorem fiveShiftEulerGammaWindowedGlobalKreinCharge_pos_of_offline
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) {q0 : XiZeroCopy}
    (hoff : (q0.1 : ℂ).re ≠ 1 / 2) :
    0 < fiveShiftEulerGammaWindowedGlobalKreinCharge L r := by
  exact Summable.tsum_pos
    (fiveShiftEulerGammaWindowedKreinDefectCombination_summable
      L (L / 2) hr)
    (fiveShiftEulerGammaWindowedKreinDefectCombination_nonneg hL hr)
    q0
    (fiveShiftEulerGammaWindowedKreinDefectCombination_pos_of_offline
      hL hr q0 hoff)

private theorem riemannHypothesis_of_forall_xiZeroCopy_re_eq_half
    (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  have hmem := mem_xi_divisor_support_of_eq_zero hzero
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) z :=
    xi_divisor_pos_on_support ⟨z, hmem⟩
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) z) := by omega
  have hre : z.re = 1 / 2 := h ⟨⟨z, hmem⟩, ⟨0, hn⟩⟩
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

/-- The new global, legal, nonnegative and multiplicity-exact charge vanishes exactly under RH. -/
theorem riemannHypothesis_iff_fiveShiftEulerGammaWindowedGlobalKreinCharge_eq_zero
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    RiemannHypothesis ↔
      fiveShiftEulerGammaWindowedGlobalKreinCharge L r = 0 := by
  constructor
  · intro hRH
    rw [fiveShiftEulerGammaWindowedGlobalKreinCharge]
    have hzero : ∀ q0 : XiZeroCopy,
        fiveShiftEulerGammaWindowedKreinDefectCombination L (L / 2) r q0 = 0 := by
      intro q0
      rw [fiveShiftEulerGammaWindowedKreinDefectCombination_eq,
        fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature hr]
      simp [xi_divisor_support_re_eq_half_of_rh hRH q0.1,
        fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature_zero]
    calc
      (∑' q0 : XiZeroCopy,
          fiveShiftEulerGammaWindowedKreinDefectCombination L (L / 2) r q0) =
          ∑' _q0 : XiZeroCopy, 0 := tsum_congr hzero
      _ = 0 := tsum_zero
  · intro hzero
    apply riemannHypothesis_of_forall_xiZeroCopy_re_eq_half
    intro q0
    by_contra hoff
    exact (ne_of_gt
      (fiveShiftEulerGammaWindowedGlobalKreinCharge_pos_of_offline
        hL hr hoff)) hzero

/-- Exact missing producer: coefficient-faithful Hermitian/source identification is RH itself. -/
theorem riemannHypothesis_iff_fiveShiftWindowedHermitianSourceIdentification
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    RiemannHypothesis ↔
      ∀ q0 : XiZeroCopy,
        ((fiveShiftEulerGammaWindowedKreinDefectCombination
            L (L / 2) r q0 : ℝ) : ℂ) =
          fiveShiftEulerGammaWindowedWeilPairCombination L (L / 2) r q0 := by
  constructor
  · intro hRH q0
    rw [fiveShiftEulerGammaWindowedWeilPairCombination_eq_zero,
      ofReal_eq_zero]
    rw [fiveShiftEulerGammaWindowedKreinDefectCombination_eq,
      fiveShiftEulerGammaKreinDefectCombination_eq_pairedFeature hr]
    simp [xi_divisor_support_re_eq_half_of_rh hRH q0.1,
      fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature_zero]
  · intro hid
    apply riemannHypothesis_of_forall_xiZeroCopy_re_eq_half
    intro q0
    by_contra hoff
    have hpos :=
      fiveShiftEulerGammaWindowedKreinDefectCombination_pos_of_offline
        hL hr q0 hoff
    have heq := hid q0
    rw [fiveShiftEulerGammaWindowedWeilPairCombination_eq_zero,
      ofReal_eq_zero] at heq
    exact (ne_of_gt hpos) heq

end

end RHTower
