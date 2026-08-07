import GaloisForLFunctions.RHTower.ProlateDunsterWeakLimit
import GaloisForLFunctions.RHTower.CCMFirstRowEnvelopeTail

/-!
# Compact off-diagonal cancellation for the Dunster/Bessel profile

The first-row difference phase may have one nondegenerate stationary point; its integral is
already controlled by `abs_integral_firstRow_leading_le`.  The companion sum phase has no
stationary point.  This file supplies its weighted first-derivative estimate and combines both
phases into cancellation of the leading Bessel product on every fixed exterior interval.
-/

noncomputable section

open Filter MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## Sum phase -/

/-- Sum of the two exterior Liouville phases in the first radial row. -/
def xiSumPhase (s k x : ℝ) : ℝ :=
  xiEndpointPhase s x + xiEndpointPhase s (k * x)

/-- Derivative of `xiSumPhase`. -/
def xiSumSpeed (s k x : ℝ) : ℝ :=
  xiSpeed s x + k * xiSpeed s (k * x)

/-- Second derivative of `xiSumPhase`. -/
def xiSumSecond (s k x : ℝ) : ℝ :=
  xiSpeedDeriv s x + k ^ 2 * xiSpeedDeriv s (k * x)

theorem hasDerivAt_xiSumPhase {s k x : ℝ} (hs0 : 0 ≤ s) (hx : 1 < x)
    (hkx : 1 < k * x) :
    HasDerivAt (xiSumPhase s k) (xiSumSpeed s k x) x := by
  have h1 := hasDerivAt_xiEndpointPhase hs0 hx
  have h2 := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := k) (x := x) hs0 hkx
  rw [xiSpeed_mul] at h2
  simpa [xiSumPhase, xiSumSpeed] using h1.add h2

theorem hasDerivAt_xiSumSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x)
    (hkx : 1 < k * x) :
    HasDerivAt (xiSumSpeed s k) (xiSumSecond s k x) x := by
  have h1 := hasDerivAt_xiSpeed hs1 hx
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have h2 : HasDerivAt (fun t : ℝ => xiSpeed s (k * t))
      (xiSpeedDeriv s (k * x) * k) x :=
    (hasDerivAt_xiSpeed hs1 hkx).comp x hlin
  have h3 := h2.const_mul k
  simpa [xiSumSpeed, xiSumSecond] using h1.add h3

theorem one_add_le_xiSumSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hk : 0 ≤ k)
    (hx : 1 < x) (hkx : 1 < k * x) :
    1 + k ≤ xiSumSpeed s k x := by
  have h1 := one_le_xiSpeed (s := s) (t := x) hs1 hx
  have h2 := one_le_xiSpeed (s := s) (t := k * x) hs1 hkx
  rw [xiSumSpeed]
  nlinarith

theorem xiSumSecond_nonpos {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hkx : 1 < k * x) : xiSumSecond s k x ≤ 0 := by
  have h1 := xiSpeedDeriv_nonpos hs1 hx
  have h2 := xiSpeedDeriv_nonpos hs1 hkx
  rw [xiSumSecond]
  nlinarith [sq_nonneg k]

theorem continuousOn_xiSumSecond {s k : ℝ} (hs1 : s ≤ 1) (hk : 2 ≤ k) :
    ContinuousOn (xiSumSecond s k) (Ioi 1) := by
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hfar : MapsTo (fun x : ℝ => k * x) (Ioi 1) (Ioi 1) := mapsTo_mul_left_Ioi hk
  have h1 := continuousOn_xiSpeedDeriv (s := s) hs1
  have h2 : ContinuousOn (fun x : ℝ => xiSpeedDeriv s (k * x)) (Ioi 1) :=
    h1.comp hlin hfar
  exact h1.add (continuousOn_const.mul h2)

theorem continuousOn_xiSumPhase {s k : ℝ} (hs0 : 0 ≤ s) (hk : 2 ≤ k) :
    ContinuousOn (xiSumPhase s k) (Ioi 1) := by
  intro x hx
  exact ((hasDerivAt_xiSumPhase hs0 hx (mapsTo_mul_left_Ioi hk hx)).continuousAt).continuousWithinAt

/-- The sum phase has speed at least `c(1+k)` and decreasing derivative. -/
theorem abs_integral_firstRow_sum_le {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a) :
    |∫ x in a..b, ampFourthRoot s k x *
        Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
      ≤ 4 * ampFourthRoot s k a / (c * (1 + k)) := by
  have hk0 : 0 ≤ k := by linarith
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hx1 : ∀ x ∈ uIcc a b, 1 < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ uIcc a b, 1 < k * x := fun x hx => mapsTo_mul_left_Ioi hk (hsub hx)
  let lam := c * (1 + k)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hw : ∀ x ∈ uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (uIcc a b) :=
    (continuousOn_ampFourthRootDeriv hs1 hk).mono hsub
  have hwnn : ∀ x ∈ uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiSumPhase s k t - Real.pi / 2)
        (c * xiSumSpeed s k x) x := by
    intro x hx
    exact ((hasDerivAt_xiSumPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).sub_const _
  have hg' : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiSumSpeed s k t)
        (c * xiSumSecond s k x) x :=
    fun x hx => (hasDerivAt_xiSumSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c
  have hg''c : ContinuousOn (fun x : ℝ => c * xiSumSecond s k x) (uIcc a b) :=
    continuousOn_const.mul ((continuousOn_xiSumSecond (by linarith) hk).mono hsub)
  have hg'lb : ∀ x ∈ uIcc a b, lam ≤ c * xiSumSpeed s k x := by
    intro x hx
    dsimp [lam]
    exact mul_le_mul_of_nonneg_left
      (one_add_le_xiSumSpeed (by linarith) hk0 (hx1 x hx) (hkx x hx)) hc.le
  have hg''np : ∀ x ∈ uIcc a b, c * xiSumSecond s k x ≤ 0 := by
    intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos hc.le
      (xiSumSecond_nonpos hs1 (hx1 x hx) (hkx x hx))
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le_anti hab hlam
    hw hw'c hwnn hwanti hg hg' hg''c hg'lb hg''np
  have hint : IntervalIntegrable
      (fun x => (ampFourthRoot s k x : ℂ) *
        Complex.exp (((c * xiSumPhase s k x - Real.pi / 2 : ℝ) : ℂ) * Complex.I))
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    have hamp : ContinuousOn (fun x : ℝ => (ampFourthRoot s k x : ℂ)) (uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuousOn_ampFourthRoot hs1 hk).mono hsub)
    have hphase : ContinuousOn (fun x : ℝ => ((c * xiSumPhase s k x - Real.pi / 2 : ℝ) : ℂ))
        (uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono hsub)).sub continuousOn_const)
    exact hamp.mul (Complex.continuous_exp.comp_continuousOn (hphase.mul continuousOn_const))
  exact (abs_integral_mul_cos_le_norm hint).trans (by simpa [lam] using hmain)

/-! ## Leading product -/

/-- Product of the two leading cosine profiles in the first radial row. -/
def firstRowLeadingProduct (s c k x : ℝ) : ℝ :=
  (Real.sqrt (2 / Real.pi) * ampFourth s x *
      Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) *
    (Real.sqrt (2 / Real.pi) * ampFourth s (k * x) *
      Real.cos (c * xiEndpointPhase s (k * x) - Real.pi / 4))

theorem ampFourth_mul_eq_ampFourthRoot {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    ampFourth s x * ampFourth s (k * x) = ampFourthRoot s k x := by
  have hkx : 1 < k * x := mapsTo_mul_left_Ioi hk hx
  have h1 := ampFourth_pos hs1 hx
  have h2 := ampFourth_pos hs1 hkx
  have hroot := ampFourthRoot_pos hs1 hk hx
  apply (sq_eq_sq₀ (mul_nonneg h1.le h2.le) hroot.le).mp
  rw [mul_pow, ampFourth_sq hs1 hx, ampFourth_sq hs1 hkx]
  rw [ampFourthRoot, div_pow, one_pow,
    Real.sq_sqrt (Real.sqrt_nonneg (ampPoly s k x))]
  have hkxsq : (k * x) ^ 2 = k ^ 2 * x ^ 2 := by ring
  rw [hkxsq, ampPoly]
  have hA : 0 < (x ^ 2 - 1) * (x ^ 2 - s) := by
    have : 0 < x := by linarith
    positivity
  have hB : 0 < (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) := by
    have hk0 : 0 < k := by linarith
    have hx0 : 0 < x := by linarith
    positivity
  rw [← Real.sqrt_mul hA.le]
  ring

theorem firstRowLeadingProduct_eq_phase_sum {s c k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    firstRowLeadingProduct s c k x =
      (1 / Real.pi) * ampFourthRoot s k x *
        (Real.cos (c * xiDiffPhase s k x) +
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [firstRowLeadingProduct, ← ampFourth_mul_eq_ampFourthRoot hs1 hk hx]
  let A := c * xiEndpointPhase s x - Real.pi / 4
  let B := c * xiEndpointPhase s (k * x) - Real.pi / 4
  have htrig := Real.two_mul_cos_mul_cos A B
  have hAB : A - B = c * xiDiffPhase s k x := by
    dsimp [A, B, xiDiffPhase]
    ring
  have hsum : A + B = c * xiSumPhase s k x - Real.pi / 2 := by
    dsimp [A, B, xiSumPhase]
    ring
  rw [hAB, hsum] at htrig
  rw [show Real.sqrt (2 / Real.pi) * ampFourth s x * Real.cos A *
      (Real.sqrt (2 / Real.pi) * ampFourth s (k * x) * Real.cos B) =
      (Real.sqrt (2 / Real.pi) ^ 2) *
        (ampFourth s x * ampFourth s (k * x)) * (Real.cos A * Real.cos B) by ring,
    hsqrt, ampFourth_mul_eq_ampFourthRoot hs1 hk hx]
  calc
    2 / Real.pi * ampFourthRoot s k x * (Real.cos A * Real.cos B)
        = (1 / Real.pi) * ampFourthRoot s k x * (2 * Real.cos A * Real.cos B) := by ring
    _ = (1 / Real.pi) * ampFourthRoot s k x *
        (Real.cos (c * xiDiffPhase s k x) +
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by rw [htrig]

/-- Both leading phases cancel on a fixed exterior interval. -/
theorem abs_integral_firstRowLeadingProduct_le {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 3 * k ≤ c) (hab : a ≤ b) (ha : 1 < a)
    (hb : Real.sqrt (1 + 2 / k ^ 2) ≤ b) :
    |∫ x in a..b, firstRowLeadingProduct s c k x|
      ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hc0 : 0 < c := by linarith
  have h1b : (1 : ℝ) ≤ b := by
    have : (1 : ℝ) ≤ Real.sqrt (1 + 2 / k ^ 2) := by
      refine Real.one_le_sqrt.mpr ?_
      positivity
    exact this.trans hb
  have hdiffFull := abs_integral_firstRow_leading_le hs0 hs1 hk hc hb
  have hdiffLeft := abs_integral_firstRow_leading_le hs0 hs1 hk hc
    (le_trans (by
      refine Real.one_le_sqrt.mpr ?_
      positivity) hb)
  have hdiff : |∫ x in a..b, ampFourthRoot s k x *
      Real.cos (c * xiDiffPhase s k x)| ≤ 340 / (Real.sqrt c * k ^ 2) := by
    have h1a : (1 : ℝ) ≤ a := ha.le
    have hsplit : (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) =
        (∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
          ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
    have htri := abs_sub_le
      (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))
      (∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) 0
    rw [sub_zero, hsplit, add_sub_cancel_left] at htri
    exact htri.trans (by linarith [hdiffFull, hdiffLeft])
  have hsum := abs_integral_firstRow_sum_le hs0 hs1 hk hc0 hab ha
  have hpoint : ∀ x ∈ uIcc a b, firstRowLeadingProduct s c k x =
      (1 / Real.pi) * (ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
    intro x hx
    have hx' : 1 < x := by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1
    rw [firstRowLeadingProduct_eq_phase_sum hs1 hk hx']
    ring
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul]
  have hInt :
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) =
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2) := by
    rw [intervalIntegral.integral_add]
    · exact (continuousOn_ampFourthRoot hs1 hk).intervalIntegrable_of_Icc
        (fun x hx => by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1)
        |>.mul_continuousOn
          (Real.continuous_cos.comp_continuousOn
            (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono
              (fun x hx => by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1))))
    · exact (continuousOn_ampFourthRoot hs1 hk).intervalIntegrable_of_Icc
        (fun x hx => by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1)
        |>.mul_continuousOn
          (Real.continuous_cos.comp_continuousOn
            ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono
              (fun x hx => by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1))).sub continuousOn_const))
  rw [hInt, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  calc
    1 / Real.pi * |(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
        ≤ (1 / Real.pi) *
          (|(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))| +
            |∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|) := by
          gcongr
          exact abs_add _ _
    _ ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by gcongr

end GaloisForLFunctions.RHTower

end
