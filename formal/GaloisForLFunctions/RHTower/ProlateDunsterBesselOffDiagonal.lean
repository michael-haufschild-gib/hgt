import GaloisForLFunctions.RHTower.ProlateDunsterWeakLimit
import GaloisForLFunctions.RHTower.CCM.CCMFirstRowEnvelopeTail

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

/-! ## Monotonicity of the squared-profile envelope -/

/-- The Dunster squared-profile weight decreases throughout the strict exterior ray. -/
theorem profileWeight_antitoneOn {s : ℝ} (hs1 : s ≤ 1 / 2) :
    AntitoneOn (profileWeight s) (Ioi 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1)
  · intro x hx
    exact (hasDerivAt_profileWeight hs1 hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_profileWeight hs1 hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_profileWeight hs1 hx).deriv]
    exact profileWeightDeriv_nonpos hs1 hx

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
  have h2' : HasDerivAt (fun x : ℝ => xiEndpointPhase s (k * x))
      (k * xiSpeed s (k * x)) x := by
    rw [xiSpeed_mul]
    exact h2
  change HasDerivAt
    (fun y : ℝ => xiEndpointPhase s y + xiEndpointPhase s (k * y))
    (xiSpeed s x + k * xiSpeed s (k * x)) x
  exact h1.add h2'

theorem hasDerivAt_xiSumSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x)
    (hkx : 1 < k * x) :
    HasDerivAt (xiSumSpeed s k) (xiSumSecond s k x) x := by
  have h1 : HasDerivAt (xiSpeed s) (xiSpeedDeriv s x) x := by
    rw [xiSpeedDeriv]
    exact hasDerivAt_xiSpeed hs1 hx
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have h2 : HasDerivAt (fun t : ℝ => xiSpeed s (k * t))
      (xiSpeedDeriv s (k * x) * k) x :=
    (hasDerivAt_xiSpeed hs1 hkx).comp x hlin
  have h3 := h2.const_mul k
  change HasDerivAt (fun y : ℝ => xiSpeed s y + k * xiSpeed s (k * y))
    (xiSpeedDeriv s x + k ^ 2 * xiSpeedDeriv s (k * x)) x
  have hcoef : k ^ 2 * xiSpeedDeriv s (k * x) =
      k * (xiSpeedDeriv s (k * x) * k) := by ring
  rw [hcoef]
  exact h1.fun_add h3

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

/-- Continuity of the sum-phase second derivative for every fixed strict dilation. -/
theorem continuousOn_xiSumSecond_fixedRatio {s k : ℝ} (hs1 : s ≤ 1) (hk : 1 < k) :
    ContinuousOn (xiSumSecond s k) (Ioi 1) := by
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hfar : MapsTo (fun x : ℝ => k * x) (Ioi 1) (Ioi 1) := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    have hxk : x < k * x := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hk hx0
    exact hx1.trans hxk
  have h1 := continuousOn_xiSpeedDeriv (s := s) hs1
  have h2 : ContinuousOn (fun x : ℝ => xiSpeedDeriv s (k * x)) (Ioi 1) :=
    h1.comp hlin hfar
  exact h1.add (continuousOn_const.mul h2)

/-- Continuity of the sum phase for every fixed strict dilation. -/
theorem continuousOn_xiSumPhase_fixedRatio {s k : ℝ} (hs0 : 0 ≤ s) (hk : 1 < k) :
    ContinuousOn (xiSumPhase s k) (Ioi 1) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hxk : x < k * x := by
    simpa [one_mul] using mul_lt_mul_of_pos_right hk hx0
  have hkx : (1 : ℝ) < k * x := hx.trans hxk
  exact ((hasDerivAt_xiSumPhase hs0 hx hkx).continuousAt).continuousWithinAt

/-- Sum-phase cancellation on a compact exterior interval for every fixed `k > 1`. -/
theorem abs_integral_firstRow_sum_le_fixedRatio {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a) :
    |∫ x in a..b, ampFourthRoot s k x *
        Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
      ≤ 4 * ampFourthRoot s k a / (c * (1 + k)) := by
  have hk0 : 0 ≤ k := (lt_trans zero_lt_one hk).le
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hx1 : ∀ x ∈ uIcc a b, 1 < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ uIcc a b, 1 < k * x := by
    intro x hx
    have := hx1 x hx
    nlinarith
  let lam := c * (1 + k)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hw : ∀ x ∈ uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot_of_one_lt hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (uIcc a b) :=
    (continuousOn_ampFourthRootDeriv_of_one_lt hs1 hk).mono hsub
  have hwnn : ∀ x ∈ uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos_of_one_lt hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos_of_one_lt hs1 hk (hx1 x hx)
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
    continuousOn_const.mul ((continuousOn_xiSumSecond_fixedRatio (by linarith) hk).mono hsub)
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
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_ampFourthRoot_fixedRatio hs1 hk).mono hsub)
    have hphase : ContinuousOn
        (fun x : ℝ => ((c * xiSumPhase s k x - Real.pi / 2 : ℝ) : ℂ)) (uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul
          ((continuousOn_xiSumPhase_fixedRatio hs0 hk).mono hsub)).sub continuousOn_const)
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
    have hleft : 0 < x ^ 2 - 1 := by nlinarith
    have hright : 0 < x ^ 2 - s := by nlinarith
    exact mul_pos hleft hright
  have hB : 0 < (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) := by
    have hk0 : 0 < k := by linarith
    have hx0 : 0 < x := by linarith
    have hleft : 0 < k ^ 2 * x ^ 2 - 1 := by nlinarith [sq_nonneg (k * x)]
    have hright : 0 < k ^ 2 * x ^ 2 - s := by nlinarith [sq_nonneg (k * x)]
    exact mul_pos hleft hright
  rw [show (x ^ 2 - 1) * (x ^ 2 - s) * (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) =
      ((x ^ 2 - 1) * (x ^ 2 - s)) *
        ((k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s)) by ring,
    Real.sqrt_mul hA.le]
  ring

/-- The exact amplitude identity for every fixed strict dilation. -/
theorem ampFourth_mul_eq_ampFourthRoot_fixedRatio {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    ampFourth s x * ampFourth s (k * x) = ampFourthRoot s k x := by
  have hkx : 1 < k * x := by nlinarith
  have h1 := ampFourth_pos hs1 hx
  have h2 := ampFourth_pos hs1 hkx
  have hroot := ampFourthRoot_pos_of_one_lt hs1 hk hx
  apply (sq_eq_sq₀ (mul_nonneg h1.le h2.le) hroot.le).mp
  rw [mul_pow, ampFourth_sq hs1 hx, ampFourth_sq hs1 hkx]
  rw [ampFourthRoot, div_pow, one_pow,
    Real.sq_sqrt (Real.sqrt_nonneg (ampPoly s k x))]
  have hkxsq : (k * x) ^ 2 = k ^ 2 * x ^ 2 := by ring
  rw [hkxsq, ampPoly]
  have hA : 0 < (x ^ 2 - 1) * (x ^ 2 - s) := by
    have hleft : 0 < x ^ 2 - 1 := by nlinarith
    have hright : 0 < x ^ 2 - s := by nlinarith
    exact mul_pos hleft hright
  have hB : 0 < (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) := by
    have hk0 : 0 < k := lt_trans zero_lt_one hk
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hleft : 0 < k ^ 2 * x ^ 2 - 1 := by nlinarith [sq_nonneg (k * x)]
    have hright : 0 < k ^ 2 * x ^ 2 - s := by nlinarith [sq_nonneg (k * x)]
    exact mul_pos hleft hright
  rw [show (x ^ 2 - 1) * (x ^ 2 - s) * (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) =
      ((x ^ 2 - 1) * (x ^ 2 - s)) *
        ((k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s)) by ring,
    Real.sqrt_mul hA.le]
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

/-- Phase decomposition of the leading product for every fixed strict dilation. -/
theorem firstRowLeadingProduct_eq_phase_sum_fixedRatio {s c k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hx : 1 < x) :
    firstRowLeadingProduct s c k x =
      (1 / Real.pi) * ampFourthRoot s k x *
        (Real.cos (c * xiDiffPhase s k x) +
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [firstRowLeadingProduct, ← ampFourth_mul_eq_ampFourthRoot_fixedRatio hs1 hk hx]
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
    hsqrt, ampFourth_mul_eq_ampFourthRoot_fixedRatio hs1 hk hx]
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
    (haCross : Real.sqrt (1 + 2 / k ^ 2) ≤ a) :
    |∫ x in a..b, firstRowLeadingProduct s c k x|
      ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hc0 : 0 < c := by linarith
  have hcrossb : Real.sqrt (1 + 2 / k ^ 2) ≤ b := haCross.trans hab
  have hdiffFull := abs_integral_firstRow_leading_le hs0 hs1 hk hc hcrossb
  have hdiffLeft := abs_integral_firstRow_leading_le hs0 hs1 hk hc haCross
  have hdiff : |∫ x in a..b, ampFourthRoot s k x *
      Real.cos (c * xiDiffPhase s k x)| ≤ 340 / (Real.sqrt c * k ^ 2) := by
    have h1a : (1 : ℝ) ≤ a := ha.le
    have h1b : (1 : ℝ) ≤ b := h1a.trans hab
    let f : ℝ → ℝ := fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)
    have hint : ∀ p q : ℝ, 1 ≤ p → p ≤ q → IntervalIntegrable f volume p q := by
      intro p q hp hpq
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
      have hbig : IntegrableOn (ampFourthRoot s k) (Ioc 1 q) volume :=
        integrableOn_ampFourthRoot hs0 hs1 hk (hp.trans hpq)
      have hsub : Ioc p q ⊆ Ioi 1 := fun _ hx => lt_of_le_of_lt hp hx.1
      have hdom : IntegrableOn (ampFourthRoot s k) (Ioc p q) volume :=
        hbig.mono_set (fun _ hx => ⟨lt_of_le_of_lt hp hx.1, hx.2⟩)
      have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc p q)) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        exact ((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
          (Real.continuous_cos.comp_continuousOn
            (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))
      refine Integrable.mono' hdom hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx1 : 1 < x := lt_of_le_of_lt hp hx.1
      have hamp := (ampFourthRoot_pos hs1 hk hx1).le
      dsimp [f]
      rw [abs_mul, abs_of_nonneg hamp]
      nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x)]
    have hsplit : (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) =
        (∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
          ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
      simpa [f] using (intervalIntegral.integral_add_adjacent_intervals
        (hint 1 a le_rfl h1a) (hint a b h1a hab)).symm
    have heq : (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) =
        (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) -
          ∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
      linarith [hsplit]
    rw [heq]
    calc
      |(∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) -
          ∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
          ≤ |∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| +
            |∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| :=
        abs_sub _ _
      _ ≤ 340 / (Real.sqrt c * k ^ 2) := by
        calc
          |∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| +
              |∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
              ≤ 170 / (Real.sqrt c * k ^ 2) + 170 / (Real.sqrt c * k ^ 2) :=
            add_le_add hdiffFull hdiffLeft
          _ = 340 / (Real.sqrt c * k ^ 2) := by ring
  have hsum := abs_integral_firstRow_sum_le hs0 hs1 hk hc0 hab ha
  have hpoint : ∀ x ∈ uIcc a b, firstRowLeadingProduct s c k x =
      (1 / Real.pi) * (ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
    intro x hx
    have hx' : 1 < x := by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1
    rw [firstRowLeadingProduct_eq_phase_sum hs1 hk hx']
    ring
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul]
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hdiffInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) volume a b :=
    (((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))).intervalIntegrable
  have hsumInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2))
      volume a b :=
    (((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono hsub)).sub
          continuousOn_const))).intervalIntegrable
  have hInt :
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) =
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2) := by
    rw [intervalIntegral.integral_add hdiffInt hsumInt]
  rw [hInt, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  calc
    1 / Real.pi * |(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
        ≤ (1 / Real.pi) *
          (|(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))| +
            |∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by gcongr

/-- Leading-product cancellation when the left endpoint lies before the stationary window.
The only additional term is the exact integrable endpoint mass on `[1,a]`. -/
theorem abs_integral_firstRowLeadingProduct_le_endpoint {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 3 * k ≤ c) (hab : a ≤ b) (ha : 1 < a)
    (hbCross : Real.sqrt (1 + 2 / k ^ 2) ≤ b) :
    |∫ x in a..b, firstRowLeadingProduct s c k x|
      ≤ (1 / Real.pi) *
        (170 / (Real.sqrt c * k ^ 2) +
          4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hc0 : 0 < c := by linarith
  have hdiffFull := abs_integral_firstRow_leading_le hs0 hs1 hk hc hbCross
  let f : ℝ → ℝ := fun x =>
    ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)
  have hint : ∀ p q : ℝ, 1 ≤ p → p ≤ q → IntervalIntegrable f volume p q := by
    intro p q hp hpq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
    have hbig : IntegrableOn (ampFourthRoot s k) (Ioc 1 q) volume :=
      integrableOn_ampFourthRoot hs0 hs1 hk (hp.trans hpq)
    have hsub : Ioc p q ⊆ Ioi 1 := fun _ hx => lt_of_le_of_lt hp hx.1
    have hdom : IntegrableOn (ampFourthRoot s k) (Ioc p q) volume :=
      hbig.mono_set (fun _ hx => ⟨lt_of_le_of_lt hp hx.1, hx.2⟩)
    have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc p q)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact ((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
        (Real.continuous_cos.comp_continuousOn
          (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : 1 < x := lt_of_le_of_lt hp hx.1
    have hamp := (ampFourthRoot_pos hs1 hk hx1).le
    dsimp [f]
    rw [abs_mul, abs_of_nonneg hamp]
    nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x)]
  have hdiffLeft : |∫ x in (1 : ℝ)..a, f x|
      ≤ 4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) := by
    have hIab : IntegrableOn f (Ioc 1 a) volume := by
      have h := hint 1 a le_rfl ha.le
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le] at h
    have hnorm : ‖∫ x in Ioc (1 : ℝ) a, f x‖
        ≤ ∫ x in Ioc (1 : ℝ) a, ‖f x‖ := norm_integral_le_integral_norm _
    have hmono : (∫ x in Ioc (1 : ℝ) a, ‖f x‖)
        ≤ ∫ x in Ioc (1 : ℝ) a, ampFourthRoot s k x := by
      refine setIntegral_mono_on hIab.norm
        (integrableOn_ampFourthRoot hs0 hs1 hk ha.le) measurableSet_Ioc fun x hx => ?_
      have hamp := (ampFourthRoot_pos hs1 hk hx.1).le
      dsimp [f]
      rw [abs_mul, abs_of_nonneg hamp]
      nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x)]
    have hend := integral_Ioc_ampFourthRoot_le
      (s := s) (k := k) (X := a) hs0 hs1 hk ha.le
    rw [intervalIntegral.integral_of_le ha.le, ← Real.norm_eq_abs]
    linarith
  have hdiff : |∫ x in a..b, f x| ≤
      170 / (Real.sqrt c * k ^ 2) +
        4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) := by
    have hsplit : (∫ x in (1 : ℝ)..b, f x) =
        (∫ x in (1 : ℝ)..a, f x) + ∫ x in a..b, f x := by
      simpa using (intervalIntegral.integral_add_adjacent_intervals
        (hint 1 a le_rfl ha.le) (hint a b ha.le hab)).symm
    have heq : (∫ x in a..b, f x) =
        (∫ x in (1 : ℝ)..b, f x) - ∫ x in (1 : ℝ)..a, f x := by
      linarith [hsplit]
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hdiffFull hdiffLeft)
  have hsum := abs_integral_firstRow_sum_le hs0 hs1 hk hc0 hab ha
  have hpoint : ∀ x ∈ uIcc a b, firstRowLeadingProduct s c k x =
      (1 / Real.pi) * (f x +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
    intro x hx
    have hx' : 1 < x := by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1
    rw [firstRowLeadingProduct_eq_phase_sum hs1 hk hx']
    dsimp [f]
    ring
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul]
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hdiffInt : IntervalIntegrable f volume a b := hint a b ha.le hab
  have hsumInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2))
      volume a b :=
    (((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono hsub)).sub
          continuousOn_const))).intervalIntegrable
  rw [intervalIntegral.integral_add hdiffInt hsumInt, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  calc
    1 / Real.pi * |(∫ x in a..b, f x) +
        ∫ x in a..b, ampFourthRoot s k x *
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
        ≤ (1 / Real.pi) *
          (|(∫ x in a..b, f x)| +
            |∫ x in a..b, ampFourthRoot s k x *
              Real.cos (c * xiSumPhase s k x - Real.pi / 2)|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (1 / Real.pi) *
        (170 / (Real.sqrt c * k ^ 2) +
          4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
        gcongr

/-- The leading first-row Bessel product vanishes on every fixed compact exterior interval. -/
theorem tendsto_integral_firstRowLeadingProduct
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {k a b : ℝ} (hk : 2 ≤ k) (hab : a ≤ b) (ha : 1 < a)
    (haCross : Real.sqrt (1 + 2 / k ^ 2) ≤ a) :
    Tendsto (fun i => ∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x)
      l (nhds 0) := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi hk ha
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have hAmp : Tendsto (fun i => ampFourthRoot (s i) k a) l
      (nhds (ampFourth 0 a * ampFourth 0 (k * a))) := by
    have hmul := hAa.mul hAka
    apply hmul.congr'
    filter_upwards [hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with i hsi
    exact ampFourth_mul_eq_ampFourthRoot hsi.le hk ha
  have hsqrt : Tendsto (fun i => Real.sqrt (c i)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hc
  have hk2 : 0 < k ^ 2 := by positivity
  have hden1 : Tendsto (fun i => Real.sqrt (c i) * k ^ 2) l atTop :=
    hsqrt.atTop_mul_const hk2
  have hterm1 : Tendsto (fun i => 340 / (Real.sqrt (c i) * k ^ 2)) l (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden1
  have h1k : 0 < 1 + k := by linarith
  have hden2 : Tendsto (fun i => c i * (1 + k)) l atTop :=
    hc.atTop_mul_const h1k
  have hnum2 : Tendsto (fun i => 4 * ampFourthRoot (s i) k a) l
      (nhds (4 * (ampFourth 0 a * ampFourth 0 (k * a)))) := hAmp.const_mul 4
  have hterm2 : Tendsto
      (fun i => 4 * ampFourthRoot (s i) k a / (c i * (1 + k))) l (nhds 0) :=
    Tendsto.div_atTop hnum2 hden2
  have hmajor : Tendsto (fun i => (1 / Real.pi) *
      (340 / (Real.sqrt (c i) * k ^ 2) +
        4 * ampFourthRoot (s i) k a / (c i * (1 + k)))) l (nhds 0) := by
    convert (hterm1.add hterm2).const_mul (1 / Real.pi) using 1 <;> ring
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcLarge : ∀ᶠ i in l, 3 * k ≤ c i := hc.eventually (eventually_ge_atTop (3 * k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun i => abs_nonneg
      (∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x))
    (by
      filter_upwards [hs0, hsHalf, hcLarge] with i hsi0 hsi1 hci
      exact abs_integral_firstRowLeadingProduct_le hsi0 hsi1 hk hci hab ha haCross)
    hmajor

/-- Compact leading-product bound for every fixed strict dilation.  The supplied curvature floor is
uniform in `s`; compactness supplies such a positive floor below. -/
theorem abs_integral_firstRowLeadingProduct_le_fixedRatio
    {s c k a b η : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a) (hη : 0 < η)
    (hcurv : ∀ x ∈ uIcc a b,
      η ≤ -(xiSpeedDeriv s x - k ^ 2 * xiSpeedDeriv s (k * x))) :
    |∫ x in a..b, firstRowLeadingProduct s c k x| ≤
      (1 / Real.pi) *
        (10 * ampFourthRoot s k a / Real.sqrt (c * η) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hdiff : |∫ x in a..b, ampFourthRoot s k x *
      Real.cos (c * xiDiffPhase s k x)| ≤
      10 * ampFourthRoot s k a / Real.sqrt (c * η) := by
    have hcongr : (∫ x in a..b, ampFourthRoot s k x *
        Real.cos (c * xiDiffPhase s k x)) =
        ∫ x in a..b, ampFourthRoot s k x *
          Real.cos (-(c * xiDiffPhase s k x)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [Real.cos_neg]
    rw [hcongr]
    have hblock := norm_integral_neg_diffPhase_block_le_of_second_ge
      (s := s) (c := c) (k := k) (a := a) (b := b) (η := η)
      hs0 hs1 hk hc hη hab ha hcurv
    refine (abs_integral_mul_cos_le_norm ?_).trans hblock
    have hint := intervalIntegrable_ampCexp_fixedRatio
      (s := s) (c := c) (k := k) (a := a) (b := b)
      hs1 hs0 hk hab ha (-1)
    simpa using hint
  have hsum := abs_integral_firstRow_sum_le_fixedRatio hs0 hs1 hk hc hab ha
  have hpoint : ∀ x ∈ uIcc a b, firstRowLeadingProduct s c k x =
      (1 / Real.pi) *
        (ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
          ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
    intro x hx
    have hx' : 1 < x := by
      rw [uIcc_of_le hab] at hx
      exact ha.trans_le hx.1
    rw [firstRowLeadingProduct_eq_phase_sum_fixedRatio hs1 hk hx']
    ring
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul]
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hdiffInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) volume a b :=
    (((continuousOn_ampFourthRoot_fixedRatio hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul
          ((continuousOn_xiDiffPhase_fixedRatio hs0 hk).mono hsub)))).intervalIntegrable
  have hsumInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2))
      volume a b :=
    (((continuousOn_ampFourthRoot_fixedRatio hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul
          ((continuousOn_xiSumPhase_fixedRatio hs0 hk).mono hsub)).sub
            continuousOn_const))).intervalIntegrable
  rw [intervalIntegral.integral_add hdiffInt hsumInt, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  calc
    1 / Real.pi * |(∫ x in a..b, ampFourthRoot s k x *
        Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x *
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
        ≤ (1 / Real.pi) *
          (|∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| +
            |∫ x in a..b, ampFourthRoot s k x *
              Real.cos (c * xiSumPhase s k x - Real.pi / 2)|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (1 / Real.pi) *
        (10 * ampFourthRoot s k a / Real.sqrt (c * η) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by gcongr

/-- The leading first-row product vanishes on every compact exterior interval for every fixed
strict dilation `k > 1`. -/
theorem tendsto_integral_firstRowLeadingProduct_fixedRatio
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {k a b : ℝ} (hk : 1 < k) (hab : a ≤ b) (ha : 1 < a) :
    Tendsto (fun i => ∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x)
      l (nhds 0) := by
  obtain ⟨η, hη, hcurv⟩ := exists_fixedRatioCurvatureFloor hk ha hab
  have hka : 1 < k * a := by nlinarith
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have hAmp : Tendsto (fun i => ampFourthRoot (s i) k a) l
      (nhds (ampFourth 0 a * ampFourth 0 (k * a))) := by
    have hmul := hAa.mul hAka
    apply hmul.congr'
    filter_upwards [hs.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hsi
    exact ampFourth_mul_eq_ampFourthRoot_fixedRatio hsi.le hk ha
  have hcη : Tendsto (fun i => c i * η) l atTop := hc.atTop_mul_const hη
  have hsqrt : Tendsto (fun i => Real.sqrt (c i * η)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hcη
  have hnum1 : Tendsto (fun i => 10 * ampFourthRoot (s i) k a) l
      (nhds (10 * (ampFourth 0 a * ampFourth 0 (k * a)))) := hAmp.const_mul 10
  have hterm1 : Tendsto
      (fun i => 10 * ampFourthRoot (s i) k a / Real.sqrt (c i * η)) l (nhds 0) :=
    Tendsto.div_atTop hnum1 hsqrt
  have h1k : 0 < 1 + k := by linarith
  have hden2 : Tendsto (fun i => c i * (1 + k)) l atTop :=
    hc.atTop_mul_const h1k
  have hnum2 : Tendsto (fun i => 4 * ampFourthRoot (s i) k a) l
      (nhds (4 * (ampFourth 0 a * ampFourth 0 (k * a)))) := hAmp.const_mul 4
  have hterm2 : Tendsto
      (fun i => 4 * ampFourthRoot (s i) k a / (c i * (1 + k))) l (nhds 0) :=
    Tendsto.div_atTop hnum2 hden2
  have hmajor : Tendsto (fun i => (1 / Real.pi) *
      (10 * ampFourthRoot (s i) k a / Real.sqrt (c i * η) +
        4 * ampFourthRoot (s i) k a / (c i * (1 + k)))) l (nhds 0) := by
    convert (hterm1.add hterm2).const_mul (1 / Real.pi) using 1 <;> ring
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcLarge : ∀ᶠ i in l, 1 ≤ c i := hc.eventually (eventually_ge_atTop 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun i => abs_nonneg
      (∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x))
    (by
      filter_upwards [hs0, hsHalf, hcLarge] with i hsi0 hsi1 hci
      apply abs_integral_firstRowLeadingProduct_le_fixedRatio
        hsi0 hsi1 hk (by linarith) hab ha hη
      intro x hx
      exact hcurv (s i) ⟨hsi0, hsi1⟩ x (by simpa [uIcc_of_le hab] using hx))
    hmajor

/-! ## Exact Bessel product on a compact interval -/

/-- The rescaled regular Dunster/Bessel profile whose square is
`radialProlateBesselDensity`. -/
def radialProlateBesselProfile (s c x : ℝ) : ℝ :=
  Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)

/-- Product of the two regular profiles in the first radial row. -/
def firstRowBesselProduct (s c k x : ℝ) : ℝ :=
  radialProlateBesselProfile s c x * radialProlateBesselProfile s c (k * x)

/-- Uniform Bessel-symbol error beyond a fixed strict exterior radius. -/
def compactBesselProfileError (s c a : ℝ) : ℝ :=
  5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s a))

/-- Uniform compact error in the product of two first-row Bessel profiles. -/
def compactFirstRowProductError (s c k a : ℝ) : ℝ :=
  compactBesselProfileError s c a * compactBesselProfileError s c (k * a)
    + compactBesselProfileError s c a *
        (Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
    + (Real.sqrt (2 / Real.pi) * ampFourth s a) *
        compactBesselProfileError s c (k * a)

theorem continuousOn_ampFourth_exterior {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (ampFourth s) (Ioi 1) := by
  intro x hx
  have hx1 : 1 < x := hx
  have hleft : 0 < x ^ 2 - 1 := by nlinarith
  have hright : 0 < x ^ 2 - s := by nlinarith
  have hden : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) ≠ 0 := by positivity
  unfold ampFourth
  exact continuousWithinAt_const.div
    (Real.continuous_sqrt.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.comp (by fun_prop))).continuousWithinAt hden

theorem continuousOn_radialProlateBesselProfile
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (radialProlateBesselProfile s c) (Ioi 1) := by
  have hamp := continuousOn_xiAmplitude hs0 hs1
  have hphase := continuousOn_xiEndpointPhase hs0
  unfold radialProlateBesselProfile
  exact (continuousOn_const.mul hamp).mul
    (continuous_besselJ0.comp_continuousOn (continuousOn_const.mul hphase))

theorem continuousOn_firstRowBesselProduct
    {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) :
    ContinuousOn (firstRowBesselProduct s c k) (Ioi 1) := by
  have hp := continuousOn_radialProlateBesselProfile (c := c) hs0 hs1
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  unfold firstRowBesselProduct
  exact hp.mul (hp.comp hlin (mapsTo_mul_left_Ioi_fixedRatio hk))

theorem continuousOn_firstRowLeadingProduct
    {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) :
    ContinuousOn (firstRowLeadingProduct s c k) (Ioi 1) := by
  have hamp := continuousOn_ampFourth_exterior hs1
  have hphase := continuousOn_xiEndpointPhase hs0
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hfarAmp := hamp.comp hlin (mapsTo_mul_left_Ioi_fixedRatio hk)
  have hfarPhase := hphase.comp hlin (mapsTo_mul_left_Ioi_fixedRatio hk)
  unfold firstRowLeadingProduct
  exact ((continuousOn_const.mul hamp).mul
    (Real.continuous_cos.comp_continuousOn
      ((continuousOn_const.mul hphase).sub continuousOn_const))).mul
    ((continuousOn_const.mul hfarAmp).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul hfarPhase).sub continuousOn_const)))

theorem compactBesselProfileError_nonneg
    {s c a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 1 < a) :
    0 ≤ compactBesselProfileError s c a := by
  rw [compactBesselProfileError]
  exact div_nonneg (mul_nonneg (by norm_num) (ampFourth_pos hs1 ha).le) (Real.sqrt_nonneg _)

/-- The Bessel asymptotic error is uniform to the right of a fixed exterior radius. -/
theorem abs_radialProlateBesselProfile_sub_leading_le
    {s c a x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |radialProlateBesselProfile s c x -
        Real.sqrt (2 / Real.pi) * ampFourth s x *
          Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ compactBesselProfileError s c a := by
  have hx : 1 < x := ha.trans_le hax
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s x :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le hax
  have harg : c * xiEndpointPhase s a ≤ c * xiEndpointPhase s x :=
    mul_le_mul_of_nonneg_left hphase hc.le
  have hraw := abs_profile_sub_model_le hs0 hs1 hx hc (hcxi.trans harg)
  change |radialProlateBesselProfile s c x - _| ≤ _
  refine hraw.trans ?_
  rw [compactBesselProfileError]
  have hamp := ampFourth_le_of_le hs1 ha hax
  have hdena : 0 < Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) := by
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hdenx : Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) ≤
      Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt harg)
  calc
    5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
        ≤ 5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
          gcongr
    _ ≤ 5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) := by
          exact div_le_div_of_nonneg_left
            (mul_nonneg (by norm_num) (ampFourth_pos hs1 ha).le) hdena hdenx

/-- Uniform absolute size of the leading cosine profile on the compact ray. -/
theorem abs_radialProlateLeadingProfile_le
    {s c a x : ℝ} (hs1 : s ≤ 1 / 2) (ha : 1 < a) (hax : a ≤ x) :
    |Real.sqrt (2 / Real.pi) * ampFourth s x *
        Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * ampFourth s a := by
  have hx : 1 < x := ha.trans_le hax
  have hamp0 := (ampFourth_pos hs1 hx).le
  have hamp := ampFourth_le_of_le hs1 ha hax
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (2 / Real.pi) * ampFourth s x)]
  have hcos := Real.abs_cos_le_one (c * xiEndpointPhase s x - Real.pi / 4)
  calc
    Real.sqrt (2 / Real.pi) * ampFourth s x *
        |Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
        ≤ Real.sqrt (2 / Real.pi) * ampFourth s x * 1 := by
          exact mul_le_mul_of_nonneg_left hcos (by positivity)
    _ ≤ Real.sqrt (2 / Real.pi) * ampFourth s a := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hamp (Real.sqrt_nonneg _)

/-- Uniform pointwise difference between the exact Bessel product and its two-cosine leading
product on a compact first-row interval. -/
theorem abs_firstRowBesselProduct_sub_leading_le
    {s c k a x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |firstRowBesselProduct s c k x - firstRowLeadingProduct s c k x|
      ≤ compactFirstRowProductError s c k a := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi_fixedRatio hk ha
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkax : k * a ≤ k * x := mul_le_mul_of_nonneg_left hax hk0.le
  have haka : a ≤ k * a := by
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hmul : a < k * a := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hk ha0
    exact hmul.le
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s (k * a) :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le haka
  have hcxiFar : 1 ≤ c * xiEndpointPhase s (k * a) :=
    hcxi.trans (mul_le_mul_of_nonneg_left hphase hc.le)
  let P := radialProlateBesselProfile s c x
  let Q := radialProlateBesselProfile s c (k * x)
  let L := Real.sqrt (2 / Real.pi) * ampFourth s x *
    Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
  let M := Real.sqrt (2 / Real.pi) * ampFourth s (k * x) *
    Real.cos (c * xiEndpointPhase s (k * x) - Real.pi / 4)
  have hP : |P - L| ≤ compactBesselProfileError s c a :=
    abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc ha hax hcxi
  have hQ : |Q - M| ≤ compactBesselProfileError s c (k * a) :=
    abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc hka hkax hcxiFar
  have hL : |L| ≤ Real.sqrt (2 / Real.pi) * ampFourth s a :=
    abs_radialProlateLeadingProfile_le hs1 ha hax
  have hM : |M| ≤ Real.sqrt (2 / Real.pi) * ampFourth s (k * a) :=
    abs_radialProlateLeadingProfile_le hs1 hka hkax
  have hEa := compactBesselProfileError_nonneg hs0 hs1 hc ha
  have hEka := compactBesselProfileError_nonneg hs0 hs1 hc hka
  have hT : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hAa : 0 ≤ ampFourth s a := (ampFourth_pos hs1 ha).le
  have hAka : 0 ≤ ampFourth s (k * a) := (ampFourth_pos hs1 hka).le
  have hfac : P * Q - L * M = (P - L) * (Q - M) + (P - L) * M + L * (Q - M) := by ring
  change |P * Q - L * M| ≤ _
  rw [compactFirstRowProductError]
  rw [hfac]
  calc
    |(P - L) * (Q - M) + (P - L) * M + L * (Q - M)|
        ≤ |P - L| * |Q - M| + |P - L| * |M| + |L| * |Q - M| := by
          calc
            |(P - L) * (Q - M) + (P - L) * M + L * (Q - M)|
                ≤ |(P - L) * (Q - M) + (P - L) * M| + |L * (Q - M)| :=
              abs_add_le _ _
            _ ≤ (|(P - L) * (Q - M)| + |(P - L) * M|) + |L * (Q - M)| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ = |P - L| * |Q - M| + |P - L| * |M| + |L| * |Q - M| := by
              simp only [abs_mul]
    _ ≤ compactBesselProfileError s c a * compactBesselProfileError s c (k * a)
        + compactBesselProfileError s c a *
            (Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
        + (Real.sqrt (2 / Real.pi) * ampFourth s a) *
            compactBesselProfileError s c (k * a) := by
          gcongr

theorem tendsto_compactBesselProfileError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => compactBesselProfileError (s i) (c i) a) l (nhds 0) := by
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hroot : Tendsto
      (fun i => Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp harg)
  have hA := tendsto_ampFourth_fixed_radius hs ha
  rw [show (fun i => compactBesselProfileError (s i) (c i) a) =
      fun i => (5 * ampFourth (s i) a) /
        Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a)) by
    funext i
    rw [compactBesselProfileError]]
  exact Tendsto.div_atTop (hA.const_mul 5) hroot

theorem tendsto_compactFirstRowProductError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {k a : ℝ} (hk : 1 < k) (ha : 1 < a) :
    Tendsto (fun i => compactFirstRowProductError (s i) (c i) k a) l (nhds 0) := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi_fixedRatio hk ha
  have hEa := tendsto_compactBesselProfileError_zero hc hs hs0 ha
  have hEka := tendsto_compactBesselProfileError_zero hc hs hs0 hka
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have h1 : Tendsto (fun i => compactBesselProfileError (s i) (c i) a *
      compactBesselProfileError (s i) (c i) (k * a)) l (nhds 0) := by
    convert hEa.mul hEka using 1 <;> ring
  have h2 : Tendsto (fun i => compactBesselProfileError (s i) (c i) a *
      (Real.sqrt (2 / Real.pi) * ampFourth (s i) (k * a))) l (nhds 0) := by
    convert hEa.mul (hAka.const_mul (Real.sqrt (2 / Real.pi))) using 1 <;> ring
  have h3 : Tendsto (fun i => (Real.sqrt (2 / Real.pi) * ampFourth (s i) a) *
      compactBesselProfileError (s i) (c i) (k * a)) l (nhds 0) := by
    convert (hAa.const_mul (Real.sqrt (2 / Real.pi))).mul hEka using 1 <;> ring
  rw [show (fun i => compactFirstRowProductError (s i) (c i) k a) = fun i =>
      compactBesselProfileError (s i) (c i) a *
          compactBesselProfileError (s i) (c i) (k * a)
        + compactBesselProfileError (s i) (c i) a *
          (Real.sqrt (2 / Real.pi) * ampFourth (s i) (k * a))
        + (Real.sqrt (2 / Real.pi) * ampFourth (s i) a) *
          compactBesselProfileError (s i) (c i) (k * a) by
    funext i
    rw [compactFirstRowProductError]]
  simpa only [zero_add] using (h1.add h2).add h3

theorem abs_intervalIntegral_firstRowBesselProduct_sub_leading_le
    {s c k a b : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |(∫ x in a..b, firstRowBesselProduct s c k x) -
        ∫ x in a..b, firstRowLeadingProduct s c k x|
      ≤ compactFirstRowProductError s c k a * |b - a| := by
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hBint : IntervalIntegrable (firstRowBesselProduct s c k) volume a b :=
    ((continuousOn_firstRowBesselProduct hs0 hs1 hk).mono hsub).intervalIntegrable
  have hLint : IntervalIntegrable (firstRowLeadingProduct s c k) volume a b :=
    ((continuousOn_firstRowLeadingProduct hs0 hs1 hk).mono hsub).intervalIntegrable
  rw [← intervalIntegral.integral_sub hBint hLint, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hab] at hx
  rw [Real.norm_eq_abs]
  exact abs_firstRowBesselProduct_sub_leading_le hs0 hs1 hk hc ha hx.1.le hcxi

/-- Exact regular Bessel first-row product cancellation on every fixed exterior interval. -/
theorem tendsto_integral_firstRowBesselProduct
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {k a b : ℝ} (hk : 1 < k) (hab : a ≤ b) (ha : 1 < a) :
    Tendsto (fun i => ∫ x in a..b, firstRowBesselProduct (s i) (c i) k x)
      l (nhds 0) := by
  have hlead := tendsto_integral_firstRowLeadingProduct_fixedRatio hc hs hs0 hk hab ha
  have hbudget := tendsto_compactFirstRowProductError_zero hc hs hs0 hk ha
  have hmajor : Tendsto (fun i => compactFirstRowProductError (s i) (c i) k a * |b - a|)
      l (nhds 0) := by
    simpa using hbudget.mul_const |b - a|
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxi : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    harg.eventually (eventually_ge_atTop 1)
  have hdiff : Tendsto (fun i =>
      (∫ x in a..b, firstRowBesselProduct (s i) (c i) k x) -
        ∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
      (Eventually.of_forall fun i => abs_nonneg
        ((∫ x in a..b, firstRowBesselProduct (s i) (c i) k x) -
          ∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x))
      (by
        filter_upwards [hs0, hsHalf, hcPos, hcxi] with i hsi0 hsi1 hci hcix
        exact abs_intervalIntegral_firstRowBesselProduct_sub_leading_le
          hsi0 hsi1 hk hci hab ha hcix)
      hmajor
  simpa only [sub_add_cancel, zero_add] using hdiff.add hlead

/-! ## Exact endpoint-normalized radial profile on a compact interval -/

/-- Rescaled exact radial profile. -/
def radialProlateRescaledProfile (c : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt c * R x

/-- Exact first-row radial product at the density scale. -/
def firstRowRadialProduct (c : ℝ) (R : ℝ → ℝ) (k x : ℝ) : ℝ :=
  radialProlateRescaledProfile c R x * radialProlateRescaledProfile c R (k * x)

/-! ## Endpoint and tail control for the exact product -/

/-- Exact mass of the limiting density between the band edge and a finite radius. -/
theorem integral_Ioc_profileDensity_eq_radialAngle_div_pi {a : ℝ} (ha : 1 ≤ a) :
    (∫ x in Ioc (1 : ℝ) a, profileDensity x) = radialAngle a / Real.pi := by
  have hint : IntervalIntegrable profileDensity volume (1 : ℝ) a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    exact integrableOn_profileDensity.mono_set Ioc_subset_Ioi_self
  have hcont : ContinuousOn (fun t : ℝ => radialAngle t / Real.pi) (Icc 1 a) :=
    (continuous_radialAngle.div_const Real.pi).continuousOn
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) a,
      HasDerivWithinAt (fun u : ℝ => radialAngle u / Real.pi)
        (profileDensity t) (Ioi t) t :=
    fun t ht => (hasDerivAt_radialAngle_div_pi ht.1).hasDerivWithinAt
  have hprimitive := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    ha hcont hderiv hint
  rw [← intervalIntegral.integral_of_le ha, hprimitive, radialAngle_one]
  ring

theorem radialProlateRescaledProfile_sq_eq_density
    {c x : ℝ} {R : ℝ → ℝ} (hc : 0 ≤ c) :
    radialProlateRescaledProfile c R x ^ 2 = radialProlateDensity c R x := by
  rw [radialProlateRescaledProfile, radialProlateDensity, mul_pow, Real.sq_sqrt hc]

/-- Arithmetic-geometric mean domination by the two exact marginal densities. -/
theorem abs_firstRowRadialProduct_le_average_density
    {c k x : ℝ} {R : ℝ → ℝ} (hc : 0 ≤ c) :
    |firstRowRadialProduct c R k x| ≤
      (1 / 2 : ℝ) *
        (radialProlateDensity c R x + radialProlateDensity c R (k * x)) := by
  let P := radialProlateRescaledProfile c R x
  let Q := radialProlateRescaledProfile c R (k * x)
  have hamgm := two_mul_le_add_sq |P| |Q|
  have hP := radialProlateRescaledProfile_sq_eq_density (R := R) (x := x) hc
  have hQ := radialProlateRescaledProfile_sq_eq_density (R := R) (x := k * x) hc
  change P ^ 2 = radialProlateDensity c R x at hP
  change Q ^ 2 = radialProlateDensity c R (k * x) at hQ
  change |P * Q| ≤ _
  rw [abs_mul]
  have hP' : |P| ^ 2 = radialProlateDensity c R x := by rw [sq_abs, hP]
  have hQ' : |Q| ^ 2 = radialProlateDensity c R (k * x) := by rw [sq_abs, hQ]
  rw [← hP', ← hQ']
  nlinarith

/-- Exact endpoint density mass: the elementary collar costs `O(c⁻¹)` and the remaining
mass is dominated by the limiting arcsine profile. -/
theorem integral_radialProlateDensity_endpoint_le
    {s c a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (ha : 1 < a) (hcrossa : dunsterEndpointCrossing c ≤ a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∫ x in (1 : ℝ)..a, radialProlateDensity c R x) ≤
      9 / (8 * c) +
        4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) := by
  let B := dunsterEndpointCrossing c
  let K := radialProlateDensityEnvelopeConstant
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 < B := dunsterEndpointCrossing_gt_one hc0
  have hBa : B ≤ a := hcrossa
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hDcont : Continuous (radialProlateDensity c R) := by
    unfold radialProlateDensity
    fun_prop
  have hDint : ∀ p q : ℝ, IntervalIntegrable (radialProlateDensity c R) volume p q :=
    fun p q => hDcont.intervalIntegrable p q
  have hcollar : (∫ x in (1 : ℝ)..B, radialProlateDensity c R x) ≤ 9 / (8 * c) := by
    have hmono : (∫ x in (1 : ℝ)..B, radialProlateDensity c R x) ≤ ∫ _ in (1 : ℝ)..B, c := by
      refine intervalIntegral.integral_mono_on hB1.le (hDint 1 B)
        intervalIntegrable_const fun x hx => ?_
      have hunit := radialProlate_unit_bounds_to_crossing hs0 hs1 hc hR1 hR hDR hode hx
      rw [radialProlateDensity]
      have hsq : R x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (R x - 1)]
      simpa using mul_le_mul_of_nonneg_left hsq hc0.le
    calc
      (∫ x in (1 : ℝ)..B, radialProlateDensity c R x)
          ≤ ∫ _ in (1 : ℝ)..B, c := hmono
      _ = c * (B - 1) := by simp only [intervalIntegral.integral_const]; ring
      _ = 9 / (8 * c) := by
        dsimp [B, dunsterEndpointCrossing]
        field_simp
        ring
  have hEnvInt : IntervalIntegrable
      (fun x : ℝ => 4 * K * profileDensity x) volume B a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hBa]
    exact (integrableOn_profileDensity.mono_set
      (fun x hx => hB1.trans hx.1)).const_mul (4 * K)
  have hext : (∫ x in B..a, radialProlateDensity c R x) ≤
      4 * K * (radialAngle a / Real.pi) := by
    have hmono : (∫ x in B..a, radialProlateDensity c R x) ≤
        ∫ x in B..a, 4 * K * profileDensity x := by
      refine intervalIntegral.integral_mono_on hBa (hDint B a) hEnvInt fun x hx => ?_
      have hdens := radialProlateDensity_le_profileWeight hs0 hs1 hc
        hR1 hR hDR hode hx.1
      have hweight := profileWeight_le_four_mul_profileDensity hs0 hs1 (hB1.trans_le hx.1)
      have hK0 := radialProlateDensityEnvelopeConstant_nonneg
      calc
        radialProlateDensity c R x ≤ K * profileWeight s x := hdens
        _ ≤ K * (4 * profileDensity x) := mul_le_mul_of_nonneg_left hweight hK0
        _ = 4 * K * profileDensity x := by ring
    have hsubset : Ioc B a ⊆ Ioc (1 : ℝ) a := fun x hx => ⟨hB1.trans hx.1, hx.2⟩
    have hglobal : IntegrableOn (fun x : ℝ => 4 * K * profileDensity x) (Ioi 1) :=
      integrableOn_profileDensity.const_mul (4 * K)
    have htarget : IntegrableOn (fun x : ℝ => 4 * K * profileDensity x) (Ioc (1 : ℝ) a) :=
      hglobal.mono_set Ioc_subset_Ioi_self
    have hnonneg : ∀ᵐ x ∂volume.restrict (Ioc (1 : ℝ) a),
        0 ≤ 4 * K * profileDensity x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (mul_nonneg (by norm_num) radialProlateDensityEnvelopeConstant_nonneg)
        (profileDensity_nonneg hx.1.le)
    calc
      (∫ x in B..a, radialProlateDensity c R x)
          ≤ ∫ x in B..a, 4 * K * profileDensity x := hmono
      _ = ∫ x in Ioc B a, 4 * K * profileDensity x :=
        intervalIntegral.integral_of_le hBa
      _ ≤ ∫ x in Ioc (1 : ℝ) a, 4 * K * profileDensity x := by
        exact setIntegral_mono_set htarget hnonneg (Eventually.of_forall hsubset)
      _ = 4 * K * (radialAngle a / Real.pi) := by
        rw [integral_const_mul, integral_Ioc_profileDensity_eq_radialAngle_div_pi ha.le]
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (hDint 1 B) (hDint B a)).symm
  change (∫ x in (1 : ℝ)..a, radialProlateDensity c R x) ≤
    9 / (8 * c) + 4 * K * (radialAngle a / Real.pi)
  rw [hsplit]
  exact add_le_add hcollar hext

/-- On the endpoint interval the dilated marginal already lies in the uniform exterior region. -/
theorem radialProlateDensity_dilate_endpoint_le
    {s c k x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hcrossk : dunsterEndpointCrossing c ≤ k)
    (hx : 1 ≤ x)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    radialProlateDensity c R (k * x) ≤
      radialProlateDensityEnvelopeConstant * profileWeight s k := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hk_le : k ≤ k * x := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left hx hk0.le
  have hkx : 1 < k * x := hk.trans_le hk_le
  have hcross : dunsterEndpointCrossing c ≤ k * x := hcrossk.trans hk_le
  have hdens := radialProlateDensity_le_profileWeight hs0 hs1 hc
    hR1 hR hDR hode hcross
  have hanti := profileWeight_antitoneOn hs1
    (show k ∈ Ioi (1 : ℝ) from hk)
    (show k * x ∈ Ioi (1 : ℝ) from hkx) hk_le
  exact hdens.trans (mul_le_mul_of_nonneg_left hanti
    radialProlateDensityEnvelopeConstant_nonneg)

/-- Endpoint contribution of the exact first-row product. -/
theorem abs_integral_firstRowRadialProduct_endpoint_le
    {s c k a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hcrossk : dunsterEndpointCrossing c ≤ k)
    (ha : 1 < a) (hcrossa : dunsterEndpointCrossing c ≤ a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ x in (1 : ℝ)..a, firstRowRadialProduct c R k x| ≤
      (1 / 2 : ℝ) *
        (9 / (8 * c) +
          4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
          radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hProdCont : Continuous (firstRowRadialProduct c R k) := by
    unfold firstRowRadialProduct radialProlateRescaledProfile
    fun_prop
  have hD1Cont : Continuous (radialProlateDensity c R) := by
    unfold radialProlateDensity
    fun_prop
  have hD2Cont : Continuous (fun x => radialProlateDensity c R (k * x)) := by
    exact hD1Cont.comp (continuous_const.mul continuous_id)
  let A : ℝ → ℝ := fun x => (1 / 2 : ℝ) *
    (radialProlateDensity c R x + radialProlateDensity c R (k * x))
  have hAint : IntervalIntegrable A volume (1 : ℝ) a := by
    dsimp [A]
    exact ((hD1Cont.intervalIntegrable 1 a).add
      (hD2Cont.intervalIntegrable 1 a)).const_mul (1 / 2)
  have hmono : (∫ x in (1 : ℝ)..a, |firstRowRadialProduct c R k x|) ≤
      ∫ x in (1 : ℝ)..a, A x := by
    refine intervalIntegral.integral_mono_on ha.le
      (hProdCont.intervalIntegrable 1 a).abs hAint fun x _ => ?_
    exact abs_firstRowRadialProduct_le_average_density hc0.le
  have hD1 := integral_radialProlateDensity_endpoint_le hs0 hs1 hc ha hcrossa
    hR1 hR hDR hode
  have hD2 : (∫ x in (1 : ℝ)..a, radialProlateDensity c R (k * x)) ≤
      radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1) := by
    have hconst : IntervalIntegrable
        (fun _ : ℝ => radialProlateDensityEnvelopeConstant * profileWeight s k)
        volume (1 : ℝ) a := intervalIntegrable_const
    have hm : (∫ x in (1 : ℝ)..a, radialProlateDensity c R (k * x)) ≤
        ∫ _ in (1 : ℝ)..a,
          radialProlateDensityEnvelopeConstant * profileWeight s k := by
      refine intervalIntegral.integral_mono_on ha.le
        (hD2Cont.intervalIntegrable 1 a) hconst fun x hx => ?_
      exact radialProlateDensity_dilate_endpoint_le hs0 hs1 hk hc hcrossk hx.1
        hR1 hR hDR hode
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    convert hm using 1 <;> ring
  calc
    |∫ x in (1 : ℝ)..a, firstRowRadialProduct c R k x|
        ≤ ∫ x in (1 : ℝ)..a, |firstRowRadialProduct c R k x| :=
          intervalIntegral.abs_integral_le_integral_abs ha.le
    _ ≤ ∫ x in (1 : ℝ)..a, A x := hmono
    _ = (1 / 2 : ℝ) *
        ((∫ x in (1 : ℝ)..a, radialProlateDensity c R x) +
          ∫ x in (1 : ℝ)..a, radialProlateDensity c R (k * x)) := by
      dsimp [A]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hD1Cont.intervalIntegrable 1 a)
          (hD2Cont.intervalIntegrable 1 a)]
    _ ≤ (1 / 2 : ℝ) *
        (9 / (8 * c) +
          4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
          radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1)) := by
      gcongr

/-- On a strict tail, the exact product is dominated by one fixed multiple of the limiting
profile density. -/
theorem abs_firstRowRadialProduct_le_profileDensity
    {s c k b x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hb : 1 < b) (hcrossb : dunsterEndpointCrossing c ≤ b) (hx : b ≤ x)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |firstRowRadialProduct c R k x| ≤
      4 * radialProlateDensityEnvelopeConstant * profileDensity x := by
  let K := radialProlateDensityEnvelopeConstant
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hx1 : 1 < x := hb.trans_le hx
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkx1 : 1 < k * x := mapsTo_mul_left_Ioi_fixedRatio hk hx1
  have hxkx : x ≤ k * x := by
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    have hmul : x < k * x := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hk hx0
    exact hmul.le
  have hd1 := radialProlateDensity_le_profileWeight hs0 hs1 hc
    hR1 hR hDR hode (hcrossb.trans hx)
  have hd2raw := radialProlateDensity_le_profileWeight hs0 hs1 hc
    hR1 hR hDR hode (hcrossb.trans (hx.trans hxkx))
  have hanti := profileWeight_antitoneOn hs1
    (show x ∈ Ioi (1 : ℝ) from hx1)
    (show k * x ∈ Ioi (1 : ℝ) from hkx1) hxkx
  have hK0 : 0 ≤ K := radialProlateDensityEnvelopeConstant_nonneg
  have hd2 : radialProlateDensity c R (k * x) ≤ K * profileWeight s x :=
    hd2raw.trans (mul_le_mul_of_nonneg_left hanti hK0)
  have hprod := abs_firstRowRadialProduct_le_average_density (R := R) (k := k) (x := x) hc0.le
  have hweight := profileWeight_le_four_mul_profileDensity hs0 hs1 hx1
  calc
    |firstRowRadialProduct c R k x|
        ≤ (1 / 2 : ℝ) *
          (radialProlateDensity c R x + radialProlateDensity c R (k * x)) := hprod
    _ ≤ K * profileWeight s x := by nlinarith
    _ ≤ K * (4 * profileDensity x) := mul_le_mul_of_nonneg_left hweight hK0
    _ = 4 * K * profileDensity x := by ring

/-- Integrability of the exact first-row product on every tail beyond the Dunster matching point. -/
theorem integrableOn_firstRowRadialProduct_Ioi
    {s c k b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hb : 1 < b) (hcrossb : dunsterEndpointCrossing c ≤ b)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    IntegrableOn (firstRowRadialProduct c R k) (Ioi b) := by
  let K := radialProlateDensityEnvelopeConstant
  have hsub : Ioi b ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hb.le
  have hdom : IntegrableOn (fun x : ℝ => 4 * K * profileDensity x) (Ioi b) :=
    (integrableOn_profileDensity.mono_set hsub).const_mul (4 * K)
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous (firstRowRadialProduct c R k) := by
    unfold firstRowRadialProduct radialProlateRescaledProfile
    fun_prop
  refine Integrable.mono' hdom
    (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs]
  exact abs_firstRowRadialProduct_le_profileDensity hs0 hs1 hk hc hb hcrossb hx.le
    hR1 hR hDR hode

/-- Uniform tail integral bound for the exact product. -/
theorem abs_integral_Ioi_firstRowRadialProduct_le
    {s c k b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hb : 1 < b) (hcrossb : dunsterEndpointCrossing c ≤ b)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ x in Ioi b, firstRowRadialProduct c R k x| ≤
      4 * radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi b, profileDensity x := by
  let K := radialProlateDensityEnvelopeConstant
  have hprod := integrableOn_firstRowRadialProduct_Ioi hs0 hs1 hk hc hb hcrossb
    hR1 hR hDR hode
  have hsub : Ioi b ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi hb.le
  have hdom : IntegrableOn (fun x : ℝ => 4 * K * profileDensity x) (Ioi b) :=
    (integrableOn_profileDensity.mono_set hsub).const_mul (4 * K)
  have hmono : (∫ x in Ioi b, |firstRowRadialProduct c R k x|) ≤
      ∫ x in Ioi b, 4 * K * profileDensity x := by
    apply integral_mono_ae hprod.abs hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact abs_firstRowRadialProduct_le_profileDensity hs0 hs1 hk hc hb hcrossb hx.le
      hR1 hR hDR hode
  calc
    |∫ x in Ioi b, firstRowRadialProduct c R k x|
        = ‖∫ x in Ioi b, firstRowRadialProduct c R k x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in Ioi b, ‖firstRowRadialProduct c R k x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x in Ioi b, |firstRowRadialProduct c R k x| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact Real.norm_eq_abs _
    _ ≤ ∫ x in Ioi b, 4 * K * profileDensity x := hmono
    _ = 4 * K * ∫ x in Ioi b, profileDensity x := by rw [integral_const_mul]

/-- Uniform compact exact-to-Bessel profile error supplied by Dunster transfer. -/
def compactExactProfileError (s c a : ℝ) : ℝ :=
  (radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant / c) *
    ampFourth s a

/-- Uniform exact-to-Bessel product error on a fixed first-row interval. -/
def compactExactFirstRowProductError (s c k a : ℝ) : ℝ :=
  compactExactProfileError s c a * compactExactProfileError s c (k * a)
    + compactExactProfileError s c a *
        (compactBesselProfileError s c (k * a) +
          Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
    + (compactBesselProfileError s c a +
        Real.sqrt (2 / Real.pi) * ampFourth s a) *
        compactExactProfileError s c (k * a)

theorem compactExactProfileError_nonneg
    {s c a : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 1 < a) :
    0 ≤ compactExactProfileError s c a := by
  rw [compactExactProfileError]
  have hK := radialProlateUniformTransferConstant_nonneg
  have hC := lgBesselCommonEnvelopeConstant_nonneg
  exact mul_nonneg (div_nonneg (mul_nonneg hK hC) hc.le) (ampFourth_pos hs1 ha).le

/-- Dunster's uniform transfer after multiplication by the natural `sqrt c` profile scale. -/
theorem abs_radialProlateRescaledProfile_sub_besselProfile_le
    {s c a x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (haCross : dunsterEndpointCrossing c ≤ a) (ha : 1 < a) (hax : a ≤ x)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |radialProlateRescaledProfile c R x - radialProlateBesselProfile s c x|
      ≤ compactExactProfileError s c a := by
  let K := radialProlateUniformTransferConstant
  let C := lgBesselCommonEnvelopeConstant
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hx : 1 < x := ha.trans_le hax
  have hraw := abs_radialProlate_sub_besselProfile_le hs0 hs1 hc hR1 hR hDR hode
    (haCross.trans hax)
  have hmul := mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg c)
  have hfac : radialProlateRescaledProfile c R x - radialProlateBesselProfile s c x =
      Real.sqrt c *
        (R x - xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) := by
    rw [radialProlateRescaledProfile, radialProlateBesselProfile]
    ring
  have hratio := sqrt_mul_xiAmplitude_div_eq hs0 hs1 hx hc0
  have heq : Real.sqrt c *
      (xiAmplitude s x * ((K / c) *
        (C / Real.sqrt (c * xiEndpointPhase s x)))) =
      (K * C / c) * ampFourth s x := by
    rw [← hratio]
    ring
  rw [hfac, abs_mul, abs_of_nonneg (Real.sqrt_nonneg c)]
  refine hmul.trans ?_
  rw [heq, compactExactProfileError]
  have hcoef : 0 ≤ K * C / c := by
    exact div_nonneg (mul_nonneg radialProlateUniformTransferConstant_nonneg
      lgBesselCommonEnvelopeConstant_nonneg) hc0.le
  exact mul_le_mul_of_nonneg_left (ampFourth_le_of_le hs1 ha hax) hcoef

theorem abs_radialProlateBesselProfile_le_compact
    {s c a x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |radialProlateBesselProfile s c x| ≤
      compactBesselProfileError s c a +
        Real.sqrt (2 / Real.pi) * ampFourth s a := by
  let L := Real.sqrt (2 / Real.pi) * ampFourth s x *
    Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
  have herror := abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc ha hax hcxi
  have hlead : |L| ≤ Real.sqrt (2 / Real.pi) * ampFourth s a :=
    abs_radialProlateLeadingProfile_le hs1 ha hax
  change |radialProlateBesselProfile s c x| ≤ _
  calc
    |radialProlateBesselProfile s c x|
        = |(radialProlateBesselProfile s c x - L) + L| := by ring_nf
    _ ≤ |radialProlateBesselProfile s c x - L| + |L| := abs_add_le _ _
    _ ≤ compactBesselProfileError s c a +
        Real.sqrt (2 / Real.pi) * ampFourth s a := add_le_add herror hlead

theorem abs_firstRowRadialProduct_sub_bessel_le
    {s c k a x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (haCross : dunsterEndpointCrossing c ≤ a) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |firstRowRadialProduct c R k x - firstRowBesselProduct s c k x|
      ≤ compactExactFirstRowProductError s c k a := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hka : 1 < k * a := mapsTo_mul_left_Ioi_fixedRatio hk ha
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkax : k * a ≤ k * x := mul_le_mul_of_nonneg_left hax hk0.le
  have haka : a ≤ k * a := by
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hmul : a < k * a := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hk ha0
    exact hmul.le
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s (k * a) :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le haka
  have hcxiFar : 1 ≤ c * xiEndpointPhase s (k * a) :=
    hcxi.trans (mul_le_mul_of_nonneg_left hphase hc0.le)
  let P := radialProlateRescaledProfile c R x
  let Q := radialProlateRescaledProfile c R (k * x)
  let B := radialProlateBesselProfile s c x
  let D := radialProlateBesselProfile s c (k * x)
  have hP : |P - B| ≤ compactExactProfileError s c a :=
    abs_radialProlateRescaledProfile_sub_besselProfile_le hs0 hs1 hc haCross ha hax
      hR1 hR hDR hode
  have hQ : |Q - D| ≤ compactExactProfileError s c (k * a) :=
    abs_radialProlateRescaledProfile_sub_besselProfile_le hs0 hs1 hc
      (haCross.trans haka) hka hkax hR1 hR hDR hode
  have hB : |B| ≤ compactBesselProfileError s c a +
      Real.sqrt (2 / Real.pi) * ampFourth s a :=
    abs_radialProlateBesselProfile_le_compact hs0 hs1 hc0 ha hax hcxi
  have hD : |D| ≤ compactBesselProfileError s c (k * a) +
      Real.sqrt (2 / Real.pi) * ampFourth s (k * a) :=
    abs_radialProlateBesselProfile_le_compact hs0 hs1 hc0 hka hkax hcxiFar
  have hEP := compactExactProfileError_nonneg hs1 hc0 ha
  have hEQ := compactExactProfileError_nonneg hs1 hc0 hka
  have hBEa := compactBesselProfileError_nonneg hs0 hs1 hc0 ha
  have hBEka := compactBesselProfileError_nonneg hs0 hs1 hc0 hka
  have hboundA : 0 ≤ compactBesselProfileError s c a +
      Real.sqrt (2 / Real.pi) * ampFourth s a :=
    add_nonneg hBEa (mul_nonneg (Real.sqrt_nonneg _) (ampFourth_pos hs1 ha).le)
  have hboundKa : 0 ≤ compactBesselProfileError s c (k * a) +
      Real.sqrt (2 / Real.pi) * ampFourth s (k * a) :=
    add_nonneg hBEka (mul_nonneg (Real.sqrt_nonneg _) (ampFourth_pos hs1 hka).le)
  have hfac : P * Q - B * D = (P - B) * (Q - D) + (P - B) * D + B * (Q - D) := by ring
  change |P * Q - B * D| ≤ _
  rw [compactExactFirstRowProductError, hfac]
  calc
    |(P - B) * (Q - D) + (P - B) * D + B * (Q - D)|
        ≤ |P - B| * |Q - D| + |P - B| * |D| + |B| * |Q - D| := by
          calc
            |(P - B) * (Q - D) + (P - B) * D + B * (Q - D)|
                ≤ |(P - B) * (Q - D) + (P - B) * D| + |B * (Q - D)| :=
              abs_add_le _ _
            _ ≤ (|(P - B) * (Q - D)| + |(P - B) * D|) + |B * (Q - D)| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ = |P - B| * |Q - D| + |P - B| * |D| + |B| * |Q - D| := by
              simp only [abs_mul]
    _ ≤ compactExactProfileError s c a * compactExactProfileError s c (k * a)
        + compactExactProfileError s c a *
            (compactBesselProfileError s c (k * a) +
              Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
        + (compactBesselProfileError s c a +
            Real.sqrt (2 / Real.pi) * ampFourth s a) *
              compactExactProfileError s c (k * a) := by
          gcongr

theorem tendsto_compactExactProfileError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => compactExactProfileError (s i) (c i) a) l (nhds 0) := by
  have hA := tendsto_ampFourth_fixed_radius hs ha
  have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) := tendsto_inv_atTop_zero.comp hc
  rw [show (fun i => compactExactProfileError (s i) (c i) a) = fun i =>
      (radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant) *
        (c i)⁻¹ * ampFourth (s i) a by
    funext i
    rw [compactExactProfileError, div_eq_mul_inv]]
  convert ((hinv.const_mul
    (radialProlateUniformTransferConstant * lgBesselCommonEnvelopeConstant)).mul hA) using 1 <;> ring

theorem tendsto_compactExactFirstRowProductError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {k a : ℝ} (hk : 1 < k) (ha : 1 < a) :
    Tendsto (fun i => compactExactFirstRowProductError (s i) (c i) k a) l (nhds 0) := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi_fixedRatio hk ha
  have hXa := tendsto_compactExactProfileError_zero hc hs ha
  have hXka := tendsto_compactExactProfileError_zero hc hs hka
  have hBa := tendsto_compactBesselProfileError_zero hc hs hs0 ha
  have hBka := tendsto_compactBesselProfileError_zero hc hs hs0 hka
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have hboundAka : Tendsto (fun i => compactBesselProfileError (s i) (c i) (k * a) +
      Real.sqrt (2 / Real.pi) * ampFourth (s i) (k * a)) l
      (nhds (Real.sqrt (2 / Real.pi) * ampFourth 0 (k * a))) := by
    simpa only [zero_add] using hBka.add (hAka.const_mul (Real.sqrt (2 / Real.pi)))
  have hboundAa : Tendsto (fun i => compactBesselProfileError (s i) (c i) a +
      Real.sqrt (2 / Real.pi) * ampFourth (s i) a) l
      (nhds (Real.sqrt (2 / Real.pi) * ampFourth 0 a)) := by
    simpa only [zero_add] using hBa.add (hAa.const_mul (Real.sqrt (2 / Real.pi)))
  have h1 := hXa.mul hXka
  have h2 := hXa.mul hboundAka
  have h3 := hboundAa.mul hXka
  rw [show (fun i => compactExactFirstRowProductError (s i) (c i) k a) = fun i =>
      compactExactProfileError (s i) (c i) a * compactExactProfileError (s i) (c i) (k * a)
        + compactExactProfileError (s i) (c i) a *
            (compactBesselProfileError (s i) (c i) (k * a) +
              Real.sqrt (2 / Real.pi) * ampFourth (s i) (k * a))
        + (compactBesselProfileError (s i) (c i) a +
            Real.sqrt (2 / Real.pi) * ampFourth (s i) a) *
              compactExactProfileError (s i) (c i) (k * a) by
    funext i
    rw [compactExactFirstRowProductError]]
  simpa only [zero_mul, zero_add, mul_zero] using (h1.add h2).add h3

theorem abs_intervalIntegral_firstRowRadialProduct_sub_bessel_le
    {s c k a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 < k) (hc : 5 ≤ c)
    (hab : a ≤ b) (ha : 1 < a) (haCross : dunsterEndpointCrossing c ≤ a)
    (hcxi : 1 ≤ c * xiEndpointPhase s a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |(∫ x in a..b, firstRowRadialProduct c R k x) -
        ∫ x in a..b, firstRowBesselProduct s c k x|
      ≤ compactExactFirstRowProductError s c k a * |b - a| := by
  have hRc : Continuous R :=
    continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hExactCont : Continuous (firstRowRadialProduct c R k) := by
    unfold firstRowRadialProduct radialProlateRescaledProfile
    fun_prop
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hExactInt : IntervalIntegrable (firstRowRadialProduct c R k) volume a b :=
    hExactCont.intervalIntegrable _ _
  have hBesselInt : IntervalIntegrable (firstRowBesselProduct s c k) volume a b :=
    ((continuousOn_firstRowBesselProduct hs0 hs1 hk).mono hsub).intervalIntegrable
  rw [← intervalIntegral.integral_sub hExactInt hBesselInt, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hab] at hx
  rw [Real.norm_eq_abs]
  exact abs_firstRowRadialProduct_sub_bessel_le hs0 hs1 hk hc haCross ha hx.1.le
    hcxi hR1 hR hDR hode

/-- Explicit compact bound valid even when the left endpoint precedes the stationary window. -/
theorem abs_intervalIntegral_firstRowRadialProduct_le_endpoint
    {s c k a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc5 : 5 ≤ c) (hcOsc : 3 * k ≤ c)
    (hab : a ≤ b) (ha : 1 < a)
    (haCross : dunsterEndpointCrossing c ≤ a)
    (hbStationary : Real.sqrt (1 + 2 / k ^ 2) ≤ b)
    (hcxi : 1 ≤ c * xiEndpointPhase s a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ x in a..b, firstRowRadialProduct c R k x| ≤
      compactExactFirstRowProductError s c k a * |b - a| +
        compactFirstRowProductError s c k a * |b - a| +
        (1 / Real.pi) *
          (170 / (Real.sqrt c * k ^ 2) +
            4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
            4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc5
  have hExact := abs_intervalIntegral_firstRowRadialProduct_sub_bessel_le
    hs0 hs1 (by linarith : (1 : ℝ) < k) hc5 hab ha haCross hcxi hR1 hR hDR hode
  have hBessel := abs_intervalIntegral_firstRowBesselProduct_sub_leading_le
    hs0 hs1 (by linarith : (1 : ℝ) < k) hc0 hab ha hcxi
  have hLeading := abs_integral_firstRowLeadingProduct_le_endpoint
    hs0 hs1 hk hcOsc hab ha hbStationary
  let E := ∫ x in a..b, firstRowRadialProduct c R k x
  let B := ∫ x in a..b, firstRowBesselProduct s c k x
  let L := ∫ x in a..b, firstRowLeadingProduct s c k x
  change |E| ≤ _
  change |E - B| ≤ _ at hExact
  change |B - L| ≤ _ at hBessel
  change |L| ≤ _ at hLeading
  calc
    |E| = |(E - B) + (B - L) + L| := by ring_nf
    _ ≤ |E - B| + |B - L| + |L| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ compactExactFirstRowProductError s c k a * |b - a| +
        compactFirstRowProductError s c k a * |b - a| +
        (1 / Real.pi) *
          (170 / (Real.sqrt c * k ^ 2) +
            4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
            4 * ampFourthRoot s k a / (c * (1 + k))) :=
      add_le_add (add_le_add hExact hBessel) hLeading

/-- Quantitative full-ray decomposition into endpoint, oscillatory compact block, and tail. -/
theorem abs_integral_Ioi_firstRowRadialProduct_full_le
    {s c k a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc5 : 5 ≤ c) (hcOsc : 3 * k ≤ c)
    (ha : 1 < a) (hab : a ≤ b)
    (haCross : dunsterEndpointCrossing c ≤ a)
    (hbStationary : Real.sqrt (1 + 2 / k ^ 2) ≤ b)
    (hcxi : 1 ≤ c * xiEndpointPhase s a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ x in Ioi (1 : ℝ), firstRowRadialProduct c R k x| ≤
      (1 / 2 : ℝ) *
          (9 / (8 * c) +
            4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
            radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1)) +
        (compactExactFirstRowProductError s c k a * |b - a| +
          compactFirstRowProductError s c k a * |b - a| +
          (1 / Real.pi) *
            (170 / (Real.sqrt c * k ^ 2) +
              4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
              4 * ampFourthRoot s k a / (c * (1 + k)))) +
        4 * radialProlateDensityEnvelopeConstant *
          ∫ x in Ioi b, profileDensity x := by
  have hb : 1 < b := ha.trans_le hab
  have hcrossb : dunsterEndpointCrossing c ≤ b := haCross.trans hab
  have hk1 : (1 : ℝ) < k := by linarith
  have hcrossk : dunsterEndpointCrossing c ≤ k :=
    (dunsterEndpointCrossing_le_eleven_tenths hc5).trans (by linarith)
  have hhead := abs_integral_firstRowRadialProduct_endpoint_le
    hs0 hs1 hk1 hc5 hcrossk ha haCross hR1 hR hDR hode
  have hmid := abs_intervalIntegral_firstRowRadialProduct_le_endpoint
    hs0 hs1 hk hc5 hcOsc hab ha haCross hbStationary hcxi hR1 hR hDR hode
  have htail := abs_integral_Ioi_firstRowRadialProduct_le
    hs0 hs1 hk1 hc5 hb hcrossb hR1 hR hDR hode
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hcont : Continuous (firstRowRadialProduct c R k) := by
    unfold firstRowRadialProduct radialProlateRescaledProfile
    fun_prop
  have hIntHead : IntervalIntegrable (firstRowRadialProduct c R k) volume (1 : ℝ) a :=
    hcont.intervalIntegrable 1 a
  have hIntMid : IntervalIntegrable (firstRowRadialProduct c R k) volume a b :=
    hcont.intervalIntegrable a b
  have hIntOneB : IntervalIntegrable (firstRowRadialProduct c R k) volume (1 : ℝ) b :=
    hcont.intervalIntegrable 1 b
  have hIoc : IntegrableOn (firstRowRadialProduct c R k) (Ioc (1 : ℝ) b) := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
  have hIoi := integrableOn_firstRowRadialProduct_Ioi
    hs0 hs1 hk1 hc5 hb hcrossb hR1 hR hDR hode
  have hsplitTail : (∫ x in Ioi (1 : ℝ), firstRowRadialProduct c R k x) =
      (∫ x in (1 : ℝ)..b, firstRowRadialProduct c R k x) +
        ∫ x in Ioi b, firstRowRadialProduct c R k x := by
    rw [intervalIntegral.integral_of_le hb.le]
    rw [← Ioc_union_Ioi_eq_Ioi hb.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi
  have hsplitCompact : (∫ x in (1 : ℝ)..b, firstRowRadialProduct c R k x) =
      (∫ x in (1 : ℝ)..a, firstRowRadialProduct c R k x) +
        ∫ x in a..b, firstRowRadialProduct c R k x := by
    exact (intervalIntegral.integral_add_adjacent_intervals hIntHead hIntMid).symm
  rw [hsplitTail, hsplitCompact]
  calc
    |((∫ x in (1 : ℝ)..a, firstRowRadialProduct c R k x) +
          ∫ x in a..b, firstRowRadialProduct c R k x) +
        ∫ x in Ioi b, firstRowRadialProduct c R k x|
        ≤ |∫ x in (1 : ℝ)..a, firstRowRadialProduct c R k x| +
            |∫ x in a..b, firstRowRadialProduct c R k x| +
              |∫ x in Ioi b, firstRowRadialProduct c R k x| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (1 / 2 : ℝ) *
          (9 / (8 * c) +
            4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
            radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1)) +
        (compactExactFirstRowProductError s c k a * |b - a| +
          compactFirstRowProductError s c k a * |b - a| +
          (1 / Real.pi) *
            (170 / (Real.sqrt c * k ^ 2) +
              4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4) +
              4 * ampFourthRoot s k a / (c * (1 + k)))) +
        4 * radialProlateDensityEnvelopeConstant *
          ∫ x in Ioi b, profileDensity x :=
      add_le_add (add_le_add hhead hmid) htail

/-- Non-vanishing part of the endpoint/compact estimate.  It is made arbitrarily small by
moving the compact cut down to the band edge. -/
def firstRowRadialEdgeBudget (s k a : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
        radialProlateDensityEnvelopeConstant * profileWeight s k * (a - 1)) +
    (1 / Real.pi) *
      (4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4))

/-- Terms which vanish for fixed endpoint and tail cuts as the prolate parameter grows. -/
def firstRowRadialVanishingBudget (s c k a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (9 / (8 * c)) +
    compactExactFirstRowProductError s c k a * |b - a| +
    compactFirstRowProductError s c k a * |b - a| +
    (1 / Real.pi) *
      (170 / (Real.sqrt c * k ^ 2) +
        4 * ampFourthRoot s k a / (c * (1 + k)))

theorem tendsto_firstRowRadialEdgeBudget_fixed
    {ι : Type*} {l : Filter ι} {s : ι → ℝ}
    (hs : Tendsto s l (nhds 0)) {k a : ℝ} (hk : 1 < k) (ha : 1 < a) :
    Tendsto (fun i => firstRowRadialEdgeBudget (s i) k a) l
      (nhds (firstRowRadialEdgeBudget 0 k a)) := by
  have hweight := tendsto_profileWeight_fixed_radius hs hk
  have hvar : Tendsto (fun i =>
      radialProlateDensityEnvelopeConstant * profileWeight (s i) k * (a - 1)) l
      (nhds (radialProlateDensityEnvelopeConstant * profileWeight 0 k * (a - 1))) :=
    (hweight.const_mul radialProlateDensityEnvelopeConstant).mul_const (a - 1)
  have hconst1 : Tendsto (fun _ : ι =>
      4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi)) l
      (nhds (4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi))) :=
    tendsto_const_nhds
  have hfirst := (hconst1.add hvar).const_mul (1 / 2)
  have hconst2 : Tendsto (fun _ : ι =>
      (1 / Real.pi) *
        (4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4))) l
      (nhds ((1 / Real.pi) *
        (4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4)))) :=
    tendsto_const_nhds
  simpa [firstRowRadialEdgeBudget] using hfirst.add hconst2

/-- The limiting edge budget vanishes as the cut approaches the band edge from either side. -/
theorem tendsto_firstRowRadialEdgeBudget_at_one (k : ℝ) :
    Tendsto (fun a : ℝ => firstRowRadialEdgeBudget 0 k a) (nhds 1) (nhds 0) := by
  have hangleRaw : Tendsto (fun a : ℝ => radialAngle a / Real.pi) (nhds 1)
      (nhds (radialAngle 1 / Real.pi)) :=
    continuous_radialAngle.continuousAt.tendsto.div_const Real.pi
  have hangle : Tendsto (fun a : ℝ => radialAngle a / Real.pi) (nhds 1) (nhds 0) := by
    simpa [radialAngle_one] using hangleRaw
  have hdelta : Tendsto (fun a : ℝ => a - 1) (nhds 1) (nhds 0) := by
    simpa using (continuousAt_id.sub_const (1 : ℝ) :
      Tendsto (fun a : ℝ => a - 1) (nhds 1) (nhds (1 - 1)))
  have hrpow0 : Tendsto (fun t : ℝ => t ^ ((3 : ℝ) / 4)) (nhds 0) (nhds 0) := by
    simpa [Real.zero_rpow (by norm_num : (3 : ℝ) / 4 ≠ 0)] using
      (Real.continuousAt_rpow_const 0 ((3 : ℝ) / 4) (Or.inr (by norm_num))).tendsto
  have hrpow : Tendsto (fun a : ℝ => (a - 1) ^ ((3 : ℝ) / 4))
      (nhds 1) (nhds 0) := hrpow0.comp hdelta
  have hangleTerm := hangle.const_mul (4 * radialProlateDensityEnvelopeConstant)
  have hlinearTerm := hdelta.const_mul
    (radialProlateDensityEnvelopeConstant * profileWeight 0 k)
  have hfirst := (hangleTerm.add hlinearTerm).const_mul (1 / 2)
  have hpowerTerm := hrpow.const_mul
    ((1 / Real.pi) * (4 / 3 * Real.sqrt (Real.sqrt 2) / k))
  have hsum : Tendsto (fun a : ℝ =>
      (1 / 2 : ℝ) *
          (4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
            radialProlateDensityEnvelopeConstant * profileWeight 0 k * (a - 1)) +
        (1 / Real.pi) * (4 / 3 * Real.sqrt (Real.sqrt 2) / k) *
          (a - 1) ^ ((3 : ℝ) / 4)) (nhds 1) (nhds 0) := by
    simpa using hfirst.add hpowerTerm
  have heq : (fun a : ℝ => firstRowRadialEdgeBudget 0 k a) = fun a : ℝ =>
      (1 / 2 : ℝ) *
          (4 * radialProlateDensityEnvelopeConstant * (radialAngle a / Real.pi) +
            radialProlateDensityEnvelopeConstant * profileWeight 0 k * (a - 1)) +
        (1 / Real.pi) * (4 / 3 * Real.sqrt (Real.sqrt 2) / k) *
          (a - 1) ^ ((3 : ℝ) / 4) := by
    funext a
    rw [firstRowRadialEdgeBudget]
    ring
  rw [heq]
  exact hsum

theorem tendsto_firstRowRadialVanishingBudget_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {k a b : ℝ} (hk : 2 ≤ k) (ha : 1 < a) :
    Tendsto (fun i => firstRowRadialVanishingBudget (s i) (c i) k a b)
      l (nhds 0) := by
  have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hcollar : Tendsto (fun i => (1 / 2 : ℝ) * (9 / (8 * c i))) l (nhds 0) := by
    convert hinv.const_mul (9 / 16) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  have hExact :=
    (tendsto_compactExactFirstRowProductError_zero hc hs hs0
      (by linarith : (1 : ℝ) < k) ha).mul_const
    |b - a|
  have hBessel :=
    (tendsto_compactFirstRowProductError_zero hc hs hs0
      (by linarith : (1 : ℝ) < k) ha).mul_const
    |b - a|
  have hsqrt : Tendsto (fun i => Real.sqrt (c i)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hc
  have hk2 : 0 < k ^ 2 := by positivity
  have hden1 : Tendsto (fun i => Real.sqrt (c i) * k ^ 2) l atTop :=
    hsqrt.atTop_mul_const hk2
  have hterm1 : Tendsto (fun i => 170 / (Real.sqrt (c i) * k ^ 2)) l (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden1
  have hka : 1 < k * a := mapsTo_mul_left_Ioi hk ha
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have hAmp : Tendsto (fun i => ampFourthRoot (s i) k a) l
      (nhds (ampFourth 0 a * ampFourth 0 (k * a))) := by
    have hmul := hAa.mul hAka
    apply hmul.congr'
    filter_upwards [hs.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with i hsi
    exact ampFourth_mul_eq_ampFourthRoot hsi.le hk ha
  have h1k : 0 < 1 + k := by linarith
  have hden2 : Tendsto (fun i => c i * (1 + k)) l atTop :=
    hc.atTop_mul_const h1k
  have hnum2 : Tendsto (fun i => 4 * ampFourthRoot (s i) k a) l
      (nhds (4 * (ampFourth 0 a * ampFourth 0 (k * a)))) := hAmp.const_mul 4
  have hterm2 : Tendsto
      (fun i => 4 * ampFourthRoot (s i) k a / (c i * (1 + k))) l (nhds 0) :=
    Tendsto.div_atTop hnum2 hden2
  have hosc := (hterm1.add hterm2).const_mul (1 / Real.pi)
  simpa [firstRowRadialVanishingBudget] using
    ((hcollar.add hExact).add hBessel).add hosc

/-- Full-ray estimate in the two-budget form used by the limiting argument. -/
theorem abs_integral_Ioi_firstRowRadialProduct_budget_le
    {s c k a b : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc5 : 5 ≤ c) (hcOsc : 3 * k ≤ c)
    (ha : 1 < a) (hab : a ≤ b)
    (haCross : dunsterEndpointCrossing c ≤ a)
    (hbStationary : Real.sqrt (1 + 2 / k ^ 2) ≤ b)
    (hcxi : 1 ≤ c * xiEndpointPhase s a)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ x in Ioi (1 : ℝ), firstRowRadialProduct c R k x| ≤
      firstRowRadialEdgeBudget s k a + firstRowRadialVanishingBudget s c k a b +
        4 * radialProlateDensityEnvelopeConstant *
          ∫ x in Ioi b, profileDensity x := by
  have h := abs_integral_Ioi_firstRowRadialProduct_full_le
    hs0 hs1 hk hc5 hcOsc ha hab haCross hbStationary hcxi hR1 hR hDR hode
  refine h.trans_eq ?_
  rw [firstRowRadialEdgeBudget, firstRowRadialVanishingBudget]
  ring

/-- Exact endpoint-normalized first-row radial product cancellation on every fixed compact
exterior interval. -/
theorem tendsto_integral_firstRowRadialProduct
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    {R DR DDR : ι → ℝ → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hR1 : ∀ᶠ i in l, R i 1 = 1)
    (hR : ∀ᶠ i in l, ∀ t, HasDerivAt (R i) (DR i t) t)
    (hDR : ∀ᶠ i in l, ∀ t, HasDerivAt (DR i) (DDR i t) t)
    (hode : ∀ᶠ i in l, ∀ t, (t ^ 2 - 1) * DDR i t + 2 * t * DR i t
      - (s i * c i ^ 2 - c i ^ 2 * t ^ 2) * R i t = 0)
    {k a b : ℝ} (hk : 1 < k) (hab : a ≤ b) (ha : 1 < a) :
    Tendsto (fun i => ∫ x in a..b, firstRowRadialProduct (c i) (R i) k x)
      l (nhds 0) := by
  have hbessel := tendsto_integral_firstRowBesselProduct hc hs hs0 hk hab ha
  have hbudget := tendsto_compactExactFirstRowProductError_zero hc hs hs0 hk ha
  have hmajor : Tendsto
      (fun i => compactExactFirstRowProductError (s i) (c i) k a * |b - a|)
      l (nhds 0) := by
    simpa using hbudget.mul_const |b - a|
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hc5 : ∀ᶠ i in l, 5 ≤ c i := hc.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one hc
  have hcrossa : ∀ᶠ i in l, dunsterEndpointCrossing (c i) ≤ a :=
    (hcross.eventually (eventually_lt_nhds ha)).mono fun _ hi => hi.le
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxi : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    harg.eventually (eventually_ge_atTop 1)
  have hdiff : Tendsto (fun i =>
      (∫ x in a..b, firstRowRadialProduct (c i) (R i) k x) -
        ∫ x in a..b, firstRowBesselProduct (s i) (c i) k x) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
      (Eventually.of_forall fun i => abs_nonneg
        ((∫ x in a..b, firstRowRadialProduct (c i) (R i) k x) -
          ∫ x in a..b, firstRowBesselProduct (s i) (c i) k x))
      (by
        filter_upwards [hs0, hsHalf, hc5, hcrossa, hcxi, hR1, hR, hDR, hode]
          with i hsi0 hsi1 hci hcrossi hcxii hR1i hRi hDRi hodei
        exact abs_intervalIntegral_firstRowRadialProduct_sub_bessel_le
          hsi0 hsi1 hk hci hab ha hcrossi hcxii
            hR1i hRi hDRi hodei)
      hmajor
  simpa only [sub_add_cancel, zero_add] using hdiff.add hbessel

/-- **Full exterior off-diagonal cancellation.**  Every endpoint-normalized exact radial
prolate solution has asymptotically vanishing first-row overlap on the entire exterior ray. -/
theorem tendsto_integral_Ioi_firstRowRadialProduct
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    {R DR DDR : ι → ℝ → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hR1 : ∀ᶠ i in l, R i 1 = 1)
    (hR : ∀ᶠ i in l, ∀ t, HasDerivAt (R i) (DR i t) t)
    (hDR : ∀ᶠ i in l, ∀ t, HasDerivAt (DR i) (DDR i t) t)
    (hode : ∀ᶠ i in l, ∀ t, (t ^ 2 - 1) * DDR i t + 2 * t * DR i t
      - (s i * c i ^ 2 - c i ^ 2 * t ^ 2) * R i t = 0)
    {k : ℝ} (hk : 2 ≤ k) :
    Tendsto (fun i => ∫ x in Ioi (1 : ℝ),
      firstRowRadialProduct (c i) (R i) k x) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hEdgeWithin : Tendsto (fun a : ℝ => firstRowRadialEdgeBudget 0 k a)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    (tendsto_firstRowRadialEdgeBudget_at_one k).mono_left inf_le_left
  have hEdgeSmall : ∀ᶠ a : ℝ in nhdsWithin 1 (Ioi 1),
      firstRowRadialEdgeBudget 0 k a < eps / 3 :=
    hEdgeWithin.eventually (eventually_lt_nhds (by positivity : 0 < eps / 3))
  have hEdgeMem : ∀ᶠ a : ℝ in nhdsWithin 1 (Ioi 1), a ∈ Ioi (1 : ℝ) :=
    self_mem_nhdsWithin
  obtain ⟨a, ha, hEdgeA⟩ := (hEdgeMem.and hEdgeSmall).exists
  have hTailTendsto : Tendsto (fun b : ℝ =>
      4 * radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi b, profileDensity x) atTop (nhds 0) := by
    simpa using tendsto_integral_Ioi_profileDensity_atTop_zero.const_mul
      (4 * radialProlateDensityEnvelopeConstant)
  have hTailSmall : ∀ᶠ b : ℝ in atTop,
      4 * radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi b, profileDensity x < eps / 3 :=
    hTailTendsto.eventually (eventually_lt_nhds (by positivity : 0 < eps / 3))
  have hCutLarge : ∀ᶠ b : ℝ in atTop,
      max a (Real.sqrt (1 + 2 / k ^ 2)) ≤ b :=
    eventually_ge_atTop (max a (Real.sqrt (1 + 2 / k ^ 2)))
  obtain ⟨b, hTailB, hCutB⟩ := (hTailSmall.and hCutLarge).exists
  have hab : a ≤ b := le_max_left _ _ |>.trans hCutB
  have hbStationary : Real.sqrt (1 + 2 / k ^ 2) ≤ b :=
    (le_max_right _ _).trans hCutB
  let T : ℝ := 4 * radialProlateDensityEnvelopeConstant *
    ∫ x in Ioi b, profileDensity x
  have hEdge := tendsto_firstRowRadialEdgeBudget_fixed hs (by linarith : (1 : ℝ) < k) ha
  have hVanish := tendsto_firstRowRadialVanishingBudget_zero hc hs hs0 hk ha
    (b := b)
  have hMajor : Tendsto (fun i =>
      firstRowRadialEdgeBudget (s i) k a +
        firstRowRadialVanishingBudget (s i) (c i) k a b + T) l
      (nhds (firstRowRadialEdgeBudget 0 k a + 0 + T)) := by
    simpa using (hEdge.add hVanish).add tendsto_const_nhds
  have hLimit : firstRowRadialEdgeBudget 0 k a + 0 + T < eps := by
    dsimp [T]
    linarith
  have hMajorSmall : ∀ᶠ i in l,
      firstRowRadialEdgeBudget (s i) k a +
        firstRowRadialVanishingBudget (s i) (c i) k a b + T < eps :=
    hMajor.eventually (eventually_lt_nhds hLimit)
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hc5 : ∀ᶠ i in l, 5 ≤ c i := hc.eventually (eventually_ge_atTop 5)
  have hcOsc : ∀ᶠ i in l, 3 * k ≤ c i :=
    hc.eventually (eventually_ge_atTop (3 * k))
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one hc
  have hcrossA : ∀ᶠ i in l, dunsterEndpointCrossing (c i) ≤ a :=
    (hcross.eventually (eventually_lt_nhds ha)).mono fun _ hi => hi.le
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxi : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    harg.eventually (eventually_ge_atTop 1)
  filter_upwards [hs0, hsHalf, hc5, hcOsc, hcrossA, hcxi, hMajorSmall,
      hR1, hR, hDR, hode]
    with i hsi0 hsi1 hci5 hciOsc hcrossi hcxii hmajori hR1i hRi hDRi hodei
  have hbound := abs_integral_Ioi_firstRowRadialProduct_budget_le
    hsi0 hsi1 hk hci5 hciOsc ha hab hcrossi hbStationary hcxii
      hR1i hRi hDRi hodei
  rw [Real.dist_eq, sub_zero]
  exact hbound.trans_lt (by simpa [T] using hmajori)

/-- **Fixed-ratio full exterior off-diagonal cancellation.**  The artificial uniform restriction
`k ≥ 2` is absent: every fixed strict dilation `k > 1` has asymptotically vanishing overlap. -/
theorem tendsto_integral_Ioi_firstRowRadialProduct_fixedRatio
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    {R DR DDR : ι → ℝ → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    (hR1 : ∀ᶠ i in l, R i 1 = 1)
    (hR : ∀ᶠ i in l, ∀ t, HasDerivAt (R i) (DR i t) t)
    (hDR : ∀ᶠ i in l, ∀ t, HasDerivAt (DR i) (DDR i t) t)
    (hode : ∀ᶠ i in l, ∀ t, (t ^ 2 - 1) * DDR i t + 2 * t * DR i t
      - (s i * c i ^ 2 - c i ^ 2 * t ^ 2) * R i t = 0)
    {k : ℝ} (hk : 1 < k) :
    Tendsto (fun i => ∫ x in Ioi (1 : ℝ),
      firstRowRadialProduct (c i) (R i) k x) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hEdgeWithin : Tendsto (fun a : ℝ => firstRowRadialEdgeBudget 0 k a)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    (tendsto_firstRowRadialEdgeBudget_at_one k).mono_left inf_le_left
  have hEdgeSmall : ∀ᶠ a : ℝ in nhdsWithin 1 (Ioi 1),
      firstRowRadialEdgeBudget 0 k a < eps / 6 :=
    hEdgeWithin.eventually (eventually_lt_nhds (by positivity : 0 < eps / 6))
  have hEdgeMem : ∀ᶠ a : ℝ in nhdsWithin 1 (Ioi 1), a ∈ Ioi (1 : ℝ) :=
    self_mem_nhdsWithin
  obtain ⟨a, ha, hEdgeA⟩ := (hEdgeMem.and hEdgeSmall).exists
  have hTailTendsto : Tendsto (fun b : ℝ =>
      4 * radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi b, profileDensity x) atTop (nhds 0) := by
    simpa using tendsto_integral_Ioi_profileDensity_atTop_zero.const_mul
      (4 * radialProlateDensityEnvelopeConstant)
  have hTailSmall : ∀ᶠ b : ℝ in atTop,
      4 * radialProlateDensityEnvelopeConstant *
        ∫ x in Ioi b, profileDensity x < eps / 3 :=
    hTailTendsto.eventually (eventually_lt_nhds (by positivity : 0 < eps / 3))
  have hCutLarge : ∀ᶠ b : ℝ in atTop, a ≤ b := eventually_ge_atTop a
  obtain ⟨b, hTailB, hab⟩ := (hTailSmall.and hCutLarge).exists
  have hEdge := tendsto_firstRowRadialEdgeBudget_fixed hs hk ha
  have hinv : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hcollar : Tendsto (fun i => (1 / 2 : ℝ) * (9 / (8 * c i))) l (nhds 0) := by
    convert hinv.const_mul (9 / 16) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  have hHeadMajor : Tendsto (fun i =>
      (1 / 2 : ℝ) * (9 / (8 * c i)) + firstRowRadialEdgeBudget (s i) k a)
      l (nhds (firstRowRadialEdgeBudget 0 k a)) := by
    simpa only [zero_add] using hcollar.add hEdge
  have hHeadSmall : ∀ᶠ i in l,
      (1 / 2 : ℝ) * (9 / (8 * c i)) + firstRowRadialEdgeBudget (s i) k a < eps / 3 :=
    hHeadMajor.eventually (eventually_lt_nhds (by linarith))
  have hmid := tendsto_integral_firstRowRadialProduct hc hs hs0 hR1 hR hDR hode hk hab ha
  have hmidNorm : Tendsto (fun i =>
      |∫ x in a..b, firstRowRadialProduct (c i) (R i) k x|) l (nhds 0) := by
    simpa [Real.norm_eq_abs] using hmid.norm
  have hMidSmall : ∀ᶠ i in l,
      |∫ x in a..b, firstRowRadialProduct (c i) (R i) k x| < eps / 3 :=
    hmidNorm.eventually (eventually_lt_nhds (by positivity : 0 < eps / 3))
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hc5 : ∀ᶠ i in l, 5 ≤ c i := hc.eventually (eventually_ge_atTop 5)
  have hcross := tendsto_dunsterEndpointCrossing_comp_atTop_one hc
  have hcrossA : ∀ᶠ i in l, dunsterEndpointCrossing (c i) ≤ a :=
    (hcross.eventually (eventually_lt_nhds ha)).mono fun _ hi => hi.le
  have hcrossK : ∀ᶠ i in l, dunsterEndpointCrossing (c i) ≤ k :=
    (hcross.eventually (eventually_lt_nhds hk)).mono fun _ hi => hi.le
  filter_upwards [hs0, hsHalf, hc5, hcrossA, hcrossK, hHeadSmall, hMidSmall,
      hR1, hR, hDR, hode]
    with i hsi0 hsi1 hci5 hcrossAi hcrossKi hheadSmalli hmidSmalli
      hR1i hRi hDRi hodei
  have hb : 1 < b := ha.trans_le hab
  have hcrossBi : dunsterEndpointCrossing (c i) ≤ b := hcrossAi.trans hab
  have hheadRaw := abs_integral_firstRowRadialProduct_endpoint_le
    hsi0 hsi1 hk hci5 hcrossKi ha hcrossAi hR1i hRi hDRi hodei
  have hhead : |∫ x in (1 : ℝ)..a, firstRowRadialProduct (c i) (R i) k x| ≤
      (1 / 2 : ℝ) * (9 / (8 * c i)) + firstRowRadialEdgeBudget (s i) k a := by
    refine hheadRaw.trans ?_
    rw [firstRowRadialEdgeBudget]
    have hpower : 0 ≤ (1 / Real.pi) *
        (4 / 3 * Real.sqrt (Real.sqrt 2) / k * (a - 1) ^ ((3 : ℝ) / 4)) := by
      exact mul_nonneg (by positivity)
        (mul_nonneg (by positivity) (Real.rpow_nonneg (sub_nonneg.mpr ha.le) _))
    linarith
  have htail := abs_integral_Ioi_firstRowRadialProduct_le
    hsi0 hsi1 hk hci5 hb hcrossBi hR1i hRi hDRi hodei
  have hRc : Continuous (R i) :=
    continuous_iff_continuousAt.mpr fun x => (hRi x).continuousAt
  have hcont : Continuous (firstRowRadialProduct (c i) (R i) k) := by
    unfold firstRowRadialProduct radialProlateRescaledProfile
    fun_prop
  have hIntHead : IntervalIntegrable (firstRowRadialProduct (c i) (R i) k)
      volume (1 : ℝ) a := hcont.intervalIntegrable 1 a
  have hIntMid : IntervalIntegrable (firstRowRadialProduct (c i) (R i) k)
      volume a b := hcont.intervalIntegrable a b
  have hIoc : IntegrableOn (firstRowRadialProduct (c i) (R i) k) (Ioc (1 : ℝ) b) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    exact hcont.intervalIntegrable 1 b
  have hIoi := integrableOn_firstRowRadialProduct_Ioi
    hsi0 hsi1 hk hci5 hb hcrossBi hR1i hRi hDRi hodei
  have hsplitTail : (∫ x in Ioi (1 : ℝ), firstRowRadialProduct (c i) (R i) k x) =
      (∫ x in (1 : ℝ)..b, firstRowRadialProduct (c i) (R i) k x) +
        ∫ x in Ioi b, firstRowRadialProduct (c i) (R i) k x := by
    rw [intervalIntegral.integral_of_le hb.le]
    rw [← Ioc_union_Ioi_eq_Ioi hb.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi
  have hsplitCompact : (∫ x in (1 : ℝ)..b, firstRowRadialProduct (c i) (R i) k x) =
      (∫ x in (1 : ℝ)..a, firstRowRadialProduct (c i) (R i) k x) +
        ∫ x in a..b, firstRowRadialProduct (c i) (R i) k x :=
    (intervalIntegral.integral_add_adjacent_intervals hIntHead hIntMid).symm
  rw [Real.dist_eq, sub_zero, hsplitTail, hsplitCompact]
  calc
    |((∫ x in (1 : ℝ)..a, firstRowRadialProduct (c i) (R i) k x) +
          ∫ x in a..b, firstRowRadialProduct (c i) (R i) k x) +
        ∫ x in Ioi b, firstRowRadialProduct (c i) (R i) k x|
        ≤ |∫ x in (1 : ℝ)..a, firstRowRadialProduct (c i) (R i) k x| +
            |∫ x in a..b, firstRowRadialProduct (c i) (R i) k x| +
              |∫ x in Ioi b, firstRowRadialProduct (c i) (R i) k x| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((1 / 2 : ℝ) * (9 / (8 * c i)) + firstRowRadialEdgeBudget (s i) k a) +
          |∫ x in a..b, firstRowRadialProduct (c i) (R i) k x| +
          4 * radialProlateDensityEnvelopeConstant * ∫ x in Ioi b, profileDensity x :=
      add_le_add (add_le_add hhead le_rfl) htail
    _ < eps := by linarith


end GaloisForLFunctions.RHTower

end
