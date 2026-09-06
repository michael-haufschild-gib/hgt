import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleFirstJets
/-!
# Square-root Chebyshev error at stationary actual even poles

Positive integral primitives bound the complete Gamma boundary slope. Exact
arithmetic cancellation then bounds the diagonal jet uniformly by exp(a).
Even stationarity gives the same scale for the actual pointwise Chebyshev error,
including every interior minimum of an actual prime-power gap. This estimate
selects stationary locations; it does not assert the energy value is positive.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace RHTower

/-- The totalized boundary logarithm is nonnegative on the admitted half-line. -/
theorem ccmGammaPoleBoundaryLog_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ccmGammaPoleBoundaryLog t := by
  unfold ccmGammaPoleBoundaryLog
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith [Real.exp_pos (-t)]))

/-- Doubling the positive boundary distance decreases its logarithmic mass. -/
theorem ccmGammaPoleBoundaryLog_two_mul_le {t : ℝ} (ht : 0 ≤ t) :
    ccmGammaPoleBoundaryLog (2*t) ≤ ccmGammaPoleBoundaryLog t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  unfold ccmGammaPoleBoundaryLog
  have hp : 0 < 1-Real.exp (-t) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : Real.exp (-(2*t)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  exact neg_le_neg (Real.log_le_log hp (by linarith))

/-- An elementary uniform bound for the boundary logarithm away from its endpoint. -/
theorem ccmGammaPoleBoundaryLog_le_one {t : ℝ} (ht : 2 ≤ t) :
    ccmGammaPoleBoundaryLog t ≤ 1 := by
  have he := Real.add_one_le_exp t
  have hi : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hm : Real.exp (-t) ≤ 1/2 := by nlinarith [Real.exp_pos (-t)]
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<1/2) (show 1/2≤1-Real.exp (-t) by linarith)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hlog : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [hlog] at hl
  unfold ccmGammaPoleBoundaryLog
  linarith

/-- The exact weighted Gamma boundary slope has a uniform exponential allowance. -/
theorem abs_ccmGammaPoleSelfBoundarySlope_le (a : SuzukiPositiveAperture) (ha : 2 ≤ a.1) :
    |ccmGammaPoleSelfBoundarySlope a.1| ≤ (2*Real.log 2+Real.pi+5)*Real.exp a.1 := by
  let F := Real.exp a.1/2 * ∫ t in 0..2*a.1, Real.exp (-t)*ccmGammaPoleBoundaryLog (2*t)
  let G := Real.exp (-a.1) * ∫ t in 0..2*a.1,
    Real.exp t*(ccmGammaPoleBoundaryLog t-ccmGammaPoleBoundaryLog (2*t)/2)
  have hF : 0 ≤ F := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (by linarith : 0≤2*a.1)
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (ccmGammaPoleBoundaryLog_nonneg (by linarith [ht.1]))
  have hG : 0 ≤ G := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (by linarith : 0≤2*a.1)
    intro t ht
    apply mul_nonneg (Real.exp_pos _).le
    have h1 := ccmGammaPoleBoundaryLog_nonneg ht.1
    have h2 := ccmGammaPoleBoundaryLog_two_mul_le ht.1
    linarith
  have hB : F+G ≤ (2*Real.log 2+Real.pi+1)*Real.exp a.1 := by
    change ccmGammaPoleSelfBoundaryPrimitive a.1 ≤ _
    rw [← ccmGammaPoleSelfBoundaryMass_eq_primitive]
    exact ccmGammaPoleSelfBoundaryMass_le a
  have h2 := ccmGammaPoleBoundaryLog_le_one (show 2≤2*a.1 by linarith)
  have h4 := ccmGammaPoleBoundaryLog_le_one (show 2≤4*a.1 by linarith)
  have h20 := ccmGammaPoleBoundaryLog_nonneg (show 0≤2*a.1 by linarith)
  have h40 := ccmGammaPoleBoundaryLog_nonneg (show 0≤4*a.1 by linarith)
  have he := Real.exp_pos a.1
  have hm := Real.exp_pos (-a.1)
  have hem : Real.exp (-a.1) ≤ Real.exp a.1 := Real.exp_le_exp.mpr (by linarith)
  change |F-G+Real.exp (-a.1)*ccmGammaPoleBoundaryLog (4*a.1)+
    2*Real.exp a.1*(ccmGammaPoleBoundaryLog (2*a.1)-ccmGammaPoleBoundaryLog (4*a.1)/2)| ≤ _
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left h2 he.le,
    mul_le_mul_of_nonneg_left h4 he.le,mul_le_mul_of_nonneg_left h4 hm.le,
    mul_nonneg hm.le h40,mul_nonneg he.le h20]

/-- Explicit uniform allowance for the normalized diagonal first jet. -/
def ccmWeilPoleUniformSlopeBound : ℝ :=
  2*|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+
    (2*Real.log 2+Real.pi+1)+12+2*(Real.log 4+5)+2*(Real.log 4+4)

theorem ccmWeilPoleUniformSlopeBound_pos : 0 < ccmWeilPoleUniformSlopeBound := by
  unfold ccmWeilPoleUniformSlopeBound
  positivity

/-- The actual diagonal jet is unconditionally of square-root size for radius at least two. -/
theorem abs_ccmWeilPoleDiagonalSlope_le (a : SuzukiPositiveAperture) (ha : 2 ≤ a.1) :
    |ccmWeilPoleDiagonalSlope a a.1| ≤ ccmWeilPoleUniformSlopeBound*Real.exp a.1 := by
  have he := Real.exp_pos a.1
  have hm := Real.exp_pos (-a.1)
  have he1 : 1≤Real.exp a.1 := Real.one_le_exp a.2.le
  have hm1 : Real.exp (-a.1)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hinv : Real.exp a.1*Real.exp (-a.1)=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have ham : a.1*Real.exp (-a.1)≤1 := by
    have hae : a.1≤Real.exp a.1 := by linarith [Real.add_one_le_exp a.1]
    have hh := mul_le_mul_of_nonneg_right hae hm.le
    rwa [hinv] at hh
  have hc : Real.cosh a.1 ≤ Real.exp a.1 := by rw [Real.cosh_eq]; linarith
  have hk : |2*(-Real.eulerMascheroniConstant-Real.log (2*Real.pi))*Real.cosh a.1| ≤
      2*|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)| *Real.exp a.1 := by
    rw [abs_mul,abs_mul,abs_of_pos (Real.cosh_pos _)]
    norm_num
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hterm : |(2*a.1-3)*Real.exp (-a.1)| ≤ 5*Real.exp a.1 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hEM := abs_ccmReciprocalMangoldtError_le (show 0≤2*a.1 by linarith)
  have hM : |(3-2*ccmReciprocalMangoldtError (2*a.1))*Real.exp a.1| ≤
      (3+2*(Real.log 4+5))*Real.exp a.1 := by
    obtain ⟨hL,hR⟩ := abs_le.mp hEM
    apply abs_le.mpr
    constructor <;> nlinarith
  have hP0 : 0≤2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) := by
    exact mul_nonneg (by positivity) (Chebyshev.psi_nonneg _)
  have hP : 2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)) ≤
      2*(Real.log 4+4)*Real.exp a.1 := by
    have hp := Chebyshev.psi_le_const_mul_self (Real.exp_pos (2*a.1)).le
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.exp (-a.1) by positivity)
    have heq : Real.exp (-a.1)*Real.exp (2*a.1)=Real.exp a.1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ 2*Real.exp (-a.1)*((Real.log 4+4)*Real.exp (2*a.1)) := hh
      _ = _ := by rw [show 2*Real.exp (-a.1)*((Real.log 4+4)*Real.exp (2*a.1)) =
        2*(Real.log 4+4)*(Real.exp (-a.1)*Real.exp (2*a.1)) by ring,heq]
  obtain ⟨hBL,hBR⟩ := abs_le.mp (abs_ccmGammaPoleSelfBoundarySlope_le a ha)
  obtain ⟨hkL,hkR⟩ := abs_le.mp hk
  obtain ⟨hML,hMR⟩ := abs_le.mp hM
  obtain ⟨htL,htR⟩ := abs_le.mp hterm
  rw [ccmWeilPoleDiagonalSlope_self_eq_error,ccmWeilPoleUniformSlopeBound]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A fixed square-root allowance for pointwise prime error at stationary even poles. -/
def ccmWeilEvenStationaryPrimeErrorBound : ℝ :=
  ccmWeilPoleUniformSlopeBound/2+|-Real.eulerMascheroniConstant-Real.log (2*Real.pi)|+
    (Real.log 4+5)+2

theorem ccmWeilEvenStationaryPrimeErrorBound_pos : 0 < ccmWeilEvenStationaryPrimeErrorBound := by
  unfold ccmWeilEvenStationaryPrimeErrorBound
  have := ccmWeilPoleUniformSlopeBound_pos
  positivity

/-- Every stationary even pole above radius two has square-root pointwise Chebyshev error. -/
theorem abs_prime_error_le_of_ccmWeilEvenPole_stationary (a : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hstat : deriv (ccmWeilEvenPoleChamber a) a.1 = 0) :
    |Real.exp (2*a.1)-Chebyshev.psi (Real.exp (2*a.1))| ≤
      ccmWeilEvenStationaryPrimeErrorBound*Real.exp a.1 := by
  obtain ⟨hAL,hAR⟩ := abs_le.mp (abs_ccmWeilPoleDiagonalSlope_le a ha)
  obtain ⟨hML,hMR⟩ := abs_le.mp (abs_ccmReciprocalMangoldtError_le (show 0≤2*a.1 by linarith))
  have hL := ccmGammaPoleBoundaryLog_le_one (show 2≤2*a.1 by linarith)
  have hL0 := ccmGammaPoleBoundaryLog_nonneg (show 0≤2*a.1 by linarith)
  have hE := Real.exp_pos (-(2*a.1))
  have hE1 : Real.exp (-(2*a.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he1 : 1 ≤ Real.exp a.1 := Real.one_le_exp a.2.le
  have hκL := neg_abs_le (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))
  have hκR := le_abs_self (-Real.eulerMascheroniConstant-Real.log (2*Real.pi))
  have hκ := mul_le_mul_of_nonneg_left he1 (abs_nonneg (-Real.eulerMascheroniConstant-Real.log (2*Real.pi)))
  have hM := mul_le_mul_of_nonneg_left he1 (show 0≤Real.log 4+5 by positivity)
  rw [ccmWeilEvenPole_stationary_prime_error a hstat,ccmWeilEvenStationaryPrimeErrorBound]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The square-root error bound applies at every interior actual even-gap minimum above radius two. -/
theorem abs_prime_error_le_at_ccmWeilEvenPole_gap_minimum (a b c : SuzukiPositiveAperture)
    (ha : 2 ≤ a.1) (hc : c.1 ∈ Ioo a.1 b.1)
    (hfree : ∀ n : ℕ, 2 ≤ n → a.1 < Real.log n/2 → Real.log n/2 < b.1 → ¬IsPrimePow n)
    (hmin : ∀ d : SuzukiPositiveAperture, d.1 ∈ Icc a.1 b.1 →
      ccmRestrictedWeilSourceQuadratic c (ccmPolarParityFormVector c 1) ≤
        ccmRestrictedWeilSourceQuadratic d (ccmPolarParityFormVector d 1)) :
    |Real.exp (2*c.1)-Chebyshev.psi (Real.exp (2*c.1))| ≤
      ccmWeilEvenStationaryPrimeErrorBound*Real.exp c.1 := by
  have hstat := ccmWeilEvenPole_gap_minimum_stationary a b c hc hfree hmin
  obtain ⟨hA,hC⟩ := ccmWeilPoleChambers_eq_on_primePower_gap a b c ⟨hc.1.le,hc.2⟩ hfree
  have heq : ccmWeilEvenPoleChamber a = ccmWeilEvenPoleChamber c := by
    unfold ccmWeilEvenPoleChamber
    rw [hA,hC]
  rw [heq] at hstat
  exact abs_prime_error_le_of_ccmWeilEvenPole_stationary c (ha.trans hc.1.le) hstat

end RHTower
