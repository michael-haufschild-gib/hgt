import GaloisForLFunctions.RHTower.XiPhysicalPrimeAperturePNTDecay

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Complex theta-Abel response of one exponential normalized-discrepancy mode. -/
def xiPhysicalThetaAbelExponentialModeResponse
    (c m u : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * ((m + c - u : ℝ) : ℂ)) -
    Complex.exp (z * ((m - u : ℝ) : ℂ)) +
      ∫ h : ℝ in (m - u)..(m + c - u), Complex.exp (z * (h : ℂ))

theorem intervalIntegral_cexp_mul_of_ne_zero
    {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
    (∫ h : ℝ in a..b, Complex.exp (z * (h : ℂ))) =
      (Complex.exp (z * (b : ℂ)) - Complex.exp (z * (a : ℂ))) / z := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun h : ℝ => Complex.exp (z * (h : ℂ)))
        (z * Complex.exp (z * (x : ℂ))) x := by
    intro x
    have hlin : HasDerivAt (fun h : ℝ => z * (h : ℂ)) z x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z
    simpa [mul_comm] using hlin.cexp
  have hprim : ∀ x : ℝ,
      HasDerivAt (fun h : ℝ => Complex.exp (z * (h : ℂ)) / z)
        (Complex.exp (z * (x : ℂ))) x := by
    intro x
    have h := (hderiv x).div_const z
    have hcancel : z * Complex.exp (z * (x : ℂ)) / z =
        Complex.exp (z * (x : ℂ)) := by field_simp
    rw [hcancel] at h
    exact h
  have hcont : ContinuousOn (fun h : ℝ => Complex.exp (z * (h : ℂ)))
      (Set.uIcc a b) :=
    (by fun_prop : Continuous (fun h : ℝ => Complex.exp (z * (h : ℂ)))).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hprim x)
    hcont.intervalIntegrable, sub_div]

/-- Abel transport restores factor `(z+1)/z` on physical window multiplier. -/
theorem xiPhysicalThetaAbelExponentialModeResponse_eq
    {z : ℂ} (hz : z ≠ 0) (c m u : ℝ) :
    xiPhysicalThetaAbelExponentialModeResponse c m u z =
      Complex.exp (z * ((m - u : ℝ) : ℂ)) *
        xiPhysicalLogWindowModeMultiplier c z * ((z + 1) / z) := by
  rw [xiPhysicalThetaAbelExponentialModeResponse,
    intervalIntegral_cexp_mul_of_ne_zero hz]
  rw [xiPhysicalLogWindowModeMultiplier]
  have hsplit : z * ((m + c - u : ℝ) : ℂ) =
      z * ((m - u : ℝ) : ℂ) + (c : ℂ) * z := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  field_simp [hz]

/-- Squared response norm factors into mode multiplier, Abel restoration, and exact spectral
height rate. -/
theorem norm_sq_xiPhysicalThetaAbelExponentialModeResponse_eq
    {z : ℂ} (hz : z ≠ 0) (c m u : ℝ) :
    ‖xiPhysicalThetaAbelExponentialModeResponse c m u z‖ ^ 2 =
      Real.exp (2 * z.re * (m - u)) *
        ‖xiPhysicalLogWindowModeMultiplier c z‖ ^ 2 * ‖(z + 1) / z‖ ^ 2 := by
  rw [xiPhysicalThetaAbelExponentialModeResponse_eq hz, norm_mul,
    norm_mul, Complex.norm_exp]
  have hre : (z * ((m - u : ℝ) : ℂ)).re = z.re * (m - u) := by
    simp
  rw [hre]
  have hexp : Real.exp (z.re * (m - u)) ^ 2 =
      Real.exp (2 * z.re * (m - u)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, hexp]

theorem intervalIntegral_rexp_mul_of_ne_zero
    {a : ℝ} (ha : a ≠ 0) (s t : ℝ) :
    (∫ x : ℝ in s..t, Real.exp (a * x)) =
      (Real.exp (a * t) - Real.exp (a * s)) / a := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (a * y) / a) (Real.exp (a * x)) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h := hlin.exp.div_const a
    have hcancel : Real.exp (a * x) * a / a = Real.exp (a * x) := by
      field_simp
    rw [hcancel] at h
    exact h
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (a * x)) (Set.uIcc s t) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x)
    hcont.intervalIntegrable, sub_div]

/-- Exact raw aperture `L²` mass of one theta-Abel exponential mode. -/
theorem intervalIntegral_norm_sq_xiPhysicalThetaAbelExponentialModeResponse_eq
    {z : ℂ} (hzre : z.re < 0) (c m A : ℝ) :
    (∫ u : ℝ in 0..A, ‖xiPhysicalThetaAbelExponentialModeResponse c m u z‖ ^ 2) =
      Real.exp (2 * z.re * m) *
        ‖xiPhysicalLogWindowModeMultiplier c z‖ ^ 2 * ‖(z + 1) / z‖ ^ 2 *
          ((Real.exp (-2 * z.re * A) - 1) / (-2 * z.re)) := by
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  rw [intervalIntegral.integral_congr (fun u hu =>
    norm_sq_xiPhysicalThetaAbelExponentialModeResponse_eq hz c m u)]
  have hpoint : ∀ u : ℝ,
      Real.exp (2 * z.re * (m - u)) *
          ‖xiPhysicalLogWindowModeMultiplier c z‖ ^ 2 * ‖(z + 1) / z‖ ^ 2 =
        (Real.exp (2 * z.re * m) *
          ‖xiPhysicalLogWindowModeMultiplier c z‖ ^ 2 * ‖(z + 1) / z‖ ^ 2) *
            Real.exp ((-2 * z.re) * u) := by
    intro u
    rw [show 2 * z.re * (m - u) = 2 * z.re * m + (-2 * z.re) * u by ring,
      Real.exp_add]
    ring
  rw [intervalIntegral.integral_congr (fun u hu => hpoint u),
    intervalIntegral.integral_const_mul,
    intervalIntegral_rexp_mul_of_ne_zero (by linarith : -2 * z.re ≠ 0)]
  simp

/-- Raw aperture `L²` mass of one exponential theta-Abel mode. -/
def xiPhysicalThetaAbelExponentialModeRawEnergy
    (A c m : ℝ) (z : ℂ) : ℝ :=
  ∫ u : ℝ in 0..A, ‖xiPhysicalThetaAbelExponentialModeResponse c m u z‖ ^ 2

/-- Height-independent coefficient in the exact raw-energy factorization. -/
def xiPhysicalThetaAbelExponentialModePrefactor
    (A c : ℝ) (z : ℂ) : ℝ :=
  ‖xiPhysicalLogWindowModeMultiplier c z‖ ^ 2 * ‖(z + 1) / z‖ ^ 2 *
    ((Real.exp (-2 * z.re * A) - 1) / (-2 * z.re))

/-- Exact height factorization of a one-mode raw aperture energy. -/
theorem xiPhysicalThetaAbelExponentialModeRawEnergy_eq
    {z : ℂ} (hzre : z.re < 0) (A c m : ℝ) :
    xiPhysicalThetaAbelExponentialModeRawEnergy A c m z =
      Real.exp (2 * z.re * m) *
        xiPhysicalThetaAbelExponentialModePrefactor A c z := by
  rw [xiPhysicalThetaAbelExponentialModeRawEnergy,
    intervalIntegral_norm_sq_xiPhysicalThetaAbelExponentialModeResponse_eq hzre,
    xiPhysicalThetaAbelExponentialModePrefactor]
  ring

/-- The exact one-mode coefficient is strictly positive for a genuine aperture and every
nontrivial-zero-shaped exponent except the Abel-cancelled mode `z = -1`. -/
theorem xiPhysicalThetaAbelExponentialModePrefactor_pos
    {A c : ℝ} {z : ℂ} (hA : 0 < A) (hc : 0 < c) (hzre : z.re < 0)
    (hznegOne : z ≠ -1) :
    0 < xiPhysicalThetaAbelExponentialModePrefactor A c z := by
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hmult : xiPhysicalLogWindowModeMultiplier c z ≠ 0 :=
    xiPhysicalLogWindowModeMultiplier_ne_zero hc hzre
  have hnum : z + 1 ≠ 0 := by
    intro h
    apply hznegOne
    calc
      z = (z + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  have hratio : (z + 1) / z ≠ 0 := div_ne_zero hnum hz
  have harg : 0 < -2 * z.re * A := mul_pos (by linarith) hA
  have hquot : 0 < (Real.exp (-2 * z.re * A) - 1) / (-2 * z.re) :=
    div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr harg)) (by linarith)
  rw [xiPhysicalThetaAbelExponentialModePrefactor]
  exact mul_pos
    (mul_pos (pow_pos (norm_pos_iff.mpr hmult) 2)
      (pow_pos (norm_pos_iff.mpr hratio) 2)) hquot

/-- Below the critical mode line `Re z = -1/2`, exponentially renormalized raw energy dies. -/
theorem tendsto_exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_zero
    {A c : ℝ} {z : ℂ} (hzre : z.re < -(1 / 2 : ℝ)) :
    Tendsto
      (fun m : ℝ => Real.exp m *
        xiPhysicalThetaAbelExponentialModeRawEnergy A c m z)
      atTop (𝓝 0) := by
  have hzre0 : z.re < 0 := by linarith
  have hgap : 0 < -(1 + 2 * z.re) := by linarith
  have hbase := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hgap)
  have hscaled : Tendsto
      (fun m : ℝ => xiPhysicalThetaAbelExponentialModePrefactor A c z *
        Real.exp (-(-(1 + 2 * z.re) * m))) atTop (𝓝 0) := by
    simpa using hbase.const_mul
      (xiPhysicalThetaAbelExponentialModePrefactor A c z)
  refine hscaled.congr' ?_
  filter_upwards with m
  rw [xiPhysicalThetaAbelExponentialModeRawEnergy_eq hzre0]
  have hexp : Real.exp m * Real.exp (2 * z.re * m) =
      Real.exp (-(-(1 + 2 * z.re) * m)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp m *
      (Real.exp (2 * z.re * m) *
        xiPhysicalThetaAbelExponentialModePrefactor A c z) =
      (Real.exp m * Real.exp (2 * z.re * m)) *
        xiPhysicalThetaAbelExponentialModePrefactor A c z by ring,
    hexp]
  ring

/-- On the critical mode line, exponentially renormalized raw energy is exactly constant. -/
theorem exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_eq_prefactor
    {A c m : ℝ} {z : ℂ} (hzre : z.re = -(1 / 2 : ℝ)) :
    Real.exp m * xiPhysicalThetaAbelExponentialModeRawEnergy A c m z =
      xiPhysicalThetaAbelExponentialModePrefactor A c z := by
  have hzre0 : z.re < 0 := by rw [hzre]; norm_num
  rw [xiPhysicalThetaAbelExponentialModeRawEnergy_eq hzre0, hzre]
  have hexp : Real.exp m * Real.exp (2 * (-(1 / 2 : ℝ)) * m) = 1 := by
    rw [show 2 * (-(1 / 2 : ℝ)) * m = -m by ring, ← Real.exp_add]
    simp
  rw [← mul_assoc, hexp, one_mul]

/-- Above the critical mode line, exponentially renormalized raw energy beats every real power.
This is the sharp rate wall for termwise-positive theta-Abel providers. -/
theorem tendsto_exp_mul_xiPhysicalThetaAbelExponentialModeRawEnergy_div_rpow_atTop
    {A c : ℝ} {z : ℂ} (hA : 0 < A) (hc : 0 < c)
    (hzre0 : z.re < 0) (hzwall : -(1 / 2 : ℝ) < z.re)
    (hznegOne : z ≠ -1) (p : ℝ) :
    Tendsto
      (fun m : ℝ =>
        Real.exp m * xiPhysicalThetaAbelExponentialModeRawEnergy A c m z / m ^ p)
      atTop atTop := by
  have hgap : 0 < 1 + 2 * z.re := by linarith
  have hpref : 0 < xiPhysicalThetaAbelExponentialModePrefactor A c z :=
    xiPhysicalThetaAbelExponentialModePrefactor_pos hA hc hzre0 hznegOne
  have hbase := tendsto_exp_mul_div_rpow_atTop p (1 + 2 * z.re) hgap
  have hscaled := hbase.const_mul_atTop hpref
  refine hscaled.congr' ?_
  filter_upwards with m
  rw [xiPhysicalThetaAbelExponentialModeRawEnergy_eq hzre0]
  have hexp : Real.exp m * Real.exp (2 * z.re * m) =
      Real.exp ((1 + 2 * z.re) * m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp m *
      (Real.exp (2 * z.re * m) *
        xiPhysicalThetaAbelExponentialModePrefactor A c z) =
      (Real.exp m * Real.exp (2 * z.re * m)) *
        xiPhysicalThetaAbelExponentialModePrefactor A c z by ring,
    hexp]
  ring

end

end RHTower
