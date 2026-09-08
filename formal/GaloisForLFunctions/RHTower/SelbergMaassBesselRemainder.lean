import GaloisForLFunctions.RHTower.SelbergMaassTailEnergy
import GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnvelope
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Critical Bessel square remainder for actual complex Maass modes

In physical height the source Bessel response obeys
`B'=B²-k²+1/(4*y²)` and tends to the positive frequency `k`.
For an actual complex Maass coefficient `a`, differentiating the real boundary
current gives `normSq(a'+B*a)-energy = (B*normSq(a))'`.

Parseval and physical tail integrability control both squared coefficient norms
and squared derivative norms. The Bessel envelope then controls the square
remainder. The actual coefficient limit makes the upper current vanish, yielding
an exact infinite-tail energy identity and a nonnegative remainder at every
positive lower height. The actual exceptional constant coefficient and its
height derivative vanish as well.

No compact-profile substitution or Bessel ansatz for the Maass coefficient is used.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassBessel
open SelbergBesselSlope SelbergMaassMean SelbergMaassFourier SelbergMaassParseval
open SelbergMaassFlux SelbergMaassTailEnergy
noncomputable section

/-- Actual critical Bessel outgoing response in physical height. -/
def response (k y : ℝ) : ℝ := (slope (k * y) - 1 / 2) / y

/-- Physical and logarithmic height formulas describe the same source response. -/
theorem response_eq_outgoing {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    response k y = outgoing (Real.log k) (Real.log y) := by
  rw [outgoing_eq, logSlope, Real.exp_add, Real.exp_log hk, Real.exp_log hy]
  rfl

/-- Exact physical-height Riccati equation of the actual critical Bessel response. -/
theorem response_hasDerivAt {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (response k) (response k y ^ 2 - k ^ 2 + 1 / (4 * y ^ 2)) y := by
  have h := ((slope_hasDerivAt (mul_pos hk hy)).comp y ((hasDerivAt_id y).const_mul k)).sub_const (1 / 2)
  apply (h.div (hasDerivAt_id y) hy.ne').congr_deriv
  simp only [id_eq, mul_one, response, Function.comp_apply]
  field_simp
  ring

/-- The actual response lies strictly between the elementary Robin slope and the frequency. -/
theorem response_bounds {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    k - 1 / (2 * y) < response k y ∧ response k y < k := by
  rw [response_eq_outgoing hk hy]
  simpa only [Real.exp_log hk, Real.exp_log hy] using
    SelbergBesselEnvelope.outgoing_bounds (Real.log k) (Real.log y)

/-- The source envelope forces the actual outgoing response to tend to its frequency. -/
theorem response_tendsto {k : ℝ} (hk : 0 < k) : Tendsto (response k) atTop (𝓝 k) := by
  have he : Tendsto (fun y : ℝ => 1 / (2 * y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using he.const_sub k) tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (response_bounds hk hy).1.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (response_bounds hk hy).2.le

/-- A uniform bound for the response on every positive tail. -/
theorem response_abs_bound {k Y y : ℝ} (hk : 0 < k) (hY : 0 < Y) (hy : Y ≤ y) :
    |response k y| ≤ k + 1 / (2 * Y) := by
  obtain ⟨hl, hu⟩ := response_bounds hk (hY.trans_le hy)
  have hfrac : 1 / (2 * y) ≤ 1 / (2 * Y) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    linarith
  rw [abs_le]
  constructor <;> linarith [one_div_pos.mpr (show 0 < 2 * Y by positivity)]

private theorem normSq_hasDerivAt {a : ℝ → ℂ} {v : ℂ} {y : ℝ} (ha : HasDerivAt a v y) :
    HasDerivAt (fun t => Complex.normSq (a t))
      (2 * (v * (starRingEnd ℂ) (a y)).re) y := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ha
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y ha
  convert (hr.mul hr).add (hi.mul hi) using 1 <;> try rfl
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem normSq_add_bound (a b : ℂ) :
    Complex.normSq (a + b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]

/-- The complete real Bessel boundary current of a complex coefficient. -/
def boundaryCurrent (k : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℝ := response k y * Complex.normSq (a y)
/-- The actual nonnegative complex square remaining after Bessel completion. -/
def remainder (k : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℝ :=
  Complex.normSq (deriv a y + (response k y : ℂ) * a y)
/-- Physical nonzero-mode Dirichlet energy minus quarter hyperbolic mass. -/
def energy (k : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℝ :=
  Complex.normSq (deriv a y) + (k ^ 2 - 1 / (4 * y ^ 2)) * Complex.normSq (a y)

private theorem boundaryCurrent_hasDerivAt {k y : ℝ} (hk : 0 < k) (hy : 0 < y)
    {a : ℝ → ℂ} (ha : HasDerivAt a (deriv a y) y) :
    HasDerivAt (boundaryCurrent k a) (remainder k a y - energy k a y) y := by
  apply ((response_hasDerivAt hk hy).mul (normSq_hasDerivAt ha)).congr_deriv
  simp only [remainder, energy, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

private theorem boundaryCurrent_decay {k : ℝ} (hk : 0 < k) {a : ℝ → ℂ}
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto (boundaryCurrent k a) atTop (𝓝 0) := by
  change Tendsto (fun y => response k y * Complex.normSq (a y)) atTop (𝓝 0)
  have hnorm := Complex.continuous_normSq.continuousAt.tendsto.comp ha
  simpa only [Complex.normSq_zero, mul_zero, Function.comp_apply] using (response_tendsto hk).mul hnorm

/-- The positive magnitude of the actual signed Maass Fourier frequency. -/
def modeRate (N : ℕ) (n : ℤ) : ℝ := |signedFrequency (N + 1 : ℕ) n|

/-- Every nonzero integer mode has strictly positive physical frequency. -/
theorem modeRate_pos (N : ℕ) {n : ℤ} (hn : n ≠ 0) : 0 < modeRate N n := by
  apply abs_pos.mpr
  unfold signedFrequency
  apply div_ne_zero ?_ (by positivity)
  apply mul_ne_zero (mul_ne_zero (by linarith) Real.pi_ne_zero)
  exact_mod_cast hn

/-- The squared magnitude is the literal squared signed Fourier frequency. -/
theorem modeRate_sq (N : ℕ) (n : ℤ) : modeRate N n ^ 2 = signedFrequency (N + 1 : ℕ) n ^ 2 := sq_abs _

private theorem mode_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ) :
    ContinuousOn (maassCoefficient N f n) (Ioi 0) := by
  intro y hy
  exact (maassCoefficient_hasDerivAt N f n hy).continuousAt.continuousWithinAt

private theorem mode_deriv_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ) :
    ContinuousOn (deriv (maassCoefficient N f n)) (Ioi 0) := by
  intro y hy
  exact (maassCoefficient_second_hasDerivAt N f n hy).continuousAt.continuousWithinAt

/-- A single actual squared Fourier coefficient is bounded by physical slice mass. -/
theorem mode_normSq_le_mass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ)
    {y : ℝ} (hy : 0 < y) : Complex.normSq (maassCoefficient N f n y) ≤ mass N f y := by
  rw [← (mass_hasSum N f hy).tsum_eq]
  exact (mass_hasSum N f hy).summable.le_tsum n (fun _ _ => Complex.normSq_nonneg _)

/-- A single actual squared height derivative is bounded by physical gradient energy. -/
theorem mode_deriv_normSq_le_gradient (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    Complex.normSq (deriv (maassCoefficient N f n) y) ≤ gradientEnergy N f y := by
  have hs := gradientEnergy_hasSum N f hy
  have hb := hs.summable.le_tsum n
    (fun j _ => add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _))
  rw [hs.tsum_eq] at hb
  exact (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))).trans hb

/-- Actual coefficient squared mass is integrable above every positive height. -/
theorem mode_mass_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (n : ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => Complex.normSq (maassCoefficient N f n y)) (Ioi Y) := by
  apply (mass_tail_integrable N lam f hY).mono'
    ((Complex.continuous_normSq.comp_continuousOn ((mode_continuousOn N f n).mono
      (Ioi_subset_Ioi hY.le))).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mode_normSq_le_mass N f n (hY.trans hy)

/-- Actual coefficient squared derivative has finite tail integral. -/
theorem mode_deriv_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (n : ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => Complex.normSq (deriv (maassCoefficient N f n) y)) (Ioi Y) := by
  apply (gradientEnergy_tail_integrable N lam f hY).mono'
    ((Complex.continuous_normSq.comp_continuousOn ((mode_deriv_continuousOn N f n).mono
      (Ioi_subset_Ioi hY.le))).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  exact mode_deriv_normSq_le_gradient N f n (hY.trans hy)

/-- Actual modal hyperbolic mass is integrable on every positive tail. -/
theorem mode_hyperbolicMass_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (n : ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => Complex.normSq (maassCoefficient N f n y) / y ^ 2) (Ioi Y) := by
  have hc := (Complex.continuous_normSq.comp_continuousOn (mode_continuousOn N f n)).div
    (continuous_id.pow 2).continuousOn (fun y hy => (sq_pos_of_pos (show 0 < y from hy)).ne')
  apply (hyperbolicMass_tail_integrable N lam f hY).mono'
    ((hc.mono (Ioi_subset_Ioi hY.le)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change ‖Complex.normSq (maassCoefficient N f n y) / y ^ 2‖ ≤ mass N f y / y ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
  exact div_le_div_of_nonneg_right (mode_normSq_le_mass N f n (hY.trans hy)) (sq_nonneg _)

/-- The literal signed modal quarter-energy is integrable on the infinite tail. -/
theorem mode_energy_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (n : ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (energy (modeRate N n) (maassCoefficient N f n)) (Ioi Y) := by
  apply (((mode_deriv_integrable N lam f n hY).add
    ((mode_mass_integrable N lam f n hY).const_mul (modeRate N n ^ 2))).sub
    ((mode_hyperbolicMass_integrable N lam f n hY).const_mul (1 / 4 : ℝ))).congr
  filter_upwards with y
  simp only [Pi.sub_apply, Pi.add_apply, energy]
  ring

private theorem response_continuousOn {k : ℝ} (hk : 0 < k) :
    ContinuousOn (response k) (Ioi 0) :=
  fun _ hy => (response_hasDerivAt hk hy).continuousAt.continuousWithinAt

/-- The actual noncompact complex coefficient has an integrable Bessel square remainder. -/
theorem mode_remainder_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (n : ℤ) (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (remainder (modeRate N n) (maassCoefficient N f n)) (Ioi Y) := by
  let C := modeRate N n + 1 / (2 * Y)
  have hc := Complex.continuous_normSq.comp_continuousOn
    ((mode_deriv_continuousOn N f n).add
      ((Complex.continuous_ofReal.comp_continuousOn (response_continuousOn (modeRate_pos N hn))).mul
        (mode_continuousOn N f n)))
  apply (((mode_deriv_integrable N lam f n hY).const_mul 2).add
    ((mode_mass_integrable N lam f n hY).const_mul (2 * C ^ 2))).mono'
      ((hc.mono (Ioi_subset_Ioi hY.le)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change ‖remainder (modeRate N n) (maassCoefficient N f n) y‖ ≤ _
  rw [remainder, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hB := response_abs_bound (modeRate_pos N hn) hY hy.le
  have hB2 : response (modeRate N n) y ^ 2 ≤ C ^ 2 := by
    simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) hB
  have hb := normSq_add_bound (deriv (maassCoefficient N f n) y)
    ((response (modeRate N n) y : ℂ) * maassCoefficient N f n y)
  rw [Complex.normSq_mul, Complex.normSq_ofReal] at hb
  have hh := mul_le_mul_of_nonneg_right hB2 (Complex.normSq_nonneg (maassCoefficient N f n y))
  change _ ≤ 2 * Complex.normSq (deriv (maassCoefficient N f n) y) +
    (2 * C ^ 2) * Complex.normSq (maassCoefficient N f n y)
  nlinarith

/-- The source coefficient limit and Bessel envelope kill the upper boundary current. -/
theorem mode_boundaryCurrent_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (n : ℤ) (hn : n ≠ 0) :
    Tendsto (boundaryCurrent (modeRate N n) (maassCoefficient N f n)) atTop (𝓝 0) :=
  boundaryCurrent_decay (modeRate_pos N hn) (maassCoefficient_decay N f n)

/-- Exact infinite-tail Bessel square decomposition for an actual nonzero complex Maass mode. -/
theorem mode_boundary_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (n : ℤ) (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    (∫ y in Ioi Y, energy (modeRate N n) (maassCoefficient N f n) y) =
      (∫ y in Ioi Y, remainder (modeRate N n) (maassCoefficient N f n) y) +
        response (modeRate N n) Y * Complex.normSq (maassCoefficient N f n Y) := by
  have hR := mode_remainder_integrable N lam f n hn hY
  have hE := mode_energy_integrable N lam f n hY
  have hd := fun y (hy : y ∈ Ici Y) => boundaryCurrent_hasDerivAt (modeRate_pos N hn)
    (hY.trans_le hy) (maassCoefficient_hasDerivAt N f n (hY.trans_le hy))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hR.sub hE)
    (mode_boundaryCurrent_decay N f n hn)
  rw [integral_sub hR hE, zero_sub] at h
  change _ - _ = -(response (modeRate N n) Y * Complex.normSq (maassCoefficient N f n Y)) at h
  linarith

/-- The actual outgoing Bessel coefficient bounds the full signed modal tail energy. -/
theorem mode_boundary_lower_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (n : ℤ) (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    response (modeRate N n) Y * Complex.normSq (maassCoefficient N f n Y) ≤
      ∫ y in Ioi Y, energy (modeRate N n) (maassCoefficient N f n) y := by
  rw [mode_boundary_identity N lam f n hn hY]
  exact le_add_of_nonneg_left (integral_nonneg (fun _ => Complex.normSq_nonneg _))

/-- The completed energy is exactly the existing physical Parseval modal summand. -/
theorem mode_energy_eq_modalQuarter (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ) (y : ℝ) :
    energy (modeRate N n) (maassCoefficient N f n) y = modalQuarter N f y n := by
  unfold energy modalQuarter
  rw [modeRate_sq]


/-- The actual exceptional Maass constant coefficient vanishes at every positive height. -/
theorem constant_mode_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) : maassCoefficient N f 0 y = 0 := by
  rw [maassCoefficient_zero]
  have hp : 0 < (point 0 y).im := by simpa [point] using hy
  have h := SelbergEulerDecay.maassMean_subquarter_zero N lam f ⟨point 0 y, hp⟩
  have hm : maassMean N f y = 0 := by simpa [UpperHalfPlane.im, point] using h
  rw [hm, mul_zero]

/-- Local vanishing forces the actual constant coefficient height derivative to vanish. -/
theorem constant_mode_deriv_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) : deriv (maassCoefficient N f 0) y = 0 := by
  apply HasDerivAt.deriv
  apply (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact constant_mode_zero N lam f ht

/-- The actual exceptional constant channel contributes zero physical quarter-energy. -/
theorem constant_mode_energy_zero (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) : energy (modeRate N 0) (maassCoefficient N f 0) y = 0 := by
  rw [energy, constant_mode_deriv_zero N lam f hy, constant_mode_zero N lam f hy,
    Complex.normSq_zero, mul_zero, add_zero]

end
end GaloisForLFunctions.RHTower.SelbergMaassBessel
