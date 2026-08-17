import GaloisForLFunctions.RHTower.XiMassJetAnalyticTest
import GaloisForLFunctions.RHTower.XiMassBesselDerivativeEnvelope
import GaloisForLFunctions.HTGeometry.PolynomialSpectralWeight

/-!
# The jet integrand on the real axis

The strip Fourier transform of the jet-modified test is an ordinary Lebesgue integral over the real
line, whose integrand is a fixed positive polynomial in the spatial frequency times the mass test
times a unimodular phase.  Every majorant needed to differentiate under the integral sign — the
integrand itself and each of its two frequency derivatives — is a polynomial times the strip
exponential, hence integrable.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- The jet integrand: the `k`-th power of the dispersion polynomial against the mass test and the
Fourier phase. -/
def xiMassJetIntegrand (a : ℝ) (k : ℕ) (τ : ℂ) (h : ℝ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k * xiMassAnalyticTest a τ (x : ℂ) *
    Complex.exp (-(I * (h : ℂ) * (x : ℂ)))

theorem norm_jetPoly_ofReal (a : ℝ) (k : ℕ) (x : ℝ) :
    ‖((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k‖ = (x ^ 2 + 4 * a ^ 4) ^ k := by
  have hcast : ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

theorem norm_xiMassJetIntegrand_le {a : ℝ} (ha : 0 < a) (k : ℕ) {τ : ℂ} (hτ : 0 ≤ τ.re)
    (h x : ℝ) :
    ‖xiMassJetIntegrand a k τ h x‖ ≤ (x ^ 2 + 4 * a ^ 4) ^ k * Real.exp (-(τ.re * |x|)) := by
  have hmem : (x : ℂ) ∈ xiMassStrip a := by
    change |((x : ℂ)).im| < a
    simpa using ha
  have hg := norm_xiMassAnalyticTest_le ha hτ hmem
  have hg' : ‖xiMassAnalyticTest a τ (x : ℂ)‖ ≤ Real.exp (-(τ.re * |x|)) := by
    refine hg.trans (le_of_eq ?_)
    congr 1
    simp
  have hphase : ‖Complex.exp (-(I * (h : ℂ) * (x : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (-(I * (h : ℂ) * (x : ℂ))).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero]
  rw [xiMassJetIntegrand, norm_mul, norm_mul, hphase, mul_one, norm_jetPoly_ofReal]
  exact mul_le_mul_of_nonneg_left hg' (by positivity)

/-- A polynomial in `|x|` of any degree is absorbed by half of the strip exponential. -/
theorem integrable_polyAbs_mul_exp_neg_abs (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => (1 + |x|) ^ m * Real.exp (-(r * |x|))) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (half_pos hr)).const_mul
      ((Nat.factorial m : ℝ) / (r / 2) ^ m * Real.exp (r / 2)))
    (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hnn : (0 : ℝ) ≤ (1 + |x|) ^ m * Real.exp (-(r * |x|)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have hgrow := HTGeometry.one_add_pow_le_const_mul_exp (abs_nonneg x) (half_pos hr) m
  have hcol : Real.exp (r / 2 * |x|) * Real.exp (-(r * |x|)) = Real.exp (-(r / 2 * |x|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + |x|) ^ m * Real.exp (-(r * |x|))
      ≤ ((Nat.factorial m : ℝ) / (r / 2) ^ m * Real.exp (r / 2) * Real.exp (r / 2 * |x|))
        * Real.exp (-(r * |x|)) := mul_le_mul_of_nonneg_right hgrow (Real.exp_pos _).le
    _ = (Nat.factorial m : ℝ) / (r / 2) ^ m * Real.exp (r / 2) *
        (Real.exp (r / 2 * |x|) * Real.exp (-(r * |x|))) := by ring
    _ = (Nat.factorial m : ℝ) / (r / 2) ^ m * Real.exp (r / 2) *
        Real.exp (-(r / 2 * |x|)) := by rw [hcol]

theorem polyPow_le_one_add_abs_pow (a : ℝ) (k j : ℕ) (x : ℝ) :
    (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j
      ≤ (1 + 4 * a ^ 4) ^ k * (1 + |x|) ^ (2 * k + j) := by
  have hbase : x ^ 2 + 4 * a ^ 4 ≤ (1 + 4 * a ^ 4) * (1 + |x|) ^ 2 := by
    have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have h1 : (1 : ℝ) ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
    have h2 : |x| ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
    have h3 : 4 * a ^ 4 * 1 ≤ 4 * a ^ 4 * (1 + |x|) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hx]
    nlinarith [h2, h3]
  have hpow : (x ^ 2 + 4 * a ^ 4) ^ k ≤ (1 + 4 * a ^ 4) ^ k * (1 + |x|) ^ (2 * k) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hbase k) (le_of_eq ?_)
    rw [mul_pow, ← pow_mul]
  have hj : |x| ^ j ≤ (1 + |x|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg x) (by linarith) j
  calc (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j
      ≤ ((1 + 4 * a ^ 4) ^ k * (1 + |x|) ^ (2 * k)) * (1 + |x|) ^ j :=
        mul_le_mul hpow hj (by positivity) (by positivity)
    _ = (1 + 4 * a ^ 4) ^ k * (1 + |x|) ^ (2 * k + j) := by
        rw [mul_assoc, ← pow_add]

theorem integrable_polyPow_abs_mul_exp (a : ℝ) (k j : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ =>
      (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(r * |x|))) := by
  refine Integrable.mono'
    ((integrable_polyAbs_mul_exp_neg_abs (2 * k + j) hr).const_mul ((1 + 4 * a ^ 4) ^ k))
    (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hnn : (0 : ℝ) ≤ (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(r * |x|)) := by
    have : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(r * |x|))
      ≤ ((1 + 4 * a ^ 4) ^ k * (1 + |x|) ^ (2 * k + j)) * Real.exp (-(r * |x|)) :=
        mul_le_mul_of_nonneg_right (polyPow_le_one_add_abs_pow a k j x) (Real.exp_pos _).le
    _ = (1 + 4 * a ^ 4) ^ k * ((1 + |x|) ^ (2 * k + j) * Real.exp (-(r * |x|))) := by ring

theorem continuous_xiMassJetIntegrand {a : ℝ} (ha : 0 < a) (k : ℕ) (τ : ℂ) (h : ℝ) :
    Continuous (xiMassJetIntegrand a k τ h) := by
  have htest : Continuous (fun x : ℝ => xiMassAnalyticTest a τ (x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      change HasDerivAt (⇑Complex.ofRealCLM) 1 x
      exact Complex.ofRealCLM.hasDerivAt
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    exact ((hasDerivAt_xiMassAnalyticTest ha τ hmem).comp x hz).continuousAt
  unfold xiMassJetIntegrand
  exact ((by fun_prop : Continuous fun x : ℝ => ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k).mul
    htest).mul (by fun_prop)

theorem integrable_absPow_mul_xiMassJetIntegrand {a : ℝ} (ha : 0 < a) (k j : ℕ) {τ : ℂ}
    (hτ : 0 < τ.re) (h : ℝ) :
    Integrable (fun x : ℝ => ((x : ℂ)) ^ j * xiMassJetIntegrand a k τ h x) := by
  refine Integrable.mono'
    (integrable_polyPow_abs_mul_exp a k j hτ)
    (((by fun_prop : Continuous fun x : ℝ => ((x : ℂ)) ^ j).mul
      (continuous_xiMassJetIntegrand ha k τ h)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hnn : (0 : ℝ) ≤ (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(τ.re * |x|)) := by
    have : (0 : ℝ) ≤ x ^ 2 + 4 * a ^ 4 := by positivity
    positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc |x| ^ j * ‖xiMassJetIntegrand a k τ h x‖
      ≤ |x| ^ j * ((x ^ 2 + 4 * a ^ 4) ^ k * Real.exp (-(τ.re * |x|))) :=
        mul_le_mul_of_nonneg_left (norm_xiMassJetIntegrand_le ha k hτ.le h x) (by positivity)
    _ = (x ^ 2 + 4 * a ^ 4) ^ k * |x| ^ j * Real.exp (-(τ.re * |x|)) := by ring

end

end RHTower
