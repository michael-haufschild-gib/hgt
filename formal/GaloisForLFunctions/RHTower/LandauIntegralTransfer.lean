import GaloisForLFunctions.RHTower.LandauSummabilityTransfer
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Landau transfer for nonnegative Laplace carriers

This is the continuous-measure analogue of `landau_summability_transfer`.  Let `X` be
nonnegative almost everywhere and let its complex moment-generating function be analytic near
zero.  If a holomorphic continuation through the closed ball of radius `R` has the same germ at
zero, then the exponential moment exists at every real `rho` with `0 <= rho < R`.

The proof is Landau's Taylor--Tonelli mechanism.  Complex-MGF derivatives at zero are the
nonnegative moments `integral X^k`; hence the norms of the continuation's Taylor coefficients
are exactly those moments divided by `k!`.  Power-series summability at `rho` and Tonelli then
reassemble `exp (rho * X)` under the integral.
-/

open Complex MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace RHTower

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **Continuous Landau summability transfer.**  For a nonnegative random variable, any
holomorphic continuation of its complex MGF through a ball forces exponential integrability at
every nonnegative real point strictly inside that ball. -/
theorem landau_complexMGF_integrable_transfer
    {X : Omega → ℝ} {mu : Measure Omega}
    (hX0 : ∀ᵐ omega ∂mu, 0 ≤ X omega)
    (hzero : 0 ∈ interior (integrableExpSet X mu))
    {R : NNReal} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (Metric.closedBall 0 (R : ℝ)))
    (hagree : G =ᶠ[𝓝 0] complexMGF X mu)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun omega => Real.exp (rho * X omega)) mu := by
  have hR0 : (0 : NNReal) < R := by
    exact_mod_cast (lt_of_le_of_lt hrho0 hrhoR)
  obtain ⟨p, hball⟩ : ∃ p, HasFPowerSeriesOnBall G p 0 R :=
    ⟨_, hGd.hasFPowerSeriesOnBall hR0⟩
  have hmoment_integrable (k : ℕ) : Integrable (fun omega => X omega ^ k) mu :=
    integrable_pow_of_mem_interior_integrableExpSet hzero k
  have hiter : ∀ k, iteratedDeriv k G 0 =
      ((∫ omega, X omega ^ k ∂mu : ℝ) : ℂ) := fun k => by
    rw [hagree.iteratedDeriv_eq k, iteratedDeriv_complexMGF hzero k]
    have hfun : (fun omega => (X omega : ℂ) ^ k * Complex.exp (0 * (X omega : ℂ))) =
        fun omega => ((X omega ^ k : ℝ) : ℂ) := by
      funext omega
      simp
    rw [hfun]
    exact Complex.ofRealCLM.integral_comp_comm (hmoment_integrable k)
  have hcoeff : ∀ k, (k.factorial : ℂ) * p.coeff k = iteratedDeriv k G 0 := by
    intro k
    have h1 := hball.factorial_smul (1 : ℂ) k
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h1, nsmul_eq_mul]
    rfl
  have hmoment_nonneg : ∀ k, 0 ≤ ∫ omega, X omega ^ k ∂mu := fun k => by
    apply integral_nonneg_of_ae
    filter_upwards [hX0] with omega homega
    positivity
  have hcoeff_norm : ∀ k, ‖p.coeff k‖ =
      (∫ omega, X omega ^ k ∂mu) / (k.factorial : ℝ) := by
    intro k
    have h2 : (k.factorial : ℂ) * p.coeff k =
        ((∫ omega, X omega ^ k ∂mu : ℝ) : ℂ) := by
      rw [hcoeff k, hiter k]
    have h3 := congrArg norm h2
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (hmoment_nonneg k)] at h3
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    rw [eq_div_iff (ne_of_gt hkpos), mul_comm]
    exact h3
  set rho' : NNReal := ⟨rho, hrho0⟩ with hrho'
  have hsum_coeff : Summable fun k => ‖p k‖ * (rho' : ℝ) ^ k := by
    refine p.summable_norm_mul_pow ?_
    calc (rho' : ENNReal) < (R : ENNReal) := by exact_mod_cast hrhoR
      _ ≤ p.radius := hball.r_le
  have hsum_moments : Summable fun k =>
      (∫ omega, X omega ^ k ∂mu) * (rho ^ k / (k.factorial : ℝ)) := by
    refine hsum_coeff.congr fun k => ?_
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hcoeff_norm k,
      show (rho' : ℝ) = rho from rfl]
    ring
  let F : ℕ → Omega → ℝ :=
    fun k omega => X omega ^ k * (rho ^ k / (k.factorial : ℝ))
  have hscalar_nonneg (k : ℕ) : 0 ≤ rho ^ k / (k.factorial : ℝ) := by positivity
  have hF_int : ∀ k, Integrable (F k) mu := fun k => by
    exact (hmoment_integrable k).mul_const _
  have hF_nonneg : ∀ᵐ omega ∂mu, ∀ k, 0 ≤ F k omega := by
    filter_upwards [hX0] with omega homega
    intro k
    exact mul_nonneg (pow_nonneg homega k) (hscalar_nonneg k)
  have hF_sum : Summable fun k => ∫ omega, ‖F k omega‖ ∂mu := by
    refine hsum_moments.congr fun k => ?_
    have hnorm : (fun omega => ‖F k omega‖) =ᵐ[mu]
        fun omega => X omega ^ k * (rho ^ k / (k.factorial : ℝ)) := by
      filter_upwards [hX0] with omega homega
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (pow_nonneg homega k) (hscalar_nonneg k)
    rw [integral_congr_ae hnorm]
    rw [integral_mul_const]
  have hlin : ∑' k, ∫⁻ omega, ‖F k omega‖ₑ ∂mu ≠ ∞ := by
    have hone (k : ℕ) : ∫⁻ omega, ‖F k omega‖ₑ ∂mu =
        ‖∫ omega, ‖F k omega‖ ∂mu‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF_int k).norm]
      simp only [coe_nnnorm]
      rw [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg (fun omega => norm_nonneg (F k omega)))]
      simp only [Real.norm_eq_abs]
    rw [funext hone]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hF_sum.abs
  have hF_meas : ∀ k, AEStronglyMeasurable (F k) mu := fun k => (hF_int k).1
  have hF_enorm_meas (k : ℕ) : AEMeasurable (‖F k ·‖ₑ) mu :=
    (hF_meas k).enorm
  have htarget_meas : AEStronglyMeasurable (fun omega => Real.exp (rho * X omega)) mu := by
    have hXmeas := aemeasurable_of_mem_interior_integrableExpSet hzero
    fun_prop
  refine ⟨htarget_meas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpoint : (fun omega => ‖Real.exp (rho * X omega)‖ₑ) =ᵐ[mu]
      fun omega => ∑' k, ‖F k omega‖ₑ := by
    filter_upwards [hX0] with omega homegaX
    have homega : ∀ k, 0 ≤ F k omega := fun k =>
      mul_nonneg (pow_nonneg homegaX k) (hscalar_nonneg k)
    have hsummable : Summable (F · omega) := by
      have hbase := Real.summable_pow_div_factorial (rho * X omega)
      refine hbase.congr fun k => ?_
      dsimp [F]
      rw [mul_pow]
      ring
    have hseries : (∑' k, F k omega) = Real.exp (rho * X omega) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      apply tsum_congr
      intro k
      dsimp [F]
      rw [mul_pow]
      ring
    rw [Real.enorm_of_nonneg (Real.exp_pos _).le, ← hseries,
      ENNReal.ofReal_tsum_of_nonneg homega hsummable]
    apply tsum_congr
    intro k
    exact (Real.enorm_of_nonneg (homega k)).symm
  rw [lintegral_congr_ae hpoint, lintegral_tsum hF_enorm_meas]
  exact lt_top_iff_ne_top.mpr hlin

end RHTower
