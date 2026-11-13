import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFullGammaFormIsQuadraticOnItsIntegrableDomain
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity

/-!
# Gamma integrability of bounded-energy limits

Adding the global Gamma lower-bound constant makes its Fourier density
nonnegative. Plancherel bounds the added mass. Fatou in weighted L² then
passes Gamma integrability to an L¹ limit without assuming it at the limit.
-/

noncomputable section
open MeasureTheory Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

private theorem memLp_cx_of_sq {f : ℝ → ℝ} (hf : Integrable f)
    (h2 : Integrable (fun u => f u ^ 2)) : MemLp (cx f) 2 volume := by
  have hi : Integrable (cx f) := hf.ofReal (𝕜 := ℂ)
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h2

/-- An L¹ limit of profiles with bounded square mass and Gamma energy has finite Gamma energy. -/
theorem integrable_gamma_of_L1_limit_bounded_archForm
    {U : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hU : ∀ n, Integrable (U n)) (hU2 : ∀ n, Integrable (fun u => U n u ^ 2))
    (hUγ : ∀ n, Integrable (fun r : ℝ => ‖paperFT (cx (U n)) r‖ ^ 2 * EF.gammaBracket r))
    (hF : Integrable F) (hF2 : Integrable (fun u => F u ^ 2))
    (hL1 : Tendsto (fun n => ∫ u, ‖U n u - F u‖) atTop (𝓝 0))
    {M A : ℝ} (hmass : ∀ n, (∫ u, U n u ^ 2) ≤ M)
    (harch : ∀ n, archForm (U n) ≤ A) :
    Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) := by
  let D : ℝ := 10 + Real.log 4
  let w : ℝ → ℝ := fun r => Real.sqrt (EF.gammaBracket r + D)
  let V : ℕ → ℝ → ℝ := fun n r => w r * ‖paperFT (cx (U n)) r‖
  let V₀ : ℝ → ℝ := fun r => w r * ‖paperFT (cx F) r‖
  let C : ℝ := 2 * Real.pi * (A + D * M)
  have hD : 0 ≤ D := by
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    linarith only [hl]
  have hγ (r : ℝ) : 0 ≤ EF.gammaBracket r + D := by
    have hg := _root_.RHTower.WeilWorkPBAP.joint_gamma_lower_log r
    have hl := Real.log_nonneg (show 1 ≤ 2 + |r| by linarith only [abs_nonneg r])
    dsimp only [D]
    linarith only [hg, hl]
  have hw : Continuous w := (WeilHerglotz.continuous_gammaBracket.add continuous_const).sqrt
  have hsq (r : ℝ) (z : ℂ) : (w r * ‖z‖) ^ 2 =
      ‖z‖ ^ 2 * EF.gammaBracket r + ‖z‖ ^ 2 * D := by
    dsimp only [w]
    rw [mul_pow, Real.sq_sqrt (hγ r)]
    ring
  have hUb (n : ℕ) : Integrable (fun r : ℝ => ‖paperFT (cx (U n)) r‖ ^ 2) :=
    _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
      ((hU n).ofReal (𝕜 := ℂ)) (memLp_cx_of_sq (hU n) (hU2 n))
  have hV2 (n : ℕ) : Integrable (fun r => V n r ^ 2) := by
    have he : (fun r => V n r ^ 2) = fun r : ℝ =>
        ‖paperFT (cx (U n)) r‖ ^ 2 * EF.gammaBracket r +
          ‖paperFT (cx (U n)) r‖ ^ 2 * D := funext fun r => hsq r _
    rw [he]
    exact (hUγ n).add ((hUb n).mul_const D)
  have hVm (n : ℕ) : MemLp (V n) 2 volume := by
    have hm : AEStronglyMeasurable (V n) volume :=
      (hw.mul (continuous_paperFT_cx (hU n)).norm).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).mpr
    exact hV2 n
  have hbound (n : ℕ) : (∫ r, V n r ^ 2) ≤ C := by
    have hi : Integrable (cx (U n)) := (hU n).ofReal (𝕜 := ℂ)
    have hpl := _root_.RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp
      hi (memLp_cx_of_sq (hU n) (hU2 n))
    simp only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpl
    have hΓ : (∫ r : ℝ, ‖paperFT (cx (U n)) r‖ ^ 2 * EF.gammaBracket r) =
        2 * Real.pi * archForm (U n) := by
      unfold archForm cx
      field_simp
    change (∫ r, (w r * ‖paperFT (cx (U n)) r‖) ^ 2) ≤ C
    simp_rw [hsq]
    rw [integral_add (hUγ n) ((hUb n).mul_const D), integral_mul_const, hΓ, hpl]
    have ha := mul_le_mul_of_nonneg_left (harch n) (by positivity : 0 ≤ 2 * Real.pi)
    have hm := mul_le_mul_of_nonneg_left (hmass n)
      (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hD)
    dsimp only [C]
    nlinarith only [ha, hm]
  have hC : 0 ≤ C := (integral_nonneg fun r : ℝ => sq_nonneg (V 0 r)).trans (hbound 0)
  have hpoint (r : ℝ) : Tendsto (fun n => V n r) atTop (𝓝 (V₀ r)) := by
    have hFT : Tendsto (fun n => paperFT (cx (U n)) r) atTop (𝓝 (paperFT (cx F) r)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun n => norm_nonneg _)
        (fun n => norm_paperFT_sub_le (hU n) hF r) hL1
    exact hFT.norm.const_mul (w r)
  have he := Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall fun n => eLpNorm_two_le_of_integral_sq_le (hVm n) (hbound n))
    (fun n => (hVm n).aestronglyMeasurable) (Eventually.of_forall hpoint)
  have hV₀ := (integral_sq_le_of_eLpNorm_two_le
    ((hw.mul (continuous_paperFT_cx hF).norm).aestronglyMeasurable) hC he).1
  have hV₀2 : Integrable (fun r => V₀ r ^ 2) :=
    (memLp_two_iff_integrable_sq hV₀.aestronglyMeasurable).mp hV₀
  have hb : Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2) :=
    _root_.RHTower.KernelStrip.integrable_norm_sq_paperFT
      (hF.ofReal (𝕜 := ℂ)) (memLp_cx_of_sq hF hF2)
  apply (hV₀2.sub (hb.mul_const D)).congr
  refine Eventually.of_forall fun r => ?_
  change (w r * ‖paperFT (cx F) r‖) ^ 2 - ‖paperFT (cx F) r‖ ^ 2 * D = _
  rw [hsq, add_sub_cancel_right]

#print axioms integrable_gamma_of_L1_limit_bounded_archForm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
