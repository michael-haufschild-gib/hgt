import GaloisForLFunctions.RHTower.ThetaMovingShellBoundaryLayer
import GaloisForLFunctions.RHTower.XiOnLineZeroLocalBounds
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.XiEntireReal
import Mathlib.Analysis.Complex.Liouville

/-!
# Full Xi jets are negligible above the moving shell's exponential boundary

Fixed-radius Cauchy estimates retain the full `exp(-πt/4)` rate for every
fixed Xi jet. Thus the omitted-shell normalization suppresses the full Xi
source at heights `lambda (N+1)^2` whenever `lambda > 4`.
-/

open Real Complex MeasureTheory Set Filter Topology Metric

namespace RHTower
noncomputable section

theorem exists_XiC_jet_exponential_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 3 ≤ b →
      ‖iteratedDeriv k XiC (b : ℂ)‖ ≤ C * (b+2)^3 * Real.exp (-Real.pi*b/4) := by
  let C := (k.factorial : ℝ) * 4^k * xiNearLineUpperConst * Real.exp (Real.pi/4)
  have hK := xiNearLineUpperConst_pos
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b hb
  let M := xiNearLineUpperConst * (b+2)^3 * Real.exp (-Real.pi*(b-1)/4)
  have hcircle : ∀ z ∈ sphere (b : ℂ) (1/4), ‖XiC z‖ ≤ M := by
    intro z hz
    have hnorm : ‖z-(b : ℂ)‖ = 1/4 := mem_sphere_iff_norm.mp hz
    have hre : |z.re-b| ≤ 1/4 := by
      simpa only [Complex.sub_re, Complex.ofReal_re, hnorm] using
        Complex.abs_re_le_norm (z-(b : ℂ))
    have him : |z.im| ≤ 1/4 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hnorm] using
        Complex.abs_im_le_norm (z-(b : ℂ))
    have hzre : 2 ≤ z.re := by linarith [(abs_le.mp hre).1]
    have h0 := norm_riemannPhiTransform_le_near_line (by linarith : |z.im| ≤ 1/2) hzre
    rw [riemannPhiTransform_eq_xi, mul_comm Complex.I z] at h0
    change ‖XiC z‖ ≤ _ at h0
    apply h0.trans
    have hupper : 1+z.re ≤ b+2 := by linarith [(abs_le.mp hre).2]
    have hlower : b-1 ≤ z.re := by linarith [(abs_le.mp hre).1]
    dsimp [M]
    gcongr
    nlinarith [Real.pi_pos]
  have hjet := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by positivity : (0 : ℝ) < 1/4)
    XiC_differentiable.diffContOnCl hcircle
  apply hjet.trans
  have he : Real.exp (-Real.pi*(b-1)/4) =
      Real.exp (Real.pi/4) * Real.exp (-Real.pi*b/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [M, C]
  rw [he]
  have hp : (1/4 : ℝ)^k = (4^k : ℝ)⁻¹ := by simp only [one_div, inv_pow]
  rw [hp, div_eq_mul_inv, inv_inv]
  ring_nf
  exact le_rfl

/-- At every fixed height ratio above four, all normalized full-Xi jets vanish. -/
theorem tendsto_normalized_XiC_jet (k : ℕ) {lambda : ℝ} (hlambda : 4 < lambda) :
    Tendsto (fun N =>
      ((Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
        thetaMovingShellScale N^k : ℝ) : ℂ) *
          iteratedDeriv k XiC ((lambda * thetaMovingShellScale N : ℝ) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_XiC_jet_exponential_bound k
  let c : ℝ := Real.pi * (lambda/4-1)
  have hc : 0 < c := mul_pos Real.pi_pos (by linarith : 0 < lambda/4-1)
  have hl : 0 < lambda := by linarith
  have hmajor (N : ℕ) :
      ‖((Real.exp (Real.pi * thetaMovingShellScale N) / thetaMovingShellScale N *
          thetaMovingShellScale N^k : ℝ) : ℂ) *
          iteratedDeriv k XiC ((lambda * thetaMovingShellScale N : ℝ) : ℂ)‖ ≤
        C * (lambda+2)^3 * thetaMovingShellScale N^(k+3) *
          Real.exp (-c*thetaMovingShellScale N) := by
    let a := thetaMovingShellScale N
    have ha : 1 ≤ a := one_le_thetaMovingShellScale N
    have ha0 : 0 < a := thetaMovingShellScale_pos N
    have hb : 3 ≤ lambda*a := by nlinarith
    have hp : (lambda*a+2)^3 ≤ ((lambda+2)*a)^3 := by
      gcongr
      nlinarith
    have hf : Real.exp (Real.pi*a) / a * a^k ≤ Real.exp (Real.pi*a) * a^k := by
      gcongr
      exact div_le_self (Real.exp_pos _).le ha
    have he : Real.exp (Real.pi*a) * Real.exp (-Real.pi*(lambda*a)/4) =
        Real.exp (-c*a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    change ‖((Real.exp (Real.pi*a) / a * a^k : ℝ) : ℂ) *
      iteratedDeriv k XiC ((lambda*a : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.exp (Real.pi*a) * a^k) *
          (C * (lambda*a+2)^3 * Real.exp (-Real.pi*(lambda*a)/4)) :=
        mul_le_mul hf (hbound _ hb) (norm_nonneg _) (by positivity)
      _ ≤ (Real.exp (Real.pi*a) * a^k) *
          (C * ((lambda+2)*a)^3 * Real.exp (-Real.pi*(lambda*a)/4)) := by gcongr
      _ = _ := by
        rw [mul_pow, pow_add]
        have hmul := congrArg (fun z : ℝ => C*(lambda+2)^3*a^k*a^3*z) he
        convert hmul using 1 <;> ring
  have hlim : Tendsto (fun N => thetaMovingShellScale N^(k+3) *
      Real.exp (-c*thetaMovingShellScale N)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k+3 : ℕ) c hc).comp
        tendsto_thetaMovingShellScale
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hmajor)
  simpa only [mul_zero, ← mul_assoc] using hlim.const_mul (C*(lambda+2)^3)

end
end RHTower
