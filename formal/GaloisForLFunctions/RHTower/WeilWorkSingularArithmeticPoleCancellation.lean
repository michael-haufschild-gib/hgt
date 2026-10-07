import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticCanonicalGaussian
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# The signed source numerator and its exact poles

Writing `p=(s-1)ζ` and `R=A-Φ`, the source contour is
`(R*p+p')*ζ(1-s)/(s-1)`. Its only possible pole in the right critical
half-plane is at one. The associated zeta-square Dirichlet expression is
`p*(R*p+p')/(s-1)^2`. Both pole coefficients come from the same holomorphic
source numerator. No zeta-zero exclusion is needed.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourcePoleNumerator {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  (zetaArchimedeanDatum s - WeilSpectral.weilContinuation hW s) * zetaResidueFactor s +
    deriv zetaResidueFactor s

theorem sourcePoleNumerator_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    sourcePoleNumerator hW 1 = zetaArchimedeanDatum 1 - WeilSpectral.weilContinuation hW 1 +
      (Real.eulerMascheroniConstant : ℂ) := by
  simp [sourcePoleNumerator]

theorem differentiableAt_sourcePoleNumerator {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (sourcePoleNumerator hW) s := by
  have hPhi := (WeilSpectral.differentiableOn_weilContinuation hW).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact (((WeilFiniteType.differentiableAt_zetaArchimedeanDatum (by linarith)).sub hPhi).mul
    (differentiable_zetaResidueFactor s)).add
      (differentiable_zetaResidueFactor.analyticAt s).deriv.differentiableAt

/-- Exact cancellation of all apparent zeta-zero poles. -/
theorem sourceZetaPairing_eq_poleNumerator {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : s ≠ 1) : sourceZetaPairing hW s =
      sourcePoleNumerator hW s * riemannZeta (1 - s) / (s - 1) := by
  unfold sourceZetaPairing sourcePoleNumerator
  rw [zetaResidueFactor_of_ne hs, deriv_zetaResidueFactor_of_ne hs]
  field_simp
  ring

theorem differentiableAt_sourceZetaPairing {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (sourceZetaPairing hW) s := by
  have hn : 1 - s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd := ((differentiableAt_sourcePoleNumerator hW hs).mul
    ((differentiableAt_riemannZeta hn).comp s (by fun_prop))).div
      (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
  exact sourceZetaPairing_eq_poleNumerator hW hz

/-- The simple pole has residue minus half the common source coefficient. -/
theorem tendsto_mul_sourceZetaPairing {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun s : ℂ => (s - 1) * sourceZetaPairing hW s) (𝓝[≠] 1)
      (𝓝 (-(sourcePoleNumerator hW 1) / 2)) := by
  have hc : ContinuousAt (fun s : ℂ => sourcePoleNumerator hW s * riemannZeta (1 - s)) 1 :=
    (differentiableAt_sourcePoleNumerator hW (by norm_num)).continuousAt.mul
      ((differentiableAt_riemannZeta (by norm_num : (1 : ℂ) - 1 ≠ 1)).continuousAt.comp (by fun_prop))
  have hv : sourcePoleNumerator hW 1 * riemannZeta (1 - 1) = -(sourcePoleNumerator hW 1) / 2 := by
    rw [sub_self, riemannZeta_zero]
    ring
  rw [← hv]
  refine hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [sourceZetaPairing_eq_poleNumerator hW hs]
  field_simp

def sourceZetaSquare {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  (zetaArchimedeanDatum s + 1 / (s - 1) - WeilSpectral.weilContinuation hW s) * riemannZeta s ^ 2 +
    deriv riemannZeta s * riemannZeta s

/-- The zeta-square expression has only the displayed double pole. -/
theorem sourceZetaSquare_eq_poleNumerator {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : s ≠ 1) : sourceZetaSquare hW s =
      zetaResidueFactor s * sourcePoleNumerator hW s / (s - 1) ^ 2 := by
  unfold sourceZetaSquare sourcePoleNumerator
  rw [zetaResidueFactor_of_ne hs, deriv_zetaResidueFactor_of_ne hs]
  field_simp
  ring

theorem differentiableAt_sourceZetaSquare {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (sourceZetaSquare hW) s := by
  have hd := ((differentiable_zetaResidueFactor s).mul
    (differentiableAt_sourcePoleNumerator hW hs)).div
      ((differentiableAt_id.sub_const 1).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr hs1))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
  exact sourceZetaSquare_eq_poleNumerator hW hz

theorem tendsto_sq_mul_sourceZetaSquare {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * sourceZetaSquare hW s) (𝓝[≠] 1)
      (𝓝 (sourcePoleNumerator hW 1)) := by
  have hc := (differentiable_zetaResidueFactor 1).continuousAt.mul
    (differentiableAt_sourcePoleNumerator hW (by norm_num)).continuousAt
  have ht := hc.tendsto.mono_left nhdsWithin_le_nhds
  simp only [zetaResidueFactor_one, one_mul] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [sourceZetaSquare_eq_poleNumerator hW hs]
  field_simp

end RHTower.WeilSingularArithmetic
