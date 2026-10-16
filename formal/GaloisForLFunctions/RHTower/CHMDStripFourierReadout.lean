import GaloisForLFunctions.RHTower.CHMDComplexKernelReadout
import GaloisForLFunctions.RHTower.CHMDCosineSourceFourier
import GaloisForLFunctions.RHTower.EvenSectorSechRepresentation

/-!
# Literal Fourier samples of every graph source on the closed critical strip

The exponential kernel divided by the mass weight is bounded by two uniformly
throughout the strip, including both polar points. Thus all samples have a
common operator norm bound on the actual completed source graph.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

def fourierKernel (z : ℂ) (x : ℝ) : ℂ := exp (I*z*x) / (Real.cosh (x/2) : ℂ)

theorem continuous_fourierKernel (z : ℂ) : Continuous (fourierKernel z) := by
  unfold fourierKernel
  fun_prop (disch := exact fun x => Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

theorem norm_fourierKernel_le {z : ℂ} (hz : |z.im| ≤ 1/2) (x : ℝ) :
    ‖fourierKernel z x‖ ≤ 2 := by
  rw [fourierKernel, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), div_le_iff₀ (Real.cosh_pos _)]
  have he : (I*z*(x : ℂ)).re ≤ |x|/2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub, mul_zero, sub_zero]
    calc
      -z.im*x = -(z.im*x) := by ring
      _ ≤ |z.im*x| := neg_le_abs _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ (1/2)*|x| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      _ = _ := by ring
  exact (Real.exp_le_exp.mpr he).trans (EvenSector.exp_abs_half_le_two_cosh x)

theorem fourierKernel_memLp {z : ℂ} (hz : |z.im| ≤ 1/2) : MemLp (fourierKernel z) 2 massMeasure := by
  apply (memLp_const (2 : ℝ)).of_le (continuous_fourierKernel z).aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa using norm_fourierKernel_le hz x

def graphFourierReadout (p : SourceGraph) (z : ℂ) : ℂ :=
  paperFT (fun x => (phiDoobTest p.val.fst x : ℂ)) z

def graphFourierReadoutCLM (z : ℂ) (hz : |z.im| ≤ 1/2) : SourceGraph →L[ℝ] ℂ :=
  complexKernelReadout (fourierKernel_memLp hz)

theorem integrable_graphFourierReadout_source (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    Integrable (fun x => (phiDoobTest p.val.fst x : ℂ) * exp (I*z*x)) := by
  have h := (integrable_withDensity_iff_integrable_smul'
    continuous_massDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp
      (integrable_complexKernel_source (fourierKernel_memLp hz) p)
  apply h.congr
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (massDensity_pos x).le]
  exact weighted_source_kernel p (exp (I*z*x)) x

theorem graphFourierReadoutCLM_apply (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphFourierReadoutCLM z hz p = graphFourierReadout p z := by
  rw [graphFourierReadoutCLM, complexKernelReadout_eq_integral]
  change (∫ x, fourierKernel z x * (p.val.fst x : ℂ)
    ∂volume.withDensity (fun x => ENNReal.ofReal (massDensity x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul continuous_massDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold graphFourierReadout paperFT
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (massDensity_pos x).le]
  exact weighted_source_kernel p (exp (I*z*x)) x

theorem continuous_graphFourierReadout {z : ℂ} (hz : |z.im| ≤ 1/2) :
    Continuous (fun p => graphFourierReadout p z) := by
  have he : (fun p => graphFourierReadout p z) = graphFourierReadoutCLM z hz :=
    funext fun p => (graphFourierReadoutCLM_apply p hz).symm
  rw [he]
  exact (graphFourierReadoutCLM z hz).continuous

theorem norm_graphFourierReadoutCLM_le {z : ℂ} (hz : |z.im| ≤ 1/2) :
    ‖graphFourierReadoutCLM z hz‖ ≤ stripReadoutBound :=
  opNorm_complexKernelReadout_le (fourierKernel_memLp hz) (norm_fourierKernel_le hz)

theorem graphFourierReadout_of_source {p : SourceGraph} {f : ℝ → ℝ}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (z : ℂ) :
    graphFourierReadout p z = paperFT (fun x => (f x : ℂ)) z := by
  unfold graphFourierReadout paperFT
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq hp] with x hx
  rw [phiDoobTest, hx]
  simp only [phiDoobInv]
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem graphFourierReadout_testLift {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (z : ℂ) :
    graphFourierReadout (testLift f hf hc) z = paperFT (fun x => (f x : ℂ)) z :=
  graphFourierReadout_of_source (testLift_source f hf hc) z

theorem conj_graphFourierReadout (p : SourceGraph) (z : ℂ) :
    conj (graphFourierReadout p z) = graphFourierReadout p (-conj z) :=
  conj_paperFT_ofReal (phiDoobTest p.val.fst) z

def EvenGraphSource (p : SourceGraph) : Prop :=
  ∀ᵐ x ∂volume, phiDoobTest p.val.fst (-x) = phiDoobTest p.val.fst x

theorem graphFourierReadout_neg_of_even {p : SourceGraph} (hp : EvenGraphSource p) (z : ℂ) :
    graphFourierReadout p (-z) = graphFourierReadout p z := by
  rw [graphFourierReadout, ← paperFT_comp_neg]
  unfold graphFourierReadout paperFT
  apply integral_congr_ae
  filter_upwards [hp] with x hx
  rw [hx]

theorem graphCosineReadout_eq_half_fourier (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphCosineReadout p z = (graphFourierReadout p z + graphFourierReadout p (-z))/2 := by
  have hn : |(-z).im| ≤ 1/2 := by simpa using hz
  rw [graphCosineReadout_eq_integral]
  unfold graphFourierReadout paperFT
  rw [← integral_add (integrable_graphFourierReadout_source p hz)
    (integrable_graphFourierReadout_source p hn), ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Complex.cos, show (z*(x : ℂ))*I = I*z*x by ring,
    show -(z*(x : ℂ))*I = I*(-z)*x by ring]
  ring

theorem graphFourierReadout_eq_cosine_of_even {p : SourceGraph} (hp : EvenGraphSource p)
    {z : ℂ} (hz : |z.im| ≤ 1/2) : graphFourierReadout p z = graphCosineReadout p z := by
  rw [graphCosineReadout_eq_half_fourier p hz, graphFourierReadout_neg_of_even hp]
  ring

theorem graphFourierReadout_real_of_re_zero (p : SourceGraph) {z : ℂ} (hz : z.re = 0) :
    (graphFourierReadout p z).im = 0 := by
  have he : -conj z = z := by apply Complex.ext <;> simp [hz]
  have h := congrArg Complex.im (conj_graphFourierReadout p z)
  rw [he, Complex.conj_im] at h
  linarith

end RHTower.CHMDDoobGraph
