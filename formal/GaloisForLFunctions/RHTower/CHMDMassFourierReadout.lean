import GaloisForLFunctions.RHTower.CHMDStripFourierReadout
import GaloisForLFunctions.RHTower.CHMDArithmeticResolvent

/-!
# Literal Fourier samples on the full CHMD mass space

The strip kernels already used on the energy graph define bounded functionals
on the entire mass Hilbert space. No jump-energy admission is needed.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def massKernelReadout {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure) : MassSpace →L[ℝ] ℂ where
  toFun w := (⟪hk.re.toLp (fun x => (k x).re), w⟫_ℝ : ℂ) +
    I * (⟪hk.im.toLp (fun x => (k x).im), w⟫_ℝ : ℂ)
  map_add' u v := by
    simp only [inner_add_right, Complex.ofReal_add]
    ring
  map_smul' c w := by
    simp only [real_inner_smul_right, Complex.ofReal_mul, RingHom.id_apply, real_smul]
    ring
  cont := (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))

theorem massKernelReadout_source {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure) (p : SourceGraph) :
    massKernelReadout hk (sourceMap p) = complexKernelReadout hk p := rfl

theorem inner_mass_toLp (w : MassSpace) {g : ℝ → ℝ} (hg : MemLp g 2 massMeasure) :
    ⟪hg.toLp g, w⟫_ℝ = ∫ x, g x * w x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  change inner ℝ (hg.toLp g x) (w x) = _
  simp [hx, mul_comm]

theorem massKernelReadout_eq_integral {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure)
    (w : MassSpace) : massKernelReadout hk w = ∫ x, k x * (w x : ℂ) ∂massMeasure := by
  have hR : Integrable (fun x => (((k x).re * w x : ℝ) : ℂ)) massMeasure :=
    (hk.re.integrable_mul (Lp.memLp w)).ofReal
  have hI : Integrable (fun x => I * (((k x).im * w x : ℝ) : ℂ)) massMeasure :=
    (hk.im.integrable_mul (Lp.memLp w)).ofReal.const_mul I
  change ((inner ℝ _ w : ℝ) : ℂ) + I * ((inner ℝ _ w : ℝ) : ℂ) = _
  rw [inner_mass_toLp, inner_mass_toLp, ← integral_complex_ofReal,
    ← integral_complex_ofReal, ← integral_const_mul, ← integral_add hR hI]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.ofReal_mul]
  rw [show (k x).re * (w x : ℂ) + I * ((k x).im * (w x : ℂ)) =
      ((k x).re + (k x).im * I) * (w x : ℂ) by ring, Complex.re_add_im]

def massStripReadoutBound : ℝ :=
  2 * ‖(memLp_const (2 : ℝ) : MemLp (fun _ : ℝ => (2 : ℝ)) 2 massMeasure).toLp (fun _ => 2)‖

theorem massStripReadoutBound_nonneg : 0 ≤ massStripReadoutBound := by
  unfold massStripReadoutBound
  positivity

theorem norm_massKernelReadout_le {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure)
    (hb : ∀ x, ‖k x‖ ≤ 2) (w : MassSpace) :
    ‖massKernelReadout hk w‖ ≤ massStripReadoutBound * ‖w‖ := by
  let d := (memLp_const (2 : ℝ) : MemLp (fun _ : ℝ => (2 : ℝ)) 2 massMeasure).toLp (fun _ => 2)
  have hd : d =ᵐ[massMeasure] (fun _ => (2 : ℝ)) := (memLp_const (2 : ℝ)).coeFn_toLp
  have hR : ‖hk.re.toLp (fun x => (k x).re)‖ ≤ ‖d‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hk.re.coeFn_toLp, hd] with x hx hy
    change (hk.re.toLp (fun x => (k x).re)) x = (k x).re at hx
    rw [hx, hy]
    exact (Complex.abs_re_le_norm _).trans (by simpa using hb x)
  have hI : ‖hk.im.toLp (fun x => (k x).im)‖ ≤ ‖d‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hk.im.coeFn_toLp, hd] with x hx hy
    change (hk.im.toLp (fun x => (k x).im)) x = (k x).im at hx
    rw [hx, hy]
    exact (Complex.abs_im_le_norm _).trans (by simpa using hb x)
  change ‖(inner ℝ _ w : ℂ) + I * (inner ℝ _ w : ℂ)‖ ≤ _
  calc
    _ ≤ ‖(inner ℝ (hk.re.toLp _) w : ℂ)‖ +
        ‖I * (inner ℝ (hk.im.toLp _) w : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖hk.re.toLp (fun x => (k x).re)‖ * ‖w‖ +
        ‖hk.im.toLp (fun x => (k x).im)‖ * ‖w‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (2*‖d‖) * ‖w‖ := by nlinarith [norm_nonneg w]
    _ = massStripReadoutBound * ‖w‖ := rfl

def massFourierReadoutCLM (z : ℂ) (hz : |z.im| ≤ 1/2) : MassSpace →L[ℝ] ℂ :=
  massKernelReadout (fourierKernel_memLp hz)

def massFourierReadout (w : MassSpace) (z : ℂ) : ℂ :=
  ∫ x, fourierKernel z x * (w x : ℂ) ∂massMeasure

theorem massFourierReadoutCLM_apply (w : MassSpace) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    massFourierReadoutCLM z hz w = massFourierReadout w z :=
  massKernelReadout_eq_integral _ _

theorem massFourierReadout_source (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    massFourierReadout (sourceMap p) z = graphFourierReadout p z := by
  rw [← massFourierReadoutCLM_apply _ hz]
  exact graphFourierReadoutCLM_apply p hz

theorem continuous_massFourierReadout {z : ℂ} (hz : |z.im| ≤ 1/2) :
    Continuous (fun w => massFourierReadout w z) := by
  have he : (fun w => massFourierReadout w z) = massFourierReadoutCLM z hz :=
    funext fun w => (massFourierReadoutCLM_apply w hz).symm
  rw [he]
  exact (massFourierReadoutCLM z hz).continuous

theorem norm_massFourierReadoutCLM_le {z : ℂ} (hz : |z.im| ≤ 1/2) :
    ‖massFourierReadoutCLM z hz‖ ≤ massStripReadoutBound :=
  (massFourierReadoutCLM z hz).opNorm_le_bound massStripReadoutBound_nonneg
    (norm_massKernelReadout_le (fourierKernel_memLp hz) (norm_fourierKernel_le hz))

theorem massFourierReadout_eq_paperFT (w : MassSpace) (z : ℂ) :
    massFourierReadout w z = paperFT (fun x => (phiDoobTest w x : ℂ)) z := by
  change (∫ x, fourierKernel z x * (w x : ℂ)
    ∂volume.withDensity (fun x => ENNReal.ofReal (massDensity x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul continuous_massDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold paperFT
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (massDensity_pos x).le]
  simp only [fourierKernel, massDensity, phiDoobTest, Complex.ofReal_mul, real_smul]
  have hc : (Real.cosh (x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  field_simp

end RHTower.CHMDDoobGraph
