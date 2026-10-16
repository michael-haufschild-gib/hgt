import GaloisForLFunctions.RHTower.CHMDGraphCosineReadout

/-! # Continuous literal-source readouts from complex L2 kernels -/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

def complexKernelReadout {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure) : SourceGraph →L[ℝ] ℂ where
  toFun p := (⟪hk.re.toLp (fun x => (k x).re), sourceMap p⟫_ℝ : ℂ) +
    I * (⟪hk.im.toLp (fun x => (k x).im), sourceMap p⟫_ℝ : ℂ)
  map_add' p q := by
    simp only [map_add, inner_add_right, Complex.ofReal_add]
    ring
  map_smul' c p := by
    simp only [map_smul, real_inner_smul_right, Complex.ofReal_mul, RingHom.id_apply, real_smul]
    ring
  cont := (Complex.continuous_ofReal.comp (continuous_const.inner sourceMap.continuous)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.inner sourceMap.continuous)))

theorem integrable_complexKernel_source {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure) (p : SourceGraph) :
    Integrable (fun x => k x * (p.val.fst x : ℂ)) massMeasure := by
  have hR : Integrable (fun x => (((k x).re * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    (hk.re.integrable_mul (Lp.memLp p.val.fst)).ofReal
  have hI : Integrable (fun x => I * (((k x).im * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    (hk.im.integrable_mul (Lp.memLp p.val.fst)).ofReal.const_mul I
  apply (hR.add hI).congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Complex.ofReal_mul]
  rw [show (k x).re * (p.val.fst x : ℂ) + I * ((k x).im * (p.val.fst x : ℂ)) =
      ((k x).re + (k x).im * I) * (p.val.fst x : ℂ) by ring, Complex.re_add_im]

theorem complexKernelReadout_eq_integral {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure) (p : SourceGraph) :
    complexKernelReadout hk p = ∫ x, k x * (p.val.fst x : ℂ) ∂massMeasure := by
  have hR : Integrable (fun x => (((k x).re * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    (hk.re.integrable_mul (Lp.memLp p.val.fst)).ofReal
  have hI : Integrable (fun x => I * (((k x).im * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    (hk.im.integrable_mul (Lp.memLp p.val.fst)).ofReal.const_mul I
  change ((inner ℝ _ (sourceMap p) : ℝ) : ℂ) + I * ((inner ℝ _ (sourceMap p) : ℝ) : ℂ) = _
  rw [inner_source_eq_integral, inner_source_eq_integral, ← integral_complex_ofReal,
    ← integral_complex_ofReal, ← integral_const_mul, ← integral_add hR hI]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.ofReal_mul]
  rw [show (k x).re * (p.val.fst x : ℂ) + I * ((k x).im * (p.val.fst x : ℂ)) =
      ((k x).re + (k x).im * I) * (p.val.fst x : ℂ) by ring, Complex.re_add_im]

theorem weighted_source_kernel (p : SourceGraph) (w : ℂ) (x : ℝ) :
    massDensity x • (w / (Real.cosh (x/2) : ℂ) * (p.val.fst x : ℂ)) =
      (phiDoobTest p.val.fst x : ℂ) * w := by
  simp only [massDensity, phiDoobTest, Complex.ofReal_mul, real_smul]
  have hc : (Real.cosh (x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  rw [div_eq_mul_inv]
  calc
    _ = ((riemannKernelReal x : ℂ) * (p.val.fst x : ℂ) * w) *
        ((Real.cosh (x/2) : ℂ) * (Real.cosh (x/2) : ℂ)⁻¹) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_one]

def stripReadoutBound : ℝ :=
  2 * ‖(memLp_const (2 : ℝ) : MemLp (fun _ : ℝ => (2 : ℝ)) 2 massMeasure).toLp (fun _ => 2)‖ * ‖sourceMap‖

theorem stripReadoutBound_nonneg : 0 ≤ stripReadoutBound := by
  unfold stripReadoutBound
  positivity

theorem norm_complexKernelReadout_le {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure)
    (hb : ∀ x, ‖k x‖ ≤ 2) (p : SourceGraph) :
    ‖complexKernelReadout hk p‖ ≤ stripReadoutBound * ‖p‖ := by
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
  change ‖(inner ℝ _ (sourceMap p) : ℂ) + I * (inner ℝ _ (sourceMap p) : ℂ)‖ ≤ _
  calc
    _ ≤ ‖(inner ℝ (hk.re.toLp _) (sourceMap p) : ℂ)‖ +
        ‖I * (inner ℝ (hk.im.toLp _) (sourceMap p) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖hk.re.toLp (fun x => (k x).re)‖ * ‖sourceMap p‖ +
        ‖hk.im.toLp (fun x => (k x).im)‖ * ‖sourceMap p‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (2*‖d‖) * ‖sourceMap p‖ := by nlinarith [norm_nonneg (sourceMap p)]
    _ ≤ (2*‖d‖) * (‖sourceMap‖ * ‖p‖) :=
      mul_le_mul_of_nonneg_left (sourceMap.le_opNorm p) (by positivity)
    _ = stripReadoutBound * ‖p‖ := by unfold stripReadoutBound; dsimp [d]; ring

theorem opNorm_complexKernelReadout_le {k : ℝ → ℂ} (hk : MemLp k 2 massMeasure)
    (hb : ∀ x, ‖k x‖ ≤ 2) : ‖complexKernelReadout hk‖ ≤ stripReadoutBound :=
  (complexKernelReadout hk).opNorm_le_bound stripReadoutBound_nonneg (norm_complexKernelReadout_le hk hb)

end RHTower.CHMDDoobGraph
