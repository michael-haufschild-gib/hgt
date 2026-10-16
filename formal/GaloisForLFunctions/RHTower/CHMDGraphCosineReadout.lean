import GaloisForLFunctions.RHTower.CHMDFiniteDivisorPairing

/-!
# Literal cosine Fourier readouts on the complete arithmetic graph

Every complex spectral point defines a continuous real-linear functional on
the original graph. Full theta exponential moments put its cosine kernel in
the actual source L2 space; the weighted integral identity identifies the
functional with the literal source integral.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

def cosineKernel (z : ℂ) (x : ℝ) : ℂ := Complex.cos (z*x) / (Real.cosh (x/2) : ℂ)

theorem continuous_cosineKernel (z : ℂ) : Continuous (cosineKernel z) := by
  unfold cosineKernel
  fun_prop (disch := exact fun x => Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

theorem cosineKernel_weighted_sq_le (z : ℂ) (x : ℝ) :
    massDensity x * ‖cosineKernel z x‖^2 ≤
      Real.exp ((2*|z.im|)*|x|) * riemannKernelReal x := by
  have hc := Real.cosh_pos (x/2)
  have h1 := Real.one_le_cosh (x/2)
  have hθ := (riemannKernelReal_pos x).le
  have hn := norm_ccos_mul_ofReal_le z x
  rw [cosineKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_pow]
  calc
    massDensity x * (‖Complex.cos (z*x)‖^2 / Real.cosh (x/2)^2) =
        riemannKernelReal x * (‖Complex.cos (z*x)‖^2 / Real.cosh (x/2)) := by
      unfold massDensity
      field_simp
    _ ≤ riemannKernelReal x * ‖Complex.cos (z*x)‖^2 := by
      gcongr
      exact div_le_self (sq_nonneg _) h1
    _ ≤ riemannKernelReal x * (Real.exp (|z.im| * |x|))^2 := by gcongr
    _ = _ := by rw [sq, ← Real.exp_add, mul_comm]; congr 1; ring_nf

theorem cosineKernel_memLp (z : ℂ) : MemLp (cosineKernel z) 2 massMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (continuous_cosineKernel z).aestronglyMeasurable).mpr
  rw [massMeasure, integrable_weighted_iff volume continuous_massDensity.measurable
    (Eventually.of_forall fun x => (massDensity_pos x).le)]
  have hi : Integrable (fun x => Real.exp ((2*|z.im|)*|x|) * riemannKernelReal x) := by
    simpa only [thetaCuspFullSource_eq_riemannKernelReal] using
      HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource (2*|z.im|)
  apply hi.mono' (continuous_massDensity.mul ((continuous_cosineKernel z).norm.pow 2)).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖massDensity x * ‖cosineKernel z x‖^2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (massDensity_pos x).le (sq_nonneg _))]
    exact cosineKernel_weighted_sq_le z x

/-- A spectral sample is built from genuine L2 source coordinates. -/
def graphCosineReadout (p : SourceGraph) (z : ℂ) : ℂ :=
  (⟪(cosineKernel_memLp z).re.toLp (fun x => (cosineKernel z x).re), sourceMap p⟫_ℝ : ℂ) +
    I * (⟪(cosineKernel_memLp z).im.toLp (fun x => (cosineKernel z x).im), sourceMap p⟫_ℝ : ℂ)

theorem continuous_graphCosineReadout (z : ℂ) : Continuous (fun p => graphCosineReadout p z) := by
  unfold graphCosineReadout
  exact (Complex.continuous_ofReal.comp (continuous_const.inner sourceMap.continuous)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.inner sourceMap.continuous)))

theorem graphCosineReadout_add (p q : SourceGraph) (z : ℂ) :
    graphCosineReadout (p+q) z = graphCosineReadout p z + graphCosineReadout q z := by
  simp only [graphCosineReadout, map_add, inner_add_right, Complex.ofReal_add]
  ring

theorem graphCosineReadout_smul (c : ℝ) (p : SourceGraph) (z : ℂ) :
    graphCosineReadout (c • p) z = (c : ℂ) * graphCosineReadout p z := by
  simp only [graphCosineReadout, map_smul, real_inner_smul_right, Complex.ofReal_mul]
  ring

theorem inner_source_eq_integral (p : SourceGraph) {g : ℝ → ℝ} (hg : MemLp g 2 massMeasure) :
    ⟪hg.toLp g, sourceMap p⟫_ℝ = ∫ x, g x * p.val.fst x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  change inner ℝ (hg.toLp g x) (p.val.fst x) = _
  simp [hx, mul_comm]

theorem integrable_cosineKernel_source (p : SourceGraph) (z : ℂ) :
    Integrable (fun x => cosineKernel z x * (p.val.fst x : ℂ)) massMeasure := by
  have hR : Integrable (fun x => (((cosineKernel z x).re * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    ((cosineKernel_memLp z).re.integrable_mul (Lp.memLp p.val.fst)).ofReal
  have hI : Integrable (fun x => I * (((cosineKernel z x).im * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    ((cosineKernel_memLp z).im.integrable_mul (Lp.memLp p.val.fst)).ofReal.const_mul I
  apply (hR.add hI).congr
  filter_upwards [] with x
  simp only [Pi.add_apply, Complex.ofReal_mul]
  rw [show (cosineKernel z x).re * (p.val.fst x : ℂ) +
      I * ((cosineKernel z x).im * (p.val.fst x : ℂ)) =
      ((cosineKernel z x).re + (cosineKernel z x).im * I) * (p.val.fst x : ℂ) by ring,
    Complex.re_add_im]

theorem cosineKernel_weighted_source (p : SourceGraph) (z : ℂ) (x : ℝ) :
    massDensity x • (cosineKernel z x * (p.val.fst x : ℂ)) =
      (phiDoobTest p.val.fst x : ℂ) * Complex.cos (z*x) := by
  simp only [cosineKernel, massDensity, phiDoobTest, Complex.ofReal_mul, real_smul]
  have hc : (Real.cosh (x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  rw [div_eq_mul_inv]
  calc
    _ = ((riemannKernelReal x : ℂ) * (p.val.fst x : ℂ) * cos (z*x)) *
        ((Real.cosh (x/2) : ℂ) * (Real.cosh (x/2) : ℂ)⁻¹) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_one]

/-- The displayed literal Fourier integral is absolutely integrable. -/
theorem integrable_graphCosineReadout_source (p : SourceGraph) (z : ℂ) :
    Integrable (fun x => (phiDoobTest p.val.fst x : ℂ) * Complex.cos (z*x)) := by
  have h := (integrable_withDensity_iff_integrable_smul'
    continuous_massDensity.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp (integrable_cosineKernel_source p z)
  apply h.congr
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (massDensity_pos x).le]
  exact cosineKernel_weighted_source p z x

theorem graphCosineReadout_eq_mass_integral (p : SourceGraph) (z : ℂ) :
    graphCosineReadout p z = ∫ x, cosineKernel z x * (p.val.fst x : ℂ) ∂massMeasure := by
  have hR : Integrable (fun x => (cosineKernel z x).re * p.val.fst x) massMeasure :=
    (cosineKernel_memLp z).re.integrable_mul (Lp.memLp p.val.fst)
  have hI : Integrable (fun x => (cosineKernel z x).im * p.val.fst x) massMeasure :=
    (cosineKernel_memLp z).im.integrable_mul (Lp.memLp p.val.fst)
  have hRc : Integrable (fun x => (((cosineKernel z x).re * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    hR.ofReal
  have hIc : Integrable (fun x => I * (((cosineKernel z x).im * p.val.fst x : ℝ) : ℂ)) massMeasure :=
    hI.ofReal.const_mul I
  rw [graphCosineReadout, inner_source_eq_integral, inner_source_eq_integral,
    ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_const_mul,
    ← integral_add hRc hIc]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.ofReal_mul]
  rw [show (cosineKernel z x).re * (p.val.fst x : ℂ) +
      I * ((cosineKernel z x).im * (p.val.fst x : ℂ)) =
      ((cosineKernel z x).re + (cosineKernel z x).im * I) * (p.val.fst x : ℂ) by ring,
    Complex.re_add_im]

/-- The continuous functional is exactly the cosine transform of the literal source. -/
theorem graphCosineReadout_eq_integral (p : SourceGraph) (z : ℂ) :
    graphCosineReadout p z = ∫ x, (phiDoobTest p.val.fst x : ℂ) * Complex.cos (z*x) := by
  rw [graphCosineReadout_eq_mass_integral]
  change (∫ x, cosineKernel z x * (p.val.fst x : ℂ)
    ∂volume.withDensity (fun x => ENNReal.ofReal (massDensity x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul continuous_massDensity.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (massDensity_pos x).le]
  exact cosineKernel_weighted_source p z x

theorem graphCosineReadout_of_source {p : SourceGraph} {f : ℝ → ℝ}
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (z : ℂ) :
    graphCosineReadout p z = ∫ x, (f x : ℂ) * Complex.cos (z*x) := by
  rw [graphCosineReadout_eq_integral]
  apply integral_congr_ae
  filter_upwards [volume_absolutelyContinuous_mass.ae_eq hp] with x hx
  rw [phiDoobTest, hx]
  simp only [phiDoobInv]
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem graphCosineReadout_neg (p : SourceGraph) (z : ℂ) :
    graphCosineReadout p (-z) = graphCosineReadout p z := by
  simp only [graphCosineReadout_eq_integral, neg_mul, Complex.cos_neg]

theorem graphCosineReadout_conj (p : SourceGraph) (z : ℂ) :
    graphCosineReadout p (conj z) = conj (graphCosineReadout p z) := by
  rw [graphCosineReadout_eq_integral, graphCosineReadout_eq_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul, Complex.conj_ofReal, ← Complex.cos_conj]

theorem graphCosineReadout_real {a : ℂ} (ha : a.im = 0) (p : SourceGraph) :
    (graphCosineReadout p a).im = 0 := by
  have hc : conj a = a := by apply Complex.ext <;> simp [ha]
  have h := congrArg Complex.im (graphCosineReadout_conj p a)
  rw [hc, Complex.conj_im] at h
  linarith

end RHTower.CHMDDoobGraph
