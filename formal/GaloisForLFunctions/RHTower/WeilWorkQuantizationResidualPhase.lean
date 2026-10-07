import GaloisForLFunctions.RHTower.WeilWorkQuantizationIntegerFloor
import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialLayerCake

/-!
# The phase of the canonical residual measure

The integer atomic floor disappears from the exponential boundary phase. If the
remaining positive measure is finite, its tail supplies every hypothesis of the
signed layer-cake estimate. Boundary zeros require no division or extra premise.
-/

open Complex Set Filter MeasureTheory
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz HamburgerStability GaloisForLFunctions.HTGeometry

/-- Endpoint inversion determines the radial reflection phase, including boundary zeros. -/
theorem quantizationCompletedTrace_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) (hny : boundaryMeasure hW {y} = 0) :
    quantizationCompletedTrace hW y =
      Complex.exp (((Real.pi * (boundaryMeasure hW).real {0} +
        2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y) : ℝ) : ℂ) * I) *
          quantizationCompletedTrace hW (-y) := by
  let θ : ℝ := Real.pi * (boundaryMeasure hW).real (Ioo 0 y) +
    Real.pi / 2 * (boundaryMeasure hW).real {0}
  have hθ : Tendsto (fun η : ℝ =>
      (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + y * I)).im)
      (𝓝[>] 0) (𝓝 θ) := by
    have ht := tendsto_re_weilContinuation_interval_endpoints hW hy
    simp only [Measure.real, hny, ENNReal.toReal_zero, mul_zero, add_zero] at ht
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    rw [← intervalIntegral.integral_of_le hy.le,
      integral_re_weilContinuation_eq_phase_sub hW (by linarith)]
    simp only [Complex.ofReal_zero, zero_mul, add_zero,
      im_quantizationLogPrimitive_real hW (by linarith : 1 / 2 < 1 / 2 + η), sub_zero]
  have hp := Complex.continuous_exp.tendsto ((2 * (θ : ℂ)) * I) |>.comp
    ((((Complex.continuous_ofReal.tendsto θ).comp hθ).const_mul (2 : ℂ)).mul_const I)
  have hc := Complex.continuous_conj.tendsto _ |>.comp (tendsto_quantizationBoundaryTrace hW y)
  have hb : quantizationBoundaryTrace hW y =
      Complex.exp ((2 * (θ : ℂ)) * I) * conj (quantizationBoundaryTrace hW y) := by
    apply tendsto_nhds_unique (tendsto_quantizationBoundaryTrace hW y)
    refine (hp.mul hc).congr' ?_
    filter_upwards [] with η
    simp only [Function.comp_apply]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [two_mul]
  have he : (2 * (θ : ℂ)) * I =
      (((Real.pi * (boundaryMeasure hW).real {0} +
        2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y)) : ℝ) : ℂ) * I := by
    dsimp only [θ]
    push_cast
    ring
  rw [he, ← quantizationBoundaryTrace_neg hW y] at hb
  simp only [quantizationCompletedTrace]
  rw [hb]
  ring

/-- Actual residual tail; its global domain is needed by the layer-cake theorem. -/
def quantizationResidualTail {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℝ :=
  (quantizationResidualMeasure hW).real (Ici (-(2 * t)))

def quantizationResidualPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ :=
  Complex.exp (((Real.pi * (boundaryMeasure hW).real {0} +
    2 * Real.pi * (quantizationResidualMeasure hW).real (Ioi 0) : ℝ) : ℂ) * I)

theorem quantizationResidualPhase_ne_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationResidualPhase hW ≠ 0 := Complex.exp_ne_zero _

theorem norm_quantizationResidualPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ‖quantizationResidualPhase hW‖ = 1 := by
  rw [quantizationResidualPhase, Complex.norm_exp]
  simp

theorem quantizationResidualTail_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    0 ≤ quantizationResidualTail hW t := ENNReal.toReal_nonneg

theorem quantizationResidualTail_mono {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) : Monotone (quantizationResidualTail hW) := by
  letI : IsFiniteMeasure (quantizationResidualMeasure hW) := ⟨hfin.lt_top⟩
  intro a b hab
  refine measureReal_mono ?_ (measure_ne_top (quantizationResidualMeasure hW) _)
  intro r hr
  change -(2 * a) ≤ r at hr
  change -(2 * b) ≤ r
  linarith

theorem quantizationResidualTail_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) (t : ℝ) :
    quantizationResidualTail hW t ≤ (quantizationResidualMeasure hW).real univ := by
  exact measureReal_mono (subset_univ _) hfin

theorem tendsto_quantizationResidualTail {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) :
    Tendsto (quantizationResidualTail hW) atBot (𝓝 0) := by
  letI : IsFiniteMeasure (quantizationResidualMeasure hW) := ⟨hfin.lt_top⟩
  have hm : Monotone (fun t : ℝ => Ici (-(2 * t))) := by
    intro a b hab r hr
    change -(2 * a) ≤ r at hr
    change -(2 * b) ≤ r
    linarith
  have he : (⋂ t : ℝ, Ici (-(2 * t))) = ∅ := by
    ext r
    simp only [mem_iInter, mem_Ici, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨-(|r| + 1), by linarith [le_abs_self r, abs_nonneg r]⟩
  have ht := tendsto_measure_iInter_atBot (μ := quantizationResidualMeasure hW)
    (fun t : ℝ => measurableSet_Ici.nullMeasurableSet) hm
    ⟨0, measure_ne_top (quantizationResidualMeasure hW) _⟩
  rw [he, measure_empty] at ht
  change Tendsto (fun t : ℝ => (quantizationResidualMeasure hW (Ici (-(2 * t)))).toReal) atBot (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

/-- The finite residual measure supplies the reflected trace phase; no trace is divided out. -/
theorem quantizationReflectedTraceF_residual_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) {t : ℝ} (ht : t < 0)
    (hno : boundaryMeasure hW {-(2 * t)} = 0) :
    quantizationReflectedTraceF hW (2 * t) = quantizationResidualPhase hW *
      Complex.exp (-(2 * Real.pi * I) * quantizationResidualTail hW t) *
        quantizationTraceF hW (2 * t) := by
  let ν := quantizationResidualMeasure hW
  let y : ℝ := -(2 * t)
  have hy : 0 < y := by dsimp [y]; linarith
  letI : IsFiniteMeasure ν := ⟨hfin.lt_top⟩
  have hμfin : boundaryMeasure hW (Ioo 0 y) ≠ ∞ := boundaryMeasure_Ioo_ne_top hW 0 y
  obtain ⟨n, hn⟩ := quantizationIntegerMeasure_nat hW measurableSet_Ioo hμfin
  have hdec := quantization_real_mass_decomposition hW measurableSet_Ioo hμfin
  have hn' : (quantizationIntegerMeasure hW).real (Ioo 0 y) = n := by
    simp only [Measure.real, hn, ENNReal.toReal_natCast]
  rw [hn'] at hdec
  have hu : Ioo 0 y ∪ Ici y = Ioi (0 : ℝ) := by
    ext r
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      rcases lt_or_ge r y with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
  have hd : Disjoint (Ioo 0 y) (Ici y) := by
    apply Set.disjoint_left.mpr
    intro r hr hr'
    exact (not_lt_of_ge hr') hr.2
  have hv := measureReal_union (μ := ν) hd measurableSet_Ici
  rw [hu] at hv
  have hm : (boundaryMeasure hW).real (Ioo 0 y) =
      ν.real (Ioi 0) - ν.real (Ici y) + n := by
    change (boundaryMeasure hW).real (Ioo 0 y) = ν.real (Ioo 0 y) + n at hdec
    linarith
  have hphase : Complex.exp (((Real.pi * (boundaryMeasure hW).real {0} +
      2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y) : ℝ) : ℂ) * I) =
      quantizationResidualPhase hW * Complex.exp (-(2 * Real.pi * I) * quantizationResidualTail hW t) := by
    have he : (((Real.pi * (boundaryMeasure hW).real {0} +
        2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y) : ℝ) : ℂ) * I) =
        (((Real.pi * (boundaryMeasure hW).real {0} + 2 * Real.pi * ν.real (Ioi 0) : ℝ) : ℂ) * I) +
        (-(2 * Real.pi * I) * (ν.real (Ici y) : ℂ)) + (n : ℂ) * (2 * Real.pi * I) := by
      rw [hm]
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
    rfl
  have htrace := quantizationCompletedTrace_phase hW hy hno
  rw [hphase] at htrace
  have hneg : -y = 2 * t := by dsimp [y]; ring
  rw [hneg] at htrace
  simp only [quantizationReflectedTraceF, quantizationTraceF]
  rw [htrace]
  ring

/-- All exceptional endpoints form a countable set, even before imposing finite remainder. -/
theorem ae_quantization_boundary_nonatom {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ᵐ t : ℝ, boundaryMeasure hW {-(2 * t)} = 0 := by
  haveI := sFinite_boundaryMeasure hW
  have hc : {r : ℝ | 0 < boundaryMeasure hW {r}}.Countable := by
    simpa using (Measure.countable_meas_level_set_pos (μ := boundaryMeasure hW)
      (g := fun r : ℝ => r) measurable_id)
  have hi : Function.Injective (fun t : ℝ => -(2 * t)) := by
    intro a b h
    linarith
  have hbad := hc.preimage hi
  apply ae_iff.mpr
  convert hbad.measure_zero volume using 1
  congr 1
  ext t
  simp [pos_iff_ne_zero]

theorem ae_quantizationReflectedTraceF_residual_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) :
    ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) = quantizationResidualPhase hW *
      Complex.exp (-(2 * Real.pi * I) * quantizationResidualTail hW t) *
        quantizationTraceF hW (2 * t) := by
  filter_upwards [ae_quantization_boundary_nonatom hW] with t ht
  exact fun ht0 => quantizationReflectedTraceF_residual_phase hW hfin ht0 ht

/-- The actual finite residual measure pays every phase premise of layer-cake cancellation. -/
theorem tendsto_quantization_residual_twist {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
      (Complex.exp (-(2 * Real.pi * I) * quantizationResidualTail hW t) - 1) *
        (quantizationTraceF hW (2 * t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_quantization_radial_monotone_twist hW (quantizationResidualTail_mono hW hfin)
    (quantizationResidualTail_nonneg hW) (quantizationResidualTail_le hW hfin)
    (tendsto_quantizationResidualTail hW hfin) hm

/-- Signed lower-half-line reflection error has no positive-integer radial residue. -/
theorem tendsto_quantization_reflection_error_lower {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hfin : quantizationResidualMeasure hW univ ≠ ∞) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
      (quantizationReflectedTraceF hW (2 * t) - quantizationResidualPhase hW * quantizationTraceF hW (2 * t)) *
        pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_quantization_residual_twist hW hfin hm).const_mul (quantizationResidualPhase hW)
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_quantizationReflectedTraceF_residual_phase hW hfin),
    ae_restrict_mem measurableSet_Iio] with t ht ht0
  rw [ht ht0]
  ring

end RHTower.WeilSpectral
