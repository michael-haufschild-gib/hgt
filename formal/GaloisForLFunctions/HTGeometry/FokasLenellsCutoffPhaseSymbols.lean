import GaloisForLFunctions.HTGeometry.FokasLenellsPhaseDistance
import GaloisForLFunctions.HTGeometry.L2DominatedDerivative

/-!
# A unitary cutoff of the singular reciprocal frequency

The explicit positive width exp(a) freezes the reciprocal frequency inside
its symmetric excluded interval. The resulting phase remains unitary, with
a bounded time generator whose exact norm is the reciprocal cutoff width.
-/

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The retained spectral set outside the concrete positive width exp(a). -/
def cutoffPhaseSet (a : ℝ) : Set ℝ := {z | Real.exp a ≤ |z|}

/-- The reciprocal time frequency, frozen to zero on the excluded interval. -/
def cutoffPhaseFrequency (a z : ℝ) : ℝ :=
  (cutoffPhaseSet a).indicator (fun z => (2*z)⁻¹) z

/-- The sharp candidate generator norm, with positivity built into its definition. -/
def cutoffPhaseBudget (a : ℝ) : ℝ := (2 * Real.exp a)⁻¹

/-- The cutoff frequency budget is strictly positive at every real width parameter. -/
theorem cutoffPhaseBudget_pos (a : ℝ) : 0 < cutoffPhaseBudget a := by
  unfold cutoffPhaseBudget
  positivity

/-- The retained set is measurable, including its two endpoints. -/
theorem measurableSet_cutoffPhaseSet (a : ℝ) : MeasurableSet (cutoffPhaseSet a) :=
  measurableSet_le measurable_const (by fun_prop)

/-- The actual cutoff reciprocal frequency is measurable. -/
theorem measurable_cutoffPhaseFrequency (a : ℝ) : Measurable (cutoffPhaseFrequency a) := by
  exact (by fun_prop : Measurable (fun z : ℝ => (2*z)⁻¹)).indicator (measurableSet_cutoffPhaseSet a)

/-- The spectral cutoff bounds the reciprocal generator by the exact candidate constant. -/
theorem abs_cutoffPhaseFrequency_le (a z : ℝ) :
    |cutoffPhaseFrequency a z| ≤ cutoffPhaseBudget a := by
  by_cases hz : z ∈ cutoffPhaseSet a
  · rw [cutoffPhaseFrequency, indicator_of_mem hz, abs_inv, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    change (2*|z|)⁻¹ ≤ (2*Real.exp a)⁻¹
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hz (by norm_num)
  · rw [cutoffPhaseFrequency, indicator_of_notMem hz, abs_zero]
    exact (cutoffPhaseBudget_pos a).le

/-- The actual cutoff phase retains unit modulus everywhere. -/
def cutoffPhase (a t z : ℝ) : ℂ :=
  Complex.exp (-((t * cutoffPhaseFrequency a z : ℝ) : ℂ) * I)

/-- The first time derivative symbol of the cutoff phase. -/
def cutoffPhaseTimeSymbol (a t z : ℝ) : ℂ :=
  (-((cutoffPhaseFrequency a z : ℝ) : ℂ) * I) * cutoffPhase a t z

/-- Freezing the singular frequency preserves unit modulus, including on the excluded interval. -/
theorem norm_cutoffPhase (a t z : ℝ) : ‖cutoffPhase a t z‖ = 1 := by
  rw [cutoffPhase, Complex.norm_exp]
  simp

/-- The cutoff phase is measurable at every time. -/
theorem measurable_cutoffPhase (a t : ℝ) : Measurable (cutoffPhase a t) := by
  have hm := measurable_cutoffPhaseFrequency a
  unfold cutoffPhase
  fun_prop

/-- The time generator has exactly the modulus of the cutoff frequency. -/
theorem norm_cutoffPhaseTimeSymbol (a t z : ℝ) :
    ‖cutoffPhaseTimeSymbol a t z‖ = |cutoffPhaseFrequency a z| := by
  simp [cutoffPhaseTimeSymbol, norm_cutoffPhase]

/-- The actual time generator is uniformly bounded by its cutoff budget. -/
theorem cutoffPhaseTimeSymbol_bound (a t z : ℝ) :
    ‖cutoffPhaseTimeSymbol a t z‖ ≤ cutoffPhaseBudget a := by
  rw [norm_cutoffPhaseTimeSymbol]
  exact abs_cutoffPhaseFrequency_le a z

/-- The actual time generator is measurable. -/
theorem measurable_cutoffPhaseTimeSymbol (a t : ℝ) : Measurable (cutoffPhaseTimeSymbol a t) := by
  have hm := measurable_cutoffPhaseFrequency a
  have hp := measurable_cutoffPhase a t
  unfold cutoffPhaseTimeSymbol
  fun_prop

/-- Differentiating the cutoff phase gives its actual generator at every spectral point. -/
theorem cutoffPhase_hasDerivAt (a t z : ℝ) :
    HasDerivAt (fun s => cutoffPhase a s z) (cutoffPhaseTimeSymbol a t z) t := by
  have h := (((hasDerivAt_id t).mul_const (cutoffPhaseFrequency a z)).ofReal_comp.neg.mul_const I).cexp
  convert! h using 1
  simp only [cutoffPhaseTimeSymbol, cutoffPhase, one_mul, Pi.neg_apply, id_eq]
  ring

/-- The actual cutoff phase defines an ordinary L-infinity class. -/
def cutoffPhaseLinfty (a t : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (measurable_cutoffPhase a t).aestronglyMeasurable 1
    (.of_forall fun z => (norm_cutoffPhase a t z).le)).toLp _

/-- The phase class agrees with its actual bounded symbol almost everywhere. -/
theorem cutoffPhaseLinfty_ae (a t : ℝ) :
    (cutoffPhaseLinfty a t : ℝ → ℂ) =ᵐ[volume] cutoffPhase a t :=
  (memLp_top_of_bound (measurable_cutoffPhase a t).aestronglyMeasurable 1
    (.of_forall fun z => (norm_cutoffPhase a t z).le)).coeFn_toLp

/-- The actual cutoff time generator defines an ordinary L-infinity class. -/
def cutoffPhaseTimeLinfty (a t : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (measurable_cutoffPhaseTimeSymbol a t).aestronglyMeasurable
    (cutoffPhaseBudget a) (.of_forall (cutoffPhaseTimeSymbol_bound a t))).toLp _

/-- The generator class agrees with its actual symbol almost everywhere. -/
theorem cutoffPhaseTimeLinfty_ae (a t : ℝ) :
    (cutoffPhaseTimeLinfty a t : ℝ → ℂ) =ᵐ[volume] cutoffPhaseTimeSymbol a t :=
  (memLp_top_of_bound (measurable_cutoffPhaseTimeSymbol a t).aestronglyMeasurable
    (cutoffPhaseBudget a) (.of_forall (cutoffPhaseTimeSymbol_bound a t))).coeFn_toLp

private theorem linfty_norm_lower_of_right_trace
    (g : Lp ℂ ∞ (volume : Measure ℝ)) (φ : ℝ → ℂ) (c L : ℝ)
    (hg : (g : ℝ → ℂ) =ᵐ[volume] φ)
    (ht : Tendsto (fun z => ‖φ z‖) (𝓝[>] c) (𝓝 L)) : L ≤ ‖g‖ := by
  have hbound : ∀ᵐ z ∂volume, ‖φ z‖ ≤ ‖g‖ := by
    have h := ae_le_lpNorm_exponent_top (Lp.memLp g)
    rw [← toReal_eLpNorm (Lp.memLp g).1, ← Lp.norm_def] at h
    filter_upwards [h,hg] with z hz he
    rwa [he] at hz
  by_contra hn
  have hlt : ‖g‖ < L := lt_of_not_ge hn
  obtain ⟨d,hd,hI⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually_const_lt hlt)
  have hzero : volume {z : ℝ | ‖g‖ < ‖φ z‖} = 0 := by
    have h := hbound.mono fun z hz => not_lt.mpr hz
    simpa only [ae_iff,not_not] using h
  have hi := measure_mono_null hI hzero
  have hp : 0 < volume (Ioo c d) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hd)
  exact hp.ne' hi

private theorem cutoffPhaseFrequency_right_trace (a : ℝ) :
    Tendsto (fun z => |cutoffPhaseFrequency a z|) (𝓝[>] Real.exp a) (𝓝 (cutoffPhaseBudget a)) := by
  have hc : ContinuousAt (fun z : ℝ => (2*z)⁻¹) (Real.exp a) := by fun_prop (disch := positivity)
  apply hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzpos : 0 < z := (Real.exp_pos a).trans hz
  have hm : z ∈ cutoffPhaseSet a := by
    change Real.exp a ≤ |z|
    rw [abs_of_pos hzpos]
    exact hz.le
  rw [cutoffPhaseFrequency, indicator_of_mem hm, abs_of_pos (by positivity)]

/-- The cutoff time generator's exact L-infinity norm is the reciprocal cutoff width, at every time. -/
theorem norm_cutoffPhaseTimeLinfty (a t : ℝ) :
    ‖cutoffPhaseTimeLinfty a t‖ = cutoffPhaseBudget a := by
  apply le_antisymm
  · rw [Lp.norm_def,eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (cutoffPhaseBudget_pos a).le
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [cutoffPhaseTimeLinfty_ae a t] with z hz
    rw [hz]
    exact cutoffPhaseTimeSymbol_bound a t z
  · apply linfty_norm_lower_of_right_trace _ _ (Real.exp a) _ (cutoffPhaseTimeLinfty_ae a t)
    simpa only [norm_cutoffPhaseTimeSymbol] using cutoffPhaseFrequency_right_trace a

end
end GaloisForLFunctions.HTGeometry.FokasLenells
