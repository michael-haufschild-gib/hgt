import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.GelfondSchneider
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual two-prime physical phase law

The Fourier mass of a physical source pushes onto a null union of affine lines in the two
independent phase coordinates. In particular, the actual normalized Weil ground has no density
relative to the independent uniform phase law. Nevertheless, the literal primes 2 and 3 recover
frequency measurably, so their joint law determines the full physical spectral measure and
retains every nonnegative spectral cost, including the exact shifted Gamma weight.

This excludes an exact independent-density identification. It does not exclude approximation
of finitely many phase correlations, prove the joint prime--polar--Gamma sign, or prove RH.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace RHTower

/-- Fractional coordinates of the literal prime phases at the unitary Fourier frequency. -/
def ccmTwoPrimePhysicalPhase (t : ℝ) : ℝ × ℝ :=
  (Int.fract (-t * Real.log 2), Int.fract (-t * Real.log 3))

private theorem phase_measurable : Measurable ccmTwoPrimePhysicalPhase := by
  exact ((measurable_id.neg.mul_const _).fract).prodMk
    ((measurable_id.neg.mul_const _).fract)

def ccmTwoPrimePhysicalPhaseSupport : Set (ℝ × ℝ) :=
  ⋃ m : ℤ, ⋃ n : ℤ, {z | Real.log 3 * z.1 - Real.log 2 * z.2 =
    Real.log 2 * n - Real.log 3 * m}

private theorem support_measurable : MeasurableSet ccmTwoPrimePhysicalPhaseSupport := by
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iUnion
  intro n
  exact (isClosed_eq ((continuous_const.mul continuous_fst).sub
    (continuous_const.mul continuous_snd)) continuous_const).measurableSet

private theorem phase_mem_support (t : ℝ) :
    ccmTwoPrimePhysicalPhase t ∈ ccmTwoPrimePhysicalPhaseSupport := by
  apply mem_iUnion.mpr
  refine ⟨⌊-t * Real.log 2⌋, mem_iUnion.mpr ⟨⌊-t * Real.log 3⌋, ?_⟩⟩
  change Real.log 3 * Int.fract (-t * Real.log 2) -
    Real.log 2 * Int.fract (-t * Real.log 3) = _
  have h2 := Int.fract_add_floor (-t * Real.log 2)
  have h3 := Int.fract_add_floor (-t * Real.log 3)
  linear_combination Real.log 3 * h2 - Real.log 2 * h3

/-- The reference marginal of two independent uniform prime phases. -/
def ccmIndependentTwoPrimePhaseLaw : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

/-- The literal physical phase orbit has zero independent phase mass. -/
theorem ccmTwoPrimePhysicalPhaseSupport_null :
    ccmIndependentTwoPrimePhaseLaw ccmTwoPrimePhysicalPhaseSupport = 0 := by
  apply measure_iUnion_null
  intro m
  apply measure_iUnion_null
  intro n
  have hs : MeasurableSet {z : ℝ × ℝ | Real.log 3 * z.1 - Real.log 2 * z.2 =
      Real.log 2 * n - Real.log 3 * m} :=
    (isClosed_eq ((continuous_const.mul continuous_fst).sub
      (continuous_const.mul continuous_snd)) continuous_const).measurableSet
  rw [ccmIndependentTwoPrimePhaseLaw, Measure.prod_apply hs]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hsections : ∀ x : ℝ, (Prod.mk x ⁻¹'
      {z : ℝ × ℝ | Real.log 3 * z.1 - Real.log 2 * z.2 =
        Real.log 2 * n - Real.log 3 * m}) =
      {(Real.log 3 * x - (Real.log 2 * n - Real.log 3 * m)) / Real.log 2} := by
    intro x
    ext y
    simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
    rw [eq_div_iff hlog]
    constructor <;> intro h <;> linarith
  simp_rw [hsections]
  simp

/-- Fourier mass of the physical source, before taking prime phases. -/
def ccmPhysicalFourierMeasure (f : SoninL2) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (‖fourierUnitary f t‖ ^ 2))

/-- Actual joint prime phase law, with its physical source unchanged. -/
def ccmPhysicalTwoPrimePhaseLaw (f : SoninL2) : Measure (ℝ × ℝ) :=
  Measure.map ccmTwoPrimePhysicalPhase (ccmPhysicalFourierMeasure f)

private theorem fourier_density_measurable (f : SoninL2) :
    AEMeasurable (fun t => ENNReal.ofReal (‖fourierUnitary f t‖ ^ 2)) volume :=
  ((Lp.aestronglyMeasurable (fourierUnitary f)).norm.pow 2).aemeasurable.ennreal_ofReal

/-- Exact Plancherel mass; there is no normalization assumption on the source. -/
theorem ccmPhysicalFourierMeasure_univ (f : SoninL2) :
    ccmPhysicalFourierMeasure f univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [ccmPhysicalFourierMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num))
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖fourierUnitary f t‖))]
  rw [← norm_sq_eq_integral, fourierUnitary.norm_map]

/-- The null orbit carries every bit of the actual source's mass. -/
theorem ccmPhysicalTwoPrimePhaseLaw_support_mass (f : SoninL2) :
    ccmPhysicalTwoPrimePhaseLaw f ccmTwoPrimePhysicalPhaseSupport =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [ccmPhysicalTwoPrimePhaseLaw, Measure.map_apply phase_measurable support_measurable]
  have hpre : ccmTwoPrimePhysicalPhase ⁻¹' ccmTwoPrimePhysicalPhaseSupport = univ := by
    ext t
    simp [phase_mem_support]
  rw [hpre, ccmPhysicalFourierMeasure_univ]

/-- Every physical source gives a singular joint phase law, including the zero source. -/
theorem ccmPhysicalTwoPrimePhaseLaw_mutuallySingular (f : SoninL2) :
    (ccmPhysicalTwoPrimePhaseLaw f).MutuallySingular ccmIndependentTwoPrimePhaseLaw := by
  refine ⟨ccmTwoPrimePhysicalPhaseSupportᶜ, support_measurable.compl, ?_, ?_⟩
  · rw [ccmPhysicalTwoPrimePhaseLaw, Measure.map_apply phase_measurable support_measurable.compl]
    have hpre : ccmTwoPrimePhysicalPhase ⁻¹' ccmTwoPrimePhysicalPhaseSupportᶜ = ∅ := by
      ext t
      simp [phase_mem_support]
    rw [hpre, measure_empty]
  · simpa only [compl_compl] using ccmTwoPrimePhysicalPhaseSupport_null

/-- Actual normalized ground: no independent-phase density can be its joint law. -/
theorem ccmNormalizedGroundTwoPrimePhaseLaw_not_absolutelyContinuous
    (a : SuzukiPositiveAperture) :
    ¬ ccmPhysicalTwoPrimePhaseLaw
      (ccmArchimedeanFormToAperture a (ccmRestrictedWeilNormalizedGroundFormVector a)) ≪
        ccmIndependentTwoPrimePhaseLaw := by
  intro h
  have hzero := h ccmTwoPrimePhysicalPhaseSupport_null
  rw [ccmPhysicalTwoPrimePhaseLaw_support_mass] at hzero
  have hn := norm_ccmRestrictedWeilNormalizedGroundFormVector_embedding a
  change ‖(ccmArchimedeanFormToAperture a
    (ccmRestrictedWeilNormalizedGroundFormVector a) : SoninL2)‖ = 1 at hn
  rw [hn] at hzero
  norm_num at hzero

/-- In particular, no square density over independent phases equals the actual ground law. -/
theorem ccmNormalizedGroundTwoPrimePhaseLaw_ne_withDensity
    (a : SuzukiPositiveAperture) (d : ℝ × ℝ → ℝ≥0∞) :
    ccmPhysicalTwoPrimePhaseLaw
      (ccmArchimedeanFormToAperture a (ccmRestrictedWeilNormalizedGroundFormVector a)) ≠
        ccmIndependentTwoPrimePhaseLaw.withDensity d := by
  intro h
  apply ccmNormalizedGroundTwoPrimePhaseLaw_not_absolutelyContinuous a
  rw [h]
  exact withDensity_absolutelyContinuous _ _

/-- Injectivity is arithmetic: the two literal prime logarithms are incommensurate. -/
theorem ccmTwoPrimePhysicalPhase_injective : Function.Injective ccmTwoPrimePhysicalPhase := by
  intro x y hxy
  obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp (congrArg Prod.fst hxy)
  obtain ⟨n, hn⟩ := Int.fract_eq_fract.mp (congrArg Prod.snd hxy)
  change -x * Real.log 2 - -y * Real.log 2 = (m : ℝ) at hm
  change -x * Real.log 3 - -y * Real.log 3 = (n : ℝ) at hn
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  by_contra hne
  have hm0 : m ≠ 0 := by
    intro hz
    have he : (y - x) * Real.log 2 = 0 := by
      rw [hz, Int.cast_zero] at hm
      linear_combination hm
    have := (mul_eq_zero.mp he).resolve_right hlog
    exact hne (by linarith)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hratio : Real.log 3 / Real.log 2 = (n : ℝ) / (m : ℝ) := by
    apply (div_eq_div_iff hlog hmR).mpr
    rw [← hm, ← hn]
    ring
  exact (irrational_iff_ne_rational _).mp
    (GaloisForLFunctions.RHTower.irrational_log_ratio
      (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)) n m hm0 hratio

/-- Borel reconstruction survives despite singularity relative to independent phases. -/
theorem ccmTwoPrimePhysicalPhase_measurableEmbedding :
    MeasurableEmbedding ccmTwoPrimePhysicalPhase :=
  phase_measurable.measurableEmbedding ccmTwoPrimePhysicalPhase_injective

/-- Joint physical phases determine the complete spectral measure. -/
theorem ccmTwoPrimePhysicalPhase_map_injective :
    Function.Injective (Measure.map ccmTwoPrimePhysicalPhase) :=
  ccmTwoPrimePhysicalPhase_measurableEmbedding.map_injective

/-- Recover the real frequency on the physical phase orbit; zero off the orbit. -/
def ccmTwoPrimePhysicalFrequency : ℝ × ℝ → ℝ :=
  Function.extend ccmTwoPrimePhysicalPhase id (fun _ => 0)

theorem ccmTwoPrimePhysicalFrequency_measurable : Measurable ccmTwoPrimePhysicalFrequency :=
  ccmTwoPrimePhysicalPhase_measurableEmbedding.measurable_extend measurable_id measurable_const

theorem ccmTwoPrimePhysicalFrequency_phase (t : ℝ) :
    ccmTwoPrimePhysicalFrequency (ccmTwoPrimePhysicalPhase t) = t :=
  ccmTwoPrimePhysicalPhase_injective.extend_apply _ _ _

/-- Every nonnegative physical spectral cost is recovered exactly from the joint phase law.
This includes the full Gamma weight, without an independence or integrability premise. -/
theorem ccmPhysicalTwoPrimePhaseLaw_recover_spectral_cost
    (f : SoninL2) (W : ℝ → ℝ≥0∞) :
    (∫⁻ z, W (ccmTwoPrimePhysicalFrequency z) ∂ccmPhysicalTwoPrimePhaseLaw f) =
      ∫⁻ t, W t ∂ccmPhysicalFourierMeasure f := by
  rw [ccmPhysicalTwoPrimePhaseLaw,
    ccmTwoPrimePhysicalPhase_measurableEmbedding.lintegral_map]
  simp_rw [ccmTwoPrimePhysicalFrequency_phase]

/-- The actual shifted archimedean weight, recovered without replacing it by a degree cost. -/
theorem ccmPhysicalTwoPrimePhaseLaw_recover_Gamma_cost (f : SoninL2) :
    (∫⁻ z, ENNReal.ofReal (ccmArchimedeanFormWeight (ccmTwoPrimePhysicalFrequency z))
      ∂ccmPhysicalTwoPrimePhaseLaw f) =
      ∫⁻ t, ENNReal.ofReal (‖fourierUnitary f t‖ ^ 2) *
        ENNReal.ofReal (ccmArchimedeanFormWeight t) := by
  rw [ccmPhysicalTwoPrimePhaseLaw_recover_spectral_cost f
    (fun t => ENNReal.ofReal (ccmArchimedeanFormWeight t)), ccmPhysicalFourierMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ (fourier_density_measurable f)
      measurable_ccmArchimedeanFormWeight.ennreal_ofReal.aemeasurable]
  rfl

end RHTower
