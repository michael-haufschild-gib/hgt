import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Support forced by the Xi null vector

This file supplies the measure-theoretic part of the Hedenmalm theta-pair metric
classification.  Once a positive translation-invariant Schwartz form has a spectral
measure, nullity of the completed theta transform says that the nonnegative integral of
`|XiC|²` is zero.  The results below force that measure onto the real Xi divisor and then
identify it as an atomic measure there.
-/

open Complex Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace RHTower

noncomputable section

/-- The real centered Xi divisor. -/
def xiRealZeroSet : Set ℝ := {t | XiC (t : ℂ) = 0}

/-- The squared modulus of the completed theta transform on the real spectral axis. -/
def xiRealNormSq (t : ℝ) : ℝ := ‖XiC (t : ℂ)‖ ^ 2

theorem continuous_xiRealNormSq : Continuous xiRealNormSq := by
  exact ((XiC_analytic.continuous.comp RCLike.continuous_ofReal).norm.pow 2)

theorem isClosed_xiRealZeroSet : IsClosed xiRealZeroSet := by
  exact isClosed_eq (XiC_analytic.continuous.comp RCLike.continuous_ofReal) continuous_const

theorem xiRealNormSq_nonneg (t : ℝ) : 0 ≤ xiRealNormSq t := by
  exact sq_nonneg _

theorem xiRealNormSq_eq_zero_iff (t : ℝ) :
    xiRealNormSq t = 0 ↔ t ∈ xiRealZeroSet := by
  simp [xiRealNormSq, xiRealZeroSet]

/-- A zero Xi energy integral forces the representing measure to live on the real Xi divisor. -/
theorem measureSupport_subset_xiRealZeroSet_of_integral_normSq_eq_zero
    (μ : Measure ℝ) (hint : Integrable xiRealNormSq μ)
    (hzero : ∫ t, xiRealNormSq t ∂μ = 0) :
    μ.support ⊆ xiRealZeroSet := by
  apply μ.support_subset_of_isClosed isClosed_xiRealZeroSet
  have hae : xiRealNormSq =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg xiRealNormSq_nonneg hint).mp hzero
  filter_upwards [hae] with t ht
  exact xiRealNormSq_eq_zero_iff t |>.mp ht

/-- The support of the global Xi divisor is countable.  This is extracted from the locally finite
divisor supplied by mathlib and sigma-compactness of the complex plane. -/
theorem xiDivisorSupport_univ_countable : (Set.univ : Set XiDivisorSupport).Countable := by
  have hlocal : LocallyFiniteSupport
      (fun z : ℂ => MeromorphicOn.divisor xi Set.univ z) := by
    intro z
    exact (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain' z (Set.mem_univ z)
  apply hlocal.locallyFinite_support.countable_univ
  intro ρ
  exact ⟨(ρ : ℂ), rfl⟩

noncomputable local instance : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp xiDivisorSupport_univ_countable

noncomputable local instance : Countable XiZeroCopy := inferInstance

/-- The real centered Xi divisor is countable, without assuming RH. -/
theorem xiRealZeroSet_countable : xiRealZeroSet.Countable := by
  apply (Set.countable_range (fun q : XiZeroCopy => (xiSpectralPoint q).re)).mono
  intro t ht
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp ht
  refine ⟨q, ?_⟩
  have := congrArg Complex.re hq
  simpa using this

/-- The real centered Xi divisor is Lebesgue-null, without assuming RH. -/
theorem volume_xiRealZeroSet : volume xiRealZeroSet = 0 :=
  xiRealZeroSet_countable.measure_zero volume

/-- The completed theta transform is nonzero almost everywhere on the real
spectral axis.  This is the source-specific input for ordinary `L²`
translation cyclicity. -/
theorem ae_XiC_ofReal_ne_zero : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), XiC (t : ℂ) ≠ 0 := by
  rw [ae_iff]
  simpa [xiRealZeroSet] using volume_xiRealZeroSet

/-- A measure concentrated on a measurable countable set is exactly the sum of its point masses.
This is the ambient-space form of mathlib's `Measure.sum_smul_dirac`, whose supplied statement is
for a countable underlying type. -/
theorem measure_eq_sum_smul_dirac_of_countable_ae
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) {S : Set α} (hSmeas : MeasurableSet S)
    (hScount : S.Countable) (hμS : ∀ᵐ x ∂μ, x ∈ S) :
    μ = Measure.sum (fun x : S => μ {(x : α)} • Measure.dirac (x : α)) := by
  letI : Encodable S := hScount.toEncodable
  let ν : Measure S := Measure.comap ((↑) : S → α) μ
  have hmap : ν.map ((↑) : S → α) = μ := by
    dsimp only [ν]
    rw [map_comap_subtype_coe hSmeas,
      Measure.restrict_eq_self_of_ae_mem hμS]
  calc
    μ = ν.map ((↑) : S → α) := hmap.symm
    _ = (Measure.sum (fun x : S => ν {x} • Measure.dirac x)).map
        ((↑) : S → α) := by rw [ν.sum_smul_dirac]
    _ = Measure.sum (fun x : S => μ {(x : α)} • Measure.dirac (x : α)) := by
      rw [Measure.map_sum measurable_subtype_coe.aemeasurable]
      apply congrArg Measure.sum
      funext x
      rw [Measure.map_smul, Measure.map_dirac]
      have hx : ν {x} = μ {(x : α)} := by
        dsimp only [ν]
        rw [comap_subtype_coe_apply hSmeas]
        simp
      rw [hx]

/-- Every measure concentrated on the real Xi divisor is an atomic Xi-zero measure. -/
theorem measure_eq_sum_smul_dirac_xiRealZeroSet
    (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, t ∈ xiRealZeroSet) :
    μ = Measure.sum
      (fun t : xiRealZeroSet => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) := by
  exact measure_eq_sum_smul_dirac_of_countable_ae μ
    isClosed_xiRealZeroSet.measurableSet xiRealZeroSet_countable hμ

/-- The complete support-to-atomicity conclusion forced by a null completed-theta vector. -/
theorem measure_eq_sum_smul_dirac_xiRealZeroSet_of_integral_normSq_eq_zero
    (μ : Measure ℝ) (hint : Integrable xiRealNormSq μ)
    (hzero : ∫ t, xiRealNormSq t ∂μ = 0) :
    μ = Measure.sum
      (fun t : xiRealZeroSet => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) := by
  have hsupp :=
    measureSupport_subset_xiRealZeroSet_of_integral_normSq_eq_zero μ hint hzero
  apply measure_eq_sum_smul_dirac_xiRealZeroSet
  filter_upwards [μ.support_mem_ae] with t ht
  exact hsupp ht

end

end RHTower
