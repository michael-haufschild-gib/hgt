import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoff

/-! Joint compact physical exhaustion of the literal full two-event Peierls density. -/

open Set MeasureTheory Filter Topology
namespace RHTower.D4BMFullAngularCausalPeierls
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullAngularCircle D4BMFullAngularReconstruction
open D4BMFullAngularGrowth D4BMFullSourceAdvanced
open D4BMLiteralCyclicPeierls
noncomputable section
set_option autoImplicit false

/-- The full two-event density with the same strict physical window on both events. -/
def cutoffFullSourcePairDensity (n : ℕ) (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (z : Event × Event) : ℂ :=
  (physicalWindow n z.1 : ℂ) * (physicalWindow n z.2 : ℂ) *
    fullSourcePairDensity q branch b c a d X k z

private theorem cutoff_full_pair_aestronglyMeasurable (n : ℕ) (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    AEStronglyMeasurable (cutoffFullSourcePairDensity n q branch b c a d X k)
      (eventMeasure.prod eventMeasure) := by
  have hw1 : Continuous (fun z : Event × Event => (physicalWindow n z.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((physicalWindow_smooth n).continuous.comp continuous_fst)
  have hw2 : Continuous (fun z : Event × Event => (physicalWindow n z.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((physicalWindow_smooth n).continuous.comp continuous_snd)
  unfold cutoffFullSourcePairDensity
  exact (hw1.aestronglyMeasurable.mul hw2.aestronglyMeasurable).mul
    (fullSourcePairDensity_integrable q branch b c a d X k).aestronglyMeasurable

private theorem cutoff_full_pair_norm_le (n : ℕ) (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (z : Event × Event) :
    ‖cutoffFullSourcePairDensity n q branch b c a d X k z‖ ≤
      ‖fullSourcePairDensity q branch b c a d X k z‖ := by
  have h1n := physicalWindow_nonneg n z.1
  have h2n := physicalWindow_nonneg n z.2
  have h1 := physicalWindow_le_one n z.1
  have h2 := physicalWindow_le_one n z.2
  have h12 : physicalWindow n z.1 * physicalWindow n z.2 ≤ 1 := by
    calc
      physicalWindow n z.1 * physicalWindow n z.2 ≤ 1 * physicalWindow n z.2 :=
        mul_le_mul_of_nonneg_right h1 h2n
      _ = physicalWindow n z.2 := by ring
      _ ≤ 1 := h2
  have hf := norm_nonneg (fullSourcePairDensity q branch b c a d X k z)
  unfold cutoffFullSourcePairDensity
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1n, abs_of_nonneg h2n]
  calc
    physicalWindow n z.1 * physicalWindow n z.2 *
        ‖fullSourcePairDensity q branch b c a d X k z‖ ≤
        1 * ‖fullSourcePairDensity q branch b c a d X k z‖ :=
      mul_le_mul_of_nonneg_right h12 hf
    _ = ‖fullSourcePairDensity q branch b c a d X k z‖ := by ring

private theorem ae_physical_pair :
    ∀ᵐ z : Event × Event ∂eventMeasure.prod eventMeasure, z.1.2 < 0 ∧ z.2.2 < 0 := by
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  apply (Measure.ae_prod_iff_ae_ae
    (((isOpen_lt continuous_fst.snd continuous_const).inter
      (isOpen_lt continuous_snd.snd continuous_const)).measurableSet :
        MeasurableSet {z : Event × Event | z.1.2 < 0 ∧ z.2.2 < 0})).mpr
  filter_upwards [he] with p hp
  filter_upwards [he] with r hr
  exact ⟨hp, hr⟩

/-- The literal full two-event density is the dominated limit of compact smooth physical
cutoffs on both events simultaneously. -/
theorem cutoffFullSourcePairDensity_integral_tendsto (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => ∫ z, cutoffFullSourcePairDensity n q branch b c a d X k z
      ∂eventMeasure.prod eventMeasure) atTop
      (𝓝 (∫ z, fullSourcePairDensity q branch b c a d X k z ∂eventMeasure.prod eventMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun z => ‖fullSourcePairDensity q branch b c a d X k z‖)
  · intro n
    exact cutoff_full_pair_aestronglyMeasurable n q branch b c a d X k
  · exact (fullSourcePairDensity_integrable q branch b c a d X k).norm
  · intro n
    exact ae_of_all _ (cutoff_full_pair_norm_le n q branch b c a d X k)
  · filter_upwards [ae_physical_pair] with z hz
    apply Filter.EventuallyEq.tendsto
    filter_upwards [physicalWindow_eventually_eq_one z.1 hz.1,
      physicalWindow_eventually_eq_one z.2 hz.2] with n hn1 hn2
    simp [cutoffFullSourcePairDensity, hn1, hn2]

end
end RHTower.D4BMFullAngularCausalPeierls
