import GaloisForLFunctions.HeckeLFunctions.HeckeDualFrequenciesHaveClassGenerators
import GaloisForLFunctions.HeckeLFunctions.HeckeDualThetaKernelsAreUnitCovariant
import GaloisForLFunctions.HeckeLFunctions.HeckeFieldElementKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HTGeometry.NumberFieldLogPeriodizationsHaveAbsoluteUnfolding
import GaloisForLFunctions.HTGeometry.NumberFieldUnitsAreTorsionTimesLogLattice

/-!
# Absolute unfolding of the actual dual Hecke unit orbits

The trace-dual Gaussian majorant controls the full class/unit series.
The fractional-ideal orbit equivalence, torsion/log-lattice decomposition,
and actual unit covariance identify dual theta minus its zero mode with
a paired logarithmic periodization. A single summable majorant proves
absolute whole-log unfolding with the exact torsion order. Haar negation
then gives the positive-profile integrals used in the Mellin calculation.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "D" => numberFieldUnitLogDomain K
local notation "L" => Units.unitLattice K

local instance : Countable L :=
  Countable.of_equiv (Fin (Units.rank K) → ℤ) (Units.basisUnitLattice K).equivFun.symm.toEquiv

variable (𝔪 : Modulus K) {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

/-- A class generator multiplied by a unit is an actual trace-dual frequency. -/
def heckeDualClassUnitFrequency (p : heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ) : Jdual :=
  ⟨(fractionalClassUnitElement (heckeDualIdealUnit 𝔪 hb0) p).1,
    (fractionalClassUnitElement (heckeDualIdealUnit 𝔪 hb0) p).2.1⟩

/-- Distinct class/unit coordinates give distinct actual frequencies. -/
theorem heckeDualClassUnitFrequency_injective :
    Function.Injective (heckeDualClassUnitFrequency 𝔪 hb0) := by
  intro p q h
  apply fractionalClassUnitElement_injective (heckeDualIdealUnit 𝔪 hb0)
  exact Subtype.ext (congrArg (fun a : Jdual => (a : K)) h)

include hb0 in
/-- The dual Gaussian majorant proves absolute convergence on the full trace-dual ideal. -/
theorem summable_norm_heckeDualThetaKernel (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun a : Jdual => ‖heckeDualThetaKernel 𝔪 hb ψ y t (a : K)‖) := by
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeDualThetaKernel_majorant 𝔪 hb hb0 ψ ht
    (∑ v : InfinitePlace K, |y v|)
  apply hu.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro a
  apply hbound y _ t le_rfl a
  intro v
  exact (le_abs_self _).trans (Finset.single_le_sum (fun w _ => abs_nonneg (y w))
    (Finset.mem_univ v))

/-- Absolute convergence is preserved by the exact fractional class/unit parametrization. -/
theorem summable_norm_heckeDualClassUnitKernels (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ =>
      ‖heckeDualThetaKernel 𝔪 hb ψ y t
        (((p.2 : 𝓞 K) : K) * (heckeDualClassFrequency 𝔪 hb0 p.1 : K))‖) := by
  exact (summable_norm_heckeDualThetaKernel 𝔪 hb hb0 ψ y ht).comp_injective
    (i := heckeDualClassUnitFrequency 𝔪 hb0) (heckeDualClassUnitFrequency_injective 𝔪 hb0)

/-- Removing the actual Fourier-weighted zero mode leaves precisely the nonzero fractional elements. -/
theorem heckeDualIdealTheta_sub_constant_eq_tsum_nonzero (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeDualIdealTheta 𝔪 hb ψ y t - heckeDualThetaConstant 𝔪 ψ =
      ∑' a : nonzeroFractionalIdealElements (heckeDualIdealUnit 𝔪 hb0 : FI),
        heckeDualThetaKernel 𝔪 hb ψ y t a.1 := by
  let e : ↥{a : Jdual | (a : K) ≠ 0} ≃
      nonzeroFractionalIdealElements (heckeDualIdealUnit 𝔪 hb0 : FI) :=
    { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : (∑' a : nonzeroFractionalIdealElements (heckeDualIdealUnit 𝔪 hb0 : FI),
      heckeDualThetaKernel 𝔪 hb ψ y t a.1) =
      ∑' a : Jdual, if (a : K) = 0 then 0 else heckeDualThetaKernel 𝔪 hb ψ y t (a : K) := by
    rw [← e.tsum_eq]
    change (∑' a : ↥{a : Jdual | (a : K) ≠ 0},
      heckeDualThetaKernel 𝔪 hb ψ y t (a.1 : K)) = _
    simpa only [Set.indicator, Set.mem_setOf_eq, ne_eq, ite_not] using
      (tsum_subtype {a : Jdual | (a : K) ≠ 0}
        (fun a : Jdual => heckeDualThetaKernel 𝔪 hb ψ y t (a : K)))
  have hs := (summable_norm_heckeDualThetaKernel 𝔪 hb hb0 ψ y ht).of_norm.tsum_eq_add_tsum_ite
    (⟨0, (Jdual).zero_mem⟩ : Jdual)
  simp only [Subtype.ext_iff, heckeDualThetaKernel, heckeDualTheta_zero_term] at hs
  rw [heckeDualIdealTheta, he]
  change (∑' a : Jdual, finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
    heckeParityKernel 𝔪 ψ y t (a : K)) - _ = _
  exact sub_eq_iff_eq_add.mpr (hs.trans (add_comm _ _))

/-- Nonzero dual theta is the absolutely convergent sum of its fractional class/unit orbits. -/
theorem heckeDualIdealTheta_sub_constant_eq_classUnitSum (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) {t : ℝ} (ht : 0 < t) :
    heckeDualIdealTheta 𝔪 hb ψ y t - heckeDualThetaConstant 𝔪 ψ =
      ∑' I : heckeDualClassIdeals 𝔪 hb0, ∑' u : (𝓞 K)ˣ,
        heckeDualThetaKernel 𝔪 hb ψ y t
          (((u : 𝓞 K) : K) * (heckeDualClassFrequency 𝔪 hb0 I : K)) := by
  rw [heckeDualIdealTheta_sub_constant_eq_tsum_nonzero 𝔪 hb hb0 ψ y ht,
    ← (nonzeroFractionalIdealElementsEquivClassUnits (heckeDualIdealUnit 𝔪 hb0)).symm.tsum_eq]
  change (∑' p : heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ,
    heckeDualThetaKernel 𝔪 hb ψ y t
      (((p.2 : 𝓞 K) : K) * (heckeDualClassFrequency 𝔪 hb0 p.1 : K))) = _
  exact (summable_norm_heckeDualClassUnitKernels 𝔪 hb hb0 ψ y ht).of_norm.tsum_prod

include hb0 in
/-- Torsion disappears from the dual kernel; its logarithmic translate has a positive sign. -/
theorem heckeDualThetaKernel_torsionLogLattice (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (x : logSpace K) (t : ℝ)
    (a : Jdual) (ζ : Units.torsion K) (l : L) :
    heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
      ((((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (ζ, l) : 𝓞 K) : K) * (a : K)) =
      heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (l : logSpace K))) t
        (a : K) := by
  rw [heckeDualThetaKernel_unit_as_negativeLogTranslate 𝔪 hb hb0 ψ hψ,
    logEmbedding_numberFieldUnitsEquivTorsionLogLattice_symm]

/-- A dual unit orbit is its log-lattice periodization times the exact torsion order. -/
theorem tsum_heckeDualClassUnitOrbit_eq_logPeriodization (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (I : heckeDualClassIdeals 𝔪 hb0)
    (x : logSpace K) {t : ℝ} (ht : 0 < t) :
    (∑' u : (𝓞 K)ˣ, heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
      (((u : 𝓞 K) : K) * (heckeDualClassFrequency 𝔪 hb0 I : K))) =
      (Units.torsionOrder K : ℂ) * ∑' l : L,
        heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (l : logSpace K))) t
          (heckeDualClassFrequency 𝔪 hb0 I : K) := by
  let e := numberFieldUnitsEquivTorsionLogLattice (K := K)
  have hunit := (summable_norm_heckeDualClassUnitKernels 𝔪 hb hb0 ψ
    (-numberFieldWeightedLogProfile x) ht).comp_injective
      (i := fun u : (𝓞 K)ˣ => (I, u)) (fun _ _ h => congrArg Prod.snd h)
  have hs := hunit.of_norm.comp_injective (i := e.symm) e.symm.injective
  simp only [Function.comp_def] at hs
  rw [← e.symm.tsum_eq, hs.tsum_prod]
  dsimp only [e]
  simp_rw [heckeDualThetaKernel_torsionLogLattice 𝔪 hb hb0 ψ hψ]
  letI := Fintype.ofFinite (Units.torsion K)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Units.torsionOrder, Nat.card_eq_fintype_card]

/-- Selecting trivial torsion embeds paired class/lattice coordinates in class/unit coordinates. -/
private def dualClassLogToClassUnit (p : heckeDualClassIdeals 𝔪 hb0 × L) :
    heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ :=
  (p.1, (numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (1, p.2))

private theorem dualClassLogToClassUnit_injective :
    Function.Injective (dualClassLogToClassUnit 𝔪 hb0) := by
  intro p q h
  have hp : p.1 = q.1 :=
    congrArg (fun z : heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ => z.1) h
  have hu := congrArg (fun z : heckeDualClassIdeals 𝔪 hb0 × (𝓞 K)ˣ => z.2) h
  have hl : p.2 = q.2 := congrArg (fun z : Units.torsion K × L => z.2)
    ((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm.injective hu)
  exact Prod.ext hp hl

/-- The full paired class/logarithm series converges absolutely at every positive theta parameter. -/
theorem summable_norm_heckeDualClassLogKernels (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (x : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : heckeDualClassIdeals 𝔪 hb0 × L =>
      ‖heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (p.2 : logSpace K))) t
        (heckeDualClassFrequency 𝔪 hb0 p.1 : K)‖) := by
  have hs := (summable_norm_heckeDualClassUnitKernels 𝔪 hb hb0 ψ
    (-numberFieldWeightedLogProfile x) ht).comp_injective
      (i := dualClassLogToClassUnit 𝔪 hb0) (dualClassLogToClassUnit_injective 𝔪 hb0)
  simpa only [Function.comp_def, dualClassLogToClassUnit,
    heckeDualThetaKernel_torsionLogLattice 𝔪 hb hb0 ψ hψ] using hs

/-- Dual theta minus its zero mode is exactly the torsion-weighted paired periodization. -/
theorem heckeDualIdealTheta_sub_constant_eq_classLogSum (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (x : logSpace K) {t : ℝ} (ht : 0 < t) :
    heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t - heckeDualThetaConstant 𝔪 ψ =
      (Units.torsionOrder K : ℂ) * ∑' p : heckeDualClassIdeals 𝔪 hb0 × L,
        heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (p.2 : logSpace K))) t
          (heckeDualClassFrequency 𝔪 hb0 p.1 : K) := by
  rw [heckeDualIdealTheta_sub_constant_eq_classUnitSum 𝔪 hb hb0 ψ _ ht]
  simp_rw [tsum_heckeDualClassUnitOrbit_eq_logPeriodization 𝔪 hb hb0 ψ hψ _ x ht]
  rw [tsum_mul_left,
    (summable_norm_heckeDualClassLogKernels 𝔪 hb hb0 ψ hψ x ht).of_norm.tsum_prod]

/-- A single summable majorant controls every dual class/lattice translate on the unit domain. -/
theorem exists_heckeDualClassLog_unitDomain_majorant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {t : ℝ} (ht : 0 < t) :
    ∃ u : heckeDualClassIdeals 𝔪 hb0 × L → ℝ, Summable u ∧
      ∀ p : heckeDualClassIdeals 𝔪 hb0 × L, ∀ x ∈ D,
        ‖heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (p.2 : logSpace K))) t
          (heckeDualClassFrequency 𝔪 hb0 p.1 : K)‖ ≤ u p := by
  obtain ⟨M, _, hM⟩ := exists_bound_numberFieldWeightedLogProfile_unitDomain (K := K)
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeDualThetaKernel_majorant 𝔪 hb hb0 ψ ht M
  let f := (heckeDualClassUnitFrequency 𝔪 hb0) ∘ (dualClassLogToClassUnit 𝔪 hb0)
  have hf : Function.Injective f := (heckeDualClassUnitFrequency_injective 𝔪 hb0).comp
    (dualClassLogToClassUnit_injective 𝔪 hb0)
  refine ⟨fun p => u (f p), hu.comp_injective (i := f) hf, ?_⟩
  rintro ⟨I, l⟩ x hx
  have h := hbound (-numberFieldWeightedLogProfile x)
    (fun v => (neg_le_abs _).trans (hM x hx v)) t le_rfl (f (I, l))
  change ‖heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
    ((((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (1, l) : 𝓞 K) : K) *
      (heckeDualClassFrequency 𝔪 hb0 I : K))‖ ≤ _ at h
  simpa only [heckeDualThetaKernel_torsionLogLattice 𝔪 hb hb0 ψ hψ] using h

/-- Actual dual kernels are continuous in the negative coordinates used by the dual average. -/
theorem continuous_heckeDualThetaKernel_negativeLogCoordinates (ψ : HeckeCharacter 𝔪)
    (t : ℝ) (a : K) :
    Continuous (fun x : logSpace K =>
      heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t a) := by
  have hm : Continuous (fun x : logSpace K => (-numberFieldWeightedLogProfile x, t)) :=
    continuous_numberFieldWeightedLogProfile.neg.prodMk continuous_const
  have hc : Continuous (fun x : logSpace K =>
      heckeParityKernel 𝔪 ψ (-numberFieldWeightedLogProfile x) t a) :=
    (continuous_heckeParityKernel_parameters 𝔪 ψ a).comp
      (f := fun x : logSpace K => (-numberFieldWeightedLogProfile x, t)) hm
  change Continuous (fun x : logSpace K => finiteHeckeFourierCoefficient 𝔪 hb ψ a *
    heckeParityKernel 𝔪 ψ (-numberFieldWeightedLogProfile x) t a)
  exact (continuous_const : Continuous (fun _ : logSpace K =>
    finiteHeckeFourierCoefficient 𝔪 hb ψ a)).mul hc

/-- Absolute unfolding gives integrable dual class kernels and a summable family of their masses. -/
theorem heckeDualClassKernels_unfold_absolutely (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {t : ℝ} (ht : 0 < t) :
    (∀ I : heckeDualClassIdeals 𝔪 hb0, Integrable (fun x : logSpace K =>
      heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
        (heckeDualClassFrequency 𝔪 hb0 I : K))) ∧
    Summable (fun I : heckeDualClassIdeals 𝔪 hb0 => ∫ x : logSpace K,
      ‖heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
        (heckeDualClassFrequency 𝔪 hb0 I : K)‖) ∧
    (∫ x in D, ∑' p : heckeDualClassIdeals 𝔪 hb0 × L,
      heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile (x + (p.2 : logSpace K))) t
        (heckeDualClassFrequency 𝔪 hb0 p.1 : K)) =
      ∑' I : heckeDualClassIdeals 𝔪 hb0, ∫ x : logSpace K,
        heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
          (heckeDualClassFrequency 𝔪 hb0 I : K) := by
  letI := fractionalInverseClassIntegralIdeals_countable (heckeDualIdealUnit 𝔪 hb0)
  obtain ⟨u, hu, hbound⟩ := exists_heckeDualClassLog_unitDomain_majorant 𝔪 hb hb0 ψ hψ ht
  exact numberFieldUnitDomain_unfold_family _
    (fun I => continuous_heckeDualThetaKernel_negativeLogCoordinates 𝔪 hb ψ t
      (heckeDualClassFrequency 𝔪 hb0 I : K)) hu hbound

/-- The actual dual unit average unfolds into whole-log class integrals, with its zero mode removed. -/
theorem heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals_negative (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {t : ℝ} (ht : 0 < t) :
    heckeUnitAveragedDualTheta 𝔪 hb ψ t - (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ =
      (Units.torsionOrder K : ℂ) * ∑' I : heckeDualClassIdeals 𝔪 hb0, ∫ x : logSpace K,
        heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
          (heckeDualClassFrequency 𝔪 hb0 I : K) := by
  have havg : heckeUnitAveragedDualTheta 𝔪 hb ψ t -
      (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ =
      ∫ x in D, heckeDualIdealTheta 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t -
        heckeDualThetaConstant 𝔪 ψ := by
    rw [integral_sub (integrableOn_heckeDualTheta_unitDomain 𝔪 hb hb0 ψ ht)
      (integrableOn_const measure_numberFieldUnitLogDomain_lt_top.ne), setIntegral_const,
      volume_numberFieldUnitLogDomain_eq_regulator, Complex.real_smul]
    rfl
  rw [havg]
  simp_rw [heckeDualIdealTheta_sub_constant_eq_classLogSum 𝔪 hb hb0 ψ hψ _ ht]
  rw [integral_const_mul, (heckeDualClassKernels_unfold_absolutely 𝔪 hb hb0 ψ hψ ht).2.2]

/-- Haar negation converts the actual dual average to the positive-profile class Mellin kernels. -/
theorem heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {t : ℝ} (ht : 0 < t) :
    heckeUnitAveragedDualTheta 𝔪 hb ψ t - (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ =
      (Units.torsionOrder K : ℂ) * ∑' I : heckeDualClassIdeals 𝔪 hb0, ∫ x : logSpace K,
        heckeDualThetaKernel 𝔪 hb ψ (numberFieldWeightedLogProfile x) t
          (heckeDualClassFrequency 𝔪 hb0 I : K) := by
  rw [heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals_negative 𝔪 hb hb0 ψ hψ ht]
  simp only [heckeDualThetaKernel, integral_const_mul,
    integral_heckeParityKernel_negativeLogProfile]

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualIdealTheta_sub_constant_eq_classLogSum
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualClassKernels_unfold_absolutely
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals
