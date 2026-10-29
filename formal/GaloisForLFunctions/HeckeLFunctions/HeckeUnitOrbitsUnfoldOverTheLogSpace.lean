import GaloisForLFunctions.HeckeLFunctions.HeckeThetaUnitOrbitsAreLogPeriodizations
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute unfolding of Hecke unit orbits

The summable ideal Gaussian majorant controls every logarithmic lattice translate
uniformly on the actual unit domain. Nonnegative unfolding first proves integrability
over the whole logarithmic space. Complex unfolding then identifies each unit-orbit
average, and the full averaged theta series, with torsion-weighted class integrals.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory Set
open scoped Classical nonZeroDivisors ENNReal
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K]
local notation "D" => numberFieldUnitLogDomain K
local notation "L" => Units.unitLattice K

local instance : Countable L :=
  Countable.of_equiv (Fin (Units.rank K) → ℤ) (Units.basisUnitLattice K).equivFun.symm.toEquiv

local instance : VAddInvariantMeasure L (logSpace K) volume where
  measure_preimage_vadd l _ hs :=
    VAddInvariantMeasure.measure_preimage_vadd (μ := (volume : Measure (logSpace K)))
      (l : logSpace K) hs

/-- A summable uniform bound controls the sum of integral norms on the finite unit domain. -/
private theorem unitDomain_summable_integral_norm {ι : Type*}
    {F : ι → logSpace K → ℂ} (hF : ∀ i, Continuous (F i))
    {u : ι → ℝ} (hu : Summable u) (hbound : ∀ i, ∀ x ∈ D, ‖F i x‖ ≤ u i) :
    (∀ i, IntegrableOn (F i) D) ∧ Summable (fun i => ∫ x in D, ‖F i x‖) := by
  refine ⟨fun i => ((hF i).continuousOn.integrableOn_compact
    (isCompact_closure_numberFieldUnitLogDomain (K := K))).mono_set subset_closure, ?_⟩
  apply (hu.abs.mul_right (volume.real D)).of_norm_bounded
  intro i
  apply norm_setIntegral_le_of_norm_le_const measure_numberFieldUnitLogDomain_lt_top
  intro x hx
  simpa only [norm_norm] using (hbound i x hx).trans (le_abs_self (u i))

/-- A summable bound on one unit domain proves whole-space integrability before complex unfolding. -/
private theorem unitDomain_unfolding_of_summable_majorant
    {f : logSpace K → ℂ} (hf : Continuous f) {u : L → ℝ} (hu : Summable u)
    (hbound : ∀ l : L, ∀ x ∈ D, ‖f (x - (l : logSpace K))‖ ≤ u l) :
    Integrable f ∧ (∫ x in D, ∑' l : L, f (x - (l : logSpace K))) = ∫ x, f x := by
  have hc (l : L) : Continuous (fun x : logSpace K => f (x - (l : logSpace K))) :=
    hf.comp (continuous_id.sub continuous_const)
  obtain ⟨hfi, hs⟩ := unitDomain_summable_integral_norm
    (F := fun l : L => fun x : logSpace K => f (x - (l : logSpace K))) hc hu hbound
  have htrans (l : L) (x : logSpace K) : (-l) +ᵥ x = x - (l : logSpace K) := by
    change -(l : logSpace K) + x = x - (l : logSpace K)
    abel
  have hwhole : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral,
      (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).lintegral_eq_tsum']
    simp_rw [htrans, ← ofReal_integral_norm_eq_lintegral_enorm (hfi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun l : L => integral_nonneg (fun _ => norm_nonneg _)) hs]
    exact ENNReal.ofReal_lt_top
  refine ⟨hwhole, ?_⟩
  have he := (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).integral_eq_tsum' f hwhole
  simp_rw [htrans] at he
  exact (integral_tsum_of_summable_integral_norm hfi hs).symm.trans he.symm

variable (𝔪 : Modulus K)

/-- Each actual Hecke kernel is continuous in weighted logarithmic coordinates. -/
theorem continuous_heckeThetaKernel_logCoordinates (ψ : HeckeCharacter 𝔪)
    (t : ℝ) (a : 𝓞 K) :
    Continuous (fun x : logSpace K =>
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a) := by
  have hm : Continuous (fun x : logSpace K => (numberFieldWeightedLogProfile x, t)) :=
    continuous_numberFieldWeightedLogProfile.prodMk continuous_const
  have hc := (continuous_heckeThetaKernel_parameters 𝔪 ψ a).comp
    (f := fun x : logSpace K => (numberFieldWeightedLogProfile x, t)) hm
  simpa only [Function.comp_def] using hc

/-- The actual ideal Gaussian majorant bounds all lattice translates uniformly on the unit domain. -/
theorem exists_heckeThetaLogPeriodization_unitDomain_majorant (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) {t : ℝ} (ht : 0 < t) :
    ∃ u : L → ℝ, Summable u ∧ ∀ l : L, ∀ x ∈ D,
      ‖heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (l : logSpace K))) t a.1‖ ≤
        u l := by
  obtain ⟨M, _, hM⟩ := exists_bound_numberFieldWeightedLogProfile_unitDomain (K := K)
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeThetaKernel_majorant 𝔪 ψ b ht M
  let g : L → (𝓞 K)ˣ :=
    fun l => (numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (1, l)
  have hg : Function.Injective g := by
    intro l m h
    exact congrArg Prod.snd ((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm.injective h)
  refine ⟨fun l => u (unitOrbitInIdeal a (g l)),
    hu.comp_injective (i := fun l => unitOrbitInIdeal a (g l))
      ((unitOrbitInIdeal_injective a).comp hg), ?_⟩
  intro l x hx
  have h := hbound (numberFieldWeightedLogProfile x)
    (fun v => (le_abs_self _).trans (hM x hx v)) t le_rfl (unitOrbitInIdeal a (g l))
  simpa only [unitOrbitInIdeal, g, heckeThetaKernel_torsionLogLattice] using h

/-- A nonzero ideal element's actual Hecke kernel is integrable over the whole logarithmic space. -/
theorem integrable_heckeThetaKernel_logCoordinates (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : logSpace K =>
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a.1) := by
  obtain ⟨u, hu, hb⟩ := exists_heckeThetaLogPeriodization_unitDomain_majorant 𝔪 ψ a ht
  exact (unitDomain_unfolding_of_summable_majorant
    (continuous_heckeThetaKernel_logCoordinates 𝔪 ψ t a.1) hu hb).1

/-- Absolute integrability justifies unfolding the actual lattice periodization. -/
theorem integral_heckeThetaLogPeriodization_unitDomain (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) {t : ℝ} (ht : 0 < t) :
    (∫ x in D, ∑' l : L,
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (l : logSpace K))) t a.1) =
      ∫ x : logSpace K, heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a.1 := by
  obtain ⟨u, hu, hb⟩ := exists_heckeThetaLogPeriodization_unitDomain_majorant 𝔪 ψ a ht
  exact (unitDomain_unfolding_of_summable_majorant
    (continuous_heckeThetaKernel_logCoordinates 𝔪 ψ t a.1) hu hb).2

/-- Averaging an actual unit orbit unfolds to the whole logarithmic space with exact torsion factor. -/
theorem integral_heckeThetaUnitOrbit_unitDomain (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (a : nonzeroIdealElements b) {t : ℝ} (ht : 0 < t) :
    (∫ x in D, ∑' u : (𝓞 K)ˣ,
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t ((u : 𝓞 K) * a.1)) =
      (Units.torsionOrder K : ℂ) *
        ∫ x : logSpace K, heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a.1 := by
  simp_rw [tsum_heckeThetaUnitOrbit_eq_logPeriodization 𝔪 ψ a _ ht]
  rw [integral_const_mul, integral_heckeThetaLogPeriodization_unitDomain 𝔪 ψ a ht]

/-- Select one actual unit for each lattice point while retaining the ideal class coordinate. -/
private def classLogToClassUnit (b : (Ideal (𝓞 K))⁰)
    (p : inverseClassIntegralIdeals b × L) : inverseClassIntegralIdeals b × (𝓞 K)ˣ :=
  (p.1, (numberFieldUnitsEquivTorsionLogLattice (K := K)).symm (1, p.2))

private theorem classLogToClassUnit_injective (b : (Ideal (𝓞 K))⁰) :
    Function.Injective (classLogToClassUnit b) := by
  intro p q h
  have hp : p.1 = q.1 :=
    congrArg (fun z : inverseClassIntegralIdeals b × (𝓞 K)ˣ => z.1) h
  have hu := congrArg (fun z : inverseClassIntegralIdeals b × (𝓞 K)ˣ => z.2) h
  have hl : p.2 = q.2 := congrArg (fun z : Units.torsion K × L => z.2)
    ((numberFieldUnitsEquivTorsionLogLattice (K := K)).symm.injective hu)
  exact Prod.ext hp hl

/-- Class and logarithmic-lattice coordinates give an absolutely convergent double kernel series. -/
theorem summable_norm_heckeThetaClassLogKernels (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (x : logSpace K) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : inverseClassIntegralIdeals b × L =>
      ‖heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (p.2 : logSpace K)))
        t (inverseClassGenerator b p.1)‖) := by
  have hs := (summable_norm_heckeThetaClassUnitKernels 𝔪 ψ b
    (numberFieldWeightedLogProfile x) ht).comp_injective
      (i := classLogToClassUnit b) (classLogToClassUnit_injective b)
  simpa only [Function.comp_def, classLogToClassUnit,
    heckeThetaKernel_torsionLogLattice] using hs

/-- One summable ideal majorant bounds every class and lattice coordinate over the unit domain. -/
theorem exists_heckeThetaClassLog_unitDomain_majorant (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {t : ℝ} (ht : 0 < t) :
    ∃ u : inverseClassIntegralIdeals b × L → ℝ, Summable u ∧
      ∀ p : inverseClassIntegralIdeals b × L, ∀ x ∈ D,
        ‖heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (p.2 : logSpace K)))
          t (inverseClassGenerator b p.1)‖ ≤ u p := by
  obtain ⟨M, _, hM⟩ := exists_bound_numberFieldWeightedLogProfile_unitDomain (K := K)
  obtain ⟨u, hu, hbound⟩ := exists_uniform_heckeThetaKernel_majorant
    𝔪 ψ (b : Ideal (𝓞 K)) ht M
  let e := nonzeroIdealElementsEquivClassUnits b
  let f : inverseClassIntegralIdeals b × L → (b : Ideal (𝓞 K)) :=
    fun p => ⟨(e.symm (classLogToClassUnit b p)).1,
      (e.symm (classLogToClassUnit b p)).2.1⟩
  have hf : Function.Injective f := by
    intro p q h
    apply classLogToClassUnit_injective b
    apply e.symm.injective
    exact Subtype.ext (congrArg (fun a : (b : Ideal (𝓞 K)) => (a : 𝓞 K)) h)
  refine ⟨fun p => u (f p), hu.comp_injective (i := f) hf, ?_⟩
  rintro ⟨I, l⟩ x hx
  have h := hbound (numberFieldWeightedLogProfile x)
    (fun v => (le_abs_self _).trans (hM x hx v)) t le_rfl (f (I, l))
  simpa only [f, e, classLogToClassUnit,
    nonzeroIdealElementsEquivClassUnits_symm_apply,
    heckeThetaKernel_torsionLogLattice] using h

/-- The chosen nonzero generators embed the inverse ideal class in a countable number field. -/
theorem inverseClassIntegralIdeals_countable (b : (Ideal (𝓞 K))⁰) :
    Countable (inverseClassIntegralIdeals b) := by
  letI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  letI : Countable (𝓞 K) := Subtype.countable
  let e := nonzeroIdealElementsEquivClassUnits b
  have hi : Function.Injective (fun I : inverseClassIntegralIdeals b => e.symm (I, 1)) := by
    intro I J h
    exact congrArg Prod.fst (e.symm.injective h)
  exact hi.countable

/-- The actual averaged theta, with its zero mode removed, unfolds into integrals indexed by ideals. -/
theorem heckeUnitAveragedTheta_sub_constant_eq_classIntegrals (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {t : ℝ} (ht : 0 < t) :
    heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) t -
        (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ =
      (Units.torsionOrder K : ℂ) * ∑' I : inverseClassIntegralIdeals b,
        ∫ x : logSpace K,
          heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t (inverseClassGenerator b I) := by
  letI := inverseClassIntegralIdeals_countable b
  let F : inverseClassIntegralIdeals b × L → logSpace K → ℂ := fun p x =>
    heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile (x - (p.2 : logSpace K)))
      t (inverseClassGenerator b p.1)
  have hF (p : inverseClassIntegralIdeals b × L) : Continuous (F p) := by
    have hm : Continuous (fun x : logSpace K => x - (p.2 : logSpace K)) :=
      continuous_id.sub continuous_const
    exact (continuous_heckeThetaKernel_logCoordinates 𝔪 ψ t (inverseClassGenerator b p.1)).comp hm
  obtain ⟨u, hu, hb⟩ := exists_heckeThetaClassLog_unitDomain_majorant 𝔪 ψ b ht
  obtain ⟨hfi, hs⟩ := unitDomain_summable_integral_norm (F := F) hF hu hb
  have hsi : Summable (fun p : inverseClassIntegralIdeals b × L => ∫ x in D, F p x) :=
    hs.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  have havg : heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) t -
      (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ =
      ∫ x in D, heckeIdealTheta 𝔪 ψ (b : Ideal (𝓞 K))
        (numberFieldWeightedLogProfile x) t - heckeThetaConstant 𝔪 ψ := by
    rw [integral_sub (integrableOn_heckeTheta_unitDomain 𝔪 ψ (b : Ideal (𝓞 K)) ht)
      (integrableOn_const measure_numberFieldUnitLogDomain_lt_top.ne), setIntegral_const,
      volume_numberFieldUnitLogDomain_eq_regulator, Complex.real_smul]
    rfl
  rw [havg]
  calc
    _ = ∫ x in D, (Units.torsionOrder K : ℂ) * ∑' p : inverseClassIntegralIdeals b × L, F p x := by
      apply setIntegral_congr_fun measurableSet_numberFieldUnitLogDomain
      intro x _
      change heckeIdealTheta 𝔪 ψ (b : Ideal (𝓞 K)) (numberFieldWeightedLogProfile x) t -
        heckeThetaConstant 𝔪 ψ = (Units.torsionOrder K : ℂ) *
          ∑' p : inverseClassIntegralIdeals b × L, F p x
      rw [heckeIdealTheta_sub_constant_eq_classLogPeriodizations 𝔪 ψ b x ht]
      congr 1
      exact (summable_norm_heckeThetaClassLogKernels 𝔪 ψ b x ht).of_norm.tsum_prod.symm
    _ = (Units.torsionOrder K : ℂ) * ∑' p : inverseClassIntegralIdeals b × L, ∫ x in D, F p x := by
      rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm hfi hs]
    _ = _ := by
      rw [hsi.tsum_prod]
      congr 1
      apply tsum_congr
      intro I
      let a : nonzeroIdealElements (b : Ideal (𝓞 K)) :=
        ⟨inverseClassGenerator b I, inverseClassGenerator_mem_ne_zero b I⟩
      have hi := integrable_heckeThetaKernel_logCoordinates 𝔪 ψ a ht
      have he := (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).integral_eq_tsum'
        (fun x : logSpace K => heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a.1) hi
      have htrans (l : L) (x : logSpace K) : (-l) +ᵥ x = x - (l : logSpace K) := by
        change -(l : logSpace K) + x = x - (l : logSpace K)
        abel
      simpa only [htrans, F, a] using he.symm

end GaloisForLFunctions.HeckeLFunctions
