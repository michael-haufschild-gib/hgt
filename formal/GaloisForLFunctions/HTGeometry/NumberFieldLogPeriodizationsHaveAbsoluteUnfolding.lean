import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogFundamentalDomain
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute unfolding of families over the unit-log lattice

A summable bound on paired family/lattice indices controls every translate
on the actual unit fundamental domain. Nonnegative tile unfolding proves
whole-space integrability and summability of absolute masses. Complex
unfolding then identifies the integrated periodization with the sum of
whole-space integrals.
-/

noncomputable section
open NumberField NumberField.Units.dirichletUnitTheorem MeasureTheory Set
open scoped Classical ENNReal
namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] [NumberField K]
local notation "D" => numberFieldUnitLogDomain K
local notation "L" => Units.unitLattice K

local instance : Countable L :=
  Countable.of_equiv (Fin (Units.rank K) → ℤ) (Units.basisUnitLattice K).equivFun.symm.toEquiv

local instance : VAddInvariantMeasure L (logSpace K) volume where
  measure_preimage_vadd l _ hs :=
    VAddInvariantMeasure.measure_preimage_vadd (μ := (volume : Measure (logSpace K)))
      (l : logSpace K) hs

/-- A joint class/lattice majorant proves absolute whole-space unfolding for the entire family. -/
theorem numberFieldUnitDomain_unfold_family {ι : Type*} [Countable ι]
    (F : ι → logSpace K → ℂ) (hF : ∀ i, Continuous (F i))
    {u : ι × L → ℝ} (hu : Summable u)
    (hbound : ∀ p : ι × L, ∀ x ∈ D, ‖F p.1 (x + (p.2 : logSpace K))‖ ≤ u p) :
    (∀ i, Integrable (F i)) ∧ Summable (fun i => ∫ x : logSpace K, ‖F i x‖) ∧
      (∫ x in D, ∑' p : ι × L, F p.1 (x + (p.2 : logSpace K))) =
        ∑' i, ∫ x : logSpace K, F i x := by
  let G : ι × L → logSpace K → ℂ := fun p x => F p.1 (x + (p.2 : logSpace K))
  have hGi (p : ι × L) : IntegrableOn (G p) D :=
    (((hF p.1).comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_closure_numberFieldUnitLogDomain (K := K))).mono_set subset_closure
  have hs : Summable (fun p : ι × L => ∫ x in D, ‖G p x‖) := by
    apply (hu.abs.mul_right (volume.real D)).of_norm_bounded
    intro p
    apply norm_setIntegral_le_of_norm_le_const measure_numberFieldUnitLogDomain_lt_top
    intro x hx
    simpa only [norm_norm] using (hbound p x hx).trans (le_abs_self (u p))
  have hrows := (summable_prod_of_nonneg
    (fun p : ι × L => integral_nonneg (fun x => norm_nonneg (G p x)))).mp hs
  have htrans (l : L) (x : logSpace K) : l +ᵥ x = x + (l : logSpace K) := by
    change (l : logSpace K) + x = x + (l : logSpace K)
    exact add_comm _ _
  have hwhole (i : ι) : Integrable (F i) := by
    refine ⟨(hF i).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral,
      (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).lintegral_eq_tsum'']
    simp_rw [htrans]
    change (∑' l : L, ∫⁻ x in D, ‖G (i, l) x‖ₑ) < ⊤
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hGi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun l : L => integral_nonneg (fun x => norm_nonneg (G (i, l) x))) (hrows.1 i)]
    exact ENNReal.ofReal_lt_top
  have hnorm (i : ι) : (∫ x : logSpace K, ‖F i x‖) =
      ∑' l : L, ∫ x in D, ‖G (i, l) x‖ := by
    have h := (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).integral_eq_tsum''
      (fun x => ‖F i x‖) (hwhole i).norm
    simpa only [htrans, G] using h
  refine ⟨hwhole, ?_, ?_⟩
  · simpa only [hnorm] using hrows.2
  · have hsi : Summable (fun p : ι × L => ∫ x in D, G p x) :=
      hs.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
    change (∫ x in D, ∑' p : ι × L, G p x) = _
    rw [← integral_tsum_of_summable_integral_norm hGi hs, hsi.tsum_prod]
    apply tsum_congr
    intro i
    have h := (isAddFundamentalDomain_numberFieldUnitLogDomain (K := K)).integral_eq_tsum''
      (F i) (hwhole i)
    simpa only [htrans, G] using h.symm

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.numberFieldUnitDomain_unfold_family
