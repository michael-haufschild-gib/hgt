import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatPeriodization
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Closedness of the finite-stage rational S-unit orbit

For a finite set `S` of rational finite places, this file proves that the
diagonal image of the rational `S`-units is a discrete, hence closed, subgroup
of the finite-stage idele group.  This is the separation input needed to treat
the Connes--Marcolli semilocal class space as a Hausdorff quotient and to make
its compact module-one fundamental domain explicit.

The proof uses the genuine adelic topology.  Simultaneous integrality of a
rational `S`-unit and its inverse at the selected places, together with its
unit norm at every omitted place, makes both rational numbers integral.  The
positive real coordinate then excludes `-1`.
-/

open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- Open identity neighborhood imposing positivity at infinity and
integrality of every selected local unit and its inverse. -/
def fieldOneFiniteStageIntegralUnitNeighborhood
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set (FieldOneFiniteStageIdele S) :=
  {u | 0 < (u.1 : ℝ) ∧ ∀ v : ↥S,
    (u.2 v : v.1.adicCompletion ℚ) ∈ v.1.adicCompletionIntegers ℚ ∧
      ((u.2 v)⁻¹ : (v.1.adicCompletion ℚ)ˣ).1 ∈
        v.1.adicCompletionIntegers ℚ}

theorem fieldOneFiniteStageIntegralUnitNeighborhood_isOpen
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpen (fieldOneFiniteStageIntegralUnitNeighborhood S) := by
  rw [show fieldOneFiniteStageIntegralUnitNeighborhood S =
      {u : FieldOneFiniteStageIdele S | 0 < (u.1 : ℝ)} ∩
        ⋂ v : ↥S,
          ({u : FieldOneFiniteStageIdele S |
              (u.2 v : v.1.adicCompletion ℚ) ∈
                v.1.adicCompletionIntegers ℚ} ∩
            {u : FieldOneFiniteStageIdele S |
              ((u.2 v)⁻¹ : (v.1.adicCompletion ℚ)ˣ).1 ∈
                v.1.adicCompletionIntegers ℚ}) by
    ext u
    simp [fieldOneFiniteStageIntegralUnitNeighborhood]]
  apply IsOpen.inter
  · exact isOpen_Ioi.preimage
      (Units.continuous_val.comp continuous_fst)
  · apply isOpen_iInter_of_finite
    intro v
    apply IsOpen.inter
    · exact (Valued.isOpen_valuationSubring (v.1.adicCompletion ℚ)).preimage
        (Units.continuous_val.comp ((continuous_apply v).comp continuous_snd))
    · exact (Valued.isOpen_valuationSubring (v.1.adicCompletion ℚ)).preimage
        (Units.continuous_val.comp
          (continuous_inv.comp ((continuous_apply v).comp continuous_snd)))

/-- A rational `S`-unit whose diagonal idele lies in the integral-unit
neighborhood is the identity. -/
theorem fieldOneSUnit_eq_one_of_diagonal_mem_integralUnitNeighborhood
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    (hq : fieldOneFiniteStageDiagonalUnit S q.1 ∈
      fieldOneFiniteStageIntegralUnitNeighborhood S) : q = 1 := by
  have hqpos : (0 : ℝ) < (((q.1 : ℚˣ) : ℚ) : ℝ) := hq.1
  have hqIntegral : (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range := by
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
    intro v
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (v := v) (q.1 : ℚ)]
    rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hv : v ∈ S
    · exact (hq.2 ⟨v, hv⟩).1
    · have hn := fieldOneSUnit_localNorm_one_of_not_mem S q hv
      exact Valued.toNormedField.norm_le_one_iff.mp hn.le
  have hqInvIntegral : ((q⁻¹).1 : ℚ) ∈ (algebraMap ℤ ℚ).range := by
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
    intro v
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      (v := v) ((q⁻¹).1 : ℚ)]
    rw [← HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hv : v ∈ S
    · have hvInv := (hq.2 ⟨v, hv⟩).2
      change algebraMap ℚ (v.adicCompletion ℚ) ((q⁻¹).1 : ℚ) ∈
        v.adicCompletionIntegers ℚ
      simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀]
      simpa [fieldOneFiniteStageDiagonalUnit,
        fieldOneRationalFiniteStageUnit,
        fieldOneRationalLocalUnit] using hvInv
    · have hn := fieldOneSUnit_localNorm_one_of_not_mem S q⁻¹ hv
      exact Valued.toNormedField.norm_le_one_iff.mp hn.le
  rcases hqIntegral with ⟨n, hn⟩
  rcases hqInvIntegral with ⟨m, hm⟩
  change (n : ℚ) = (q.1 : ℚ) at hn
  change (m : ℚ) = ((q⁻¹).1 : ℚ) at hm
  have hnmQ : (n : ℚ) * (m : ℚ) = 1 := by
    rw [hn, hm]
    simp
  have hnm : n * m = 1 := by
    exact_mod_cast hnmQ
  have hnUnit : IsUnit n := by
    apply isUnit_iff_dvd_one.2
    exact ⟨m, hnm.symm⟩
  rcases Int.isUnit_iff.mp hnUnit with hnOne | hnNeg
  · apply Subtype.ext
    apply Units.ext
    rw [← hn]
    simpa using congrArg (fun z : ℤ => (z : ℚ)) hnOne
  · exfalso
    have hqneg : (((q.1 : ℚˣ) : ℚ) : ℝ) = -1 := by
      rw [← hn]
      have hcast := congrArg (fun z : ℤ => ((z : ℚ) : ℝ)) hnNeg
      simpa using hcast
    linarith

/-- The diagonal rational `S`-unit image carries the discrete topology induced
from the finite-stage idele group. -/
noncomputable instance fieldOneFiniteStageSUnitImageDiscreteTopology
    (S : Finset (HeightOneSpectrum ℤ)) :
    DiscreteTopology (fieldOneFiniteStageSUnitImage S) := by
  rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff]
  refine ⟨fieldOneFiniteStageIntegralUnitNeighborhood S,
    fieldOneFiniteStageIntegralUnitNeighborhood_isOpen S, ?_⟩
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.2
    apply Subtype.ext
    change z.1 = 1
    have hzmem := z.property
    change z.1 ∈ Subgroup.map
      (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at hzmem
    rw [Subgroup.mem_map] at hzmem
    rcases hzmem with ⟨q, hqS, hqz⟩
    let qS : fieldOneSUnitSubgroup S := ⟨q, hqS⟩
    have hqOne : qS = 1 := by
      apply fieldOneSUnit_eq_one_of_diagonal_mem_integralUnitNeighborhood S qS
      rw [hqz]
      exact hz
    rw [← hqz]
    change fieldOneFiniteStageDiagonalUnit S qS.1 = 1
    rw [hqOne]
    exact map_one (fieldOneFiniteStageDiagonalUnit S)
  · intro hz
    have hzOne : z = 1 := Set.mem_singleton_iff.1 hz
    subst z
    change (1 : FieldOneFiniteStageIdele S) ∈
      fieldOneFiniteStageIntegralUnitNeighborhood S
    simp [fieldOneFiniteStageIntegralUnitNeighborhood]

/-- The diagonal rational `S`-unit image is closed in the finite-stage idele
group. -/
theorem fieldOneFiniteStageSUnitImage_isClosed
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsClosed (fieldOneFiniteStageSUnitImage S :
      Set (FieldOneFiniteStageIdele S)) := by
  exact Subgroup.isClosed_of_discrete

end

end GaloisForLFunctions.RHTower
