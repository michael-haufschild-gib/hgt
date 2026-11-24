import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.PrecisionFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.Prescribed.FiniteHeightAtoms

/-! # Countably many exceptional first-return tolerances before the disorder draw -/

open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits.Prescribed
open AccuracyScales.MaximumIntervals PrescribedTimes ShortWindows PrecisionReturns
noncomputable section

private def windowHeights (k s n : ℕ) (ω : PathPauliDisorder) : Set ℝ :=
  let H := chainGenerator ω k
  orbitCircuitDistance H s '' {t ∈ Icc (-(n:ℝ)) (n:ℝ) |
    HasProjectiveCircuitApproximation (k+3) 0 (fineBudget k) (unitaryEvolution H.val t)}

private theorem numbered_distance (k s : ℕ) (ω : PathPauliDisorder) (t : ℝ) :
    pathGateDistance (k+1) s (prefixPoint k ω) t = orbitCircuitDistance (chainGenerator ω k) s t := by
  unfold pathGateDistance orbitCircuitDistance chainGenerator
  rw [show numberedGenerator (k+1) (prefixPoint k ω)=pathHamiltonian (pathPauliDisorderShell ω (k+1))
    from numberedGenerator_shell _]

private theorem measurable_height (k s n : ℕ) (e : ℝ) :
    MeasurableSet {ω | e ∈ windowHeights k s n ω} := by
  let X := PrefixIndex (k+1) → ℝ
  let I := Icc (-(n:ℝ)) (n:ℝ)
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let d (j : ℕ) (p : X × I) := pathGateDistance (k+1) j p.1 p.2.val
  have hc (j : ℕ) : Continuous (d j) := (continuous_distance (k+1) j).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  let F := {p : X × I | d (fineBudget k) p ≤ 0 ∧ d s p=e}
  have hF : IsClosed F := (isClosed_le (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)
  have heq : {ω | e ∈ windowHeights k s n ω} = prefixPoint k ⁻¹' (Prod.fst '' F) := by
    ext ω
    constructor
    · rintro ⟨t,⟨ht,hfit⟩,he⟩
      refine ⟨(prefixPoint k ω,⟨t,ht⟩),⟨?_,?_⟩,rfl⟩
      · exact (numbered_distance k _ ω t).le.trans ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit)
      · exact (numbered_distance k _ ω t).trans he
    · rintro ⟨⟨p,t⟩,⟨hd,he⟩,hp⟩
      change p=prefixPoint k ω at hp
      subst p
      refine ⟨t.val,⟨t.property,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr ?_⟩,?_⟩
      · exact (numbered_distance k _ ω t.val).symm.le.trans hd
      · exact (numbered_distance k _ ω t.val).symm.trans he
  rw [heq]
  exact ((isClosedMap_fst_of_compactSpace _ hF).measurableSet).preimage
    (gaussian_pauli_prefix_coordinates_law (k+1)).measurable

/-- A deterministic countable set contains every coarse tolerance that
can coincide, with positive probability, with the error at an exact
short-circuit date on any prefix of the frozen chain. -/
theorem countable_prescribed_contact_values :
    ∃ E : Set ℝ, E.Countable ∧ ∀ e ∉ E, ∀ᵐ ω ∂pathPauliDisorderLaw, e ∉ contactValues ω := by
  let μ := pathPauliDisorderLaw
  let A (k s n : ℕ) := {e : ℝ | 0 < μ.real {ω | e ∈ windowHeights k s n ω}}
  have hA (k s n : ℕ) : (A k s n).Countable := by
    apply countable_height_atoms μ _ (measurable_height k s n)
    filter_upwards [gaussian_finite_exact_circuit_dates] with ω hω
    have hsize : 16*fineBudget k < 2^(k+3)-1 := by
      have hh := Nat.div_mul_le_self (2^(k+3)-2) 16
      have hp : 2 ≤ 2^(k+3) := (show 2^1 ≤ 2^(k+3) from Nat.pow_le_pow_right (by decide) (by omega))
      dsimp only [fineBudget]; omega
    exact (hω k (fineBudget k) hsize (-(n:ℝ)) (n:ℝ)).image _
  refine ⟨⋃ (k : ℕ) (s : ℕ) (n : ℕ), A k s n,
    countable_iUnion fun k => countable_iUnion fun s => countable_iUnion fun n => hA k s n,?_⟩
  intro e he
  have hmiss (k s n : ℕ) : ∀ᵐ ω ∂μ, e ∉ windowHeights k s n ω := by
    apply measure_eq_zero_iff_ae_notMem.mp
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    apply le_antisymm _ measureReal_nonneg
    exact le_of_not_gt (fun hp => he (mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨n,hp⟩⟩⟩))
  filter_upwards [ae_all_iff.mpr fun k => ae_all_iff.mpr fun s => ae_all_iff.mpr fun n => hmiss k s n]
    with ω hw
  intro eh
  obtain ⟨k,hk⟩ := mem_iUnion.mp eh
  obtain ⟨s,hs⟩ := mem_iUnion.mp hk
  obtain ⟨n,hn⟩ := mem_iUnion.mp hs
  exact hw k s n hn

/-- At each coarse tolerance outside one deterministic countable set,
almost every draw has a fine-error exponential floor at all genuine
first visits, including from origins depending on that draw. -/
theorem prescribed_first_visit_precisions :
    ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e ∉ E → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ (k s : ℕ) (a : ℝ), let H := chainGenerator ω k
      e < orbitCircuitDistance H s a → let v := firstVisit H a s e
        ∃ δ > (0:ℝ), δ < orbitCircuitDistance H (fineBudget k) v := by
  obtain ⟨E,hE,h⟩ := countable_prescribed_contact_values
  refine ⟨E,hE,?_⟩
  intro e he hr
  filter_upwards [h e hr,gaussian_coarse_contact_precision] with ω hω hcoarse
  intro k s a H hout v
  obtain ⟨δ,hδ,hd⟩ := hcoarse.2 e hω k s v v
  refine ⟨δ,hδ,hd v ⟨le_rfl,le_rfl⟩ ?_⟩
  rw [firstVisit_distance H a s he hout,sub_self,abs_zero]
  exact hδ.le

#print axioms prescribed_first_visit_precisions
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits.Prescribed
