import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.OnePrime
import GaloisForLFunctions.RHTower.RouteEProductTruncatedReservoirMass
import GaloisForLFunctions.HTGeometry.SortedSpectrumContinuity

/-! # Ordered occupation spectra and their injective prime enumerations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount

open Filter Topology Set MeasureTheory _root_.RHTower
open GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
local instance : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective

/-- Sorting a finite tuple is continuous, including where coordinates coincide. -/
theorem continuous_sort (k : ℕ) : Continuous (sortedTuple (D := k)) := by
  let C (σ : Equiv.Perm (Fin k)) := ⋂ ij : {ij : Fin k × Fin k // ij.1 ≤ ij.2},
    {v : Fin k → ℝ | v (σ ij.val.1) ≤ v (σ ij.val.2)}
  have hC (σ) : IsClosed (C σ) := isClosed_iInter fun ij =>
    isClosed_le (continuous_apply _) (continuous_apply _)
  have hm (σ) (v : Fin k → ℝ) : v ∈ C σ ↔ Monotone (v ∘ σ) := by
    constructor
    · intro hv i j hij
      exact mem_iInter.mp hv ⟨(i,j),hij⟩
    · intro hv
      exact mem_iInter.mpr fun ij => hv ij.property
  apply continuous_iff_isClosed.mpr
  intro s hs
  have he : sortedTuple ⁻¹' s = ⋃ σ : Equiv.Perm (Fin k), C σ ∩ (fun v : Fin k → ℝ => v ∘ σ) ⁻¹' s := by
    ext v
    constructor
    · intro hv
      exact mem_iUnion.mpr ⟨Tuple.sort v,(hm _ _).mpr (Tuple.monotone_sort v),hv⟩
    · intro hv
      obtain ⟨σ,hσ,hs'⟩ := mem_iUnion.mp hv
      have he : v ∘ σ = sortedTuple v := Tuple.comp_sort_eq_comp_iff_monotone.mpr ((hm _ _).mp hσ)
      change sortedTuple v ∈ s
      rw [← he]
      exact hs'
  rw [he]
  exact isClosed_iUnion_of_finite fun σ => (hC σ).inter
    (hs.preimage (continuous_pi fun i => continuous_apply (σ i)))

/-- List the actual occupied energies in nondecreasing order. -/
def spectrum {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) (R : BreadthSubset k ↥S) : Fin k → ℝ :=
  sortedTuple fun i => location h ((R.val.orderIsoOfFin R.property i).val).val

/-- Born mass on the exact count slice, before conditioning. -/
def slice (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) : FiniteMeasure (Fin k → ℝ) :=
  atomic (fun R : BreadthSubset k ↥S =>
    ⟨finiteSquarefreeBornWeight S s ((squarefreeOccupationEquiv S).symm R.val),(weight_pos _ _ _).le⟩) (spectrum h)

theorem slice_mass (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :
    ((slice S s h k).mass:ℝ) = atom S s k := by
  let W (T : Finset ↥S) := finiteSquarefreeBornWeight S s ((squarefreeOccupationEquiv S).symm T)
  rw [slice,atomic_mass,NNReal.coe_sum,atom]
  change (∑ R : BreadthSubset k ↥S,W R.val) = _
  rw [← (squarefreeOccupationEquiv S).symm.sum_comp (fun x =>
    if (squarefreeOccupationFinset x).card=k then finiteSquarefreeBornWeight S s x else 0)]
  have ho (T : Finset ↥S) : squarefreeOccupationFinset ((squarefreeOccupationEquiv S).symm T) = T :=
    (squarefreeOccupationEquiv S).apply_symm_apply T
  simp only [ho]
  change _ = ∑ T : Finset ↥S, if T.card=k then W T else 0
  rw [← Finset.sum_filter]
  simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := fun T : Finset ↥S => T.card=k) W)

/-- The Gibbs denominator disappears on multiplying a configuration weight by its partition. -/
theorem configuration_product (S : Finset Nat.Primes) (s : ℝ) (T : Finset ↥S) :
    finiteSquarefreePartition S s*finiteSquarefreeBornWeight S s ((squarefreeOccupationEquiv S).symm T) =
      ∏ p ∈ T, squarefreePrimeNome s p.val := by
  rw [finiteSquarefreeBornWeight_eq,show ∀ x : ℝ, finiteSquarefreePartition S s*(x/finiteSquarefreePartition S s)=x
    from fun x => by field_simp [(finiteSquarefreePartition_pos S s).ne']]
  rw [finiteSquarefreeHamiltonian_eq_sum_occupation,
    show squarefreeOccupationFinset ((squarefreeOccupationEquiv S).symm T) = T from
      (squarefreeOccupationEquiv S).apply_symm_apply T]
  simp only [squarefreePrimeNome_eq_exp,← Real.exp_sum,← Finset.mul_sum]

/-- Unnormalized expectation after discarding repeated prime labels from independent draws. -/
def distinctSum {ι : Type*} [Fintype ι] (q : ι → ℝ) (x : ι → ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :=
  ∑ y : Fin k → ι, if Function.Injective y then (∏ i, q (y i))*F (sortedTuple (x ∘ y)) else 0

private theorem embeddings {ι : Type*} [Fintype ι] (q : ι → ℝ) (x : ι → ℝ) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    distinctSum q x k F =
      ∑ e : Fin k ↪ ι, (∏ i, q (e i))*F (sortedTuple (x ∘ e)) := by
  classical
  let g (y : Fin k → ι) := (∏ i, q (y i))*F (sortedTuple (x ∘ y))
  change (∑ y, if Function.Injective y then g y else 0) = _
  rw [← Finset.sum_filter]
  have hs : (∑ y : {y : Fin k → ι // Function.Injective y}, g y.val) =
      ∑ y ∈ Finset.univ.filter Function.Injective,g y := by
    simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := Function.Injective) g)
  rw [← hs]
  exact Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin k) ι) _ _ (fun _ => rfl)

/-- Each physical configuration of count k appears exactly k! times among distinct ordered draws. -/
theorem distinct_born (S : Finset Nat.Primes) (a : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    distinctSum (fun p : ↥S => (odds a h p.val:ℝ)) (fun p => location h p.val) k F =
      (k.factorial:ℝ)*finiteSquarefreePartition S (1+a*h.val)*(∫ t,F t ∂(slice S (1+a*h.val) h k : Measure _)) := by
  let q (p : ↥S) : ℝ := odds a h p.val
  let x (p : ↥S) := location h p.val
  let E := embeddingRangePermEquiv k ↥S
  let G (e : Fin k ↪ ↥S) := (∏ i, q (e i))*F (sortedTuple (x ∘ e))
  have hz (R : BreadthSubset k ↥S) (π : Equiv.Perm (Fin k)) :
      G (E.symm (R,π)) = (∏ p ∈ R.val, q p)*F (spectrum h R) := by
    let v (i : Fin k) := x ((R.val.orderIsoOfFin R.property i).val)
    change (∏ i, q ((R.val.orderIsoOfFin R.property (π i)).val))*F (sortedTuple (v ∘ π)) = _
    rw [prod_embedding_eq_prod_range k ↥S q R π,
      show sortedTuple (v ∘ π) = sortedTuple v from Tuple.comp_perm_comp_sort_eq_comp_sort]
    rfl
  have hn : Fintype.card (Equiv.Perm (Fin k)) = k.factorial := by rw [Fintype.card_perm,Fintype.card_fin]
  rw [embeddings]
  change (∑ e, G e) = _
  rw [← E.symm.sum_comp G,Fintype.sum_prod_type]
  simp only [hz,Finset.sum_const,Finset.card_univ,hn,nsmul_eq_mul,← Finset.mul_sum]
  rw [slice,atomic_integral,mul_assoc]
  apply congrArg ((k.factorial:ℝ)*·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  exact (congrArg (fun t : ℝ => t*F (spectrum h R))
    (configuration_product S (1+a*h.val) R.val).symm).trans (mul_assoc _ _ _)

#print axioms continuous_sort
#print axioms slice_mass
#print axioms configuration_product
#print axioms distinct_born

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
