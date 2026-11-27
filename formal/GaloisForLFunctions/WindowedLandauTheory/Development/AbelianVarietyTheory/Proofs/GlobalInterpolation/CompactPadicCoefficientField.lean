import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountablePadicSubfields
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.Lemmas

/-! A continuous matrix representation of a compact group over the
algebraic closure of the p-adics is defined over a finite extension. -/

noncomputable section

open IntermediateField

namespace GlobalTheory.CompactRepField

private def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

/-- Baire's theorem gives an open subgroup defined over a finite extension.
Adjoin the entries of its finitely many coset representatives. -/
theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

end GlobalTheory.CompactRepField
