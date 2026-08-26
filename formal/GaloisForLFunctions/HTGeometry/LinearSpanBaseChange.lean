import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence

/-!
# Finite coordinate spans under field extension

An arbitrary finite linearly independent family in a finite coordinate space remains independent
after extending the coefficient field.  Consequently, membership of a base-field vector in its
span is reflected by every field extension.  Unlike the existing square-family result, the family
may have any finite cardinality.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry
namespace LinearSpanBaseChange

open ABHN

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {m ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linearly independent family in a finite coordinate space remains independent after applying
the coefficient-field embedding coordinatewise. -/
theorem linearIndependent_coordinate_algebraMap
    (v : m → (ι → K)) (hv : LinearIndependent K v) :
    LinearIndependent L (fun j i => algebraMap K L (v j i)) := by
  have ht : LinearIndependent L (fun j => (1 : L) ⊗ₜ[K] v j) :=
    (linearIndependent_one_tmul_iff v).mp hv
  have hmapped := ht.map'
    (TensorProduct.piScalarRight K L L ι).toLinearMap
    (LinearMap.ker_eq_bot.mpr (TensorProduct.piScalarRight K L L ι).injective)
  simpa [Function.comp_def, Algebra.smul_def] using hmapped

/- For a finite independent family, extending scalars reflects membership of a base-field vector
in the family's span. -/
set_option maxHeartbeats 800000 in
theorem mem_span_coordinate_algebraMap_iff
    {r : ℕ} (v : Fin r → (ι → K)) (hv : LinearIndependent K v)
    (x : ι → K) :
    (fun i => algebraMap K L (x i)) ∈
        Submodule.span L (Set.range fun j => fun i => algebraMap K L (v j i)) ↔
      x ∈ Submodule.span K (Set.range v) := by
  constructor
  · intro hx
    by_contra hxK
    have hconsK : LinearIndependent K (Fin.cons x v) :=
      linearIndependent_finCons.2 ⟨hv, hxK⟩
    let xL : ι → L := fun i => algebraMap K L (x i)
    let vL : Fin r → (ι → L) := fun j i => algebraMap K L (v j i)
    have hconsL : LinearIndependent L (Fin.cons xL vL) := by
      have h := linearIndependent_coordinate_algebraMap (L := L) (Fin.cons x v) hconsK
      convert h using 1
      funext j i
      refine Fin.cases ?_ (fun q => ?_) j
      · rfl
      · rfl
    exact (linearIndependent_finCons.1 hconsL).2 (by simpa [xL, vL] using hx)
  · intro hx
    refine Submodule.span_induction (p := fun x _ =>
      (fun i => algebraMap K L (x i)) ∈
        Submodule.span L (Set.range fun j => fun i => algebraMap K L (v j i))) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    · convert (Submodule.zero_mem
        (Submodule.span L (Set.range fun j => fun i => algebraMap K L (v j i)))) using 1
      funext i
      simp
    · intro y z _ _ hy hz
      convert Submodule.add_mem _ hy hz using 1
      funext i
      simp
    · intro a y _ hy
      have hs := Submodule.smul_mem
        (Submodule.span L (Set.range fun j => fun i => algebraMap K L (v j i)))
        (algebraMap K L a) hy
      convert hs using 1
      funext i
      simp [Pi.smul_apply]

end LinearSpanBaseChange
end GaloisForLFunctions.HTGeometry
