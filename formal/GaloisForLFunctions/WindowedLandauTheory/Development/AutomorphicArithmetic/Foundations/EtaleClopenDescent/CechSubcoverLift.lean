import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverCechRestriction

/-! Ordered subcovers inherit the differential, and any cochain on a
subcover extends to the full cover. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k M ι κ : Type} [Field k] [AddCommGroup M] [Module k M]
  [LinearOrder ι] [LinearOrder κ]

/-- Restrict the ambient space of cochains to the indicated ordered indices. -/
def restrictIndex (j : κ ↪o ι) : (Finset ι → M) →ₗ[k] (Finset κ → M) :=
  LinearMap.pi fun I => LinearMap.proj (I.map j.toEmbedding)

theorem restrictIndex_apply (j : κ ↪o ι) (a : Finset ι → M) (I : Finset κ) :
    restrictIndex (k := k) j a I = a (I.map j.toEmbedding) := rfl

theorem restrictIndex_delta (j : κ ↪o ι) (a : Finset ι → M) :
    restrictIndex (k := k) j (deltaL k ι M a) = deltaL k κ M (restrictIndex (k := k) j a) := by
  funext I
  simp only [restrictIndex_apply, deltaL_apply, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show j.toEmbedding i = j i from rfl, cubeSign, cechSign_orderEmbedding]
  have he : (I.map j.toEmbedding).erase (j i) = (I.erase i).map j.toEmbedding :=
    (Finset.map_erase j.toEmbedding I i).symm
  exact congrArg (fun J => cubeSign I i • a J) he

theorem isMap_restrictIndex (A : Finset ι → Submodule k M) (B : Finset κ → Submodule k M)
    (j : κ ↪o ι) (h : ∀ I, I.Nonempty → A (I.map j.toEmbedding) ≤ B I) :
    IsMap (cech A) (cech B) (restrictIndex j) := by
  intro n a ha
  refine ⟨Submodule.mem_pi.mpr fun I _ => ?_, restrictIndex_delta j a⟩
  change a (I.map j.toEmbedding) ∈ (if I.Nonempty ∧ (I.card : ℤ) = n + 1 then B I else ⊥)
  have hm := (Submodule.mem_pi.mp ha) (I.map j.toEmbedding) (Set.mem_univ _)
  change a (I.map j.toEmbedding) ∈
    (if (I.map j.toEmbedding).Nonempty ∧ ((I.map j.toEmbedding).card : ℤ) = n + 1
      then A (I.map j.toEmbedding) else ⊥) at hm
  simp only [Finset.map_nonempty, Finset.card_map] at hm
  split_ifs at hm ⊢ with hI
  · exact h I hI.1 hm
  · exact hm

/-- Extend a homogeneous subcover cochain by zero on all other intersections. -/
theorem exists_cochainLift_restrictIndex (A : Finset ι → Submodule k M)
    (B : Finset κ → Submodule k M) (j : κ ↪o ι)
    (h : ∀ I, I.Nonempty → B I ≤ A (I.map j.toEmbedding)) (n : ℤ)
    (a : Finset κ → M) (ha : a ∈ (cech B).C n) :
    ∃ b ∈ (cech A).C n, restrictIndex (k := k) j b = a := by
  classical
  let b (I : Finset ι) : M := if hi : ∃ J : Finset κ, J.map j.toEmbedding = I then a hi.choose else 0
  have hb (J : Finset κ) : b (J.map j.toEmbedding) = a J := by
    have hJ : ∃ I : Finset κ, I.map j.toEmbedding = J.map j.toEmbedding := ⟨J, rfl⟩
    simp only [b, dif_pos hJ, Finset.map_injective j.toEmbedding hJ.choose_spec]
  refine ⟨b, Submodule.mem_pi.mpr fun I _ => ?_, funext hb⟩
  by_cases hI : ∃ J : Finset κ, J.map j.toEmbedding = I
  · obtain ⟨J, rfl⟩ := hI
    rw [hb]
    simp only [Finset.map_nonempty, Finset.card_map]
    have haJ : a J ∈ (if J.Nonempty ∧ (J.card : ℤ) = n + 1 then B J else ⊥) :=
      (Submodule.mem_pi.mp ha) J (Set.mem_univ _)
    split_ifs at haJ ⊢ with hJ
    · exact h J hJ.1 haJ
    · exact haJ
  · simp only [b, dif_neg hI]
    exact zero_mem _

/-- A cocycle can be lifted with its values unchanged on the subcover
whenever restriction is surjective on cohomology. -/
theorem exists_cycleLift_restrictIndex (A : Finset ι → Submodule k M)
    (B : Finset κ → Submodule k M) (j : κ ↪o ι)
    (h : ∀ I, I.Nonempty → A (I.map j.toEmbedding) = B I)
    (hA : (cech A).IsCx) (n : ℤ)
    (hs : Function.Surjective ((cech A).hmap (cech B) (restrictIndex j)
      (isMap_restrictIndex A B j (fun I hI => (h I hI).le)) n))
    (a : (cech B).Z n) :
    ∃ b : (cech A).Z n, restrictIndex (k := k) j b.val = a.val := by
  let K := cech A
  let L := cech B
  let f := restrictIndex (k := k) (M := M) j
  have hf : IsMap K L f := isMap_restrictIndex A B j (fun I hI => (h I hI).le)
  obtain ⟨y, hy⟩ := hs (Submodule.Quotient.mk a)
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hb : f b.val ∈ L.Z n := ⟨(hf n b.val b.property.1).1,
    LinearMap.mem_ker.mpr (by
      rw [← (hf n b.val b.property.1).2, LinearMap.mem_ker.mp b.property.2, map_zero])⟩
  change (Submodule.Quotient.mk (⟨f b.val, hb⟩ : L.Z n) : L.H n) =
    Submodule.Quotient.mk a at hy
  have hh : f b.val - a.val ∈ L.B n :=
    (Submodule.Quotient.eq ((L.B n).submoduleOf (L.Z n))).mp hy
  obtain ⟨v, hv, hδ⟩ := Submodule.mem_map.mp hh
  obtain ⟨w, hw, hfw⟩ := exists_cochainLift_restrictIndex A B j
    (fun I hI => (h I hI).ge) (n - 1) v hv
  have hDw : K.D w ∈ K.Z n :=
    Cx.boundaries_le_cycles hA n (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
  refine ⟨b - ⟨K.D w, hDw⟩, ?_⟩
  change f (b.val - K.D w) = a.val
  rw [map_sub, (hf (n - 1) w hw).2, hfw, hδ, sub_sub_cancel]

end GlobalTheory.PD
