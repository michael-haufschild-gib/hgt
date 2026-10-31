import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnRepresentation
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Column representations of zero subgroups

Columns indexed by a subgroup form an invariant subspace for that subgroup. If a Hermitian
kernel vanishes there, its negative index bounds the dimension of this column space. Ambient
unipotence restricts to the subgroup action without assuming invariance under the whole group.
-/

open Complex Finset
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- Columns indexed by a subgroup, retaining their values on the whole group. -/
def kernelSubgroupColumnSpan (k : G → ℂ) (H : Subgroup G) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range (fun h : H => kernelColumn k (h : G)))

theorem kernelSubgroupColumnSpan_le (k : G → ℂ) (H : Subgroup G) :
    kernelSubgroupColumnSpan k H ≤ kernelColumnSpan k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  exact Submodule.subset_span ⟨(h : G), rfl⟩

/-- A zero subgroup of a kernel of index at most `r` has at most `r` independent columns. -/
theorem finite_kernelSubgroupColumnSpan {k : G → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r) (H : Subgroup G) (hH : ∀ h ∈ H, k h = 0) :
    Module.Finite ℂ (kernelSubgroupColumnSpan k H) ∧
      Module.finrank ℂ (kernelSubgroupColumnSpan k H) ≤ r := by
  classical
  obtain ⟨m, a, hm, ha⟩ := exists_null_subgroup_column_generators hk hi H hH
  have hs : kernelSubgroupColumnSpan k H =
      Submodule.span ℂ (Set.range (fun j : Fin m => kernelColumn k (a j : G))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      obtain ⟨c, hc⟩ := ha h
      have he : kernelColumn k (h : G) = ∑ j, c j • kernelColumn k (a j : G) := by
        funext y
        simpa only [kernelColumn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc y
      change kernelColumn k (h : G) ∈ _
      rw [he]
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨j, rfl⟩))
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨a j, rfl⟩
  rw [hs]
  refine ⟨Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _)), ?_⟩
  exact (finrank_range_le_card (R := ℂ) _).trans (by simpa only [Fintype.card_fin] using hm)

theorem kernelColumnTranslate_mem_subgroup (k : G → ℂ) (H : Subgroup G) (a : H)
    {f : G → ℂ} (hf : f ∈ kernelSubgroupColumnSpan k H) :
    kernelColumnTranslate (a : G) f ∈ kernelSubgroupColumnSpan k H := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨h, rfl⟩ := hf
    rw [kernelColumnTranslate_column]
    exact Submodule.subset_span ⟨a * h, rfl⟩
  | zero => simpa only [map_zero] using (kernelSubgroupColumnSpan k H).zero_mem
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (kernelSubgroupColumnSpan k H).add_mem ihf ihg
  | smul c f hf ih =>
    simpa only [map_smul] using (kernelSubgroupColumnSpan k H).smul_mem c ih

/-- The subgroup acts on its own column span by inverse pullback. -/
def kernelSubgroupRepresentation (k : G → ℂ) (H : Subgroup G) :
    H →* Module.End ℂ (kernelSubgroupColumnSpan k H) where
  toFun a := (kernelColumnTranslate (a : G)).restrict
    (fun f hf => kernelColumnTranslate_mem_subgroup k H a hf)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (f : G → ℂ) ((1 : G)⁻¹ * x) = (f : G → ℂ) x
    rw [inv_one, one_mul]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (f : G → ℂ) (((a : G) * b)⁻¹ * x) =
      (f : G → ℂ) ((b : G)⁻¹ * ((a : G)⁻¹ * x))
    rw [_root_.mul_inv_rev, mul_assoc]

/-- The identity column belongs to every subgroup column span. -/
def kernelSubgroupVector (k : G → ℂ) (H : Subgroup G) : kernelSubgroupColumnSpan k H :=
  ⟨kernelColumn k 1, Submodule.subset_span ⟨(1 : H), rfl⟩⟩

theorem kernelSubgroupVector_ne_zero {k : G → ℂ} (H : Subgroup G) (hk : k ≠ 0) :
    kernelSubgroupVector k H ≠ 0 := by
  intro h
  apply hk
  funext g
  have he := congrArg (fun f : kernelSubgroupColumnSpan k H => (f : G → ℂ) g⁻¹) h
  change k ((g⁻¹)⁻¹ * 1) = 0 at he
  simpa only [inv_inv, mul_one, Pi.zero_apply] using he

/-- Evaluation at the inverse point reads products with the subgroup on the right. -/
def kernelSubgroupObservation (k : G → ℂ) (H : Subgroup G) (a : G) :
    kernelSubgroupColumnSpan k H →ₗ[ℂ] ℂ where
  toFun f := (f : G → ℂ) a⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelSubgroupRepresentation_vector (k : G → ℂ) (H : Subgroup G) (h : H) :
    (kernelSubgroupRepresentation k H h (kernelSubgroupVector k H) : G → ℂ) =
      kernelColumn k (h : G) := by
  change kernelColumnTranslate (h : G) (kernelColumn k 1) = _
  rw [kernelColumnTranslate_column, mul_one]

/-- Subgroup orbits recover every right-coset reading of the kernel. -/
theorem kernelSubgroupObservation_representation (k : G → ℂ) (H : Subgroup G)
    (a : G) (h : H) :
    kernelSubgroupObservation k H a
      (kernelSubgroupRepresentation k H h (kernelSubgroupVector k H)) = k (a * h) := by
  change (kernelSubgroupRepresentation k H h (kernelSubgroupVector k H) : G → ℂ) a⁻¹ = _
  rw [kernelSubgroupRepresentation_vector]
  simp only [kernelColumn, inv_inv]

/-- Nilpotence of a group element minus identity passes to its subgroup column action. -/
theorem isNilpotent_subgroup_sub_one (k : G → ℂ) (H : Subgroup G) (h : H)
    (hnil : IsNilpotent (kernelColumnRepresentation k (h : G) - 1)) :
    IsNilpotent (kernelSubgroupRepresentation k H h - 1) := by
  let N := kernelColumnTranslate (h : G) - 1
  have hV : ∀ f ∈ kernelColumnSpan k, N f ∈ kernelColumnSpan k := by
    intro f hf
    exact (kernelColumnSpan k).sub_mem (kernelColumnTranslate_mem k (h : G) hf) hf
  have hW : ∀ f ∈ kernelSubgroupColumnSpan k H, N f ∈ kernelSubgroupColumnSpan k H := by
    intro f hf
    exact (kernelSubgroupColumnSpan k H).sub_mem
      (kernelColumnTranslate_mem_subgroup k H h hf) hf
  change IsNilpotent (N.restrict hV) at hnil
  change IsNilpotent (N.restrict hW)
  exact Module.End.isNilpotent_restrict_of_le (kernelSubgroupColumnSpan_le k H) hnil

#print axioms finite_kernelSubgroupColumnSpan
#print axioms kernelSubgroupRepresentation
#print axioms kernelSubgroupObservation_representation
#print axioms isNilpotent_subgroup_sub_one
end GaloisForLFunctions.HeckeKreinToeplitz
