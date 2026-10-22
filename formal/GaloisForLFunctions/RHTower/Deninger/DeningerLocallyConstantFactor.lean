import GaloisForLFunctions.RHTower.Deninger.DeningerClopenPartition
import Mathlib.Topology.LocallyConstant.Basic

/-!
# A locally constant function on a compact profinite space factors through a finite quotient

Around every point a locally constant function is constant on a clopen neighbourhood, compactness
selects finitely many of them, and the atoms of the finite family they generate form a clopen
partition on which the function is constant.

This is why the locally constant sections over a profinite factor form a filtered union of finite
direct sums: every section already lives at a finite stage.

* `deningerLocallyConstant_clopen_nhd` : a clopen neighbourhood of constancy.
* `deningerLocallyConstant_factors` : the finite clopen partition of constancy.
-/

namespace RHTower

open Set TopologicalSpace

universe u v

section Factor

variable {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [TotallyDisconnectedSpace B] {Y : Type v}

/-- **Around every point a locally constant function is constant on a clopen neighbourhood.** -/
theorem deningerLocallyConstant_clopen_nhd {F : B → Y} (hF : IsLocallyConstant F) (b : B) :
    ∃ C : Set B, IsClopen C ∧ b ∈ C ∧ ∀ b' ∈ C, F b' = F b := by
  obtain ⟨U, hUopen, hbU, hUconst⟩ := (IsLocallyConstant.iff_exists_open F).mp hF b
  obtain ⟨C, hCclopen, hbC, hCU⟩ :=
    isTopologicalBasis_isClopen.exists_subset_of_mem_open hbU hUopen
  exact ⟨C, hCclopen, hbC, fun b' hb' => hUconst b' (hCU hb')⟩

/-- **A locally constant function on a compact profinite space is constant on the pieces of a
finite clopen partition.** -/
theorem deningerLocallyConstant_factors {F : B → Y} (hF : IsLocallyConstant F) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ι → Set B),
      (∀ a, IsClopen (D a)) ∧ (∀ b : B, ∃! a, b ∈ D a)
        ∧ ∀ (a : ι) (b b' : B), b ∈ D a → b' ∈ D a → F b = F b' := by
  classical
  choose C hCclopen hmemC hCconst using deningerLocallyConstant_clopen_nhd hF
  have hcover : (univ : Set B) ⊆ ⋃ b : B, C b := fun b _ => mem_iUnion.mpr ⟨b, hmemC b⟩
  obtain ⟨T, hT⟩ :=
    isCompact_univ.elim_finite_subcover C (fun b => (hCclopen b).isOpen) hcover
  -- index the finite subcover
  set ι₀ : Type u := {b : B // b ∈ T} with hι₀
  haveI : Fintype ι₀ := FinsetCoe.fintype T
  set Cs : ι₀ → Set B := fun j => C j.val with hCs
  have hCsClopen : ∀ j : ι₀, IsClopen (Cs j) := fun j => hCclopen j.val
  have hCsCover : ∀ b : B, ∃ j : ι₀, b ∈ Cs j := by
    intro b
    obtain ⟨j, hjT, hj⟩ := Set.mem_iUnion₂.mp (hT (mem_univ b))
    exact ⟨⟨j, hjT⟩, hj⟩
  refine ⟨Finset ι₀, inferInstance, fun P => deningerAtom Cs P,
    fun P => deningerAtom_isClopen hCsClopen P, deningerAtom_existsUnique Cs, ?_⟩
  intro P b b' hb hb'
  obtain ⟨j, hj⟩ := hCsCover b
  have hjP : j ∈ P := (hb j).mpr hj
  have hbC : b ∈ Cs j := hj
  have hb'C : b' ∈ Cs j := deningerAtom_subset hjP hb'
  rw [hCconst j.val b hbC, hCconst j.val b' hb'C]

end Factor

end RHTower
