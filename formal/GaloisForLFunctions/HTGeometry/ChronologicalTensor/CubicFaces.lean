import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicComplex
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Faces of the physical cubic norming complex

The support of a physical cubic probe is a face precisely when adjacent gaps
cannot both be active. Its maximal faces are one triangle and three edges.
An exact symbolic face polynomial gives the Euler coefficient used for joins.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Finset


def cubicProbeSupport (g : Fin 5 → ℝ) : Finset (Fin 5) :=
  Finset.univ.filter (fun q => g q ≠ 0)

def cubicFacets : Finset (Finset (Fin 5)) :=
  {{0,2,4},{0,3},{1,3},{1,4}}

def cubicFaces : Finset (Finset (Fin 5)) := cubicFacets.biUnion Finset.powerset

theorem cubicProbeSupport_subset (g : Fin 5 → ℝ) (σ : Finset (Fin 5)) :
    cubicProbeSupport g ⊆ σ ↔ ∀ q ∉ σ, g q=0 := by
  constructor
  · intro h q hq
    by_contra hne
    exact hq (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩))
  · intro h q hq
    by_contra hn
    exact (Finset.mem_filter.mp hq).2 (h q hn)

theorem cubicProbeSupport_face (g : Fin 5 → ℝ) :
    cubicProbeSupport g ∈ cubicFaces ↔
      (g 0=0 ∨ g 1=0) ∧ (g 1=0 ∨ g 2=0) ∧
        (g 2=0 ∨ g 3=0) ∧ (g 3=0 ∨ g 4=0) := by
  have hT : cubicProbeSupport g ⊆ {0,2,4} ↔ g 1=0 ∧ g 3=0 := by
    rw [cubicProbeSupport_subset]
    constructor
    · intro h
      exact ⟨h 1 (by simp),h 3 (by simp)⟩
    · rintro ⟨h1,h3⟩ q hq
      fin_cases q
      · exact (hq (by simp)).elim
      · exact h1
      · exact (hq (by simp)).elim
      · exact h3
      · exact (hq (by simp)).elim
  have hB : cubicProbeSupport g ⊆ {0,3} ↔ g 1=0 ∧ g 2=0 ∧ g 4=0 := by
    rw [cubicProbeSupport_subset]
    constructor
    · intro h
      exact ⟨h 1 (by simp),h 2 (by simp),h 4 (by simp)⟩
    · rintro ⟨h1,h2,h4⟩ q hq
      fin_cases q
      · exact (hq (by simp)).elim
      · exact h1
      · exact h2
      · exact (hq (by simp)).elim
      · exact h4
  have hD : cubicProbeSupport g ⊆ {1,3} ↔ g 0=0 ∧ g 2=0 ∧ g 4=0 := by
    rw [cubicProbeSupport_subset]
    constructor
    · intro h
      exact ⟨h 0 (by simp),h 2 (by simp),h 4 (by simp)⟩
    · rintro ⟨h0,h2,h4⟩ q hq
      fin_cases q
      · exact h0
      · exact (hq (by simp)).elim
      · exact h2
      · exact (hq (by simp)).elim
      · exact h4
  have hC : cubicProbeSupport g ⊆ {1,4} ↔ g 0=0 ∧ g 2=0 ∧ g 3=0 := by
    rw [cubicProbeSupport_subset]
    constructor
    · intro h
      exact ⟨h 0 (by simp),h 2 (by simp),h 3 (by simp)⟩
    · rintro ⟨h0,h2,h3⟩ q hq
      fin_cases q
      · exact h0
      · exact (hq (by simp)).elim
      · exact h2
      · exact h3
      · exact (hq (by simp)).elim
  have hm : cubicProbeSupport g ∈ cubicFaces ↔
      cubicProbeSupport g ⊆ {0,2,4} ∨ cubicProbeSupport g ⊆ {0,3} ∨
        cubicProbeSupport g ⊆ {1,3} ∨ cubicProbeSupport g ⊆ {1,4} := by
    simp [cubicFaces,cubicFacets]
  rw [hm,hT,hB,hD,hC]
  clear hm hT hB hD hC
  tauto


theorem cubicProbeSection_faces :
    cubicProbeSection={g | (∀ q, 0 ≤ g q) ∧ g 0+g 1+g 2+g 3+g 4=1 ∧
      cubicProbeSupport g ∈ cubicFaces} := by
  ext g
  simp only [cubicProbeSection,mem_setOf_eq,cubicProbeSupport_face,mul_eq_zero]

def cubicExtraFaces : Finset (Finset (Fin 5)) :=
  {{1},{3},{0,3},{1,3},{1,4}}

theorem cubicFaces_decomposition :
    cubicFaces=({0,2,4} : Finset (Fin 5)).powerset ∪ cubicExtraFaces := by
  ext σ
  simp [cubicFaces,cubicFacets,cubicExtraFaces,Finset.powerset_insert,
    or_and_right,exists_or,eq_comm]
  tauto

theorem cubicFaces_disjoint :
    Disjoint ({0,2,4} : Finset (Fin 5)).powerset cubicExtraFaces := by
  apply Finset.disjoint_left.mpr
  intro σ hσ he
  simp only [cubicExtraFaces,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals simp [Finset.mem_powerset,Finset.insert_subset_iff] at hσ

def cubicFacePolynomial (z : ℤ) : ℤ := ∑ σ ∈ cubicFaces, z^σ.card

theorem cubicFacePolynomial_eq (z : ℤ) :
    cubicFacePolynomial z=(1+z)^3+2*z+3*z^2 := by
  have ht := Finset.prod_add (fun _ : Fin 5 => z) (fun _ => (1 : ℤ)) {0,2,4}
  have ht' : ∑ σ ∈ ({0,2,4} : Finset (Fin 5)).powerset, z^σ.card=(1+z)^3 := by
    simpa [add_comm] using ht.symm
  unfold cubicFacePolynomial
  rw [cubicFaces_decomposition,Finset.sum_union cubicFaces_disjoint,ht']
  simp [cubicExtraFaces,Finset.sum_insert,Finset.ext_iff,Fin.forall_fin_succ]
  ring

theorem cubicFaces_euler : ∑ σ ∈ cubicFaces, (-1 : ℤ)^σ.card=1 := by
  change cubicFacePolynomial (-1)=1
  rw [cubicFacePolynomial_eq]
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
