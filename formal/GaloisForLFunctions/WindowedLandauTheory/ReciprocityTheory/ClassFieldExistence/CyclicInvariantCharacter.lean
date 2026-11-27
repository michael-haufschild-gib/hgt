import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A conjugation-invariant character of a normal subgroup with cyclic
quotient gives an abelian quotient by the character's kernel. -/

namespace GlobalTheory.Reciprocity

variable {G A : Type*} [Group G] [Group A]
  (H : Subgroup G) [H.Normal]

/-- Conjugation by an ambient element preserves a normal subgroup. -/
def conjugateIn (t : G) (x : H) : H :=
  ⟨t * x.val * t⁻¹, Subgroup.Normal.conj_mem inferInstance x.val x.2 t⟩

theorem normal_map_ker_of_conjugation_invariant (ρ : H →* A)
    (hρ : ∀ (t : G) (x : H), ρ (conjugateIn H t x) = ρ x) :
    (ρ.ker.map H.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨x, hx, rfl⟩ t
  exact ⟨conjugateIn H t x, (MonoidHom.mem_ker.mpr ((hρ t x).trans hx)), rfl⟩

theorem quotient_isMulCommutative_of_conjugation_invariant [IsCyclic (G ⧸ H)]
    (ρ : H →* A) (hρ : ∀ (t : G) (x : H), ρ (conjugateIn H t x) = ρ x) :
    letI := normal_map_ker_of_conjugation_invariant H ρ hρ
    IsMulCommutative (G ⧸ ρ.ker.map H.subtype) := by
  let N := ρ.ker.map H.subtype
  letI : N.Normal := normal_map_ker_of_conjugation_invariant H ρ hρ
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f := QuotientGroup.lift N (QuotientGroup.mk' H) (fun _ ⟨x, _, hx⟩ =>
    (QuotientGroup.eq_one_iff _).mpr (hx ▸ x.2))
  apply f.isMulCommutative_of_isCyclic_of_ker_le_center
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hg : g ∈ H := (QuotientGroup.eq_one_iff g).mp hy
  let x : H := ⟨g, hg⟩
  refine Subgroup.mem_center_iff.mpr fun z => ?_
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N z
  have h : q (t * g * t⁻¹) = q g := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨conjugateIn H t x * x⁻¹, MonoidHom.mem_ker.mpr ?_, rfl⟩
    rw [map_mul, hρ, map_inv, mul_inv_cancel]
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa only [map_mul, map_inv] using h) :
    q t * q g = q g * q t)

end GlobalTheory.Reciprocity
