import GaloisForLFunctions.RHTower.Artin.ArtinBrauerElementarySpan

/-! Detect virtual characters by restricting to Brauer-elementary subgroups. -/

open GaloisForLFunctions

namespace GlobalTheory.CuspGL

variable {G : Type} [Group G] [Fintype G]

/-- Inducing a virtual character gives a virtual character. -/
theorem inducedFunction_mem_virtual (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ virtualCharacterGroup H) : inducedFunction H f ∈ virtualCharacterGroup G := by
  have hle : virtualCharacterGroup H ≤ (virtualCharacterGroup G).comap (inducedFunctionHom H) := by
    rw [virtualCharacterGroup, AddSubgroup.closure_le]
    intro χ hχ
    exact AddSubgroup.subset_closure (inducedFunction_mem_fdCharacterSet H hχ)
  exact hle hf

/-- Brauer induction and the projection formula reduce virtuality to elementary subgroups. -/
theorem virtual_of_brauer_restrictions (ψ : G → ℂ)
    (hclass : ∀ x g : G, ψ (x * g * x⁻¹) = ψ g)
    (hlocal : ∀ H ∈ brauerElementaryFamily G, (fun h : H => ψ h) ∈ virtualCharacterGroup H) :
    ψ ∈ virtualCharacterGroup G := by
  classical
  have h1 : (1 : G → ℂ) ∈ inducedSpan (brauerElementaryFamily G) := by
    rw [inducedSpan_brauerElementaryFamily]
    exact AddSubgroup.subset_closure one_mem_fdCharacterSet
  have hmul (f : G → ℂ) (hf : f ∈ inducedSpan (brauerElementaryFamily G)) :
      f * ψ ∈ virtualCharacterGroup G := by
    refine AddSubgroup.closure_induction (p := fun φ _ => φ * ψ ∈ virtualCharacterGroup G)
      ?_ ?_ ?_ ?_ hf
    · rintro φ ⟨H, hH, χ, hχ, rfl⟩
      change (fun g => inducedFunction H χ g * ψ g) ∈ virtualCharacterGroup G
      rw [← inducedFunction_mul_restrict H χ ψ hclass]
      exact inducedFunction_mem_virtual H (mul_mem_virtualCharacterGroup
        (AddSubgroup.subset_closure hχ) (hlocal H hH))
    · rw [zero_mul]
      exact zero_mem _
    · intro a b _ _ ha hb
      rw [add_mul]
      exact add_mem ha hb
    · intro a _ ha
      rw [neg_mul]
      exact neg_mem ha
  simpa only [one_mul] using hmul 1 h1

end GlobalTheory.CuspGL
