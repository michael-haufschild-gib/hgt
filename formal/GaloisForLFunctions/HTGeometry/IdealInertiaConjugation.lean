import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Conjugation transport for ideal inertia

Conjugating an ideal and a group element transports its inertia subgroup exactly.  This belongs
below both the horizon valuation arguments and the Artin local-factor applications.
-/

open scoped Pointwise

noncomputable section

universe u

namespace GaloisForLFunctions

variable {S G : Type u}
variable [CommRing S] [Group G] [MulSemiringAction G S]

/-- Conjugation by `τ` transports the inertia subgroup of `Q` to the inertia subgroup of
`τ • Q`. -/
theorem inertia_map_conj (τ : G) (Q : Ideal S) :
    (Q.inertia G).map (MulAut.conj τ).toMonoidHom = (τ • Q).inertia G := by
  ext σ
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro x
    change (MulAut.conj τ) s • x - x ∈ τ • Q
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.conj_apply, smul_sub, mul_smul] using hs (τ⁻¹ • x)
  · intro hσ
    rw [Subgroup.mem_map_equiv]
    intro x
    have hx := hσ (τ • x)
    change σ • τ • x - τ • x ∈ τ • Q at hx
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
    change (MulAut.conj τ).symm σ • x - x ∈ Q
    simpa [MulAut.conj_symm_apply, smul_sub, mul_smul] using hx

end GaloisForLFunctions
