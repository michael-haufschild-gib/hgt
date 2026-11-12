import GaloisForLFunctions.RHTower.Artin.ArtinRangeOfACommutingIdempotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A normal subgroup acting by scalars

Let `ρ` be a representation of `E` on `V`, `P` an idempotent commuting with `ρ(E)`, and `A` a
normal subgroup with `ρ(a) P = χ(a) P` for a linear character `χ` of `A`. Then `A` acts on the
range of `P` by the scalars `χ(a)` (`rangeRepresentation_apply_of_scalar`), so the commutators
`a g a⁻¹ g⁻¹` act trivially there, and the representation on the range factors through
`E / [A, E]`. Hence `g ↦ tr(ρ(g) P)` is the pullback of a character of `E / [A, E]`
(`exists_character_quotient_commutator`).
-/

noncomputable section

universe u w

namespace GaloisForLFunctions

variable {E : Type u} [Group E] {V : Type w} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ E V) (P : Module.End ℂ V)

/-- If `ρ(a) P = c P` then `a` acts on the range of `P` by the scalar `c`. -/
theorem rangeRepresentation_apply_of_scalar (hP : P * P = P) (hcomm : ∀ g, ρ g * P = P * ρ g)
    {a : E} {c : ℂ} (ha : ρ a * P = c • P) :
    rangeRepresentation ρ P hP hcomm a = c • (1 : Module.End ℂ (LinearMap.range P)) := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  have hw := idempotent_apply_of_mem_range P hP w
  have h1 : ρ a (P (w : V)) = c • P (w : V) := LinearMap.congr_fun ha (w : V)
  rw [hw] at h1
  show P (ρ a (w : V)) = c • (w : V)
  rw [h1, map_smul, hw]

variable (A : Subgroup E) [A.Normal] [FiniteDimensional ℂ V]

/-- **If `A` acts on the range of a commuting idempotent `P` by scalars, then `g ↦ tr(ρ(g) P)`
is the pullback of a character of `E / [A, E]`.** -/
theorem exists_character_quotient_commutator (hP : P * P = P)
    (hcomm : ∀ g, ρ g * P = P * ρ g) (χ : A →* ℂˣ)
    (hχ : ∀ a : A, ρ (a : E) * P = ((χ a : ℂˣ) : ℂ) • P) :
    ∃ τ ∈ fdCharacterSet (E ⧸ ⁅A, (⊤ : Subgroup E)⁆),
      ∀ g : E, τ (g : E ⧸ ⁅A, (⊤ : Subgroup E)⁆) = LinearMap.trace ℂ V (ρ g * P) := by
  -- the commutators act trivially on the range
  have hker : ⁅A, (⊤ : Subgroup E)⁆ ≤ (rangeRepresentation ρ P hP hcomm).ker := by
    rw [Subgroup.commutator_le]
    intro a ha g _
    have hc : ((χ ⟨a, ha⟩ : ℂˣ) : ℂ) * ((χ ⟨a⁻¹, A.inv_mem ha⟩ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul,
        show (⟨a, ha⟩ : A) * ⟨a⁻¹, A.inv_mem ha⟩ = 1 from Subtype.ext (mul_inv_cancel a), map_one,
        Units.val_one]
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul,
      rangeRepresentation_apply_of_scalar ρ P hP hcomm (hχ ⟨a, ha⟩),
      rangeRepresentation_apply_of_scalar ρ P hP hcomm (hχ ⟨a⁻¹, A.inv_mem ha⟩)]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    rw [mul_comm, hc, one_smul, ← map_mul, mul_inv_cancel, map_one]
  refine ⟨Representation.character (QuotientGroup.lift _ (rangeRepresentation ρ P hP hcomm) hker),
    representation_character_mem_fdCharacterSet _ _, fun g => ?_⟩
  show LinearMap.trace ℂ _
    (QuotientGroup.lift _ (rangeRepresentation ρ P hP hcomm) hker (g : E ⧸ _)) = _
  rw [QuotientGroup.lift_mk]
  exact rangeRepresentation_character ρ P hP hcomm g

end GaloisForLFunctions
