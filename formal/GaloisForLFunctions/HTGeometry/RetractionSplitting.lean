import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Splitting a commutative group along a retraction

A retraction `r` of the inclusion of a subgroup `M` into a commutative group `A` splits `A` as
`M × ker r`, by `a ↦ (r a , a · ι (r a)⁻¹)`.  Consequently the character group splits: restricting
a character to `M` and to `ker r` is a bijection onto pairs, with inverse the product of the two
restrictions.

This is the group-theoretic content of Deninger's splitting of `1 → μ(κ(x)) → κ(x)^× → κ(x)^× ⊗ ℚ
→ 1` and of the resulting decomposition of `Hom(κ(x)^× , C^×)`.
-/

namespace HTGeometry

variable {A M : Type*} [CommGroup A] [CommGroup M]
variable (ι : M →* A) (r : A →* M) (hr : ∀ m, r (ι m) = m)

include hr in
theorem mem_ker_retraction (a : A) : a * (ι (r a))⁻¹ ∈ MonoidHom.ker r := by
  show r (a * (ι (r a))⁻¹) = 1
  simp [hr]

/-- A retraction splits the group as the product of the subgroup and the kernel of the
retraction. -/
def retractionProdEquiv : A ≃* M × (MonoidHom.ker r) where
  toFun a := (r a, ⟨a * (ι (r a))⁻¹, mem_ker_retraction ι r hr a⟩)
  invFun mb := ι mb.1 * (mb.2 : A)
  left_inv a := by
    show ι (r a) * (a * (ι (r a))⁻¹) = a
    rw [mul_comm, inv_mul_cancel_right]
  right_inv mb := by
    obtain ⟨m, b, hb⟩ := mb
    have hb' : r b = 1 := hb
    refine Prod.ext ?_ ?_
    · show r (ι m * b) = m
      rw [map_mul, hr, hb', mul_one]
    · refine Subtype.ext ?_
      show ι m * b * (ι (r (ι m * b)))⁻¹ = b
      rw [map_mul, hr, hb', mul_one, mul_comm (ι m) b, mul_inv_cancel_right]
  map_mul' a b := by
    refine Prod.ext ?_ ?_
    · exact map_mul r a b
    · refine Subtype.ext ?_
      show a * b * (ι (r (a * b)))⁻¹ = a * (ι (r a))⁻¹ * (b * (ι (r b))⁻¹)
      rw [map_mul, map_mul, mul_inv, mul_mul_mul_comm]

theorem retractionProdEquiv_apply (a : A) :
    retractionProdEquiv ι r hr a = (r a, ⟨a * (ι (r a))⁻¹, mem_ker_retraction ι r hr a⟩) := rfl

theorem retractionProdEquiv_symm_apply (mb : M × (MonoidHom.ker r)) :
    (retractionProdEquiv ι r hr).symm mb = ι mb.1 * (mb.2 : A) := rfl

variable (T : Type*) [CommGroup T]

/-- **The character group of a retracted extension splits.**  Restricting a character to the
retracted subgroup and to the kernel of the retraction is a bijection onto pairs of characters. -/
def homRetractionEquiv :
    (A →* T) ≃ (M →* T) × ((MonoidHom.ker r) →* T) where
  toFun χ := (χ.comp ι, χ.comp (MonoidHom.ker r).subtype)
  invFun p := (MonoidHom.coprod p.1 p.2).comp (retractionProdEquiv ι r hr).toMonoidHom
  left_inv χ := by
    refine MonoidHom.ext fun a => ?_
    show χ (ι (r a)) * χ (a * (ι (r a))⁻¹) = χ a
    rw [← map_mul, mul_comm, inv_mul_cancel_right]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · refine MonoidHom.ext fun m => ?_
      show p.1 (r (ι m)) * p.2 ⟨ι m * (ι (r (ι m)))⁻¹, mem_ker_retraction ι r hr (ι m)⟩ = p.1 m
      have hval : (⟨ι m * (ι (r (ι m)))⁻¹, mem_ker_retraction ι r hr (ι m)⟩ :
          MonoidHom.ker r) = 1 := Subtype.ext (by simp [hr])
      rw [hval, map_one, mul_one, hr]
    · refine MonoidHom.ext fun b => ?_
      show p.1 (r (b : A)) * p.2 ⟨(b : A) * (ι (r (b : A)))⁻¹, mem_ker_retraction ι r hr b⟩
        = p.2 b
      have hb : r (b : A) = 1 := b.2
      have hval : (⟨(b : A) * (ι (r (b : A)))⁻¹, mem_ker_retraction ι r hr b⟩ :
          MonoidHom.ker r) = b := Subtype.ext (by simp [hb])
      rw [hval, hb, map_one, one_mul]

/-- **Deninger, Proposition 9.1.**  The explicit factorization `χ = χ̃₁ · χ̃₂` of a character
through the retraction. -/
theorem homRetraction_apply (χ : A →* T) (a : A) :
    χ a = (homRetractionEquiv ι r hr T χ).1 (r a)
      * (homRetractionEquiv ι r hr T χ).2 ⟨a * (ι (r a))⁻¹, mem_ker_retraction ι r hr a⟩ := by
  show χ a = χ (ι (r a)) * χ (a * (ι (r a))⁻¹)
  rw [← map_mul, mul_comm, inv_mul_cancel_right]

end HTGeometry

namespace HTGeometry


variable {A M : Type*} [CommGroup A] [CommGroup M]
variable (ι : M →* A) (r : A →* M) (hr : ∀ m, r (ι m) = m)
variable (T : Type*) [CommGroup T]

theorem homRetractionEquiv_fst (χ : A →* T) :
    (homRetractionEquiv ι r hr T χ).1 = χ.comp ι := rfl

/-- **Deninger, equation (90).**  The fibre of restriction to the retracted subgroup over a fixed
character is in bijection with the characters of the kernel of the retraction. -/
def homRetractionFibreEquiv (χM : M →* T) :
    {χ : A →* T // χ.comp ι = χM} ≃ ((MonoidHom.ker r) →* T) where
  toFun χ := (homRetractionEquiv ι r hr T χ.1).2
  invFun ψ := ⟨(homRetractionEquiv ι r hr T).symm (χM, ψ), by
    have h := (homRetractionEquiv ι r hr T).apply_symm_apply (χM, ψ)
    have h1 := congrArg Prod.fst h
    rw [homRetractionEquiv_fst] at h1
    exact h1⟩
  left_inv := by
    rintro ⟨χ, hχ⟩
    refine Subtype.ext ?_
    have hpair : ((χM : M →* T), (homRetractionEquiv ι r hr T χ).2)
        = homRetractionEquiv ι r hr T χ := by
      refine Prod.ext ?_ rfl
      rw [homRetractionEquiv_fst, hχ]
    show (homRetractionEquiv ι r hr T).symm (χM, (homRetractionEquiv ι r hr T χ).2) = χ
    rw [hpair, Equiv.symm_apply_apply]
  right_inv ψ := by
    show (homRetractionEquiv ι r hr T ((homRetractionEquiv ι r hr T).symm (χM, ψ))).2 = ψ
    rw [Equiv.apply_symm_apply]

end HTGeometry
