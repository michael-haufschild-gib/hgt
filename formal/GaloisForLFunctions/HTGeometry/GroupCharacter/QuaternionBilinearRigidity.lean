import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualGroupRepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Invariant bilinear forms of the actual quaternionic representation

The two quaternionic generators force the diagonal entries of an invariant
bilinear form to vanish and its off-diagonal entries to be opposite.
Consequently the invariant forms are exactly the scalar multiples of the
existing alternating form. Their space has dimension one, and its symmetric
part is zero. This identifies the alternating type behind the square-character
mechanism in Aoki, arXiv:2611.20592, on the corpus's literal representation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GroupCharacter
open RHTower

private def e₁ : Q8Carrier := (1, 0)
private def e₂ : Q8Carrier := (0, 1)

private theorem bilin_coordinates (B : LinearMap.BilinForm ℂ Q8Carrier) (p q : Q8Carrier) :
    B p q = p.1 * q.1 * B e₁ e₁ + p.1 * q.2 * B e₁ e₂ +
      p.2 * q.1 * B e₂ e₁ + p.2 * q.2 * B e₂ e₂ := by
  have hp : p = p.1 • e₁ + p.2 • e₂ := by ext <;> simp [e₁, e₂]
  have hq : q = q.1 • e₁ + q.2 • e₂ := by ext <;> simp [e₁, e₂]
  conv_lhs => rw [hp, hq]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Invariant bilinear forms on the literal quaternionic carrier are exactly multiples of its alternating form. -/
theorem q8_bilinear_invariant_iff (B : LinearMap.BilinForm ℂ Q8Carrier) :
    (∀ g : QuaternionGroup 2, ∀ p q : Q8Carrier,
      B (deningerQ8Representation g p) (deningerQ8Representation g q) = B p q) ↔
      B = (B (1, 0) (0, 1)) • deningerQ8TransitionSymplectic := by
  constructor
  · intro hB
    have hI₁ : deningerQ8Representation (QuaternionGroup.a 1) e₁ = Complex.I • e₁ := by
      rw [deningerQ8Representation_a_one_apply]
      ext <;> simp [deningerQuaternionTransitionI, e₁]
    have hI₂ : deningerQ8Representation (QuaternionGroup.a 1) e₂ = (-Complex.I) • e₂ := by
      rw [deningerQ8Representation_a_one_apply]
      ext <;> simp [deningerQuaternionTransitionI, e₂]
    have hK₁ : deningerQ8Representation (QuaternionGroup.xa 0) e₁ = e₂ := by
      rw [deningerQ8Representation_xa_zero_apply]
      ext <;> simp [deningerQuaternionTransitionK, e₁, e₂]
    have hK₂ : deningerQ8Representation (QuaternionGroup.xa 0) e₂ = -e₁ := by
      rw [deningerQ8Representation_xa_zero_apply]
      ext <;> simp [deningerQuaternionTransitionK, e₁, e₂]
    have h11 := hB (QuaternionGroup.a 1) e₁ e₁
    rw [hI₁] at h11
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h11
    have hz11 : B e₁ e₁ = 0 := by
      have he : Complex.I * (Complex.I * B e₁ e₁) = -B e₁ e₁ := by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
      rw [he] at h11
      linear_combination -(1 / 2 : ℂ) * h11
    have h22 := hB (QuaternionGroup.a 1) e₂ e₂
    rw [hI₂] at h22
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h22
    have hz22 : B e₂ e₂ = 0 := by
      have he : -Complex.I * (-Complex.I * B e₂ e₂) = -B e₂ e₂ := by
        rw [← mul_assoc, neg_mul_neg, Complex.I_mul_I, neg_one_mul]
      rw [he] at h22
      linear_combination -(1 / 2 : ℂ) * h22
    have h12 := hB (QuaternionGroup.xa 0) e₁ e₂
    rw [hK₁, hK₂, map_neg] at h12
    have hz21 : B e₂ e₁ = -B e₁ e₂ := by linear_combination -h12
    apply LinearMap.ext
    intro p
    apply LinearMap.ext
    intro q
    rw [bilin_coordinates B p q, hz11, hz22, hz21]
    simp only [LinearMap.smul_apply, smul_eq_mul, deningerQ8TransitionSymplectic_apply, e₁, e₂]
    ring
  · intro hB g p q
    rw [hB]
    simp only [LinearMap.smul_apply, smul_eq_mul,
      deningerQ8Representation_preserves_symplectic]

/-- The invariant bilinear forms, as an actual subspace of all bilinear forms. -/
def q8InvariantBilinear : Submodule ℂ (LinearMap.BilinForm ℂ Q8Carrier) where
  carrier := {B | ∀ g : QuaternionGroup 2, ∀ p q : Q8Carrier,
    B (deningerQ8Representation g p) (deningerQ8Representation g q) = B p q}
  zero_mem' := by
    change ∀ g : QuaternionGroup 2, ∀ p q : Q8Carrier, (0 : LinearMap.BilinForm ℂ Q8Carrier)
      (deningerQ8Representation g p) (deningerQ8Representation g q) = 0
    intros
    rfl
  add_mem' hB hC := by
    intro g p q
    simp only [LinearMap.add_apply, hB g p q, hC g p q]
  smul_mem' c B hB := by
    intro g p q
    simp only [LinearMap.smul_apply, smul_eq_mul, hB g p q]

/-- Evaluation on the standard oriented pair identifies the invariant subspace with the scalar line. -/
def q8InvariantBilinearEquiv : q8InvariantBilinear ≃ₗ[ℂ] ℂ where
  toFun B := B.val e₁ e₂
  invFun c := ⟨c • deningerQ8TransitionSymplectic, by
    intro g p q
    simp only [LinearMap.smul_apply, smul_eq_mul, deningerQ8Representation_preserves_symplectic]⟩
  left_inv B := Subtype.ext ((q8_bilinear_invariant_iff B.val).mp B.property).symm
  right_inv c := by simp [e₁, e₂]
  map_add' B C := by simp
  map_smul' c B := by simp

/-- There is precisely one invariant bilinear degree of freedom on the quaternionic carrier. -/
theorem q8InvariantBilinear_finrank : Module.finrank ℂ q8InvariantBilinear = 1 := by
  rw [q8InvariantBilinearEquiv.finrank_eq]
  exact Module.finrank_self ℂ

/-- Quaternionic invariance leaves no nonzero symmetric bilinear form. -/
theorem q8_symmetric_bilinear_invariant_iff (B : LinearMap.BilinForm ℂ Q8Carrier) :
    (B ∈ q8InvariantBilinear ∧ B.IsSymm) ↔ B = 0 := by
  constructor
  · rintro ⟨hB, hs⟩
    have he := (q8_bilinear_invariant_iff B).mp hB
    have hc := hs.eq e₁ e₂
    rw [he] at hc
    simp [e₁, e₂] at hc
    have hz : B (1, 0) (0, 1) = 0 := by linear_combination (1 / 2 : ℂ) * hc
    rw [he, hz, zero_smul]
  · rintro rfl
    refine ⟨q8InvariantBilinear.zero_mem, ?_⟩
    exact ⟨fun _ _ => rfl⟩

#print axioms q8_bilinear_invariant_iff
#print axioms q8InvariantBilinear_finrank
#print axioms q8_symmetric_bilinear_invariant_iff

end GaloisForLFunctions.HTGeometry.GroupCharacter
