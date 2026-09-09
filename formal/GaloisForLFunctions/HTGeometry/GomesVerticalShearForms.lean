import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.Analysis.Complex.Basic

/-!
# Sesquilinear forms under vertical shear representations

The real-versus-complex representation distinction in Gomes, arXiv:2607.24901,
extends to arbitrary complex vector spaces. A nontrivial complex vertical shear
preserves precisely the sesquilinear forms pulled back from its residual quotient,
with unique descent. A real affine orbit permits an antisymmetric mixed term but
still forces its displacement direction to be null. No finite-dimensional,
Hermitian, or positivity assumption is used in the classifications.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A complex affine line has constant sesquilinear square exactly when its direction
annihilates itself and both mixed pairings. Hermitian symmetry is unnecessary. -/
theorem sesq_affine_line_constant_iff
    (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (e w : V) :
    (∀ z : ℂ, B (w + z • e) (w + z • e) = B w w) ↔
      B e e = 0 ∧ B e w = 0 ∧ B w e = 0 := by
  have hexp (z : ℂ) : B (w + z • e) (w + z • e) =
      B w w + z * B w e + star z * B e w + star z * z * B e e := by
    simp only [map_add,map_smulₛₗ,LinearMap.add_apply,LinearMap.smul_apply,RingHom.id_apply,
      starRingEnd_apply,smul_eq_mul]
    ring
  constructor
  · intro h
    have h1 := h 1
    have hm := h (-1)
    have hi := h Complex.I
    rw [hexp] at h1 hm hi
    simp only [star_one,one_mul,star_neg,neg_mul,mul_neg,neg_neg] at h1 hm
    simp only [Complex.star_def,Complex.conj_I,neg_mul,Complex.I_mul_I] at hi
    have he : B e e = 0 := by linear_combination (h1 + hm) / 2
    have hs : B w e + B e w = 0 := by linear_combination (h1 - hm) / 2
    have hd : -Complex.I * B e w + Complex.I * B w e = 0 := by
      simp only [he,mul_zero,neg_zero,add_zero] at hi
      linear_combination hi
    refine ⟨he,?_,?_⟩
    · linear_combination hs / 2 + Complex.I / 2 * hd +
        (B e w - B w e) / 2 * Complex.I_sq
    · linear_combination hs / 2 - Complex.I / 2 * hd +
        (B w e - B e w) / 2 * Complex.I_sq
  · rintro ⟨he,hew,hwe⟩ z
    rw [hexp,he,hew,hwe]
    ring

/-- The universal vertical shear over a complex vector space. -/
def gomesVerticalShear (ell : V →ₗ[ℂ] ℂ) (z : ℂ) (x : V × ℂ) : V × ℂ :=
  (x.1,x.2 + z * ell x.1)

/-- Every vertical shear is an affine displacement along the distinguished final coordinate. -/
theorem gomesVerticalShear_displacement (ell : V →ₗ[ℂ] ℂ) (z : ℂ) (x : V × ℂ) :
    gomesVerticalShear ell z x = x + (z * ell x.1) • ((0 : V),(1 : ℂ)) := by
  ext <;> simp [gomesVerticalShear]

/-- The complete invariant-form classification for arbitrary vertical shear spaces: a zero
functional acts trivially; otherwise every invariant form kills the marked direction in both slots. -/
theorem gomesVerticalShear_sesq_invariants (ell : V →ₗ[ℂ] ℂ)
    (B : (V × ℂ) →ₛₗ[starRingEnd ℂ] (V × ℂ) →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : V × ℂ,
      B (gomesVerticalShear ell z x) (gomesVerticalShear ell z y) = B x y) ↔
      ell = 0 ∨ ∀ x : V × ℂ, B (0,1) x = 0 ∧ B x (0,1) = 0 := by
  constructor
  · intro h
    by_cases hell : ell = 0
    · exact Or.inl hell
    right
    obtain ⟨v,hv⟩ : ∃ v : V, ell v ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hell
      exact LinearMap.ext hn
    let w : V × ℂ := ((ell v)⁻¹ • v,0)
    have hw : ell w.1 = 1 := by simp [w,map_smul,smul_eq_mul,hv]
    have hline : ∀ z : ℂ, B (w + z • ((0 : V),1)) (w + z • ((0 : V),1)) = B w w := by
      intro z
      simpa only [gomesVerticalShear_displacement,hw,mul_one] using h z w w
    obtain ⟨hee,hew,hwe⟩ := (sesq_affine_line_constant_iff B ((0 : V),1) w).mp hline
    intro x
    have hl := h 1 w x
    have hr := h 1 x w
    simp only [gomesVerticalShear_displacement,hw,mul_one,one_mul,one_smul,
      map_add,map_smulₛₗ,LinearMap.add_apply,LinearMap.smul_apply,RingHom.id_apply,starRingEnd_apply,
      smul_eq_mul,hee,hew,hwe,mul_zero,add_zero] at hl hr
    constructor
    · linear_combination hl
    · linear_combination hr
  · rintro (rfl | hb) z x y
    · simp [gomesVerticalShear]
    · simp only [gomesVerticalShear_displacement,map_add,map_smulₛₗ,
        LinearMap.add_apply,LinearMap.smul_apply,RingHom.id_apply,starRingEnd_apply,smul_eq_mul,
        (hb y).1,(hb x).2,(hb (0,1)).1,mul_zero,add_zero]

/-- Invariant forms for a nonzero vertical shear are exactly forms depending only on the
residual coordinates; the erased coordinate contributes no mixed or quadratic term. -/
theorem gomesVerticalShear_residual_forms (ell : V →ₗ[ℂ] ℂ)
    (B : (V × ℂ) →ₛₗ[starRingEnd ℂ] (V × ℂ) →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : V × ℂ,
      B (gomesVerticalShear ell z x) (gomesVerticalShear ell z y) = B x y) ↔
      ell = 0 ∨ ∀ x y : V × ℂ, B x y = B (x.1,0) (y.1,0) := by
  rw [gomesVerticalShear_sesq_invariants]
  apply or_congr_right
  constructor
  · intro h x y
    have hx : x = (x.1,0) + x.2 • ((0 : V),1) := by ext <;> simp
    have hy : y = (y.1,0) + y.2 • ((0 : V),1) := by ext <;> simp
    conv_lhs => rw [hx,hy]
    simp only [map_add,map_smulₛₗ,LinearMap.add_apply,LinearMap.smul_apply,RingHom.id_apply,
      starRingEnd_apply,smul_eq_mul,(h (x.1,0)).2,(h (y.1,0)).1,
      (h (0,1)).1,mul_zero,add_zero]
  · intro h x
    constructor
    · rw [h (0,1) x]
      change B 0 (x.1,0) = 0
      simp
    · rw [h x (0,1)]
      change B (x.1,0) 0 = 0
      simp

/-- Restriction of a product-space form to its residual coordinate. -/
def gomesResidualSesqForm
    (B : (V × ℂ) →ₛₗ[starRingEnd ℂ] (V × ℂ) →ₗ[ℂ] ℂ) :
    V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ :=
  (B.comp (LinearMap.inl ℂ V ℂ)).compl₂ (LinearMap.inl ℂ V ℂ)

/-- Pullback of a residual form along the quotient that forgets the marked coordinate. -/
def gomesResidualSesqPullback (C : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) :
    (V × ℂ) →ₛₗ[starRingEnd ℂ] (V × ℂ) →ₗ[ℂ] ℂ :=
  (C.comp (LinearMap.fst ℂ V ℂ)).compl₂ (LinearMap.fst ℂ V ℂ)

/-- Restriction recovers every residual form exactly. -/
theorem gomesResidualSesq_restrict_pullback
    (C : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) :
    gomesResidualSesqForm (gomesResidualSesqPullback C) = C := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- Nontrivial vertical-shear invariant forms are precisely unique pullbacks of arbitrary
sesquilinear forms on the residual quotient. -/
theorem gomesVerticalShear_unique_residual_form (ell : V →ₗ[ℂ] ℂ)
    (B : (V × ℂ) →ₛₗ[starRingEnd ℂ] (V × ℂ) →ₗ[ℂ] ℂ) :
    (∀ z : ℂ, ∀ x y : V × ℂ,
      B (gomesVerticalShear ell z x) (gomesVerticalShear ell z y) = B x y) ↔
      ell = 0 ∨ ∃! C : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ,
        B = gomesResidualSesqPullback C := by
  rw [gomesVerticalShear_residual_forms]
  apply or_congr_right
  constructor
  · intro h
    refine ⟨gomesResidualSesqForm B,?_,?_⟩
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact h x y
    · intro C hc
      rw [hc,gomesResidualSesq_restrict_pullback]
  · rintro ⟨C,rfl,_⟩ x y
    rfl

/-- A real affine line can retain an antisymmetric mixed pairing; its quadratic direction
must still be null. This is the sharp real/complex distinction. -/
theorem sesq_real_affine_line_constant_iff
    (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (e w : V) :
    (∀ t : ℝ, B (w + (t : ℂ) • e) (w + (t : ℂ) • e) = B w w) ↔
      B e e = 0 ∧ B e w + B w e = 0 := by
  have hexp (t : ℝ) : B (w + (t : ℂ) • e) (w + (t : ℂ) • e) =
      B w w + (t : ℂ) * (B e w + B w e) + (t : ℂ)^2 * B e e := by
    simp only [map_add,map_smulₛₗ,LinearMap.add_apply,LinearMap.smul_apply,
      RingHom.id_apply,Complex.conj_ofReal,smul_eq_mul]
    ring
  constructor
  · intro h
    have h1 := h 1
    have hm := h (-1)
    rw [hexp] at h1 hm
    simp only [Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_mul,one_pow,neg_one_sq] at h1 hm
    constructor
    · linear_combination (h1 + hm) / 2
    · linear_combination (h1 - hm) / 2
  · rintro ⟨he,hm⟩ t
    rw [hexp,he,hm,mul_zero,mul_zero,add_zero,add_zero]

end GaloisForLFunctions.HTGeometry
