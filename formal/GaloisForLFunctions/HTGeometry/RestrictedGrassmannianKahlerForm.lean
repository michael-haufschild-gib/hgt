import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal

/-!
# The restricted Grassmannian and its determinant-line Kähler form

For a polarization `P₊` (an orthogonal projection) the restricted Grassmannian is the set of
orthogonal projections `P` with `P − P₊` Hilbert–Schmidt; re-centring at any of its points gives
the same set.  Tangent vectors `X` at `P` (`P X + X P = X`) are off-diagonal: `P X P = 0` and
`(1 − P) X (1 − P) = 0`, and a product of three of them has vanishing trace.  The determinant-line
curvature `Tr(P[X, Y])` is purely imaginary on self-adjoint Hilbert–Schmidt tangent vectors, and
`ω_det(X, Y) = Tr(P[X, Y]) / 2πi` is the real, antisymmetric Kähler form of the determinant line.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The restricted Grassmannian of the polarization `P₊`: orthogonal projections differing from
`P₊` by a Hilbert–Schmidt operator. -/
def restrictedGrassmannian (Pp : H →L[ℂ] H) : Set (H →L[ℂ] H) :=
  {P | IsStarProjection P ∧ IsHilbertSchmidt (P - Pp)}

theorem restrictedGrassmannian_recentre {Pp P : H →L[ℂ] H}
    (hP : P ∈ restrictedGrassmannian Pp) :
    restrictedGrassmannian P = restrictedGrassmannian Pp := by
  ext Q
  refine ⟨fun ⟨hQ, hQP⟩ => ⟨hQ, ?_⟩, fun ⟨hQ, hQP⟩ => ⟨hQ, ?_⟩⟩
  · simpa using hQP.add hP.2
  · simpa using hQP.sub hP.2

/-! ## Tangent vectors are off-diagonal -/

section Tangent

variable {R : Type*} [Ring R] {P X X₁ X₂ X₃ : R}

theorem tangent_mul_left (hX : P * X + X * P = X) : P * X = X * (1 - P) := by
  rw [mul_sub, mul_one]
  exact eq_sub_of_add_eq hX

theorem tangent_mul_right (hX : P * X + X * P = X) : X * P = (1 - P) * X := by
  rw [sub_mul, one_mul]
  exact eq_sub_of_add_eq' hX

theorem tangent_compress (hP : IsIdempotentElem P) (hX : P * X + X * P = X) :
    P * X * P = 0 := by
  rw [tangent_mul_left hX, mul_assoc, sub_mul, one_mul, hP.eq, sub_self, mul_zero]

theorem tangent_compress_compl (hP : IsIdempotentElem P) (hX : P * X + X * P = X) :
    (1 - P) * X * (1 - P) = 0 := by
  rw [← tangent_mul_right hX, mul_assoc, mul_sub, mul_one, hP.eq, sub_self, mul_zero]

/-- A product of three tangent vectors is again off-diagonal: `P (X₁X₂X₃) = (X₁X₂X₃)(1 − P)`. -/
theorem tangent_triple (hX₁ : P * X₁ + X₁ * P = X₁) (hX₂ : P * X₂ + X₂ * P = X₂)
    (hX₃ : P * X₃ + X₃ * P = X₃) : P * (X₁ * X₂ * X₃) = X₁ * X₂ * X₃ * (1 - P) := by
  have h₁ := tangent_mul_left hX₁
  have h₂ := tangent_mul_left hX₂
  have h₃ := tangent_mul_left hX₃
  calc P * (X₁ * X₂ * X₃) = P * X₁ * X₂ * X₃ := by noncomm_ring
    _ = X₁ * (X₂ - P * X₂) * X₃ := by rw [h₁]; noncomm_ring
    _ = X₁ * X₂ * X₃ - X₁ * (X₂ * (X₃ - P * X₃)) := by rw [h₂]; noncomm_ring
    _ = X₁ * X₂ * X₃ * (1 - P) := by rw [h₃]; noncomm_ring

end Tangent

/-! ## The determinant-line Kähler form -/

section KahlerForm

/-- The determinant-line curvature `Tr(P[X, Y])` on tangent vectors `X, Y`. -/
def detCurvature (P X Y : H →L[ℂ] H) : ℂ := opTrace (P * (X * Y - Y * X))

variable {P X Y : H →L[ℂ] H}

theorem commutator_mem_hsTraceIdeal (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    X * Y - Y * X ∈ hsTraceIdeal H :=
  sub_mem (comp_mem_hsTraceIdeal hX hY) (comp_mem_hsTraceIdeal hY hX)

/-- For self-adjoint data the curvature is purely imaginary. -/
theorem conj_detCurvature (hP : IsSelfAdjoint P) (hXs : IsSelfAdjoint X) (hYs : IsSelfAdjoint Y)
    (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    conj (detCurvature P X Y) = -detCurvature P X Y := by
  have hT := commutator_mem_hsTraceIdeal hX hY
  have hstar : adjoint (P * (X * Y - Y * X)) = -(X * Y - Y * X) * P := by
    rw [← star_eq_adjoint, star_mul, star_sub, star_mul, star_mul, hXs.star_eq, hYs.star_eq,
      hP.star_eq]
    noncomm_ring
  unfold detCurvature
  rw [← opTrace_adjoint, hstar, neg_mul, opTrace_neg']
  congr 1
  exact (opTrace_comp_comm_of_mem hT P).symm

/-- The determinant-line Kähler form `ω_det(X, Y) = Tr(P[X, Y]) / 2πi`, real-valued. -/
def detKahlerForm (P X Y : H →L[ℂ] H) : ℝ := (detCurvature P X Y).im / (2 * Real.pi)

theorem detCurvature_eq_two_pi_I_mul (hP : IsSelfAdjoint P) (hXs : IsSelfAdjoint X)
    (hYs : IsSelfAdjoint Y) (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    detCurvature P X Y = 2 * Real.pi * Complex.I * detKahlerForm P X Y := by
  have h := conj_detCurvature hP hXs hYs hX hY
  have hre : (detCurvature P X Y).re = 0 := by
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  have hz := Complex.re_add_im (detCurvature P X Y)
  rw [hre, Complex.ofReal_zero, zero_add] at hz
  conv_lhs => rw [← hz]
  unfold detKahlerForm
  push_cast
  field_simp

theorem detKahlerForm_antisymm (P X Y : H →L[ℂ] H) :
    detKahlerForm P Y X = -detKahlerForm P X Y := by
  unfold detKahlerForm detCurvature
  rw [show P * (Y * X - X * Y) = -(P * (X * Y - Y * X)) by noncomm_ring, opTrace_neg',
    Complex.neg_im, neg_div]

/-- The trace of a product of three tangent vectors at a projection vanishes. -/
theorem opTrace_tangent_triple (hP : IsIdempotentElem P) {X₁ X₂ X₃ : H →L[ℂ] H}
    (hX₁ : P * X₁ + X₁ * P = X₁) (hX₂ : P * X₂ + X₂ * P = X₂) (hX₃ : P * X₃ + X₃ * P = X₃)
    (h₁ : IsHilbertSchmidt X₁) (h₂ : IsHilbertSchmidt X₂) :
    opTrace (X₁ * X₂ * X₃) = 0 := by
  have hT : X₁ * X₂ * X₃ ∈ hsTraceIdeal H :=
    hsTraceIdeal_mul_right (mul_mem_hsTraceIdeal h₁ h₂) X₃
  have hPT := tangent_triple hX₁ hX₂ hX₃
  generalize X₁ * X₂ * X₃ = T at hT hPT ⊢
  -- `Tr(P T) = Tr(P T P) = 0` and `Tr((1 − P) T) = Tr((1 − P) T (1 − P)) = 0`
  have hPT' : (1 - P) * T = T * P := by
    rw [sub_mul, one_mul, hPT, mul_sub, mul_one, sub_sub_cancel]
  have hA : opTrace (P * T) = 0 := by
    have hc := opTrace_mul_comm_of_mem (hsTraceIdeal_mul_left hT P) P
    rw [← mul_assoc, hP.eq, hPT, mul_assoc, sub_mul, one_mul, hP.eq, sub_self, mul_zero] at hc
    rw [hPT, hc]; simp [opTrace]
  have hB : opTrace ((1 - P) * T) = 0 := by
    have hc := opTrace_mul_comm_of_mem (hsTraceIdeal_mul_left hT (1 - P)) (1 - P)
    have hQ : (1 - P) * (1 - P) = 1 - P := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hP.eq, sub_self, sub_zero]
    rw [← mul_assoc, hQ, hPT', mul_assoc, mul_sub, mul_one, hP.eq, sub_self, mul_zero] at hc
    rw [hPT', hc]; simp [opTrace]
  have hsplit : T = P * T + (1 - P) * T := by noncomm_ring
  rw [hsplit, opTrace_add_of_mem (hsTraceIdeal_mul_left hT P)
    (hsTraceIdeal_mul_left hT (1 - P)), hA, hB, add_zero]

end KahlerForm

end

end GaloisForLFunctions.HTGeometry
