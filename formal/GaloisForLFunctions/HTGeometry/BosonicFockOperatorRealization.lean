import GaloisForLFunctions.HTGeometry.BosonicFockDiagonalModel
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaSharpness
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaValues

/-!
# The second quantization as an operator on the occupation Hilbert space

A strict contraction `p` on the one-particle index gives a bounded operator on the square-summable
occupation space `ℓ²(ι →₀ ℕ)`: multiplication by the occupation monomials.  Every occupation vector
is an eigenvector, its eigenvalue is the occupation monomial and is recovered from the operator as a
diagonal matrix element, the eigenvalues are multiplicative in the occupation, and the vacuum is a
unit eigenvector with eigenvalue one, so the operator norm is exactly one.

The quantities of the diagonal model are then read off the operator rather than posited: the
singular value at an occupation is the norm of the image of that occupation vector and the square
root of the corresponding diagonal element of the modulus square `Γ* Γ`; Schatten membership is
summability of those norms; and at exponent two it is the coordinate-free Hilbert–Schmidt property,
which holds exactly when the one-particle contraction is square-summable.  Finally the regularized
determinant of the model is the primary-factor product over the operator's own diagonal elements.
-/

open scoped ENNReal InnerProductSpace BigOperators NNReal

noncomputable section

namespace HTGeometry

variable {ι : Type*} [DecidableEq ι]

/-- The occupation Hilbert space: square-summable families indexed by occupations. -/
abbrev BosonicFock (ι : Type*) [DecidableEq ι] := IndexedEllTwo (ι →₀ ℕ)

/-- The occupation vectors, as a Hilbert basis of the occupation Hilbert space. -/
def occupationBasis (ι : Type*) [DecidableEq ι] :
    HilbertBasis (ι →₀ ℕ) ℂ (BosonicFock ι) :=
  ellTwoCoordinateBasis (ι →₀ ℕ)

omit [DecidableEq ι] in
theorem norm_bosonicEigenvalue_le_one (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) (ν : ι →₀ ℕ) :
    ‖bosonicEigenvalue p ν‖ ≤ 1 :=
  norm_nomeMonomial_le_one p hp_lt ν

/-- **The multiplicative second quantization, as a bounded operator on the occupation Hilbert
space.**  It is multiplication by the occupation monomials of the one-particle contraction. -/
def bosonicSecondQuantization (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    BosonicFock ι →L[ℂ] BosonicFock ι :=
  ellTwoDiagonal (bosonicEigenvalue p) (norm_bosonicEigenvalue_le_one p hp_lt)

theorem bosonicSecondQuantization_eq (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    bosonicSecondQuantization p hp_lt
      = ellTwoDiagonal (bosonicEigenvalue p) (norm_bosonicEigenvalue_le_one p hp_lt) := rfl

/-- **Every occupation vector is an eigenvector**, with the occupation monomial as eigenvalue. -/
theorem bosonicSecondQuantization_occupationBasis (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (ν : ι →₀ ℕ) :
    bosonicSecondQuantization p hp_lt (occupationBasis ι ν)
      = bosonicEigenvalue p ν • occupationBasis ι ν :=
  ellTwoDiagonal_coordinateBasis _ _ ν

/-- **The eigenvalue is a diagonal matrix element.**  Each occupation monomial is recovered from the
operator by pairing against the corresponding occupation vector. -/
theorem inner_occupationBasis_bosonicSecondQuantization (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (ν : ι →₀ ℕ) :
    ⟪occupationBasis ι ν, bosonicSecondQuantization p hp_lt (occupationBasis ι ν)⟫_ℂ
      = bosonicEigenvalue p ν :=
  inner_coordinateBasis_ellTwoDiagonal _ _ ν

/-- The second quantization is a contraction. -/
theorem norm_bosonicSecondQuantization_le_one (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    ‖bosonicSecondQuantization p hp_lt‖ ≤ 1 :=
  norm_ellTwoDiagonal_le _ _ zero_le_one

/-- The vacuum is a unit eigenvector with eigenvalue one. -/
theorem bosonicSecondQuantization_vacuum (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    bosonicSecondQuantization p hp_lt (occupationBasis ι 0) = occupationBasis ι 0 := by
  rw [bosonicSecondQuantization_occupationBasis]
  simp only [bosonicEigenvalue, nomeMonomial_zero, one_smul]

/-- **The second quantization has operator norm exactly one**, attained on the vacuum. -/
theorem norm_bosonicSecondQuantization_eq_one (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    ‖bosonicSecondQuantization p hp_lt‖ = 1 := by
  refine le_antisymm (norm_bosonicSecondQuantization_le_one p hp_lt) ?_
  have h := le_norm_ellTwoDiagonal (bosonicEigenvalue p)
    (norm_bosonicEigenvalue_le_one p hp_lt) (0 : ι →₀ ℕ)
  rw [bosonicSecondQuantization_eq]
  simpa [bosonicEigenvalue] using h

/-- The one-particle sector reproduces the one-particle contraction: the eigenvalue at a single
excitation of mode `a` is `p a`. -/
theorem bosonicEigenvalue_single (p : ι → ℂ) (a : ι) :
    bosonicEigenvalue p (Finsupp.single a 1) = p a :=
  nomeMonomial_single p a

omit [DecidableEq ι] in
/-- **The eigenvalues are multiplicative in the occupation.**  This is the second-quantization law:
superposing occupations multiplies eigenvalues. -/
theorem bosonicEigenvalue_add (p : ι → ℂ) (ν μ : ι →₀ ℕ) :
    bosonicEigenvalue p (ν + μ) = bosonicEigenvalue p ν * bosonicEigenvalue p μ := by
  simp only [bosonicEigenvalue, nomeMonomial]
  exact Finsupp.prod_add_index' (fun a => pow_zero (p a)) (fun a m n => pow_add (p a) m n)

/-! ## The model's quantities, read off the operator -/

/-- **The singular value is the norm of the image of the occupation vector.** -/
theorem bosonicSingularValue_eq_norm_apply (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) (ν : ι →₀ ℕ) :
    bosonicSingularValue p ν
      = ‖bosonicSecondQuantization p hp_lt (occupationBasis ι ν)‖ :=
  (norm_ellTwoDiagonal_coordinateBasis _ _ ν).symm

/-- **The singular value squared is the diagonal element of the modulus square `Γ* Γ`.** -/
theorem inner_occupationBasis_adjoint_comp_self (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (ν : ι →₀ ℕ) :
    ⟪occupationBasis ι ν,
        (ContinuousLinearMap.adjoint (bosonicSecondQuantization p hp_lt) ∘L
          bosonicSecondQuantization p hp_lt) (occupationBasis ι ν)⟫_ℂ
      = ((bosonicSingularValue p ν ^ 2 : ℝ) : ℂ) :=
  inner_coordinateBasis_adjoint_comp_self_ellTwoDiagonal _ _ ν

/-- **Schatten membership is summability of the operator's occupation norms.** -/
theorem bosonicSchatten_iff_summable_apply (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) (σ : ℝ) :
    BosonicSchatten p σ
      ↔ Summable (fun ν : ι →₀ ℕ =>
          ‖bosonicSecondQuantization p hp_lt (occupationBasis ι ν)‖ ^ σ) :=
  summable_congr fun ν => by rw [bosonicSingularValue_eq_norm_apply p hp_lt ν]

/-- **The second quantization is Hilbert–Schmidt exactly when the one-particle contraction is
square-summable.**  The Hilbert–Schmidt property is coordinate-free, so this is a statement about
the operator, not about the occupation basis. -/
theorem isHilbertSchmidt_bosonicSecondQuantization_iff (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    ContinuousLinearMap.IsHilbertSchmidt (bosonicSecondQuantization p hp_lt)
      ↔ Summable (fun a => ‖p a‖ ^ 2) := by
  have hcast : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x _
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [bosonicSecondQuantization_eq, isHilbertSchmidt_ellTwoDiagonal_iff]
  have hmodel := bosonicSchatten_iff_oneParticleSchatten p hp_lt (σ := 2) (by norm_num)
  have hleft : Summable (fun ν : ι →₀ ℕ => ‖bosonicEigenvalue p ν‖ ^ 2) ↔ BosonicSchatten p 2 :=
    summable_congr fun ν => (hcast _ (norm_nonneg _)).symm
  have hright : OneParticleSchatten p 2 ↔ Summable (fun a => ‖p a‖ ^ 2) :=
    summable_congr fun a => hcast _ (norm_nonneg _)
  exact hleft.trans (hmodel.trans hright)

/-- **The Hilbert–Schmidt norm is the occupation mass at exponent two.** -/
theorem hsNormSq_bosonicSecondQuantization (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ 2)) :
    ContinuousLinearMap.hsNormSq (bosonicSecondQuantization p hp_lt)
      = ∑' ν : ι →₀ ℕ, ‖nomeMonomial p ν‖ ^ 2 :=
  hsNormSq_ellTwoDiagonal _ _
    ((isHilbertSchmidt_ellTwoDiagonal_iff _ _).mp
      ((isHilbertSchmidt_bosonicSecondQuantization_iff p hp_lt).mpr hsum))

/-- **The regularized determinant is built from the operator's own diagonal elements.**  The
order-`g+1` regularized determinant of `I - x Γ` is the primary-factor product over the diagonal
matrix elements of `Γ` in the occupation basis. -/
theorem regularizedFredholmDet_eq_tprod_inner (g : ℕ) (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (x : ℂ) :
    regularizedFredholmDet g p x
      = ∏' ν : ι →₀ ℕ, primaryFactor g
          (x * ⟪occupationBasis ι ν,
            bosonicSecondQuantization p hp_lt (occupationBasis ι ν)⟫_ℂ) :=
  tprod_congr fun ν => by
    rw [inner_occupationBasis_bosonicSecondQuantization]

end HTGeometry

end
