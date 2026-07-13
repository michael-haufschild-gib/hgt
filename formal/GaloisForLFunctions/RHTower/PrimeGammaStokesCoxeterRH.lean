import GaloisForLFunctions.RHTower.ArakelovW
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Prime--Gamma Stokes/Seifert Coxeter route to RH

For an invertible Seifert matrix `S`, its Coxeter transform

`C = -S⁻¹ Sᵀ`

preserves the symmetrized form `S + Sᵀ`.  If that form is positive definite, the usual
positive-form conjugation turns `C` into a unitary operator, so every Coxeter eigenvalue lies on
the unit circle.  The matrix preservation identity and the unitary eigenvalue lemma are proved
here without an RH hypothesis.

The RH-facing predicate isolates the missing source comparison: a prime--Gamma Stokes category
would have to realize the Arakelov coordinate `1 - rho⁻¹` of every right-half Xi zero as such a
unitary Coxeter eigenvalue.  The final equivalence is also a circularity audit: pointwise unitary
spectral data indexed only after selecting Xi zeros is exactly RH, so the data must instead come
from a determinant comparison constructed before the divisor is read.
-/

namespace GaloisForLFunctions

noncomputable section

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coxeter transformation attached to an invertible Seifert matrix. -/
def coxeterTransform (S : Matrix n n ℂ) : Matrix n n ℂ :=
  -(S⁻¹ * S.transpose)

/-- Symmetrized Seifert form. -/
def seifertSymmetrization (S : Matrix n n ℂ) : Matrix n n ℂ :=
  S + S.transpose

theorem coxeterTransform_transpose (S : Matrix n n ℂ) :
    (coxeterTransform S).transpose = -(S * (S.transpose)⁻¹) := by
  simp [coxeterTransform, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]

/-- **Coxeter--Seifert preservation law.**  The Coxeter transform preserves the symmetrized
Seifert form exactly.  Positivity is a separate source property of that form. -/
theorem coxeterTransform_preserves_symmetrization (S : Matrix n n ℂ)
    (hS : IsUnit S.det) :
    (coxeterTransform S).transpose * seifertSymmetrization S * coxeterTransform S =
      seifertSymmetrization S := by
  rw [coxeterTransform_transpose]
  simp only [coxeterTransform, seifertSymmetrization]
  simp only [neg_mul, mul_neg, neg_neg]
  have hST : IsUnit S.transpose.det := by simpa using hS
  calc
    S * S.transpose⁻¹ * (S + S.transpose) * (S⁻¹ * S.transpose) =
        S * S.transpose⁻¹ * (S * S⁻¹) * S.transpose +
          S * (S.transpose⁻¹ * S.transpose) * S⁻¹ * S.transpose := by
            noncomm_ring
    _ = S * S.transpose⁻¹ * 1 * S.transpose + S * 1 * S⁻¹ * S.transpose := by
      rw [Matrix.mul_nonsing_inv _ hS, Matrix.nonsing_inv_mul _ hST]
    _ = S + S.transpose := by
      simp only [Matrix.mul_one]
      rw [Matrix.mul_assoc S S.transpose⁻¹ S.transpose,
        Matrix.nonsing_inv_mul _ hST, Matrix.mul_nonsing_inv _ hS]
      simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An eigenvalue of a norm-preserving complex linear operator has unit norm. -/
theorem norm_eigenvalue_eq_one_of_norm_preserving
    (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ = ‖x‖)
    {v : E} (hv : v ≠ 0) {w : ℂ} (heig : T v = w • v) :
    ‖w‖ = 1 := by
  have hnormv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := hT v
  rw [heig, norm_smul] at h
  nlinarith

end


end GaloisForLFunctions

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- A finite unitary spectral packet carrying `w` as an eigenvalue.  A positive finite Coxeter
matrix supplies such a packet after conjugating its positive form to the standard norm.  A global
Xi realization is expected to be an infinite/regularized limit rather than one finite matrix. -/
structure FiniteUnitaryEigenDatum (w : ℂ) where
  n : ℕ
  operator : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)
  eigenvector : Fin n → ℂ
  eigenvector_ne_zero : eigenvector ≠ 0
  norm_preserving : ∀ x, ‖operator x‖ = ‖x‖
  eigenvector_eq : operator eigenvector = w • eigenvector

/-- The finite unitary eigenpacket is exactly a unit-circle certificate. -/
theorem finiteUnitaryEigenDatum_iff_norm_eq_one (w : ℂ) :
    Nonempty (FiniteUnitaryEigenDatum w) ↔ ‖w‖ = 1 := by
  constructor
  · rintro ⟨h⟩
    exact norm_eigenvalue_eq_one_of_norm_preserving h.operator h.norm_preserving
      h.eigenvector_ne_zero h.eigenvector_eq
  · intro hw
    let v : Fin 1 → ℂ := fun _ => 1
    have hv : v ≠ 0 := by
      intro h
      have := congrFun h 0
      norm_num [v] at this
    refine ⟨⟨1, w • LinearMap.id, v, hv, ?_, ?_⟩⟩
    · intro x
      rw [LinearMap.smul_apply, LinearMap.id_apply, norm_smul, hw, one_mul]
    · simp

/-- The RH-facing Coxeter spectral interface.  The open source theorem must construct this from
the completed prime--Gamma Stokes/Seifert category before selecting the Xi divisor. -/
def XiArakelovUnitarySpectralData : Prop :=
  ∀ rho : ℂ, rho ∈ rightHalf → xi rho = 0 →
    Nonempty (FiniteUnitaryEigenDatum (arakelovW rho))

/-- Unit-circle Coxeter spectral data at every hypothetical right-half zero forces RH. -/
theorem riemannHypothesis_of_xiArakelovUnitarySpectralData
    (h : XiArakelovUnitarySpectralData) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrho0 : rho ≠ 0 := by
    intro hz
    subst rho
    have hpos := Set.mem_setOf.mp hrho
    norm_num at hpos
  have hnorm : ‖arakelovW rho‖ = 1 :=
    (finiteUnitaryEigenDatum_iff_norm_eq_one _).mp (h rho hrho hzero)
  have hline := (arakelovW_norm_one_iff_critical rho hrho0).mp hnorm
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hline

/-- **Circularity audit.**  Bare zero-indexed unitary packets are equivalent to RH.  A viable
Coxeter route must therefore supply one global source determinant and its positive Seifert form,
not manufacture a packet after a zero has been selected. -/
theorem xiArakelovUnitarySpectralData_iff_riemannHypothesis :
    XiArakelovUnitarySpectralData ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiArakelovUnitarySpectralData
  · intro hRH rho hrho hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH rho hrho hzero).elim

end


end RHTower
