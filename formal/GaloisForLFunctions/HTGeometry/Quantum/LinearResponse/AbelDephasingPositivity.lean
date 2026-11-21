import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingChannel
import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Complete positivity and the choice of center

The zero-centered Abel response is positive in every ancilla dimension.
At a nonzero center the response to the identity has a nonreal scalar
factor, which obstructs even ordinary positivity.
-/

open Matrix Set
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

private theorem dampedGapResponse_zero_eq_unitary (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    hamiltonianDampedGapResponse hH 0 ε X =
      (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        abelEnergyChannel ε hH.eigenvalues (hamiltonianEnergyCoordinates hH X) *
        star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  have hh := congrArg (fun Z => (hamiltonianEnergyCoordinates hH).symm Z)
    (energyCoordinates_dampedGapResponse_zero_eq_abelEnergyChannel hH ε X)
  rw [StarAlgEquiv.symm_apply_apply] at hh
  exact hh

theorem hamiltonianDampedGapResponse_zero_posSemidef (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosSemidef) :
    (hamiltonianDampedGapResponse hH 0 ε X).PosSemidef := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hC : (hamiltonianEnergyCoordinates hH X).PosSemidef := by
    change (star U * X * U).PosSemidef
    rw [Matrix.star_eq_conjTranspose]
    exact hX.conjTranspose_mul_mul_same U
  rw [dampedGapResponse_zero_eq_unitary, Matrix.star_eq_conjTranspose]
  exact (abelEnergyChannel_posSemidef ε hH.eigenvalues hC).mul_mul_conjTranspose_same U

private theorem amplify_abelEnergyChannel_posSemidef {κ : Type*} [Fintype κ]
    (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ) {X : Matrix (Fin n × κ) (Fin n × κ) ℂ}
    (hX : X.PosSemidef) : (amplify (abelEnergyChannel ε E) κ X).PosSemidef := by
  change (((abelEnergySymbol ε E).submatrix Prod.fst Prod.fst) ⊙ X).PosSemidef
  exact ((abelEnergySymbol_posSemidef ε E).submatrix Prod.fst).hadamard hX

/-- Complete positivity in the physical basis, using block amplification
on an arbitrary finite ancilla. -/
theorem amplify_hamiltonianDampedGapResponse_zero_posSemidef {κ : Type*}
    [Fintype κ] [DecidableEq κ] (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    {X : Matrix (Fin n × κ) (Fin n × κ) ℂ} (hX : X.PosSemidef) :
    (amplify (hamiltonianDampedGapResponse hH 0 ε) κ X).PosSemidef := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have he : amplify (hamiltonianDampedGapResponse hH 0 ε) κ X =
      amplify (fun Y => U * Y * star U) κ
        (amplify (abelEnergyChannel ε hH.eigenvalues) κ
          (amplify (fun Y => star U * Y * star (star U)) κ X)) := by
    ext p q
    simp only [amplify_apply, dampedGapResponse_zero_eq_unitary, star_star]
    rfl
  rw [he, amplify_conj, amplify_conj,
    Matrix.star_eq_conjTranspose (U ⊗ₖ (1 : Matrix κ κ ℂ)),
    Matrix.star_eq_conjTranspose (star U ⊗ₖ (1 : Matrix κ κ ℂ))]
  exact (amplify_abelEnergyChannel_posSemidef ε hH.eigenvalues
    (hX.mul_mul_conjTranspose_same _)).mul_mul_conjTranspose_same _

/-- In positive dimension, positivity of the damped filter holds
exactly at frequency zero. -/
theorem hamiltonianDampedGapResponse_positivity_iff {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    (∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      X.PosSemidef → (hamiltonianDampedGapResponse hH μ ε X).PosSemidef) ↔ μ = 0 := by
  constructor
  · intro hp
    have hh := (hp 1 Matrix.PosSemidef.one).isHermitian.apply 0 0
    simp only [hamiltonianDampedGapResponse_one_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at hh
    have him := congrArg Complex.im hh
    rw [Complex.star_def, Complex.conj_im] at him
    have hz : (abelCoherence ε (-μ)).im = 0 := by linarith only [him]
    rw [abelCoherence_im, neg_eq_zero] at hz
    have hε : 0 < (ε : ℝ) := ε.2
    have hd : (ε : ℝ) ^ 2 + (-μ) ^ 2 ≠ 0 :=
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε.ne') (sq_nonneg _)).ne'
    have hprod := (div_eq_zero_iff.mp hz).resolve_right hd
    exact neg_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hε.ne')
  · rintro rfl X hX
    exact hamiltonianDampedGapResponse_zero_posSemidef hH ε hX

#print axioms amplify_hamiltonianDampedGapResponse_zero_posSemidef
#print axioms hamiltonianDampedGapResponse_positivity_iff

end

end GaloisForLFunctions.HTGeometry
