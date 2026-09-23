import GaloisForLFunctions.HTGeometry.PolyatomicConservation
import GaloisForLFunctions.HTGeometry.TransportMomentKreinWeld
import GaloisForLFunctions.HTGeometry.FinitePauliDepolarizing
import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithDifferentialField

/-!
# Conservation-and-exchange correction in existing operator and transport models

The mechanism of arXiv:2608.29825, Section 4.2, transfers to three existing
corpus constructions: the two-component transport jet, the projective
Wigner--Smith trace quotient, and the full-Pauli conjugation average.
These are applications of the invariant/exchange decomposition; the Pauli
average is not identified with the SO(3) Boltzmann integral.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- On equal-weight conserved channels, the Krein exchange form becomes a negative Gram. -/
theorem collisionProject_exchangePair (x y : ℝ × ℝ) :
    HTGeometry.exchangePair (collisionConservationProject 1 x)
      (collisionConservationProject 1 y) =
      -(collisionExchange 1 x * collisionExchange 1 y) / 2 := by
  simp only [HTGeometry.exchangePair, collisionConservationProject]
  ring

/-- Conservation correction makes every instantaneous transport-jet self-pairing nonpositive. -/
theorem collisionProject_transportJet_nonpositive (i : ℕ) (t : ℝ) :
    HTGeometry.exchangePair
      (collisionConservationProject 1 (HTGeometry.transportDiracJet i t))
      (collisionConservationProject 1 (HTGeometry.transportDiracJet i t)) ≤ 0 := by
  rw [collisionProject_exchangePair]
  nlinarith [sq_nonneg (collisionExchange 1 (HTGeometry.transportDiracJet i t))]

/-- All corrected instantaneous transport jets occupy one exchange line: every two-by-two
exchange Gram determinant vanishes, even when the original jets were independent. -/
theorem collisionProject_transportJet_gram_det (i j : ℕ) (t : ℝ) :
    let u := collisionConservationProject 1 (HTGeometry.transportDiracJet i t)
    let v := collisionConservationProject 1 (HTGeometry.transportDiracJet j t)
    HTGeometry.exchangePair u u * HTGeometry.exchangePair v v -
      HTGeometry.exchangePair u v ^ (2 : ℕ) = 0 := by
  dsimp only
  rw [collisionProject_exchangePair, collisionProject_exchangePair,
    collisionProject_exchangePair]
  ring

/-- The retained transport energy never exceeds the existing positive Dirac majorant. -/
theorem collisionProject_transportJet_majorant (b : ℝ) (i : ℕ) (t : ℝ) :
    (collisionConservationProject b (HTGeometry.transportDiracJet i t)).1 ^ (2 : ℕ) +
      (collisionConservationProject b (HTGeometry.transportDiracJet i t)).2 ^ (2 : ℕ) ≤
      HTGeometry.transportDiracMajorant i t := by
  convert collisionConservationProject_contractive b (HTGeometry.transportDiracJet i t) using 1
  simp only [HTGeometry.transportDiracJet, HTGeometry.transportDiracMajorant,
    mul_pow, ← pow_mul]
  rw [show i * 2 = 2 * i by omega, show (i + 1) * 2 = 2 * i + 2 by omega]

/-- The existing projective matrix quotient is an exact conservation projector. -/
theorem matrixTracelessPartField_idempotent {n : ℕ}
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixTracelessPartField (matrixTracelessPartField X) = matrixTracelessPartField X := by
  rw [matrixTracelessPartField, matrixTracelessPartField_trace]
  simp

/-- Projective trace correction retains every commutator source exactly. -/
theorem matrixTracelessPartField_commutator {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixTracelessPartField (A * B - B * A) = A * B - B * A := by
  have ht : Matrix.trace (A * B - B * A) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]
  rw [matrixTracelessPartField, ht]
  simp

/-- Removing invariant scalar directions from both inputs preserves their exchange bracket. -/
theorem matrixTracelessPartField_bracket_preserved {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixTracelessPartField A * matrixTracelessPartField B -
      matrixTracelessPartField B * matrixTracelessPartField A = A * B - B * A := by
  simp only [matrixTracelessPartField, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, smul_smul]
  rw [mul_comm (-(A.trace / (n + 1 : ℂ))) (-(B.trace / (n + 1 : ℂ)))]
  abel

section Pauli
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Full-Pauli collision generator: normalized conjugation gain minus the original state. -/
def pauliCollisionGenerator
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :=
  ((4 : ℂ) ^ Fintype.card σ)⁻¹ •
    (∑ L : σ → Option (Fin 3), finitePauliMatrix L * X * finitePauliMatrix L) - X

/-- The whole microscopic Pauli conjugation sum reduces to trace equilibrium minus exchange. -/
theorem pauliCollisionGenerator_eq
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliCollisionGenerator X =
      (X.trace / (2 : ℂ) ^ Fintype.card σ) • 1 - X := by
  rw [pauliCollisionGenerator, sum_finitePauliMatrix_conj, smul_smul]
  congr 2
  have h2 : (2 : ℂ) ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (by norm_num)
  have hp : (4 : ℂ) ^ Fintype.card σ = ((2 : ℂ) ^ Fintype.card σ) ^ (2 : ℕ) := by
    rw [← pow_mul, mul_comm (Fintype.card σ) 2, pow_mul]
    congr 1
    ring
  rw [hp]
  field_simp

/-- The Pauli collision generator conserves trace for every operator, without a trace premise. -/
theorem pauliCollisionGenerator_trace
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (pauliCollisionGenerator X).trace = 0 := by
  rw [pauliCollisionGenerator_eq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  have hc : (Fintype.card (FiniteQubitConfiguration σ) : ℂ) =
      (2 : ℂ) ^ Fintype.card σ := by
    simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hc, smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num)), sub_self]

/-- Exact exchange spectrum: applying the generator twice is its negative. -/
theorem pauliCollisionGenerator_sq
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliCollisionGenerator (pauliCollisionGenerator X) = -pauliCollisionGenerator X := by
  rw [pauliCollisionGenerator_eq, pauliCollisionGenerator_trace]
  simp

/-- The fixed collision states are exactly scalar equilibrium matrices. -/
theorem pauliCollisionGenerator_zero_iff
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliCollisionGenerator X = 0 ↔
      X = (X.trace / (2 : ℂ) ^ Fintype.card σ) • 1 := by
  rw [pauliCollisionGenerator_eq, sub_eq_zero, eq_comm]

/-- Scalar changes of state affect only the conserved mode. -/
theorem pauliCollisionGenerator_add_scalar
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) (c : ℂ) :
    pauliCollisionGenerator (X + c • 1) = pauliCollisionGenerator X := by
  rw [pauliCollisionGenerator_eq, pauliCollisionGenerator_eq,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  have hc : (Fintype.card (FiniteQubitConfiguration σ) : ℂ) =
      (2 : ℂ) ^ Fintype.card σ := by
    simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hc, smul_eq_mul, add_div, mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num)), add_smul]
  abel

/-- Every double-commutator Casimir source already lies in the exchange eigenspace. -/
theorem pauliCollisionGenerator_casimir
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliCollisionGenerator
      (∑ L : σ → Option (Fin 3), pauliAd (finitePauliMatrix L)
        (pauliAd (finitePauliMatrix L) X)) =
      -(∑ L : σ → Option (Fin 3), pauliAd (finitePauliMatrix L)
        (pauliAd (finitePauliMatrix L) X)) := by
  have ht : (∑ L : σ → Option (Fin 3), pauliAd (finitePauliMatrix L)
      (pauliAd (finitePauliMatrix L) X)).trace = 0 := by
    rw [Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro L _
    rw [pauliAd, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [pauliCollisionGenerator_eq, ht]
  simp

end Pauli
end GaloisForLFunctions.HTGeometry
