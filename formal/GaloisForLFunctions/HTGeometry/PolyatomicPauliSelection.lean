import GaloisForLFunctions.HTGeometry.FinitePauliCharacterProjector
import GaloisForLFunctions.HTGeometry.PauliLabelAnticommute

/-!
# Wigner--Eckart factorization for the corpus's Pauli character sectors

The geometric/physical separation in arXiv:2608.29825, equations (18)--(20),
has an exact finite-character analogue. Averaging three Pauli characters
produces a sparse geometric tensor: an output grade survives precisely
when it is the product of the two input grades. Arbitrary spectator
indices and physical coefficients factor out unchanged. The proof uses
matrix conjugation and character orthogonality, without enumerating a
register or assuming the desired selection rule.

This is a finite Pauli-symmetry application, not the SO(3) 3-j formula.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Pauli conjugation characters multiply according to the actual matrix-product grade. -/
theorem finitePauliConjugationSign_optMulLabel
    (Q P S : σ → Option (Fin 3)) :
    finitePauliConjugationSign Q (optMulLabel P S) =
      finitePauliConjugationSign Q P * finitePauliConjugationSign Q S := by
  have hm : finitePauliMatrix Q * (finitePauliMatrix P * finitePauliMatrix S) *
      finitePauliMatrix Q =
      (finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix Q) *
      (finitePauliMatrix Q * finitePauliMatrix S * finitePauliMatrix Q) := by
    calc
      _ = finitePauliMatrix Q * finitePauliMatrix P *
          (finitePauliMatrix Q * finitePauliMatrix Q) *
          finitePauliMatrix S * finitePauliMatrix Q := by
        rw [finitePauliMatrix_mul_self]
        simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  rw [finitePauliMatrix_conj, finitePauliMatrix_conj] at hm
  rw [finitePauliMatrix_mul' P S] at hm
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    finitePauliMatrix_conj] at hm
  rw [finitePauliMatrix_mul' P S, smul_smul] at hm
  have hc := congrArg (fun M => Matrix.trace (finitePauliMatrix (optMulLabel P S) * M)) hm
  simp only [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_mul,
    ite_true, smul_eq_mul] at hc
  have hzero :
      (finitePauliConjugationSign Q (optMulLabel P S) -
        finitePauliConjugationSign Q P * finitePauliConjugationSign Q S) *
      (optPhaseProd P S * (2 : ℂ) ^ Fintype.card σ) = 0 := by
    linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right
    (mul_ne_zero (optPhaseProd_ne_zero P S) (pow_ne_zero _ (by norm_num))))

/-- The geometric three-character coupling tensor, independently of physical coefficients. -/
def pauliAngularCoupling (K P S : σ → Option (Fin 3)) : ℂ :=
  ((4 : ℂ) ^ Fintype.card σ)⁻¹ *
    ∑ Q : σ → Option (Fin 3),
      finitePauliConjugationSign Q K * finitePauliConjugationSign Q P *
        finitePauliConjugationSign Q S

/-- Exact selection rule: one output grade per input pair, for every register size. -/
theorem pauliAngularCoupling_selection (K P S : σ → Option (Fin 3)) :
    pauliAngularCoupling K P S = if K = optMulLabel P S then 1 else 0 := by
  unfold pauliAngularCoupling
  simp_rw [mul_assoc, ← finitePauliConjugationSign_optMulLabel _ P S]
  rw [finitePauliConjugationSign_orthogonality]
  by_cases h : K = optMulLabel P S
  · simp only [if_pos h]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  · simp only [if_neg h, mul_zero]

/-- Contracting the angular output axis is an exact single-grade extraction. -/
theorem pauliAngularCoupling_contract
    (P S : σ → Option (Fin 3)) (f : (σ → Option (Fin 3)) → ℂ) :
    ∑ K, pauliAngularCoupling K P S * f K = f (optMulLabel P S) := by
  simp_rw [pauliAngularCoupling_selection]
  simp

/-- Arbitrary internal multiplicity indices accompany a raw three-character tensor. -/
def pauliSpectatorTwirl {ι κ η : Type*} (B : ι → κ → η → ℂ)
    (K P S : σ → Option (Fin 3)) (i : ι) (j : κ) (k : η) : ℂ :=
  ((4 : ℂ) ^ Fintype.card σ)⁻¹ *
    ∑ Q : σ → Option (Fin 3),
      (finitePauliConjugationSign Q K * finitePauliConjugationSign Q P *
        finitePauliConjugationSign Q S) * B i j k

/-- Exact geometric/physical factorization survives every spectator multiplicity. -/
theorem pauliSpectatorTwirl_factorization {ι κ η : Type*} (B : ι → κ → η → ℂ)
    (K P S : σ → Option (Fin 3)) (i : ι) (j : κ) (k : η) :
    pauliSpectatorTwirl B K P S i j k = pauliAngularCoupling K P S * B i j k := by
  rw [pauliSpectatorTwirl, ← Finset.sum_mul, pauliAngularCoupling]
  ring

/-- The explicit averaged tensor is zero on forbidden transitions and unchanged otherwise. -/
theorem pauliSpectatorTwirl_selection {ι κ η : Type*} (B : ι → κ → η → ℂ)
    (K P S : σ → Option (Fin 3)) (i : ι) (j : κ) (k : η) :
    pauliSpectatorTwirl B K P S i j k =
      if K = optMulLabel P S then B i j k else 0 := by
  rw [pauliSpectatorTwirl_factorization, pauliAngularCoupling_selection]
  split <;> simp

/-- Gain and loss use one shared angular tensor; adding internal channels does not alter routing. -/
theorem pauliSpectatorTwirl_gain_loss {ι κ η : Type*} (gain loss : ι → κ → η → ℂ)
    (K P S : σ → Option (Fin 3)) (i : ι) (j : κ) (k : η) :
    pauliSpectatorTwirl (fun i j k => gain i j k - loss i j k) K P S i j k =
      pauliAngularCoupling K P S * (gain i j k - loss i j k) :=
  pauliSpectatorTwirl_factorization _ K P S i j k

/-- The existing Pauli commutator coefficients have precisely this Wigner--Eckart separation:
all angular zeros lie in the character tensor and the physical coefficient is a phase difference. -/
theorem trace_pauli_commutator_angular_factorization (K P S : σ → Option (Fin 3)) :
    Matrix.trace (finitePauliMatrix K *
      (finitePauliMatrix P * finitePauliMatrix S -
        finitePauliMatrix S * finitePauliMatrix P)) =
      (2 : ℂ) ^ Fintype.card σ * pauliAngularCoupling K P S *
        (optPhaseProd P S - optPhaseProd S P) := by
  rw [trace_pauli_commutator, pauliAngularCoupling_selection]
  split <;> ring

end GaloisForLFunctions.HTGeometry
