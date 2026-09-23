import GaloisForLFunctions.HTGeometry.PauliCommutator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact Pauli double-commutator evolution

Every finite Pauli string supplies an explicit dissipative semigroup. Its derivative is
the double-commutator master equation, its trace is conserved, and its forward evolution
preserves the constructed positive matrix cone.

Source: Singh, arXiv:2609.10571, section 6.4, equation (43).
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
local notation "M" => Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ

def pauliConjugate (P : σ → Option (Fin 3)) (X : M) : M :=
  finitePauliMatrix P * X * finitePauliMatrix P

theorem pauliConjugate_involutive (P : σ → Option (Fin 3)) (X : M) :
    pauliConjugate P (pauliConjugate P X) = X := by
  unfold pauliConjugate
  calc
    _ = (finitePauliMatrix P * finitePauliMatrix P) * X *
        (finitePauliMatrix P * finitePauliMatrix P) := by noncomm_ring
    _ = X := by rw [finitePauliMatrix_mul_self, one_mul, mul_one]

theorem pauliConjugate_add (P : σ → Option (Fin 3)) (X Y : M) :
    pauliConjugate P (X+Y) = pauliConjugate P X + pauliConjugate P Y := by
  simp [pauliConjugate, mul_add, add_mul]

theorem pauliConjugate_sub (P : σ → Option (Fin 3)) (X Y : M) :
    pauliConjugate P (X-Y) = pauliConjugate P X - pauliConjugate P Y := by
  simp [pauliConjugate, mul_sub, sub_mul]

theorem pauliConjugate_smul (P : σ → Option (Fin 3)) (c : ℂ) (X : M) :
    pauliConjugate P (c • X) = c • pauliConjugate P X := by
  simp [pauliConjugate]

def pauliStaticPart (P : σ → Option (Fin 3)) (X : M) : M :=
  (1/2 : ℂ) • (X + pauliConjugate P X)

theorem pauliConjugate_static (P : σ → Option (Fin 3)) (X : M) :
    pauliConjugate P (pauliStaticPart P X) = pauliStaticPart P X := by
  simp [pauliStaticPart, pauliConjugate_smul, pauliConjugate_add,
    pauliConjugate_involutive, add_comm]

theorem pauliStaticPart_idempotent (P : σ → Option (Fin 3)) (X : M) :
    pauliStaticPart P (pauliStaticPart P X) = pauliStaticPart P X := by
  rw [pauliStaticPart, pauliConjugate_static]
  module

def pauliCollapseEvolution (P : σ → Option (Fin 3)) (a : ℝ) (X : M) (t : ℝ) : M :=
  pauliStaticPart P X + (Real.exp (-4*a^(2 : ℕ)*t) : ℂ) • (X - pauliStaticPart P X)

theorem pauliCollapseEvolution_zero (P : σ → Option (Fin 3)) (a : ℝ) (X : M) :
    pauliCollapseEvolution P a X 0 = X := by
  simp [pauliCollapseEvolution]

theorem pauliStaticPart_evolution (P : σ → Option (Fin 3)) (a : ℝ) (X : M) (t : ℝ) :
    pauliStaticPart P (pauliCollapseEvolution P a X t) = pauliStaticPart P X := by
  simp only [pauliStaticPart, pauliCollapseEvolution, pauliConjugate_add,
    pauliConjugate_smul, pauliConjugate_sub, pauliConjugate_involutive]
  module

theorem pauliCollapseEvolution_semigroup (P : σ → Option (Fin 3)) (a : ℝ)
    (X : M) (s t : ℝ) :
    pauliCollapseEvolution P a (pauliCollapseEvolution P a X s) t =
      pauliCollapseEvolution P a X (s+t) := by
  unfold pauliCollapseEvolution at *
  rw [show pauliStaticPart P
      (pauliStaticPart P X + (Real.exp (-4*a^(2 : ℕ)*s) : ℂ) • (X - pauliStaticPart P X)) =
      pauliStaticPart P X from pauliStaticPart_evolution P a X s]
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  module

theorem pauli_doubleCommutator (P : σ → Option (Fin 3)) (X : M) :
    finitePauliMatrix P * (finitePauliMatrix P * X - X * finitePauliMatrix P) -
      (finitePauliMatrix P * X - X * finitePauliMatrix P) * finitePauliMatrix P =
      (4 : ℂ) • (X - pauliStaticPart P X) := by
  have hx : finitePauliMatrix P * (finitePauliMatrix P * X) = X := by
    rw [← mul_assoc, finitePauliMatrix_mul_self, one_mul]
  have hy : X * finitePauliMatrix P * finitePauliMatrix P = X := by
    rw [mul_assoc, finitePauliMatrix_mul_self, mul_one]
  simp only [mul_sub, sub_mul, hx, hy, ← mul_assoc]
  unfold pauliStaticPart pauliConjugate
  module

/-- Exact master equation for every finite Pauli string, with a constructed nonnegative rate. -/
theorem hasDerivAt_pauliCollapseEvolution (P : σ → Option (Fin 3)) (a : ℝ)
    (X : M) (t : ℝ) :
    HasDerivAt (pauliCollapseEvolution P a X)
      (-(a^(2 : ℕ) : ℂ) •
        (finitePauliMatrix P *
            (finitePauliMatrix P * pauliCollapseEvolution P a X t -
              pauliCollapseEvolution P a X t * finitePauliMatrix P) -
          (finitePauliMatrix P * pauliCollapseEvolution P a X t -
            pauliCollapseEvolution P a X t * finitePauliMatrix P) * finitePauliMatrix P)) t := by
  have he := (((hasDerivAt_id t).const_mul (-4*a^(2 : ℕ))).exp).ofReal_comp
  apply ((he.smul_const (X - pauliStaticPart P X)).const_add
    (pauliStaticPart P X)).congr_deriv
  rw [pauli_doubleCommutator, pauliStaticPart_evolution]
  simp only [pauliCollapseEvolution, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_pow, id_eq]
  module

theorem pauliConjugate_trace (P : σ → Option (Fin 3)) (X : M) :
    (pauliConjugate P X).trace = X.trace := by
  unfold pauliConjugate
  rw [Matrix.trace_mul_comm, ← mul_assoc, finitePauliMatrix_mul_self, one_mul]

theorem pauliCollapseEvolution_trace (P : σ → Option (Fin 3)) (a : ℝ)
    (X : M) (t : ℝ) :
    (pauliCollapseEvolution P a X t).trace = X.trace := by
  simp only [pauliCollapseEvolution, pauliStaticPart, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sub, pauliConjugate_trace, smul_eq_mul]
  ring

/-- At forward times the evolution is a convex mixture of identity and Pauli conjugation. -/
theorem pauliCollapseEvolution_mixture (P : σ → Option (Fin 3)) (a : ℝ)
    (X : M) (t : ℝ) :
    pauliCollapseEvolution P a X t =
      ((1 + (Real.exp (-4*a^(2 : ℕ)*t) : ℂ))/2) • X +
      ((1 - (Real.exp (-4*a^(2 : ℕ)*t) : ℂ))/2) • pauliConjugate P X := by
  unfold pauliCollapseEvolution pauliStaticPart
  module

/-- The constructed positive matrix cone is preserved at every nonnegative square time. -/
theorem pauliCollapseEvolution_positive (P : σ → Option (Fin 3)) (a t : ℝ) (B : M) :
    (pauliCollapseEvolution P a (B*Bᴴ) (t^(2 : ℕ))).PosSemidef := by
  rw [pauliCollapseEvolution_mixture]
  have hB := Matrix.posSemidef_self_mul_conjTranspose B
  have hC : (pauliConjugate P (B*Bᴴ)).PosSemidef := by
    simpa only [pauliConjugate, (finitePauliMatrix_isHermitian P).eq] using
      hB.mul_mul_conjTranspose_same (finitePauliMatrix P)
  have he : Real.exp (-4*a^(2 : ℕ)*t^(2 : ℕ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg t)]
  apply Matrix.PosSemidef.add
  · apply hB.smul
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div]
    exact_mod_cast (show (0 : ℝ) ≤ (1 + Real.exp (-4*a^(2 : ℕ)*t^(2 : ℕ)))/2 by positivity)
  · apply hC.smul
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div]
    exact_mod_cast (show (0 : ℝ) ≤ (1 - Real.exp (-4*a^(2 : ℕ)*t^(2 : ℕ)))/2 by linarith)

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
