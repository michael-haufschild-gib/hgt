import GaloisForLFunctions.HTGeometry.ProjectiveHorizonA2CurrentAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Laurent residue seam of the projective-horizon `A₂` current algebra

The polynomial projective-horizon currents are one-sided.  This file isolates the algebraic
topology that appears only after a Laurent double is supplied.  On pure loop modes the residue
pairing is

`ω(A t^m, B t^n) = n δ_(m+n,0) tr(AB)`.

Lean proves that this is alternating and satisfies the Lie `2`-cocycle identity.  Both the
nonnegative and nonpositive current halves are isotropic, while every opposite Chevalley-root pair
has the exact nonzero central seam `-m` in degrees `(m,-m)`.

This is the classical affine-current local model.  The separate scientific problem is to derive
the negative half and the Laurent coordinate from the HT source rather than imposing them.
-/

open scoped Matrix

namespace GaloisForLFunctions

noncomputable section

variable (K : Type*) [Field K]

/-- The pure-mode affine residue pairing `Res(t^m d(t^n)) tr(AB)`. -/
def a2LaurentResiduePairing
    (m n : ℤ) (A B : Matrix (Fin 3) (Fin 3) K) : K :=
  if m + n = 0 then (n : K) * Matrix.trace (A * B) else 0

/-- The affine residue pairing is alternating on pure Laurent modes. -/
theorem a2LaurentResiduePairing_swap
    (m n : ℤ) (A B : Matrix (Fin 3) (Fin 3) K) :
    a2LaurentResiduePairing K m n A B =
      -a2LaurentResiduePairing K n m B A := by
  by_cases h : m + n = 0
  · have h' : n + m = 0 := by omega
    have hmn : m = -n := by omega
    simp only [a2LaurentResiduePairing, if_pos h, if_pos h']
    rw [Matrix.trace_mul_comm, hmn]
    simp
  · have h' : n + m ≠ 0 := by omega
    simp [a2LaurentResiduePairing, h, h']

/-- The nonnegative polynomial-current half is residue-isotropic. -/
theorem a2LaurentResiduePairing_nonneg_zero
    (m n : ℤ) (A B : Matrix (Fin 3) (Fin 3) K)
    (hm : 0 ≤ m) (hn : 0 ≤ n) :
    a2LaurentResiduePairing K m n A B = 0 := by
  by_cases h : m + n = 0
  · have hm0 : m = 0 := by omega
    have hn0 : n = 0 := by omega
    subst m
    subst n
    simp [a2LaurentResiduePairing]
  · simp [a2LaurentResiduePairing, h]

/-- The nonpositive opposite-current half is residue-isotropic. -/
theorem a2LaurentResiduePairing_nonpos_zero
    (m n : ℤ) (A B : Matrix (Fin 3) (Fin 3) K)
    (hm : m ≤ 0) (hn : n ≤ 0) :
    a2LaurentResiduePairing K m n A B = 0 := by
  by_cases h : m + n = 0
  · have hm0 : m = 0 := by omega
    have hn0 : n = 0 := by omega
    subst m
    subst n
    simp [a2LaurentResiduePairing]
  · simp [a2LaurentResiduePairing, h]

private theorem trace_lie_mul_cyclic
    (A B C : Matrix (Fin 3) (Fin 3) K) :
    Matrix.trace (⁅A, B⁆ * C) = Matrix.trace (⁅B, C⁆ * A) := by
  simp only [LieRing.of_associative_ring_bracket, sub_mul, Matrix.trace_sub]
  have hpos : Matrix.trace ((A * B) * C) = Matrix.trace ((B * C) * A) := by
    rw [Matrix.mul_assoc]
    exact Matrix.trace_mul_comm A (B * C)
  have hneg : Matrix.trace ((B * A) * C) = Matrix.trace ((C * B) * A) := by
    rw [Matrix.trace_mul_comm (B * A) C, Matrix.mul_assoc]
  rw [hpos, hneg]

section CharZero

variable [CharZero K]

/-- **Affine residue `2`-cocycle identity on pure modes.** -/
theorem a2LaurentResiduePairing_cocycle
    (m n l : ℤ) (A B C : Matrix (Fin 3) (Fin 3) K) :
    a2LaurentResiduePairing K (m + n) l ⁅A, B⁆ C +
      a2LaurentResiduePairing K (n + l) m ⁅B, C⁆ A +
      a2LaurentResiduePairing K (l + m) n ⁅C, A⁆ B = 0 := by
  by_cases h : m + n + l = 0
  · have h1 : m + n + l = 0 := h
    have h2 : n + l + m = 0 := by omega
    have h3 : l + m + n = 0 := by omega
    simp only [a2LaurentResiduePairing, if_pos h1, if_pos h2, if_pos h3]
    rw [trace_lie_mul_cyclic K A B C, trace_lie_mul_cyclic K B C A]
    have hcast : (l : K) + (m : K) + (n : K) = 0 := by
      exact_mod_cast h3
    calc
      (l : K) * Matrix.trace (⁅C, A⁆ * B) +
            (m : K) * Matrix.trace (⁅C, A⁆ * B) +
            (n : K) * Matrix.trace (⁅C, A⁆ * B) =
          ((l : K) + (m : K) + (n : K)) * Matrix.trace (⁅C, A⁆ * B) := by
            ring
      _ = 0 := by rw [hcast]; simp
  · have h1 : m + n + l ≠ 0 := h
    have h2 : n + l + m ≠ 0 := by omega
    have h3 : l + m + n ≠ 0 := by omega
    simp [a2LaurentResiduePairing, h1, h2, h3]

/-! ## Exact seams on the three positive `A₂` roots -/

def a2ConstantE01 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 0, 0, 0; 0, 0, 0]

def a2ConstantE10 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0; 1, 0, 0; 0, 0, 0]

def a2ConstantE02 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 0, 0; 0, 0, 0]

def a2ConstantE20 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0; 0, 0, 0; 1, 0, 0]

def a2ConstantE12 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0; 0, 0, 1; 0, 0, 0]

def a2ConstantE21 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 0; 0, 0, 0; 0, 1, 0]

omit [CharZero K] in
private theorem trace_a2ConstantE01_mul_E10 :
    Matrix.trace (a2ConstantE01 K * a2ConstantE10 K) = 1 := by
  simp [a2ConstantE01, a2ConstantE10, Matrix.trace, Fin.sum_univ_succ]

omit [CharZero K] in
private theorem trace_a2ConstantE02_mul_E20 :
    Matrix.trace (a2ConstantE02 K * a2ConstantE20 K) = 1 := by
  simp [a2ConstantE02, a2ConstantE20, Matrix.trace, Fin.sum_univ_succ]

omit [CharZero K] in
private theorem trace_a2ConstantE12_mul_E21 :
    Matrix.trace (a2ConstantE12 K * a2ConstantE21 K) = 1 := by
  simp [a2ConstantE12, a2ConstantE21, Matrix.trace, Fin.sum_univ_succ]

omit [CharZero K] in
/-- Every positive Chevalley root and its negative partner carry the same exact central seam in
opposite Laurent degrees. -/
theorem a2LaurentResiduePairing_opposite_chevalley_roots (m : ℤ) :
    a2LaurentResiduePairing K m (-m) (a2ConstantE01 K) (a2ConstantE10 K) =
        (-m : K) ∧
      a2LaurentResiduePairing K m (-m) (a2ConstantE02 K) (a2ConstantE20 K) =
        (-m : K) ∧
      a2LaurentResiduePairing K m (-m) (a2ConstantE12 K) (a2ConstantE21 K) =
        (-m : K) := by
  simp [a2LaurentResiduePairing, trace_a2ConstantE01_mul_E10,
    trace_a2ConstantE02_mul_E20, trace_a2ConstantE12_mul_E21]

/-- Every nonzero opposite mode has a nontrivial central seam. -/
theorem a2LaurentResiduePairing_opposite_E01_ne_zero
    {m : ℤ} (hm : m ≠ 0) :
    a2LaurentResiduePairing K m (-m) (a2ConstantE01 K) (a2ConstantE10 K) ≠ 0 := by
  rw [(a2LaurentResiduePairing_opposite_chevalley_roots K m).1]
  exact_mod_cast neg_ne_zero.mpr hm

end CharZero

end

end GaloisForLFunctions
