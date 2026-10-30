import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Operations

/-!
# Euler differentiation and ideal multiplicity

Leibniz lowers the power of any polynomial ideal by at most one. A word of
shifted coordinate Euler operators therefore loses at most its length in
point multiplicity. Finite linearity permits exact monomial extraction.
-/

open MvPolynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Leibniz differentiation loses at most one factor of any ideal power. -/
theorem derivation_mem_ideal_pow (D : Derivation R A A) (I : Ideal A) (m : ℕ)
    {f : A} (hf : f ∈ I ^ (m + 1)) : D f ∈ I ^ m := by
  induction m generalizing f with
  | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ m ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      apply (I ^ (m + 1)).add_mem
      · exact (I ^ (m + 1)).mul_mem_right (D y) hx
      · rw [pow_succ, mul_comm y]
        exact Ideal.mul_mem_mul (ih hx) hy
    · intro x y hx hy
      rw [map_add]
      exact (I ^ (m + 1)).add_mem hx hy

variable {ι : Type*}

/-- The shifted coordinate Euler operator `Xᵢ ∂ᵢ − s`. -/
def shiftedCoordinateEuler (i : ι) (s : R) (f : MvPolynomial ι R) :
    MvPolynomial ι R := X i * pderiv i f - C s * f

/-- Each shifted Euler factor loses at most one order of ideal multiplicity. -/
theorem shiftedCoordinateEuler_mem_ideal_pow (i : ι) (s : R)
    (I : Ideal (MvPolynomial ι R)) (m : ℕ) {f : MvPolynomial ι R}
    (hf : f ∈ I ^ (m + 1)) : shiftedCoordinateEuler i s f ∈ I ^ m := by
  apply (I ^ m).sub_mem
  · exact (I ^ m).mul_mem_left _ (derivation_mem_ideal_pow (pderiv i) I m hf)
  · exact (I ^ m).mul_mem_left _ (Ideal.pow_le_pow_right (Nat.le_succ m) hf)

/-- Apply a finite word of shifted coordinate Euler operators. -/
def shiftedEulerWord : List (ι × R) → MvPolynomial ι R → MvPolynomial ι R
  | [], f => f
  | (i, s) :: L, f => shiftedCoordinateEuler i s (shiftedEulerWord L f)

/-- A word of length `k` lowers any ideal multiplicity by at most `k`. -/
theorem shiftedEulerWord_mem_ideal_pow (L : List (ι × R))
    (I : Ideal (MvPolynomial ι R)) (m : ℕ) {f : MvPolynomial ι R}
    (hf : f ∈ I ^ (m + L.length)) : shiftedEulerWord L f ∈ I ^ m := by
  induction L generalizing m with
  | nil => simpa only [List.length_nil, Nat.add_zero, shiftedEulerWord] using hf
  | cons v L ih =>
    apply shiftedCoordinateEuler_mem_ideal_pow v.1 v.2 I m
    apply ih (m + 1)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf

theorem shiftedCoordinateEuler_sum {κ : Type*} (i : ι) (s : R)
    (S : Finset κ) (f : κ → MvPolynomial ι R) :
    shiftedCoordinateEuler i s (∑ n ∈ S, f n) =
      ∑ n ∈ S, shiftedCoordinateEuler i s (f n) := by
  simp only [shiftedCoordinateEuler, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]

theorem shiftedEulerWord_sum {κ : Type*} (L : List (ι × R))
    (S : Finset κ) (f : κ → MvPolynomial ι R) :
    shiftedEulerWord L (∑ n ∈ S, f n) = ∑ n ∈ S, shiftedEulerWord L (f n) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [shiftedEulerWord, ih, shiftedCoordinateEuler_sum]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
