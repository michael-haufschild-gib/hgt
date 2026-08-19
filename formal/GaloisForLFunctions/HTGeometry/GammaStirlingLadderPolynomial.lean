import Mathlib

/-!
# The Stirling ladder polynomial and its vanishing order

Clearing the denominator `(1+u)^M` from the one-step difference of the `M`-th Stirling defect
produces a polynomial `P_M`.  The whole finite-order Stirling ladder is the single assertion that
the ladder coefficients can be chosen so that `X^(M+2) ∣ P_M`.

The point of this module is that the recursion for `P_M` is *linear and explicit*:

`P_{M+1} = (1+X) P_M + ((-1)^M/(M+2)) X^(M+2) (1+X)^(M+1) + c_M X^(M+1) (1 - (1+X)^(M+1))`

and each of the three summands is already divisible by `X^(M+2)`, so only the single coefficient in
degree `M+2` has to be killed — which is exactly what the choice of `c_M` does.  No Bernoulli input
is needed: the coefficients are *forced*.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The ladder coefficient forced by the degree-`M+2` obstruction of `P`. -/
def ladderCoeffOf (P : ℂ[X]) (M : ℕ) : ℂ :=
  (P.coeff (M + 2) + (-1) ^ M / ((M : ℂ) + 2)) / ((M : ℂ) + 1)

/-- The Stirling ladder polynomial: the numerator of the one-step difference of the `M`-th defect
after clearing `(1+u)^M`. -/
def ladderPoly : ℕ → ℂ[X]
  | 0 => 0
  | (M + 1) =>
      (1 + X) * ladderPoly M
        + C ((-1) ^ M / ((M : ℂ) + 2)) * (X ^ (M + 2) * (1 + X) ^ (M + 1))
        + C (ladderCoeffOf (ladderPoly M) M) * (X ^ (M + 1) * (1 - (1 + X) ^ (M + 1)))

/-- The `M`-th Stirling ladder coefficient. -/
def ladderCoeff (M : ℕ) : ℂ := ladderCoeffOf (ladderPoly M) M

theorem ladderPoly_succ (M : ℕ) :
    ladderPoly (M + 1) =
      (1 + X) * ladderPoly M
        + C ((-1) ^ M / ((M : ℂ) + 2)) * (X ^ (M + 2) * (1 + X) ^ (M + 1))
        + C (ladderCoeff M) * (X ^ (M + 1) * (1 - (1 + X) ^ (M + 1))) := rfl

theorem coeff_zero_one_add_X_pow (n : ℕ) : (((1 + X : ℂ[X]) ^ n)).coeff 0 = 1 := by
  rw [Polynomial.coeff_one_add_X_pow]
  simp

theorem coeff_one_one_add_X_pow (n : ℕ) : (((1 + X : ℂ[X]) ^ n)).coeff 1 = (n : ℂ) := by
  rw [Polynomial.coeff_one_add_X_pow]
  simp

theorem X_dvd_one_sub_one_add_X_pow (n : ℕ) :
    (X : ℂ[X]) ∣ 1 - (1 + X) ^ n := by
  have h : ((X : ℂ[X]) ^ 1) ∣ 1 - (1 + X) ^ n := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    simp [coeff_zero_one_add_X_pow]
  simpa using h

/-- **The ladder polynomial vanishes to order `M+2`.** -/
theorem X_pow_dvd_ladderPoly : ∀ M : ℕ, ((X : ℂ[X]) ^ (M + 2)) ∣ ladderPoly M := by
  intro M
  induction M with
  | zero => simp [ladderPoly]
  | succ M ih =>
      have hcM : (ladderPoly M).coeff (M + 1) = 0 :=
        (Polynomial.X_pow_dvd_iff.mp ih) (M + 1) (by omega)
      -- every summand already vanishes to order `M+2`
      have hd1 : ((X : ℂ[X]) ^ (M + 2)) ∣ (1 + X) * ladderPoly M := ih.mul_left _
      have hd2 : ((X : ℂ[X]) ^ (M + 2)) ∣
          C ((-1) ^ M / ((M : ℂ) + 2)) * (X ^ (M + 2) * (1 + X) ^ (M + 1)) :=
        (dvd_mul_right _ _).mul_left _
      have hd3 : ((X : ℂ[X]) ^ (M + 2)) ∣
          C (ladderCoeff M) * (X ^ (M + 1) * (1 - (1 + X) ^ (M + 1))) := by
        refine Dvd.dvd.mul_left ?_ _
        have hx := X_dvd_one_sub_one_add_X_pow (M + 1)
        have : ((X : ℂ[X]) ^ (M + 1)) * X ∣ (X : ℂ[X]) ^ (M + 1) * (1 - (1 + X) ^ (M + 1)) :=
          mul_dvd_mul_left _ hx
        simpa [pow_succ] using this
      have hdvd2 : ((X : ℂ[X]) ^ (M + 2)) ∣ ladderPoly (M + 1) := by
        rw [ladderPoly_succ]
        exact dvd_add (dvd_add hd1 hd2) hd3
      -- the degree `M+2` coefficient is killed by the choice of `ladderCoeff M`
      have hkey : (ladderPoly (M + 1)).coeff (M + 2) = 0 := by
        have hne : ((M : ℂ) + 1) ≠ 0 := by
          have h := Nat.cast_add_one_ne_zero (R := ℂ) M
          simpa using h
        have e1 : ((1 + X : ℂ[X]) * ladderPoly M).coeff (M + 2)
            = (ladderPoly M).coeff (M + 2) + (ladderPoly M).coeff (M + 1) := by
          rw [add_mul, one_mul, Polynomial.coeff_add]
          congr 1
          exact Polynomial.coeff_X_mul _ (M + 1)
        have e2 : (C ((-1 : ℂ) ^ M / ((M : ℂ) + 2)) *
            (X ^ (M + 2) * (1 + X) ^ (M + 1))).coeff (M + 2)
            = (-1 : ℂ) ^ M / ((M : ℂ) + 2) := by
          rw [Polynomial.coeff_C_mul]
          have : ((X : ℂ[X]) ^ (M + 2) * (1 + X) ^ (M + 1)).coeff (M + 2)
              = ((1 + X : ℂ[X]) ^ (M + 1)).coeff 0 := by
            simpa using Polynomial.coeff_X_pow_mul ((1 + X : ℂ[X]) ^ (M + 1)) (M + 2) 0
          rw [this, coeff_zero_one_add_X_pow, mul_one]
        have e3 : (C (ladderCoeff M) *
            (X ^ (M + 1) * (1 - (1 + X) ^ (M + 1)))).coeff (M + 2)
            = ladderCoeff M * (-((M : ℂ) + 1)) := by
          rw [Polynomial.coeff_C_mul]
          have hidx : M + 2 = 1 + (M + 1) := by omega
          have hshift : ((X : ℂ[X]) ^ (M + 1) * (1 - (1 + X) ^ (M + 1))).coeff (M + 2)
              = ((1 : ℂ[X]) - (1 + X) ^ (M + 1)).coeff 1 := by
            rw [hidx]
            exact Polynomial.coeff_X_pow_mul _ (M + 1) 1
          rw [hshift, Polynomial.coeff_sub, coeff_one_one_add_X_pow, Polynomial.coeff_one]
          norm_num
        rw [ladderPoly_succ, Polynomial.coeff_add, Polynomial.coeff_add, e1, e2, e3, hcM]
        rw [ladderCoeff, ladderCoeffOf]
        field_simp
        ring
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      rcases Nat.lt_or_ge d (M + 2) with h | h
      · exact (Polynomial.X_pow_dvd_iff.mp hdvd2) d h
      · have : d = M + 2 := by omega
        rw [this]; exact hkey

end

end GaloisForLFunctions.HTGeometry
