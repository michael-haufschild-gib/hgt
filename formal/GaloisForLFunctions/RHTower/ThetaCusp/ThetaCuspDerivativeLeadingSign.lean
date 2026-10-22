import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeDerivatives
import Mathlib.Analysis.Polynomial.Basic

/-!
# Leading sign of every theta-cusp source derivative polynomial

Logarithmic differentiation raises polynomial degree by two and multiplies its leading
coefficient by `-2π`. Hence the `4m`-th polynomial dominates the seed positively
at infinity. This is the first source-specific gate for positive differential
deformations carrying exact nonreal divisor packets.
-/

open Polynomial Filter Topology
namespace RHTower

private theorem logDerivativeStep_degree_leading (P : ℝ[X]) :
    (thetaCuspLogDerivativeStep P).degree = P.degree + 2 ∧
    (thetaCuspLogDerivativeStep P).leadingCoeff =
      -(2 * Real.pi) * P.leadingCoeff := by
  by_cases hP : P = 0
  · subst P
    simp [thetaCuspLogDerivativeStep]
  let L : ℝ[X] := C (1 / 2) * P + X * derivative P
  let H : ℝ[X] := C (2 * Real.pi) * X ^ (2 : ℕ) * P
  have hhalf : IsUnit (1 / 2 : ℝ) := isUnit_iff_ne_zero.mpr (by norm_num)
  have hpi : IsUnit (2 * Real.pi : ℝ) :=
    isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hfirst : (C (1 / 2) * P).degree = P.degree :=
    degree_C_mul_of_isUnit hhalf P
  have hsecond : (X * derivative P).degree = (derivative P).degree + 1 := by
    rw [mul_comm, degree_mul_X]
  have hL : L.degree ≤ P.degree + 1 := by
    dsimp [L]
    refine (degree_add_le _ _).trans ?_
    rw [hfirst, hsecond]
    exact max_le (le_add_of_nonneg_right (by norm_num))
      (by simpa [add_comm] using
        (add_le_add_right (Polynomial.degree_derivative_le (p := P)) 1))
  have hH : H.degree = P.degree + 2 := by
    dsimp [H]
    rw [show C (2 * Real.pi) * X ^ (2 : ℕ) * P =
      C (2 * Real.pi) * (P * X ^ (2 : ℕ)) by ring]
    rw [degree_C_mul_of_isUnit hpi, degree_mul_X_pow]
    norm_cast
  have hlt : L.degree < H.degree := by
    rw [hH]
    rw [degree_eq_natDegree hP] at hL ⊢
    have hn : P.natDegree + 1 < P.natDegree + 2 := by omega
    exact lt_of_le_of_lt hL (by exact_mod_cast hn)
  have hstep : thetaCuspLogDerivativeStep P = L - H := by
    rfl
  constructor
  · rw [hstep, degree_sub_eq_right_of_degree_lt hlt, hH]
  · rw [hstep, leadingCoeff_sub_of_degree_lt' hlt]
    dsimp [H]
    rw [show C (2 * Real.pi) * X ^ (2 : ℕ) * P =
      C (2 * Real.pi) * (P * X ^ (2 : ℕ)) by ring]
    rw [leadingCoeff_C_mul_of_isUnit hpi, leadingCoeff_mul_X_pow]
    ring

private theorem thetaSeed_degree_leading :
    thetaCuspSeedPolynomial.degree = 4 ∧
    thetaCuspSeedPolynomial.leadingCoeff = 4 * Real.pi ^ (2 : ℕ) := by
  have ha : 4 * Real.pi ^ (2 : ℕ) ≠ 0 := by positivity
  have hb : 6 * Real.pi ≠ 0 := by positivity
  have hA : (C (4 * Real.pi ^ (2 : ℕ)) * X ^ (4 : ℕ) : ℝ[X]).degree = 4 :=
    degree_C_mul_X_pow 4 ha
  have hB : (C (6 * Real.pi) * X ^ (2 : ℕ) : ℝ[X]).degree = 2 :=
    degree_C_mul_X_pow 2 hb
  have hlt : (C (6 * Real.pi) * X ^ (2 : ℕ) : ℝ[X]).degree <
      (C (4 * Real.pi ^ (2 : ℕ)) * X ^ (4 : ℕ) : ℝ[X]).degree := by
    rw [hA, hB]
    norm_num
  unfold thetaCuspSeedPolynomial
  constructor
  · rw [degree_sub_eq_left_of_degree_lt hlt, hA]
  · rw [leadingCoeff_sub_of_degree_lt hlt, leadingCoeff_C_mul_X_pow]

/-- Exact degree and leading coefficient of every logarithmic theta derivative. -/
theorem thetaCuspLogDerivativePolynomial_degree_leading (n : ℕ) :
    (thetaCuspLogDerivativePolynomial n).degree = (4 + 2*n : ℕ) ∧
    (thetaCuspLogDerivativePolynomial n).leadingCoeff =
      (4 * Real.pi ^ (2 : ℕ)) * (-(2 * Real.pi)) ^ n := by
  induction n with
  | zero => simpa [thetaCuspLogDerivativePolynomial] using thetaSeed_degree_leading
  | succ n ih =>
      have hs := logDerivativeStep_degree_leading (thetaCuspLogDerivativePolynomial n)
      constructor
      · change (thetaCuspLogDerivativeStep (thetaCuspLogDerivativePolynomial n)).degree =
          (4 + 2*(n+1) : ℕ)
        rw [hs.1, ih.1]
        norm_cast
      · change (thetaCuspLogDerivativeStep (thetaCuspLogDerivativePolynomial n)).leadingCoeff =
          (4 * Real.pi ^ (2 : ℕ)) * (-(2 * Real.pi)) ^ (n+1)
        rw [hs.2, ih.2, pow_succ]
        ring

/-- Every positive fourth-multiple derivative polynomial dominates the seed on the tail. -/
theorem thetaCuspLogDerivativePolynomial_four_mul_ratio_tendsto_atTop
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x : ℝ =>
      eval (Real.exp x) (thetaCuspLogDerivativePolynomial (4*m)) /
        eval (Real.exp x) thetaCuspSeedPolynomial) atTop atTop := by
  have hnum := thetaCuspLogDerivativePolynomial_degree_leading (4*m)
  have hden := thetaSeed_degree_leading
  have hdeg : thetaCuspSeedPolynomial.degree <
      (thetaCuspLogDerivativePolynomial (4*m)).degree := by
    rw [hnum.1, hden.1]
    exact_mod_cast (show 4 < 4 + 2 * (4*m) by omega)
  have hpos : 0 <
      (thetaCuspLogDerivativePolynomial (4*m)).leadingCoeff /
        thetaCuspSeedPolynomial.leadingCoeff := by
    rw [hnum.2, hden.2]
    have heven : 0 < (-(2 * Real.pi) : ℝ) ^ (4*m) := by
      rw [show 4*m = 2*(2*m) by omega, pow_mul]
      have hne : (-(2 * Real.pi) : ℝ) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact pow_pos (sq_pos_of_ne_zero hne) _
    exact div_pos (mul_pos (by positivity) heven) (by positivity)
  exact (Polynomial.div_tendsto_atTop_of_degree_gt'
    (thetaCuspLogDerivativePolynomial (4*m)) thetaCuspSeedPolynomial
    hdeg hpos).comp Real.tendsto_exp_atTop

end RHTower
