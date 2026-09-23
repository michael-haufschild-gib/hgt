import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# The Báez--Duarte coefficients as a Möbius series

The finite binomial transform `c_k = Σ_{j≤k} (-1)^j C(k,j)/ζ(2j+2)` of reciprocal zeta values at
even integers is the absolutely convergent Möbius series `Σ_{n≥1} μ(n) n^{-2} (1 - n^{-2})^k`.
Only a finite binomial sum is interchanged with an absolutely convergent Dirichlet series, so every
value stays in the Euler half-plane.
-/

namespace RHTower

open ArithmeticFunction LSeries Complex
open scoped LSeries.notation Moebius

noncomputable section

/-- The sequential Báez--Duarte coefficient `c_k = Σ_{j≤k} (-1)^j C(k,j)/ζ(2j+2)`. -/
def bdCoeff (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) / riemannZeta (2 * (j : ℂ) + 2)

/-- The Möbius summand `μ(n) n^{-2} (1 - n^{-2})^k`. -/
def bdMobiusTerm (k n : ℕ) : ℂ :=
  ((moebius n : ℤ) : ℂ) * ((n : ℂ) ^ (2 : ℕ))⁻¹ * (1 - ((n : ℂ) ^ (2 : ℕ))⁻¹) ^ k

theorem one_lt_re_bdExponent (j : ℕ) : 1 < (2 * (j : ℂ) + 2).re := by
  have h : (2 * (j : ℂ) + 2).re = 2 * (j : ℝ) + 2 := by
    simp [Complex.add_re, Complex.mul_re]
  rw [h]
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem hasSum_bdShift (j : ℕ) :
    HasSum (fun n => LSeries.term (fun n => ((μ n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) n)
      (riemannZeta (2 * (j : ℂ) + 2))⁻¹ := by
  have hs := one_lt_re_bdExponent j
  have hsum : LSeriesSummable (fun n => ((μ n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) :=
    LSeriesSummable_moebius_iff.mpr hs
  have h2 : (∑' b : ℕ, LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) b)
      = (riemannZeta (2 * (j : ℂ) + 2))⁻¹ := LSeries_moebius_eq_inv_riemannZeta hs
  have := hsum.hasSum
  rw [h2] at this
  exact this

theorem term_bdShift_eq {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) n
      = ((moebius n : ℤ) : ℂ) * (((n : ℂ) ^ (2 : ℕ))⁻¹) ^ (j + 1) := by
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0]
  have hcast : 2 * (j : ℂ) + 2 = ((2 * j + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.cpow_natCast]
  have hpow : (n : ℂ) ^ (2 * j + 2) = ((n : ℂ) ^ (2 : ℕ)) ^ (j + 1) := by
    rw [← pow_mul, show 2 * j + 2 = 2 * (j + 1) by ring]
  rw [hpow, div_eq_mul_inv, ← inv_pow]

theorem sum_bdMobiusTerm (k n : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ)
        * LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) n
      = bdMobiusTerm k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [bdMobiusTerm, LSeries.term_zero]
  · have hterm := fun j => term_bdShift_eq hn j
    simp only [hterm]
    set x : ℂ := ((n : ℂ) ^ (2 : ℕ))⁻¹ with hx
    have hbinom : (1 - x) ^ k = ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ) * x ^ j := by
      have h := add_pow (-x) (1 : ℂ) k
      simp only [one_pow, mul_one] at h
      rw [show (-x + 1 : ℂ) = 1 - x by ring] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [neg_pow]
      ring
    rw [bdMobiusTerm, ← hx, hbinom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring

/-- **Equations (1)–(2).**  The Báez--Duarte coefficient is the Möbius series
`Σ_{n≥1} μ(n) n^{-2} (1 - n^{-2})^k`. -/
theorem hasSum_bdMobiusTerm (k : ℕ) : HasSum (bdMobiusTerm k) (bdCoeff k) := by
  have h : HasSum
      (fun n => ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ)
        * LSeries.term (fun n => ((moebius n : ℤ) : ℂ)) (2 * (j : ℂ) + 2) n)
      (∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ)
        * (riemannZeta (2 * (j : ℂ) + 2))⁻¹) :=
    hasSum_sum fun j _ => (hasSum_bdShift j).mul_left _
  have heq : (∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * (k.choose j : ℂ)
      * (riemannZeta (2 * (j : ℂ) + 2))⁻¹) = bdCoeff k := by
    rw [bdCoeff]
    exact Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
  rw [heq] at h
  simpa only [sum_bdMobiusTerm] using h

/-- The Möbius series representation as a `tsum`. -/
theorem bdCoeff_eq_tsum (k : ℕ) : bdCoeff k = ∑' n : ℕ, bdMobiusTerm k n :=
  (hasSum_bdMobiusTerm k).tsum_eq.symm

end

end RHTower
