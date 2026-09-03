import GaloisForLFunctions.RHTower.SemilocalBoostContiguousRelations

/-!
# The Route J residual jet as a combination of first differences

With `m_n = ∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} (−1)^n C_n F_n(x)`, `x = sech² δ`, the first
contiguous relation gives

`m_{n+1} − m_n = (cosh δ)^{-1/2} (−1)^{n+1} Q_n`,   `Q_n = C_n (4n+3)(1 − x) H_n / (2(n+1))`,

a *smooth* (non-alternating) sequence.  The four-radius residual jet of the first-order response
then collapses to first differences of `Q` and of `r² Q`:

`J_k = (cosh δ)^{-1/2} [ r_{2k} r_{2k+1} (Q_{2k+1} − Q_{2k}) + 2 (r_{2k+2}² Q_{2k+2} − r_{2k+1}² Q_{2k+1})
        + r_{2k+2} r_{2k+3} (Q_{2k+3} − Q_{2k+2}) ]`,

and the second contiguous relation evaluates those differences in closed form through `H_n` and
`K_n`.  This is the exact algebraic skeleton of the Route J profile.
-/

open Finset
open scoped BigOperators

namespace RHTower

namespace RouteJProfile

open ScaledHypergeometric CosineModeResponse

/-- `C_n = binom(2n,n)/4^n`. -/
noncomputable def cb (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

theorem cb_succ (n : ℕ) : cb (n + 1) = cb n * (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) := by
  unfold cb
  have h := Nat.succ_mul_centralBinom_succ n
  have h' : ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
  push_cast at h'
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  linear_combination 2 * h'

theorem cb_pos (n : ℕ) : 0 < cb n := by
  unfold cb
  have := Nat.centralBinom_pos n
  positivity

/-- `x = sech² δ`. -/
noncomputable def sq (δ : ℝ) : ℝ := (1 / Real.cosh δ) ^ 2

noncomputable def Fh (δ : ℝ) (n : ℕ) : ℝ := hypSumSq n (1 / 2) (1 / 2) (sq δ)
noncomputable def Hh (δ : ℝ) (n : ℕ) : ℝ := hypSumSq n (3 / 2) (1 / 2) (sq δ)
noncomputable def Kh (δ : ℝ) (n : ℕ) : ℝ := hypSumSq n (5 / 2) (3 / 2) (sq δ)

theorem cosineDiagonalMoment_eq_cb (δ : ℝ) (n : ℕ) :
    cosineDiagonalMoment δ n = Real.cosh δ ^ (-(1 / 2 : ℝ)) * ((-1) ^ n * cb n * Fh δ n) := by
  rw [cosineDiagonalMoment_eq_hypSum, hypSum_eq_hypSumSq]
  rfl

/-- The smooth first-difference sequence `Q_n`. -/
noncomputable def Qsmooth (δ : ℝ) (n : ℕ) : ℝ :=
  cb n * (4 * (n : ℝ) + 3) * (1 - sq δ) * Hh δ n / (2 * ((n : ℝ) + 1))

/-- `m_{n+1} − m_n = (cosh δ)^{-1/2} (−1)^{n+1} Q_n`. -/
theorem diff_cosineDiagonalMoment (δ : ℝ) (n : ℕ) :
    cosineDiagonalMoment δ (n + 1) - cosineDiagonalMoment δ n =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * ((-1) ^ (n + 1) * Qsmooth δ n) := by
  have hQ : Qsmooth δ n = cb n * ((2 * (n : ℝ) + 1) * Fh δ (n + 1) + 2 * ((n : ℝ) + 1) * Fh δ n) /
      (2 * ((n : ℝ) + 1)) := by
    unfold Qsmooth Fh Hh
    have hc := contiguous_F n (sq δ)
    linear_combination (-(cb n) / (2 * ((n : ℝ) + 1))) * hc
  rw [hQ, cosineDiagonalMoment_eq_cb, cosineDiagonalMoment_eq_cb, cb_succ]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  ring

/-- **The residual jet as first differences of `Q` and `r² Q`.** -/
theorem residualJetOf_cosineMode_eq (δ : ℝ) (k : ℕ) :
    residualJetOf (cosineModeDeterminantJet δ) k =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) *
        (semilocalArchimedeanJacobiCoefficient (2 * k) * semilocalArchimedeanJacobiCoefficient (2 * k + 1) *
            (Qsmooth δ (2 * k + 1) - Qsmooth δ (2 * k)) +
          2 * (semilocalArchimedeanJacobiCoefficient (2 * k + 2) ^ 2 * Qsmooth δ (2 * k + 2) -
            semilocalArchimedeanJacobiCoefficient (2 * k + 1) ^ 2 * Qsmooth δ (2 * k + 1)) +
          semilocalArchimedeanJacobiCoefficient (2 * k + 2) * semilocalArchimedeanJacobiCoefficient (2 * k + 3) *
            (Qsmooth δ (2 * k + 3) - Qsmooth δ (2 * k + 2))) := by
  unfold residualJetOf
  simp only [radiusJetOf_cosineMode]
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 3 by ring,
    show 2 * k + 3 + 1 = 2 * k + 4 by ring]
  rw [show cosineDiagonalMoment δ (2 * k + 4) - cosineDiagonalMoment δ (2 * k + 3) =
      cosineDiagonalMoment δ (2 * k + 3 + 1) - cosineDiagonalMoment δ (2 * k + 3) from rfl,
    show cosineDiagonalMoment δ (2 * k + 3) - cosineDiagonalMoment δ (2 * k + 2) =
      cosineDiagonalMoment δ (2 * k + 2 + 1) - cosineDiagonalMoment δ (2 * k + 2) from rfl,
    show cosineDiagonalMoment δ (2 * k + 2) - cosineDiagonalMoment δ (2 * k + 1) =
      cosineDiagonalMoment δ (2 * k + 1 + 1) - cosineDiagonalMoment δ (2 * k + 1) from rfl,
    show cosineDiagonalMoment δ (2 * k + 1) - cosineDiagonalMoment δ (2 * k) =
      cosineDiagonalMoment δ (2 * k + 1) - cosineDiagonalMoment δ (2 * k) from rfl]
  rw [diff_cosineDiagonalMoment δ (2 * k + 3), diff_cosineDiagonalMoment δ (2 * k + 2),
    diff_cosineDiagonalMoment δ (2 * k + 1), diff_cosineDiagonalMoment δ (2 * k)]
  have h1 : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; simp
  have h2 : ((-1 : ℝ)) ^ (2 * k + 2) = 1 := by rw [pow_add, pow_mul]; simp
  have h3 : ((-1 : ℝ)) ^ (2 * k + 3) = -1 := by rw [pow_add, pow_mul]; simp; norm_num
  have h4 : ((-1 : ℝ)) ^ (2 * k + 3 + 1) = 1 := by rw [pow_succ, h3]; norm_num
  have h5 : ((-1 : ℝ)) ^ (2 * k + 2 + 1) = -1 := by rw [pow_succ, h2]; norm_num
  have h6 : ((-1 : ℝ)) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h1]; norm_num
  rw [h4, h5, h6, h1]
  ring

/-! ## The differences of `Q` and `r² Q` in closed form -/

theorem Hh_succ (δ : ℝ) (n : ℕ) :
    Hh δ (n + 1) = Hh δ n - (4 * (n : ℝ) + 5) * (sq δ * Kh δ n) := by
  have := contiguous_H n (sq δ)
  unfold Hh Kh
  linear_combination this

/-- `Q_{n+1} − Q_n = −C_n (1−x)(4n+5)/(4(n+1)(n+2)) · (H_n + (2n+1)(4n+7) x K_n)`. -/
theorem Q_succ_sub (δ : ℝ) (n : ℕ) :
    Qsmooth δ (n + 1) - Qsmooth δ n =
      -(cb n * (1 - sq δ) * (4 * (n : ℝ) + 5) / (4 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) *
        (Hh δ n + (2 * (n : ℝ) + 1) * (4 * (n : ℝ) + 7) * (sq δ * Kh δ n)) := by
  unfold Qsmooth
  rw [cb_succ, Hh_succ]
  push_cast
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hn3 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- `r_{n+1}² Q_{n+1} − r_n² Q_n = C_n (1−x)(2n+1)(4n+5)/(8(n+1)) · (3 H_n − (2n+3)(4n+7) x K_n)`. -/
theorem rsq_Q_succ_sub (δ : ℝ) (n : ℕ) :
    semilocalArchimedeanJacobiCoefficient (n + 1) ^ 2 * Qsmooth δ (n + 1) -
        semilocalArchimedeanJacobiCoefficient n ^ 2 * Qsmooth δ n =
      cb n * (1 - sq δ) * (2 * (n : ℝ) + 1) * (4 * (n : ℝ) + 5) / (8 * ((n : ℝ) + 1)) *
        (3 * Hh δ n - (2 * (n : ℝ) + 3) * (4 * (n : ℝ) + 7) * (sq δ * Kh δ n)) := by
  rw [semilocalArchimedeanJacobiCoefficient_sq, semilocalArchimedeanJacobiCoefficient_sq]
  unfold Qsmooth
  rw [cb_succ, Hh_succ]
  push_cast
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn3 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
  field_simp
  ring

end RouteJProfile

end RHTower
