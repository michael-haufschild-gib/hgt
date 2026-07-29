import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal
import Mathlib.Data.Nat.Squarefree

/-!
# Global squarefree-times-square carrier

This module formalizes the classical global index change underlying the
squarefree/dyadic Euler source.  Every positive integer has a unique
decomposition

`n = m² d`, with `d` squarefree.

The induced equivalence sends the logarithmic Euler cutoff to the affine
joint cutoff

`log d + 2 log m < T`.

These are source-side connector theorems.  They contain no Xi divisor and
make no RH claim.
-/

namespace RHTower

/-- Uniqueness of the positive squarefree-times-square decomposition. -/
theorem squarefree_square_decomposition_unique
    {d m d' m' : ℕ}
    (hd0 : d ≠ 0) (hm0 : m ≠ 0) (hd'0 : d' ≠ 0) (hm'0 : m' ≠ 0)
    (hd : Squarefree d) (hd' : Squarefree d')
    (h : m ^ 2 * d = m' ^ 2 * d') :
    d = d' ∧ m = m' := by
  have hfac (p : ℕ) :
      2 * m.factorization p + d.factorization p =
        2 * m'.factorization p + d'.factorization p := by
    have hp := congrArg (fun n : ℕ => n.factorization p) h
    rw [Nat.factorization_mul (pow_ne_zero _ hm0) hd0,
      Nat.factorization_mul (pow_ne_zero _ hm'0) hd'0,
      Nat.factorization_pow, Nat.factorization_pow] at hp
    change 2 * m.factorization p + d.factorization p =
      2 * m'.factorization p + d'.factorization p at hp
    omega
  have hdfac : d.factorization = d'.factorization := by
    ext p
    have hle := hd.natFactorization_le_one p
    have hle' := hd'.natFactorization_le_one p
    have hp := hfac p
    omega
  have hdd' : d = d' :=
    Nat.eq_of_factorization_eq hd0 hd'0
      (fun p => congrFun (congrArg DFunLike.coe hdfac) p)
  subst d'
  have hsquares : m ^ 2 = m' ^ 2 := by
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd0) h
  exact ⟨rfl, Nat.pow_left_injective (by norm_num) hsquares⟩

/-- Positive squarefree integers, used as the first global carrier. -/
abbrev SquarefreePNat := {d : ℕ+ // Squarefree (d : ℕ)}

/-- Chosen positive squarefree-times-square data for one positive integer. -/
noncomputable def dyadicSquarefreeSquareData (n : ℕ+) :
    {p : ℕ × ℕ // 0 < p.1 ∧ 0 < p.2 ∧ p.2 ^ 2 * p.1 = n ∧ Squarefree p.1} := by
  let d := Classical.choose (Nat.sq_mul_squarefree_of_pos n.property)
  let m := Classical.choose
    (Classical.choose_spec (Nat.sq_mul_squarefree_of_pos n.property))
  have hdm := Classical.choose_spec
    (Classical.choose_spec (Nat.sq_mul_squarefree_of_pos n.property))
  exact ⟨(d, m), hdm.1, hdm.2.1, hdm.2.2.1, hdm.2.2.2⟩

/-- Global source index equivalence `n ↔ (squarefree part, square root of square part)`. -/
noncomputable def dyadicSquarefreeSquareEquiv :
    ℕ+ ≃ SquarefreePNat × ℕ+ where
  toFun n :=
    (⟨⟨(dyadicSquarefreeSquareData n).1.1,
          (dyadicSquarefreeSquareData n).2.1⟩,
        (dyadicSquarefreeSquareData n).2.2.2.2⟩,
      ⟨(dyadicSquarefreeSquareData n).1.2,
        (dyadicSquarefreeSquareData n).2.2.1⟩)
  invFun p :=
    ⟨(p.2 : ℕ) ^ 2 * (p.1.1 : ℕ),
      mul_pos (pow_pos p.2.property _) p.1.1.property⟩
  left_inv n := by
    apply Subtype.ext
    exact (dyadicSquarefreeSquareData n).2.2.2.1
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      let data := dyadicSquarefreeSquareData
        ⟨(p.2 : ℕ) ^ 2 * (p.1.1 : ℕ),
          mul_pos (pow_pos p.2.property _) p.1.1.property⟩
      have hu := squarefree_square_decomposition_unique
        data.2.1.ne' data.2.2.1.ne' p.1.1.property.ne' p.2.property.ne'
        data.2.2.2.2 p.1.2
        (data.2.2.2.1.trans rfl)
      exact hu.1
    · apply Subtype.ext
      let data := dyadicSquarefreeSquareData
        ⟨(p.2 : ℕ) ^ 2 * (p.1.1 : ℕ),
          mul_pos (pow_pos p.2.property _) p.1.1.property⟩
      have hu := squarefree_square_decomposition_unique
        data.2.1.ne' data.2.2.1.ne' p.1.1.property.ne' p.2.property.ne'
        data.2.2.2.2 p.1.2
        (data.2.2.2.1.trans rfl)
      exact hu.2

/-- Multiplicative reconstruction under the global carrier equivalence. -/
theorem dyadicSquarefreeSquareEquiv_mul
    (n : ℕ+) :
    ((dyadicSquarefreeSquareEquiv n).2 : ℕ) ^ 2 *
        ((dyadicSquarefreeSquareEquiv n).1.1 : ℕ) = n := by
  exact (dyadicSquarefreeSquareData n).2.2.2.1

/-- The Euler logarithmic clock becomes the sum of the squarefree clock and twice the residual
square clock. -/
theorem dyadicSquarefreeSquareEquiv_log
    (n : ℕ+) :
    Real.log (n : ℝ) =
      Real.log ((dyadicSquarefreeSquareEquiv n).1.1 : ℝ) +
        2 * Real.log ((dyadicSquarefreeSquareEquiv n).2 : ℝ) := by
  have heq := congrArg (fun k : ℕ => Real.log (k : ℝ))
    (dyadicSquarefreeSquareEquiv_mul n)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow] at heq
  · calc
      Real.log (n : ℝ) =
          2 * Real.log ((dyadicSquarefreeSquareEquiv n).2 : ℝ) +
            Real.log ((dyadicSquarefreeSquareEquiv n).1.1 : ℝ) := heq.symm
      _ = _ := by ring
  · positivity
  · positivity

/-- Exact covariance of every sharp logarithmic cutoff under the global carrier equivalence. -/
theorem dyadicSquarefreeSquareEquiv_affineCutoff
    (T : ℝ) (n : ℕ+) :
    Real.log (n : ℝ) < T ↔
      Real.log ((dyadicSquarefreeSquareEquiv n).1.1 : ℝ) +
        2 * Real.log ((dyadicSquarefreeSquareEquiv n).2 : ℝ) < T := by
  rw [dyadicSquarefreeSquareEquiv_log]

end RHTower
