import GaloisForLFunctions.RHTower.DeningerRationalWittHazewinkelHankel
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Rev

/-!
# Counterexample to the additive stage bound for big-Witt multiplication

Deninger, arXiv:2508.05329v1, equation (15), Lemma 2.6, and Theorem 2.8 state that
both Witt addition and Witt multiplication map stages `(n,m)` to stage `n+m`.
The multiplication bound is false.

This module proves a complete symbolic counterexample over `ℤ`.  Let `E_r` be the ordinary
power-series product of `r` copies of the Teichmüller vector `[1]`.  Then

* `E_r` has exact Hazewinkel stage `r+1`;
* `E_r ⊙ E_s = E_(r*s)` for canonical big-Witt multiplication;
* hence `E_2` and `E_4` have stages `3` and `5`, while their product `E_8` has exact stage `9`,
  contradicting the asserted target stage `3+5=8`.

Exact stage is certified without computation: the series is `(1-T)^r`, all coefficients above
degree `r` vanish, and the reversed top Hankel minor is triangular with nonzero diagonal
coefficient `(-1)^r`.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

def deningerTeichOnePacket (n : ℕ) : DeningerBigWittAdditive ℤ :=
  deningerBigWittTeichCarrier (1 : ℤ) ^ n

def deningerTeichOnePolynomial (n : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.X) ^ n

theorem deningerTeichOnePacket_series (n : ℕ) :
    deningerBigWittSeries (deningerTeichOnePacket n) =
      (deningerTeichOnePolynomial n : PowerSeries ℤ) := by
  induction n with
  | zero => simp [deningerTeichOnePacket, deningerTeichOnePolynomial,
      deningerBigWittSeries]
  | succ n ih =>
      rw [deningerTeichOnePacket, pow_succ]
      change deningerBigWittSeries (deningerTeichOnePacket n *
        deningerBigWittTeichCarrier (1 : ℤ)) = _
      change deningerBigWittSeries (deningerTeichOnePacket n) *
        deningerBigWittSeries (deningerBigWittTeichCarrier (1 : ℤ)) = _
      rw [ih, deningerBigWittSeries_teichCarrier]
      simp [deningerTeichOnePolynomial, pow_succ, deningerBigWittFactor]

theorem deningerBigWittMul_teichOnePacket (n m : ℕ) :
    deningerBigWittMul (deningerTeichOnePacket n) (deningerTeichOnePacket m) =
      deningerTeichOnePacket (n * m) := by
  induction n with
  | zero => simp [deningerTeichOnePacket, deningerBigWittZero_mul]
  | succ n ih =>
      rw [Nat.succ_mul, deningerTeichOnePacket, pow_succ,
        deningerBigWittAdd_mul]
      change deningerBigWittMul (deningerTeichOnePacket n)
          (deningerTeichOnePacket m) *
        deningerBigWittMul (deningerBigWittTeichCarrier (1 : ℤ))
          (deningerTeichOnePacket m) = deningerTeichOnePacket (n * m + m)
      rw [ih]
      have hone : deningerBigWittTeichCarrier (1 : ℤ) = deningerBigWittOne ℤ :=
        deningerBigWittTeichCarrier_one
      rw [hone, deningerBigWittOne_mul]
      simp [deningerTeichOnePacket, pow_add]

theorem deningerTeichOnePolynomial_natDegree (n : ℕ) :
    (deningerTeichOnePolynomial n).natDegree = n := by
  have hbase : (1 - Polynomial.X : Polynomial ℤ) =
      -(Polynomial.X - Polynomial.C 1) := by
    simp [sub_eq_add_neg, add_comm]
  rw [deningerTeichOnePolynomial, hbase, Polynomial.natDegree_pow,
    Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  omega

theorem deningerTeichOnePolynomial_coeff_self (n : ℕ) :
    (deningerTeichOnePolynomial n).coeff n = (-1 : ℤ) ^ n := by
  have hd := deningerTeichOnePolynomial_natDegree n
  calc
    (deningerTeichOnePolynomial n).coeff n =
        (deningerTeichOnePolynomial n).coeff
          (deningerTeichOnePolynomial n).natDegree := by rw [hd]
    _ = (deningerTeichOnePolynomial n).leadingCoeff := Polynomial.coeff_natDegree
    _ = (-1 : ℤ) ^ n := by
      have hbase : (1 - Polynomial.X : Polynomial ℤ) =
          -(Polynomial.X - Polynomial.C 1) := by
        simp [sub_eq_add_neg, add_comm]
      have hlead : (1 - Polynomial.X : Polynomial ℤ).leadingCoeff = -1 := by
        rw [hbase, Polynomial.leadingCoeff_neg,
          Polynomial.leadingCoeff_X_sub_C]
      rw [deningerTeichOnePolynomial, Polynomial.leadingCoeff_pow, hlead]

theorem deningerTeichOnePacket_coeff_eq_zero_of_lt
    (n r : ℕ) (h : n < r) :
    PowerSeries.coeff r (deningerBigWittSeries (deningerTeichOnePacket n)) = 0 := by
  rw [deningerTeichOnePacket_series, Polynomial.coeff_coe]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simpa [deningerTeichOnePolynomial_natDegree] using h

theorem deningerTeichOnePacket_coeff_self (n : ℕ) :
    PowerSeries.coeff n (deningerBigWittSeries (deningerTeichOnePacket n)) =
      (-1 : ℤ) ^ n := by
  rw [deningerTeichOnePacket_series, Polynomial.coeff_coe,
    deningerTeichOnePolynomial_coeff_self]

theorem hankelColumnGenerated_of_eq_zero_ge
    {A : Type*} [CommRing A] (a : ℕ → A) (d : ℕ)
    (hzero : ∀ n : ℕ, d ≤ n → a n = 0) :
    DeningerHankelColumnGenerated a d := by
  intro j
  by_cases hj : j < d
  · let tj : Fin d := ⟨j, hj⟩
    refine ⟨fun t => if t = tj then 1 else 0, ?_⟩
    intro i
    simp [tj]
  · refine ⟨0, ?_⟩
    intro i
    rw [hzero (i + j) (le_add_left (Nat.le_of_not_gt hj))]
    simp
theorem deningerTeichOnePacket_rankLT_succ_succ (n : ℕ) :
    DeningerBigWittHankelRankLT (n + 2) (deningerTeichOnePacket n) := by
  intro rows cols
  change (Matrix.submatrix
    (fun i j => PowerSeries.coeff (i + j)
      (deningerBigWittSeries (deningerTeichOnePacket n))) rows cols).det = 0
  let a : ℕ → ℤ := fun r => PowerSeries.coeff r
    (deningerBigWittSeries (deningerTeichOnePacket n))
  have hzero : ∀ r : ℕ, n + 1 ≤ r → a r = 0 := by
    intro r hr
    apply deningerTeichOnePacket_coeff_eq_zero_of_lt
    omega
  have hcol : DeningerHankelColumnGenerated a (n + 1) :=
    hankelColumnGenerated_of_eq_zero_ge a (n + 1) hzero
  exact hankelRankLT_succ_of_columnGenerated a (n + 1) hcol rows cols

def deningerTeichOnePacketTopMinor (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  (deningerBigWittHankel (deningerTeichOnePacket n)).submatrix
    (fun i => i.val) (fun j => j.val)

theorem deningerTeichOnePacketTopMinor_reverseRows_lowerTriangular (n : ℕ) :
    ((deningerTeichOnePacketTopMinor n).submatrix Fin.rev id).BlockTriangular
      (fun i : Fin (n + 1) => OrderDual.toDual i) := by
  intro i j hij
  change PowerSeries.coeff ((Fin.rev i).val + j.val)
    (deningerBigWittSeries (deningerTeichOnePacket n)) = 0
  apply deningerTeichOnePacket_coeff_eq_zero_of_lt
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  have hijval : i.val < j.val := hij'
  simp only [Fin.rev]
  omega

theorem deningerTeichOnePacketTopMinor_reverseRows_diagonal
    (n : ℕ) (i : Fin (n + 1)) :
    (deningerTeichOnePacketTopMinor n).submatrix Fin.rev id i i =
      (-1 : ℤ) ^ n := by
  change PowerSeries.coeff ((Fin.rev i).val + i.val)
    (deningerBigWittSeries (deningerTeichOnePacket n)) = (-1 : ℤ) ^ n
  have hindex : (Fin.rev i).val + i.val = n := by
    simp only [Fin.rev]
    omega
  rw [hindex, deningerTeichOnePacket_coeff_self]

theorem deningerTeichOnePacketTopMinor_reverseRows_det (n : ℕ) :
    ((deningerTeichOnePacketTopMinor n).submatrix Fin.rev id).det =
      ((-1 : ℤ) ^ n) ^ (n + 1) := by
  rw [Matrix.det_of_lowerTriangular _
    (deningerTeichOnePacketTopMinor_reverseRows_lowerTriangular n)]
  simp_rw [deningerTeichOnePacketTopMinor_reverseRows_diagonal]
  simp

theorem deningerTeichOnePacketTopMinor_det_ne_zero (n : ℕ) :
    (deningerTeichOnePacketTopMinor n).det ≠ 0 := by
  intro hzero
  have hp := Matrix.det_permute
    (Fin.revPerm : Equiv.Perm (Fin (n + 1))) (deningerTeichOnePacketTopMinor n)
  rw [hzero, mul_zero] at hp
  have hfun : ((Fin.revPerm : Equiv.Perm (Fin (n + 1))) :
      Fin (n + 1) → Fin (n + 1)) = Fin.rev := by
    funext i
    rfl
  rw [hfun, deningerTeichOnePacketTopMinor_reverseRows_det] at hp
  have hne : ((-1 : ℤ) ^ n) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  exact hne hp

theorem deningerTeichOnePacket_not_rankLT_succ (n : ℕ) :
    ¬ DeningerBigWittHankelRankLT (n + 1) (deningerTeichOnePacket n) := by
  intro h
  have hminor := h (fun i : Fin (n + 1) => i.val) (fun j : Fin (n + 1) => j.val)
  exact deningerTeichOnePacketTopMinor_det_ne_zero n hminor

theorem deningerTeichOnePacket_exact_Hazewinkel_stage (n : ℕ) :
    DeningerBigWittHankelRankLT (n + 2) (deningerTeichOnePacket n) ∧
      ¬ DeningerBigWittHankelRankLT (n + 1) (deningerTeichOnePacket n) :=
  ⟨deningerTeichOnePacket_rankLT_succ_succ n,
    deningerTeichOnePacket_not_rankLT_succ n⟩

theorem deningerHazewinkel_wittMul_stage_add_counterexample :
    ∃ u v : DeningerBigWittAdditive ℤ,
      DeningerBigWittHankelRankLT 4 u ∧
      DeningerBigWittHankelRankLT 6 v ∧
      ¬ DeningerBigWittHankelRankLT 9 (deningerBigWittMul u v) := by
  refine ⟨deningerTeichOnePacket 2, deningerTeichOnePacket 4, ?_, ?_, ?_⟩
  · simpa using deningerTeichOnePacket_rankLT_succ_succ 2
  · simpa using deningerTeichOnePacket_rankLT_succ_succ 4
  · rw [deningerBigWittMul_teichOnePacket]
    simpa using deningerTeichOnePacket_not_rankLT_succ 8

end
end RHTower
