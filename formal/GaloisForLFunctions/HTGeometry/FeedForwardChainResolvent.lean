import GaloisForLFunctions.HTGeometry.FeedForwardGreenReachability
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite feed-forward resolvent and physical port columns

The geometric matrix is proved to be the two-sided inverse of the normalized
open-chain operator `I - q S`, for every complex `q`. Its physical port columns
are exactly the fields used in Theorem S4 of arXiv:2609.04996.
-/

open scoped BigOperators Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry


/-- Unit downstream shift with open boundaries. -/
def feedForwardChainShift (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i.val = j.val + 1 then 1 else 0

/-- Exact geometric Green matrix of a finite feed-forward chain. -/
def feedForwardChainGreen (N : ℕ) (q : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if j.val ≤ i.val then q ^ (i.val - j.val) else 0

/-- Normalized frequency-domain response operator. -/
def feedForwardChainOperator (N : ℕ) (q : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - q • feedForwardChainShift N

theorem feedForwardChainShift_mul_green (N : ℕ) (q : ℂ) (i j : Fin N) :
    (feedForwardChainShift N * feedForwardChainGreen N q) i j =
      if j.val < i.val then q ^ (i.val - j.val - 1) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i.val = 0
  · have hz : ∀ k : Fin N, feedForwardChainShift N i k = 0 := by
      intro k
      simp [feedForwardChainShift, hi]
    simp [hz, hi]
  let p : Fin N := ⟨i.val - 1, by have := i.isLt; omega⟩
  rw [Finset.sum_eq_single p]
  · have hp : i.val = p.val + 1 := by dsimp [p]; omega
    have hs : feedForwardChainShift N i p = 1 := by
      simp only [feedForwardChainShift, if_pos hp]
    rw [hs, one_mul]
    simp only [feedForwardChainGreen]
    by_cases hj : j.val < i.val
    · have hjp : j.val ≤ p.val := by omega
      have he : p.val - j.val = i.val - j.val - 1 := by omega
      rw [if_pos hjp, if_pos hj, he]
    · have hjp : ¬ j.val ≤ p.val := by omega
      rw [if_neg hjp, if_neg hj]
  · intro k _ hk
    have hne : i.val ≠ k.val + 1 := by
      intro h
      apply hk
      apply Fin.ext
      dsimp [p]
      omega
    simp [feedForwardChainShift, hne]
  · simp

/-- The geometric response is a genuine inverse, without any nonzero-hopping assumption. -/
theorem feedForwardChainOperator_mul_green (N : ℕ) (q : ℂ) :
    feedForwardChainOperator N q * feedForwardChainGreen N q = 1 := by
  rw [feedForwardChainOperator, sub_mul, one_mul, smul_mul_assoc]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    feedForwardChainShift_mul_green, feedForwardChainGreen, Matrix.one_apply]
  by_cases heq : i = j
  · subst j
    simp
  by_cases hlt : j.val < i.val
  · have hp : i.val - j.val = (i.val - j.val - 1) + 1 := by omega
    simp only [if_pos hlt.le, if_pos hlt, if_neg heq]
    rw [← pow_succ', ← hp, sub_self]
  · have hle : ¬ j.val ≤ i.val := by
      intro h
      exact heq (Fin.ext (by omega))
    simp [hle, hlt, heq]

theorem feedForwardChainGreen_mul_operator (N : ℕ) (q : ℂ) :
    feedForwardChainGreen N q * feedForwardChainOperator N q = 1 :=
  mul_eq_one_comm.mpr (feedForwardChainOperator_mul_green N q)

theorem feedForwardChainOperator_inverse (N : ℕ) (q : ℂ) :
    (feedForwardChainOperator N q)⁻¹ = feedForwardChainGreen N q :=
  Matrix.inv_eq_right_inv (feedForwardChainOperator_mul_green N q)

/-- Map interval coordinates into the physical finite chain. -/
def feedForwardPhysicalSite {m : ℕ} (n : ℕ → ℕ)
    (s : Σ i : Fin m, Fin (n i.val + 1)) : Fin (feedForwardPortStart n m) :=
  ⟨feedForwardPortStart n s.1.val + s.2.val, by
    have hp := feedForwardPortStart_monotone n (show s.1.val + 1 ≤ m by omega)
    rw [feedForwardPortStart_succ] at hp
    have ht := s.2.isLt
    omega⟩

/-- The previously isolated Green columns are exact columns of the finite chain's matrix inverse. -/
theorem feedForwardGreenColumn_eq_resolvent_column {m : ℕ} (q : ℂ) (n : ℕ → ℕ)
    (j : Fin m) (s : Σ i : Fin m, Fin (n i.val + 1)) :
    feedForwardGreenColumn q n j.val s =
      (feedForwardChainOperator (feedForwardPortStart n m) q)⁻¹
        (feedForwardPhysicalSite n s) (feedForwardPhysicalSite n ⟨j, 0⟩) := by
  rw [feedForwardChainOperator_inverse]
  simp only [feedForwardChainGreen, feedForwardPhysicalSite, Fin.val_zero, add_zero,
    feedForwardGreenColumn]
  by_cases hj : j.val ≤ s.1.val
  · have hp := feedForwardPortStart_monotone n hj
    simp [hj, show feedForwardPortStart n j.val ≤
      feedForwardPortStart n s.1.val + s.2.val by omega]
  · have hp := feedForwardPortStart_monotone n (show s.1.val + 1 ≤ j.val by omega)
    rw [feedForwardPortStart_succ] at hp
    have ht := s.2.isLt
    simp [hj, show ¬ feedForwardPortStart n j.val ≤
      feedForwardPortStart n s.1.val + s.2.val by omega]

end GaloisForLFunctions.HTGeometry
