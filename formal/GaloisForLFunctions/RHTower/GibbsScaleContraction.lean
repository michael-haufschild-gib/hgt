import Mathlib
import GaloisForLFunctions.RHTower.GibbsClusterRepulsion

/-!
# Cancellation as a two-scale contraction

Adjoining a prime differences the current across the dilated pair of couplings while
*averaging* the partition function over them:

  `J_{S∪p}(x) = J_S(x) − J_S(px)`,     `Z_{S∪p}(x) = Z_S(x) + Z_S(px)`.

Hence the normalized current `ψ_S = J_S / Z_S` is non-expansive: a uniform bound at the two
scales passes to the enlarged set.  And when the normalized current is *scale invariant*
across the dilation, adjoining the prime contracts it by the explicit factor

  `(Z_S(x) − Z_S(px)) / (Z_S(x) + Z_S(px))`,

which is where the parity cancellation of a Möbius–Laplace sum is manufactured.
-/

namespace RHTower.GibbsGas

open Real

/-- The partition function averages across the dilated pair. -/
theorem gibbs_partition_insert (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsDiag (insert p S) x 1
      = gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 := by
  rw [gibbsDiag_insert p S hp]
  ring

/-- The partition function is positive. -/
theorem gibbs_partition_pos (S : Finset ℕ) (x : ℝ) : 0 < gibbsDiag S x 1 := by
  rw [gibbsDiag]
  refine Finset.sum_pos (fun T _ => ?_) ⟨∅, by simp⟩
  positivity

/-- The partition function strictly decreases in the coupling. -/
theorem gibbs_partition_strict_anti (S : Finset ℕ) {y y' : ℝ} (h : y < y') :
    gibbsDiag S y' 1 < gibbsDiag S y 1 := by
  classical
  rw [gibbsDiag, gibbsDiag]
  refine Finset.sum_lt_sum (fun T _ => ?_) ⟨∅, Finset.empty_mem_powerset S, ?_⟩
  · have hT : (0 : ℝ) ≤ ∏ q ∈ T, (q : ℝ) :=
      Finset.prod_nonneg fun q _ => Nat.cast_nonneg q
    have hexp : Real.exp (-(y' * ∏ q ∈ T, (q : ℝ)))
        ≤ Real.exp (-(y * ∏ q ∈ T, (q : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hT]
    simp only [one_pow, one_mul]
    exact hexp
  · simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, one_mul]
    exact Real.exp_lt_exp.mpr (by linarith)

/-- **Non-expansiveness.**  A uniform bound on the normalized current at the two dilated
couplings passes to the enlarged prime set. -/
theorem normalized_current_nonexpansive (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x M : ℝ)
    (h1 : |gibbsDiag S x (-1)| ≤ M * gibbsDiag S x 1)
    (h2 : |gibbsDiag S ((p : ℝ) * x) (-1)| ≤ M * gibbsDiag S ((p : ℝ) * x) 1) :
    |gibbsDiag (insert p S) x (-1)| ≤ M * gibbsDiag (insert p S) x 1 := by
  rw [gibbs_current_insert p S hp, gibbs_partition_insert p S hp]
  calc |gibbsDiag S x (-1) - gibbsDiag S ((p : ℝ) * x) (-1)|
      ≤ |gibbsDiag S x (-1)| + |gibbsDiag S ((p : ℝ) * x) (-1)| := abs_sub _ _
    _ ≤ M * gibbsDiag S x 1 + M * gibbsDiag S ((p : ℝ) * x) 1 := add_le_add h1 h2
    _ = M * (gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1) := by ring

/-- **The contraction.**  If the normalized current is scale invariant across the dilation,
adjoining the prime multiplies it by `(Z_S(x) − Z_S(px)) / (Z_S(x) + Z_S(px))`. -/
theorem normalized_current_contraction (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ)
    (hinv : gibbsDiag S x (-1) * gibbsDiag S ((p : ℝ) * x) 1
      = gibbsDiag S ((p : ℝ) * x) (-1) * gibbsDiag S x 1) :
    gibbsDiag (insert p S) x (-1) * gibbsDiag S x 1
      = gibbsDiag S x (-1) * (gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1) := by
  rw [gibbs_current_insert p S hp]
  linear_combination hinv

/-- The contraction is strict: at a dilated coupling the partition function is smaller. -/
theorem contraction_factor_lt_one (p : ℕ) (S : Finset ℕ) (x : ℝ) (hx : 0 < x)
    (hp : 2 ≤ p) :
    gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1 < gibbsDiag S x 1
      ∧ 0 < gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1 := by
  have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlt : x < (p : ℝ) * x := by nlinarith
  have hZ := gibbs_partition_strict_anti S hlt
  have hpos := gibbs_partition_pos S ((p : ℝ) * x)
  exact ⟨by linarith, by linarith⟩

/-- **The exact decomposition.**  Adjoining a prime splits the current into the
scale-invariant contraction plus the scale-invariance defect

  `Δ = J_S(px)·Z_S(x) − J_S(x)·Z_S(px)`,

which vanishes exactly when the normalized current is scale invariant.  All cancellation
beyond the contraction is carried by `Δ`. -/
theorem normalized_current_decomposition (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsDiag (insert p S) x (-1) * gibbsDiag S x 1
      = gibbsDiag S x (-1) * (gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1)
        - (gibbsDiag S ((p : ℝ) * x) (-1) * gibbsDiag S x 1
            - gibbsDiag S x (-1) * gibbsDiag S ((p : ℝ) * x) 1) := by
  rw [gibbs_current_insert p S hp]
  ring

end RHTower.GibbsGas
