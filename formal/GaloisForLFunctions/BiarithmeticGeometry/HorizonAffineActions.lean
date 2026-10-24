import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-!+# The affine action with an absorbing horizon

An affine map `j ↦ a*j+b`, with positive multiplier, sends a basis cell to its image or to zero
when it leaves the horizon. No cell can re-enter. Hence truncation retains the affine semigroup
law, including the joint additive and multiplicative relation.
-/

noncomputable section

namespace GaloisForLFunctions.BiarithmeticGeometry

open Finset

/-- Signed cell data on the horizon `{0,...,N}`. -/
abbrev HorizonSpace (N : ℕ) := Fin (N + 1) → ℝ

/-- A cell outside the horizon is the zero vector. -/
def horizonCell (N j : ℕ) : HorizonSpace N := fun i => if i.val = j then 1 else 0

/-- Affine pushforward, with every cell beyond the horizon absorbed. -/
def horizonAffine (N : ℕ) (a : ℕ+) (b : ℕ) :
    HorizonSpace N →ₗ[ℝ] HorizonSpace N where
  toFun v := ∑ j : Fin (N + 1), v j • horizonCell N (a * j.val + b)
  map_add' v w := by simp only [Pi.add_apply, add_smul, sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem horizonCell_eq_zero (N j : ℕ) :
    N < j → horizonCell N j = 0 := by
  intro hj
  funext i
  simp only [horizonCell, Pi.zero_apply]
  exact if_neg (by omega)

theorem horizonAffine_cell (N : ℕ) (a : ℕ+) (b : ℕ) (j : Fin (N + 1)) :
    horizonAffine N a b (horizonCell N j.val) = horizonCell N (a * j.val + b) := by
  classical
  change (∑ k : Fin (N + 1), (if k.val = j.val then (1 : ℝ) else 0) •
    horizonCell N (a * k.val + b)) = _
  simp only [Fin.val_inj, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, if_true]

/-- Every signed row is recovered from its cell coefficients. -/
theorem sum_horizonCell (N : ℕ) (v : HorizonSpace N) :
    (∑ j : Fin (N + 1), v j • horizonCell N j.val) = v := by
  classical
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, horizonCell, Fin.val_inj,
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]

/-- Once an affine image leaves the horizon, every subsequent positive affine map does too. -/
theorem horizonAffine_cell_nat (N : ℕ) (a : ℕ+) (b j : ℕ) :
    horizonAffine N a b (horizonCell N j) = horizonCell N (a * j + b) := by
  by_cases hj : j ≤ N
  · exact horizonAffine_cell N a b ⟨j, by omega⟩
  · have haj : j ≤ (a : ℕ) * j := by
      exact (Nat.le_mul_of_pos_left j a.pos)
    rw [horizonCell_eq_zero N j (by omega), map_zero,
      horizonCell_eq_zero N (a * j + b) (by omega)]

/-- Exact affine composition survives the finite horizon. -/
theorem horizonAffine_comp (N : ℕ) (a c : ℕ+) (b d : ℕ) :
    (horizonAffine N a b).comp (horizonAffine N c d) =
      horizonAffine N (a * c) (a * d + b) := by
  apply LinearMap.ext
  intro v
  funext i
  change (horizonAffine N a b (∑ j : Fin (N + 1),
    v j • horizonCell N (c * j.val + d))) i = _
  rw [map_sum]
  simp only [map_smul, horizonAffine_cell_nat]
  change (∑ j : Fin (N + 1), v j • horizonCell N (a * (c * j.val + d) + b)) i =
    (∑ j : Fin (N + 1), v j • horizonCell N ((a * c : ℕ+) * j.val + (a * d + b))) i
  congr 1
  apply sum_congr rfl
  intro j _
  congr 2
  change (a : ℕ) * ((c : ℕ) * j.val + d) + b =
    ((a : ℕ) * c) * j.val + (a * d + b)
  ring

theorem horizonAffine_one_zero (N : ℕ) :
    horizonAffine N 1 0 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  change (∑ j : Fin (N + 1), v j • horizonCell N ((1 : ℕ+) * j.val + 0)) i = v i
  simpa only [PNat.val_ofNat, one_mul, add_zero] using congrFun (sum_horizonCell N v) i

/-- Dilation followed by one successor equals `a` successors followed by dilation. -/
theorem horizon_ring_relation (N : ℕ) (a : ℕ+) :
    (horizonAffine N a 0).comp (horizonAffine N 1 1) =
      (horizonAffine N 1 a).comp (horizonAffine N a 0) := by
  simp only [horizonAffine_comp, mul_one, one_mul, mul_zero, add_zero, zero_add]

end GaloisForLFunctions.BiarithmeticGeometry
