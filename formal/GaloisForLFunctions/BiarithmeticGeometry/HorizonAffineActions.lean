import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Ring

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
  apply congrArg (fun w : HorizonSpace N => w i)
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

theorem horizonAffine_apply (N : ℕ) (a : ℕ+) (b : ℕ)
    (v : HorizonSpace N) (i : Fin (N + 1)) :
    horizonAffine N a b v i =
      ∑ j : Fin (N + 1), v j * (if i.val = (a : ℕ) * j.val + b then 1 else 0) := by
  simp only [horizonAffine, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, horizonCell]

/-- Dyadic dilation keeps precisely the even cells, without any periodic wraparound. -/
theorem horizon_double_apply (N : ℕ) (v : HorizonSpace N) (i : Fin (N + 1)) :
    horizonAffine N 2 0 v i =
      if 2 ∣ i.val then v ⟨i.val / 2, by omega⟩ else 0 := by
  classical
  rw [horizonAffine_apply]
  change (∑ j : Fin (N + 1), v j * (if i.val = 2 * j.val then 1 else 0)) = _
  by_cases hi : 2 ∣ i.val
  · rw [if_pos hi]
    have he : i.val = 2 * (i.val / 2) := by omega
    rw [Finset.sum_eq_single ⟨i.val / 2, by omega⟩]
    · rw [if_pos he, mul_one]
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro heq
      apply hj
      apply Fin.ext
      dsimp
      omega
    · exact fun h => False.elim (h (mem_univ _))
  · rw [if_neg hi]
    apply sum_eq_zero
    intro j _
    rw [if_neg, mul_zero]
    exact fun heq => hi ⟨j.val, heq⟩

/-- The origin is the entire fixed space of dyadic dilation at a finite horizon. -/
theorem horizon_double_fixed_iff (N : ℕ) (v : HorizonSpace N) :
    horizonAffine N 2 0 v = v ↔ v = v 0 • horizonCell N 0 := by
  constructor
  · intro hv
    have hz : ∀ n : ℕ, ∀ hn : n < N + 1, 0 < n → v ⟨n, hn⟩ = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn hn0
        have he := congrFun hv ⟨n, hn⟩
        rw [horizon_double_apply] at he
        by_cases hd : 2 ∣ n
        · rw [if_pos hd] at he
          have hk0 : 0 < n / 2 := by omega
          have hkn : n / 2 < n := by omega
          exact he.symm.trans (ih (n / 2) hkn (by omega) hk0)
        · rw [if_neg hd] at he
          exact he.symm
    funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      simp only [Pi.smul_apply, smul_eq_mul, horizonCell, Fin.val_zero, if_true, mul_one]
    · simp only [Pi.smul_apply, smul_eq_mul, horizonCell, if_neg hi, mul_zero]
      exact hz i.val i.isLt (by omega)
  · intro hv
    rw [hv, map_smul, horizonAffine_cell_nat]
    rfl

/-- Successor and dyadic dilation have scalar common commutant on every finite horizon. -/
theorem horizon_joint_commutant (N : ℕ) (A : HorizonSpace N →ₗ[ℝ] HorizonSpace N) :
    (A.comp (horizonAffine N 1 1) = (horizonAffine N 1 1).comp A ∧
      A.comp (horizonAffine N 2 0) = (horizonAffine N 2 0).comp A) ↔
        ∃ c : ℝ, A = c • LinearMap.id := by
  constructor
  · rintro ⟨hu, hd⟩
    let c : ℝ := A (horizonCell N 0) 0
    have hfix : horizonAffine N 2 0 (A (horizonCell N 0)) = A (horizonCell N 0) := by
      have h := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
        L (horizonCell N 0)) hd
      simpa only [LinearMap.comp_apply, horizonAffine_cell_nat,
        mul_zero, add_zero] using h.symm
    have hbase : A (horizonCell N 0) = c • horizonCell N 0 :=
      (horizon_double_fixed_iff N _).mp hfix
    have hcell : ∀ j : ℕ, A (horizonCell N j) = c • horizonCell N j := by
      intro j
      induction j with
      | zero => exact hbase
      | succ j ih =>
        have h := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N =>
          L (horizonCell N j)) hu
        have hshift : horizonAffine N 1 1 (horizonCell N j) = horizonCell N (j + 1) := by
          simpa only [PNat.val_ofNat, one_mul] using horizonAffine_cell_nat N 1 1 j
        simpa only [LinearMap.comp_apply, hshift, ih, map_smul] using h
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro v
    change A v = c • v
    calc
      A v = A (∑ j : Fin (N + 1), v j • horizonCell N j.val) :=
        congrArg A (sum_horizonCell N v).symm
      _ = ∑ j : Fin (N + 1), v j • A (horizonCell N j.val) := by
        rw [map_sum]
        simp only [map_smul]
      _ = c • (∑ j : Fin (N + 1), v j • horizonCell N j.val) := by
        rw [Finset.smul_sum]
        apply sum_congr rfl
        intro j _
        rw [hcell]
        exact smul_comm _ _ _
      _ = c • v := congrArg (fun w => c • w) (sum_horizonCell N v)
  · rintro ⟨c, rfl⟩
    constructor <;> apply LinearMap.ext <;> intro v <;>
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

end GaloisForLFunctions.BiarithmeticGeometry
