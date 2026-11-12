import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBlockMatrixOfTheDegreesTheJetsAndTheFloorMaps
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Weil's form on step packets is the charges, a potential and a Dirichlet form

The block matrix is `d(a) + d(b)` plus a **neutral part** `N(a, b)` (`neutralBlock`): the density
on the diagonal, minus the jets, minus the contacts. A step packet `σ` on the blocks
`R, …, R + J − 1` has two **charges**, `c₀ = Σ σ_j` and `c₁ = Σ σ_j d(R + j)`, and

  `Σ σ_j σ_l m(R + j, R + l) = 2 c₀ c₁ + Σ_j V_j σ_j² + ½ Σ_{j,l} w_{jl} (σ_j − σ_l)²`

(`sum_blockMatrix_eq_charges_potential_dirichlet`), with the potential `V_j = Σ_l N(R + j, R + l)`
and the weights `w_{jl} = −N(R + j, R + l)`.

* **Jets and contacts attract**: `w_{jl} > 0` for `j ≠ l` (`blockWeight_pos`). The jets are
  positive because `x log x` is strictly convex (`xLogXDiff_pos`); they join every pair of blocks.
  The contacts join a block to its images under the floor maps.
* So the neutral part is a potential plus the Dirichlet form of a weighted graph on the blocks,
  and the form of the neutral part does not increase when `σ` is replaced by `|σ|`
  (`sum_neutralBlock_abs_le`).
* **The ground state representation** (`sum_sum_mul_eq_doob`): for a positive `v`,
  `Σ σ_j σ_l N_{jl} = Σ_j (σ_j²/v_j) (N v)_j + ½ Σ w_{jl} v_j v_l (σ_j/v_j − σ_l/v_l)²`.
* **A positive supersolution is a certificate on charge-free packets**
  (`sum_blockMatrix_ge_of_supersolution`): if `v > 0` and `N v ≥ c v`, then Weil's form is at
  least `c Σ σ_j²` on the step packets with `c₀ = 0` or `c₁ = 0`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Jets and contacts attract -/

/-- The second difference of `n log n` is positive: `x log x` is strictly convex. -/
theorem xLogXDiff_pos {n : ℕ} (hn : 1 ≤ n) : 0 < xLogXDiff n := by
  have hx : ((n - 1 : ℕ) : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (Nat.cast_nonneg _)
  have hy : ((n + 1 : ℕ) : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (Nat.cast_nonneg _)
  have hne : ((n - 1 : ℕ) : ℝ) ≠ ((n + 1 : ℕ) : ℝ) := by
    intro h
    have := Nat.cast_injective (R := ℝ) h
    omega
  have hconv := Real.strictConvexOn_mul_log.2
  have h := hconv hx hy hne (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • ((n - 1 : ℕ) : ℝ) + (1 / 2 : ℝ) • ((n + 1 : ℕ) : ℝ) = (n : ℝ) := by
    rw [smul_eq_mul, smul_eq_mul, Nat.cast_sub hn, Nat.cast_add, Nat.cast_one]
    ring
  rw [hmid] at h
  simp only [smul_eq_mul] at h
  unfold xLogXDiff xLogX
  linarith

/-- The neutral part of the block matrix: the block matrix without the degrees. -/
def neutralBlock (Q a b : ℕ) : ℝ :=
  blockMatrix Q a b - blockDegree a - blockDegree b

theorem neutralBlock_comm (Q a b : ℕ) : neutralBlock Q a b = neutralBlock Q b a := by
  unfold neutralBlock
  rw [blockMatrix_comm]
  ring

/-- **Jets and contacts attract**: off the diagonal the neutral part is negative. -/
theorem neutralBlock_neg_of_lt {a b : ℕ} (hab : a < b) (Q : ℕ) : neutralBlock Q a b < 0 := by
  rw [neutralBlock, blockMatrix_of_lt hab]
  have hJ : 0 < blockJet a b := by
    unfold blockJet
    have h1 := xLogXDiff_pos (n := a + b + 1) (by omega)
    have h2 := xLogXDiff_pos (n := b - a) (by omega)
    linarith
  have hC : 0 ≤ floorContact Q a b := Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    · exact le_rfl
  linarith

theorem neutralBlock_neg {a b : ℕ} (hab : a ≠ b) (Q : ℕ) : neutralBlock Q a b < 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact neutralBlock_neg_of_lt h Q
  · rw [neutralBlock_comm]
    exact neutralBlock_neg_of_lt h Q

/-- The weight of the pair of blocks `a`, `b`: the jets and the contacts between them. -/
def blockWeight (Q a b : ℕ) : ℝ := -neutralBlock Q a b

theorem blockWeight_pos {a b : ℕ} (hab : a ≠ b) (Q : ℕ) : 0 < blockWeight Q a b :=
  neg_pos.mpr (neutralBlock_neg hab Q)

/-- The potential of the block `R + j` among the blocks `R, …, R + J − 1`: the row sum of the
neutral part. -/
def blockPotential (Q R J j : ℕ) : ℝ := ∑ l ∈ range J, neutralBlock Q (R + j) (R + l)

/-! ### The form of a symmetric matrix -/

/-- **The form of a symmetric matrix is its row sums minus a sum over the pairs.** -/
theorem sum_sum_mul_eq_rowSum_sub_pairs {J : ℕ} (σ : ℕ → ℝ) (m : ℕ → ℕ → ℝ)
    (hm : ∀ j l, m j l = m l j) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * m j l =
      ∑ j ∈ range J, σ j ^ 2 * ∑ l ∈ range J, m j l -
        (1 / 2) * ∑ j ∈ range J, ∑ l ∈ range J, m j l * (σ j - σ l) ^ 2 := by
  have hswap : ∑ j ∈ range J, ∑ l ∈ range J, m j l * σ l ^ 2 =
      ∑ j ∈ range J, ∑ l ∈ range J, m j l * σ j ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [hm l j]
  have hexp : ∑ j ∈ range J, ∑ l ∈ range J, m j l * (σ j - σ l) ^ 2 =
      ∑ j ∈ range J, ∑ l ∈ range J, m j l * σ j ^ 2 -
        2 * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * m j l +
          ∑ j ∈ range J, ∑ l ∈ range J, m j l * σ l ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hrow : ∑ j ∈ range J, σ j ^ 2 * ∑ l ∈ range J, m j l =
      ∑ j ∈ range J, ∑ l ∈ range J, m j l * σ j ^ 2 :=
    Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, hswap, hrow]
  ring

/-- **The ground state representation** of the form of a symmetric matrix with respect to a
vector `v` without zero entries. -/
theorem sum_sum_mul_eq_doob {J : ℕ} (σ v : ℕ → ℝ) (m : ℕ → ℕ → ℝ) (hm : ∀ j l, m j l = m l j)
    (hv : ∀ j, j < J → v j ≠ 0) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * m j l =
      ∑ j ∈ range J, σ j ^ 2 / v j * ∑ l ∈ range J, m j l * v l -
        (1 / 2) * ∑ j ∈ range J, ∑ l ∈ range J,
          m j l * v j * v l * (σ j / v j - σ l / v l) ^ 2 := by
  have h := sum_sum_mul_eq_rowSum_sub_pairs (J := J) (fun j => σ j / v j)
    (fun j l => m j l * v j * v l) (fun j l => by rw [hm j l]; ring)
  have hL : ∑ j ∈ range J, ∑ l ∈ range J, σ j / v j * (σ l / v l) * (m j l * v j * v l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * m j l :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => by
      have hj' := hv j (Finset.mem_range.mp hj)
      have hl' := hv l (Finset.mem_range.mp hl)
      field_simp
  have hR : ∑ j ∈ range J, (σ j / v j) ^ 2 * ∑ l ∈ range J, m j l * v j * v l =
      ∑ j ∈ range J, σ j ^ 2 / v j * ∑ l ∈ range J, m j l * v l :=
    Finset.sum_congr rfl fun j hj => by
      have hj' := hv j (Finset.mem_range.mp hj)
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        field_simp
  rw [← hL, ← hR]
  exact h

/-! ### The block matrix -/

/-- The block matrix is the product of the two charges plus the neutral part. -/
theorem sum_blockMatrix_eq_charges_add_neutral (Q R J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) =
      2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) +
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  have h1 : (∑ j ∈ range J, σ j * blockDegree (R + j)) * (∑ l ∈ range J, σ l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * blockDegree (R + j) * σ l :=
    Finset.sum_mul_sum _ _ _ _
  have h2 : (∑ j ∈ range J, σ j) * (∑ l ∈ range J, σ l * blockDegree (R + l)) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * (σ l * blockDegree (R + l)) :=
    Finset.sum_mul_sum _ _ _ _
  rw [show 2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) =
      (∑ j ∈ range J, σ j * blockDegree (R + j)) * (∑ l ∈ range J, σ l) +
        (∑ j ∈ range J, σ j) * (∑ l ∈ range J, σ l * blockDegree (R + l)) by ring,
    h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by
    unfold neutralBlock
    ring

/-- **Weil's form on step packets: the product of the charges, a potential, and the Dirichlet
form of the jets and the floor maps.** -/
theorem sum_blockMatrix_eq_charges_potential_dirichlet (Q R J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) =
      2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) +
        ∑ j ∈ range J, σ j ^ 2 * blockPotential Q R J j +
          (1 / 2) * ∑ j ∈ range J, ∑ l ∈ range J,
            blockWeight Q (R + j) (R + l) * (σ j - σ l) ^ 2 := by
  rw [sum_blockMatrix_eq_charges_add_neutral,
    sum_sum_mul_eq_rowSum_sub_pairs σ (fun j l => neutralBlock Q (R + j) (R + l))
      (fun j l => neutralBlock_comm Q _ _)]
  have hw : ∑ j ∈ range J, ∑ l ∈ range J, blockWeight Q (R + j) (R + l) * (σ j - σ l) ^ 2 =
      -∑ j ∈ range J, ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) * (σ j - σ l) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by
      unfold blockWeight
      ring
  rw [hw]
  unfold blockPotential
  ring

/-- **The neutral part does not increase under the modulus.** -/
theorem sum_neutralBlock_abs_le (Q R J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, |σ j| * |σ l| * neutralBlock Q (R + j) (R + l) ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hjl : j = l
  · subst hjl
    rw [abs_mul_abs_self]
  · have hneg := neutralBlock_neg (show R + j ≠ R + l by omega) Q
    have habs : σ j * σ l ≤ |σ j| * |σ l| := by
      rw [← abs_mul]
      exact le_abs_self _
    nlinarith

/-- **A positive supersolution of the neutral part bounds Weil's form on charge-free step
packets.** -/
theorem sum_blockMatrix_ge_of_supersolution {Q R J : ℕ} {v : ℕ → ℝ} (hv : ∀ j, j < J → 0 < v j)
    {c : ℝ}
    (hsup : ∀ j, j < J → c * v j ≤ ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) * v l)
    {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range J, σ j = 0 ∨ ∑ j ∈ range J, σ j * blockDegree (R + j) = 0) :
    c * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  have hcharge : 2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J, σ j * blockDegree (R + j)) = 0 := by
    rcases hσ with h | h
    · rw [h, mul_zero, zero_mul]
    · rw [h, mul_zero]
  rw [sum_blockMatrix_eq_charges_add_neutral, hcharge, zero_add,
    sum_sum_mul_eq_doob σ v (fun j l => neutralBlock Q (R + j) (R + l))
      (fun j l => neutralBlock_comm Q _ _) (fun j hj => (hv j hj).ne')]
  have hpairs : ∑ j ∈ range J, ∑ l ∈ range J,
      neutralBlock Q (R + j) (R + l) * v j * v l * (σ j / v j - σ l / v l) ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => Finset.sum_nonpos fun l hl => ?_
    by_cases hjl : j = l
    · subst hjl
      rw [sub_self]
      simp
    · have hneg := neutralBlock_neg (show R + j ≠ R + l by omega) Q
      have hvj := hv j (Finset.mem_range.mp hj)
      have hvl := hv l (Finset.mem_range.mp hl)
      have h1 : neutralBlock Q (R + j) (R + l) * v j * v l ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hneg.le hvj.le) hvl.le
      exact mul_nonpos_of_nonpos_of_nonneg h1 (sq_nonneg _)
  have hrows : c * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, σ j ^ 2 / v j * ∑ l ∈ range J, neutralBlock Q (R + j) (R + l) * v l := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hvj := hv j (Finset.mem_range.mp hj)
    have h1 := hsup j (Finset.mem_range.mp hj)
    have h2 : 0 ≤ σ j ^ 2 / v j := div_nonneg (sq_nonneg _) hvj.le
    calc c * σ j ^ 2 = σ j ^ 2 / v j * (c * v j) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
