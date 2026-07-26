/-
# Gaussian clustering for Bourgain's double large sieve

The Bombieri--Iwaniec double-large-sieve argument bounds a smooth pair
energy by a sharp coordinatewise spacing energy.  This file proves that
clustering step directly with an explicit Gaussian majorant.

Each real coordinate is placed in a half-unit floor cell.  Gaussian decay
is dominated by a bilateral half-geometric kernel.  Its exact row mass is
three, so the four-dimensional Schur constant is `3^4 = 81`.  Equal floor
cells are coordinatewise near.  All sums are finite and all constants are
explicit.
-/
import GaloisForLFunctions.RHTower.BourgainGaussianSpacing
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Bilateral half-geometric kernel on the integers. -/
def bourgainHalfGeometric (m : ℤ) : ℝ :=
  ((1 : ℝ) / 2) ^ m.natAbs

theorem summable_bourgainHalfGeometric :
    Summable bourgainHalfGeometric := by
  rw [summable_int_iff_summable_nat_and_neg_add_zero]
  constructor
  · simpa [bourgainHalfGeometric] using summable_geometric_two
  · apply (summable_geometric_two.mul_left ((1 : ℝ) / 2)).congr
    intro n
    rw [bourgainHalfGeometric, Int.natAbs_neg]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
    rw [Int.natAbs_natCast, pow_succ, mul_comm]

/-- Exact bilateral row mass `1 + 2(1/2 + 1/4 + ...) = 3`. -/
theorem tsum_bourgainHalfGeometric :
    ∑' m : ℤ, bourgainHalfGeometric m = 3 := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (fun m => by
      unfold bourgainHalfGeometric
      rw [Int.natAbs_neg])
    summable_bourgainHalfGeometric]
  have hp :
      (∑' n : ℕ+, ((1 : ℝ) / 2) ^ (n : ℕ)) = 1 := by
    have hzero := tsum_zero_pnat_eq_tsum_nat summable_geometric_two
    norm_num [tsum_geometric_two] at hzero ⊢
    linarith
  simp_rw [bourgainHalfGeometric, Int.natAbs_natCast]
  rw [hp]
  norm_num

theorem sum_bourgainHalfGeometric_sub_le
    (s : Finset ℤ) (k : ℤ) :
    ∑ l ∈ s, bourgainHalfGeometric (k - l) ≤ 3 := by
  have hs :
      Summable fun l : ℤ => bourgainHalfGeometric (k - l) := by
    apply summable_bourgainHalfGeometric.comp_injective
    intro a b hab
    omega
  refine (hs.sum_le_tsum s (fun l hl => by
    unfold bourgainHalfGeometric
    positivity)).trans_eq ?_
  have hreindex :=
    (Equiv.subRight k).tsum_eq bourgainHalfGeometric
  rw [show (fun l : ℤ => bourgainHalfGeometric (k - l)) =
      fun l : ℤ => bourgainHalfGeometric ((Equiv.subRight k) l) by
    funext l
    unfold bourgainHalfGeometric
    congr 1
    change (k - l).natAbs = (l - k).natAbs
    rw [show k - l = -(l - k) by ring, Int.natAbs_neg]]
  rw [hreindex, tsum_bourgainHalfGeometric]

/-- Finite Schur estimate for a symmetric nonnegative kernel. -/
theorem bourgainFiniteSymmetricSchur
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (w : κ → κ → ℝ) (M : κ → ℝ) (C : ℝ)
    (hw_nonneg : ∀ k l, 0 ≤ w k l)
    (hw_symm : ∀ k l, w k l = w l k)
    (hrow : ∀ k ∈ s, ∑ l ∈ s, w k l ≤ C) :
    ∑ k ∈ s, ∑ l ∈ s, w k l * M k * M l ≤
      C * ∑ k ∈ s, M k ^ (2 : ℕ) := by
  let A : ℝ := ∑ k ∈ s, M k ^ (2 : ℕ) * ∑ l ∈ s, w k l
  have hA : A ≤ C * ∑ k ∈ s, M k ^ (2 : ℕ) := by
    unfold A
    calc
      (∑ k ∈ s, M k ^ (2 : ℕ) * ∑ l ∈ s, w k l)
          ≤ ∑ k ∈ s, M k ^ (2 : ℕ) * C := by
            gcongr with k hk
            exact hrow k hk
      _ = C * ∑ k ∈ s, M k ^ (2 : ℕ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hquad :
      2 * (∑ k ∈ s, ∑ l ∈ s, w k l * M k * M l) ≤ 2 * A := by
    have hpoint (k l : κ) :
        2 * (w k l * M k * M l) ≤
          w k l * (M k ^ (2 : ℕ) + M l ^ (2 : ℕ)) := by
      nlinarith [mul_nonneg (hw_nonneg k l) (sq_nonneg (M k - M l))]
    calc
      2 * (∑ k ∈ s, ∑ l ∈ s, w k l * M k * M l)
          = ∑ k ∈ s, ∑ l ∈ s, 2 * (w k l * M k * M l) := by
              simp_rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ s, ∑ l ∈ s,
          w k l * (M k ^ (2 : ℕ) + M l ^ (2 : ℕ)) := by
            apply Finset.sum_le_sum
            intro k hk
            apply Finset.sum_le_sum
            intro l hl
            exact hpoint k l
      _ = 2 * A := by
        unfold A
        simp_rw [mul_add, Finset.sum_add_distrib]
        have hfirst :
            (∑ k ∈ s, ∑ l ∈ s, w k l * M k ^ (2 : ℕ)) =
              ∑ k ∈ s, M k ^ (2 : ℕ) * ∑ l ∈ s, w k l := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
        rw [hfirst]
        have hsecond :
            (∑ k ∈ s, ∑ l ∈ s, w k l * M l ^ (2 : ℕ)) =
              ∑ k ∈ s, M k ^ (2 : ℕ) * ∑ l ∈ s, w k l := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [← hw_symm k l]
          ring
        rw [hsecond]
        ring
  nlinarith

/-- Product half-geometric kernel on the four-dimensional integer cell
lattice. -/
def bourgainFourCellKernel
    (k l : Fin 4 → ℤ) : ℝ :=
  ∏ j : Fin 4, bourgainHalfGeometric (k j - l j)

theorem bourgainFourCellKernel_nonneg
    (k l : Fin 4 → ℤ) :
    0 ≤ bourgainFourCellKernel k l := by
  unfold bourgainFourCellKernel bourgainHalfGeometric
  positivity

theorem bourgainFourCellKernel_symm
    (k l : Fin 4 → ℤ) :
    bourgainFourCellKernel k l = bourgainFourCellKernel l k := by
  unfold bourgainFourCellKernel bourgainHalfGeometric
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [show k j - l j = -(l j - k j) by ring, Int.natAbs_neg]

/-- Four-dimensional product row bound `3^4 = 81`. -/
theorem sum_bourgainFourCellKernel_grid_le
    (S : Fin 4 → Finset ℤ) (k : Fin 4 → ℤ) :
    ∑ l ∈ Fintype.piFinset S, bourgainFourCellKernel k l ≤ 81 := by
  have hfactor :
      (∑ l ∈ Fintype.piFinset S, bourgainFourCellKernel k l) =
        ∏ j : Fin 4,
          ∑ n ∈ S j, bourgainHalfGeometric (k j - n) := by
    have hprod := Finset.prod_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (t := S)
      (f := fun j n => bourgainHalfGeometric (k j - n))
    rw [Finset.sum_univ_pi] at hprod
    simpa [bourgainFourCellKernel] using hprod.symm
  rw [hfactor]
  calc
    (∏ j : Fin 4,
        ∑ n ∈ S j, bourgainHalfGeometric (k j - n))
        ≤ ∏ _j : Fin 4, (3 : ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            exact Finset.sum_nonneg fun n hn => by
              unfold bourgainHalfGeometric
              positivity
          · intro j hj
            exact sum_bourgainHalfGeometric_sub_le (S j) (k j)
    _ = 81 := by norm_num [Fin.prod_univ_four]

theorem sum_bourgainFourCellKernel_image_le
    {ι : Type*} [Fintype ι]
    (c : ι → Fin 4 → ℤ) (k : Fin 4 → ℤ) :
    ∑ l ∈ Finset.univ.image c, bourgainFourCellKernel k l ≤ 81 := by
  classical
  let S : Fin 4 → Finset ℤ :=
    fun j => Finset.univ.image fun i : ι => c i j
  have hsubset :
      Finset.univ.image c ⊆ Fintype.piFinset S := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc
    (∑ l ∈ Finset.univ.image c, bourgainFourCellKernel k l)
        ≤ ∑ l ∈ Fintype.piFinset S, bourgainFourCellKernel k l :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun l hl hnot => bourgainFourCellKernel_nonneg k l)
    _ ≤ 81 := sum_bourgainFourCellKernel_grid_le S k

/-- Four-cell kernel energy is bounded by `81` times squared cell masses. -/
theorem sum_bourgainFourCellKernel_le_cellMass
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → Fin 4 → ℤ) :
    ∑ i : ι, ∑ j : ι,
        bourgainFourCellKernel (c i) (c j) * a i * a j ≤
      81 * ∑ k ∈ Finset.univ.image c,
        (∑ i : ι with c i = k, a i) ^ (2 : ℕ) := by
  classical
  let S : Finset (Fin 4 → ℤ) := Finset.univ.image c
  let M : (Fin 4 → ℤ) → ℝ :=
    fun k => ∑ i : ι with c i = k, a i
  have hschur :
      ∑ k ∈ S, ∑ l ∈ S,
          bourgainFourCellKernel k l * M k * M l ≤
        81 * ∑ k ∈ S, M k ^ (2 : ℕ) := by
    exact bourgainFiniteSymmetricSchur S bourgainFourCellKernel M 81
      bourgainFourCellKernel_nonneg bourgainFourCellKernel_symm
      (fun k hk => sum_bourgainFourCellKernel_image_le c k)
  have hmaps :
      ∀ i ∈ (Finset.univ : Finset ι), c i ∈ S := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hexpand :
      (∑ k ∈ S, ∑ l ∈ S,
          bourgainFourCellKernel k l * M k * M l) =
        ∑ i : ι, ∑ j : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j := by
    unfold M
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ y ∈ S, ∑ x ∈ S, ∑ j : ι with c j = y,
          ∑ i : ι with c i = x,
            bourgainFourCellKernel x y * a i * a j)
          =
        ∑ y ∈ S, ∑ j : ι with c j = y, ∑ i : ι,
          bourgainFourCellKernel (c i) y * a i * a j := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_fiberwise_of_maps_to hmaps]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro i hi
            rw [(Finset.mem_filter.mp hi).2]
      _ = ∑ j : ι, ∑ i : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j := by
            rw [← Finset.sum_fiberwise_of_maps_to hmaps]
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro j hj
            rw [(Finset.mem_filter.mp hj).2]
      _ = ∑ i : ι, ∑ j : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j := by
            rw [Finset.sum_comm]
  change
    (∑ i : ι, ∑ j : ι,
        bourgainFourCellKernel (c i) (c j) * a i * a j) ≤
      81 * ∑ k ∈ S, M k ^ (2 : ℕ)
  rw [← hexpand]
  exact hschur

/-- Squared cell masses are exactly the same-cell pair energy. -/
theorem sum_cellMass_sq_eq_sameCell
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (a : ι → ℝ) (c : ι → κ) :
    (∑ k ∈ Finset.univ.image c,
        (∑ i : ι with c i = k, a i) ^ (2 : ℕ)) =
      ∑ i : ι, ∑ j : ι, if c i = c j then a i * a j else 0 := by
  let S : Finset κ := Finset.univ.image c
  have hmaps :
      ∀ i ∈ (Finset.univ : Finset ι), c i ∈ S := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  change (∑ k ∈ S, (∑ i : ι with c i = k, a i) ^ (2 : ℕ)) = _
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ k ∈ S, ∑ j : ι with c j = k, ∑ i : ι with c i = k,
        a j * a i)
        = ∑ k ∈ S, ∑ j : ι with c j = k,
            ∑ i : ι with c i = c j, a j * a i := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
      _ = ∑ j : ι, ∑ i : ι with c i = c j, a j * a i := by
          rw [Finset.sum_fiberwise_of_maps_to hmaps]
      _ = ∑ j : ι, ∑ i : ι, if c i = c j then a j * a i else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show (∑ i : ι, if c i = c j then a j * a i else 0) =
              ∑ i : ι with c i = c j, a j * a i by
            rw [Finset.sum_filter]]
      _ = ∑ i : ι, ∑ j : ι, if c i = c j then a i * a j else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : c i = c j <;> simp [h, mul_comm]

/-- Floor-cell separation in one real coordinate. -/
theorem bourgainFloorCellSeparation (x y : ℝ) :
    ((⌊2 * x⌋ - ⌊2 * y⌋).natAbs : ℝ) <
      2 * |x - y| + 1 := by
  have hfract :
      |Int.fract (2 * x) - Int.fract (2 * y)| < (1 : ℝ) := by
    rw [abs_lt]
    constructor <;>
      linarith [Int.fract_nonneg (2 * x), Int.fract_lt_one (2 * x),
        Int.fract_nonneg (2 * y), Int.fract_lt_one (2 * y)]
  have hcast :
      (((⌊2 * x⌋ - ⌊2 * y⌋ : ℤ) : ℤ) : ℝ) =
        (2 * x - 2 * y) -
          (Int.fract (2 * x) - Int.fract (2 * y)) := by
    push_cast
    linarith [Int.fract_add_floor (2 * x), Int.fract_add_floor (2 * y)]
  calc
    ((⌊2 * x⌋ - ⌊2 * y⌋).natAbs : ℝ) =
        |(((⌊2 * x⌋ - ⌊2 * y⌋ : ℤ) : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
    _ = |(2 * x - 2 * y) -
          (Int.fract (2 * x) - Int.fract (2 * y))| := by rw [hcast]
    _ ≤ |2 * x - 2 * y| +
          |Int.fract (2 * x) - Int.fract (2 * y)| := abs_sub _ _
    _ < 2 * |x - y| + 1 := by
          rw [show 2 * x - 2 * y = 2 * (x - y) by ring,
            abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          linarith

/-- A normalized Gaussian is dominated by eight times the half-geometric
kernel associated with half-unit floor cells. -/
theorem bourgainGaussian_le_halfGeometric
    (d : ℝ) (n : ℕ)
    (hsep : (n : ℝ) < 2 * |d| + 1) :
    Real.exp (-Real.pi * d ^ (2 : ℕ)) ≤
      8 * ((1 : ℝ) / 2) ^ n := by
  have hexp : Real.exp (-Real.pi * d ^ (2 : ℕ)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg d)
  by_cases hn : n ≤ 3
  · calc
      Real.exp (-Real.pi * d ^ (2 : ℕ)) ≤ 1 := hexp
      _ ≤ 8 * ((1 : ℝ) / 2) ^ n := by
        interval_cases n <;> norm_num
  · have hn4 : 4 ≤ n := by omega
    have habs :
        ((n : ℝ) - 1) / 2 ≤ |d| := by
      linarith
    have hbase : 0 ≤ ((n : ℝ) - 1) / 2 := by
      have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
      linarith
    have hsq :
        (((n : ℝ) - 1) / 2) ^ (2 : ℕ) ≤
          d ^ (2 : ℕ) := by
      calc
        (((n : ℝ) - 1) / 2) ^ (2 : ℕ) ≤ |d| ^ (2 : ℕ) :=
          pow_le_pow_left₀ hbase habs 2
        _ = d ^ (2 : ℕ) := sq_abs d
    have hlog : Real.log 2 ≤ (1 : ℝ) := by
      convert
        (Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num))
          using 1 <;> norm_num
    have hmain :
        ((n : ℝ) - 3) * Real.log 2 ≤
          Real.pi * d ^ (2 : ℕ) := by
      have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
      have hn3 : 0 ≤ (n : ℝ) - 3 := by linarith
      have hlin :
          (n : ℝ) - 3 ≤ ((n : ℝ) - 1) ^ (2 : ℕ) / 2 := by
        nlinarith
      calc
        ((n : ℝ) - 3) * Real.log 2 ≤ (n : ℝ) - 3 :=
          mul_le_of_le_one_right hn3 hlog
        _ ≤ ((n : ℝ) - 1) ^ (2 : ℕ) / 2 := hlin
        _ = 2 * (((n : ℝ) - 1) / 2) ^ (2 : ℕ) := by ring
        _ ≤ 2 * d ^ (2 : ℕ) := by gcongr
        _ ≤ Real.pi * d ^ (2 : ℕ) := by
          gcongr
          exact Real.two_le_pi
    calc
      Real.exp (-Real.pi * d ^ (2 : ℕ)) ≤
          Real.exp (-((n : ℝ) - 3) * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = 8 * ((1 : ℝ) / 2) ^ n := by
        rw [show -((n : ℝ) - 3) * Real.log 2 =
            3 * Real.log 2 + -(n : ℝ) * Real.log 2 by ring,
          Real.exp_add]
        rw [show 3 * Real.log 2 = (3 : ℕ) * Real.log 2 by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [show -(n : ℝ) * Real.log 2 =
            -(n * Real.log 2) by ring,
          Real.exp_neg, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [div_pow]
        norm_num

/-- Half-unit floor cell of a four-dimensional point after applying the
spacing scales. -/
def bourgainScaledCell
    (X u : BourgainPhaseSpace) : Fin 4 → ℤ :=
  fun j => ⌊2 * (X j * u j)⌋

/-- Coordinatewise nearness in normalized coordinates. -/
def BourgainScaledNear
    (X u v : BourgainPhaseSpace) : Prop :=
  ∀ j : Fin 4, |X j * (u j - v j)| < 1 / 2

theorem bourgainScaledNear_of_cell_eq
    {X u v : BourgainPhaseSpace}
    (hcell : bourgainScaledCell X u = bourgainScaledCell X v) :
    BourgainScaledNear X u v := by
  intro j
  have hfloor :
      ⌊2 * (X j * u j)⌋ = ⌊2 * (X j * v j)⌋ :=
    congrFun hcell j
  have h :=
    Int.abs_sub_lt_one_of_floor_eq_floor hfloor
  have hscaled :
      |2 * (X j * (u j - v j))| < (1 : ℝ) := by
    convert h using 1 <;> ring_nf
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hscaled
  linarith

/-- Pointwise four-dimensional Gaussian domination by the product cell
kernel.  The explicit factor is `8^4 = 4096`. -/
theorem bourgainGaussianPairWeight_le_cellKernel
    (X u v : BourgainPhaseSpace) :
    Real.exp (-Real.pi * bourgainScaledSqDist X u v) ≤
      4096 *
        bourgainFourCellKernel
          (bourgainScaledCell X u) (bourgainScaledCell X v) := by
  have hcoord (j : Fin 4) :
      Real.exp (-Real.pi * (X j * (u j - v j)) ^ (2 : ℕ)) ≤
        8 * bourgainHalfGeometric
          (bourgainScaledCell X u j - bourgainScaledCell X v j) := by
    apply bourgainGaussian_le_halfGeometric
    have hsep :=
      bourgainFloorCellSeparation (X j * u j) (X j * v j)
    simpa [bourgainScaledCell, bourgainHalfGeometric,
      show X j * u j - X j * v j = X j * (u j - v j) by ring]
      using hsep
  calc
    Real.exp (-Real.pi * bourgainScaledSqDist X u v) =
        ∏ j : Fin 4,
          Real.exp (-Real.pi * (X j * (u j - v j)) ^ (2 : ℕ)) := by
      unfold bourgainScaledSqDist
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ j : Fin 4,
        (8 * bourgainHalfGeometric
          (bourgainScaledCell X u j - bourgainScaledCell X v j)) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact hcoord j
    _ = 4096 *
        bourgainFourCellKernel
          (bourgainScaledCell X u) (bourgainScaledCell X v) := by
      rw [Finset.prod_mul_distrib]
      norm_num [bourgainFourCellKernel, Fin.prod_univ_four]

/-- Gaussian pair energy of a finite weighted point family. -/
def bourgainWeightedGaussianEnergy
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    Real.exp (-Real.pi * bourgainScaledSqDist X (p i) (p j)) *
      a i * a j

/-- Sharp normalized near-pair energy of a finite weighted point family. -/
def bourgainWeightedScaledNearEnergy
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) : ℝ := by
  classical
  exact
    ∑ i : ι, ∑ j : ι,
      if BourgainScaledNear X (p i) (p j) then a i * a j else 0

/-- Unconditional Gaussian clustering estimate in four dimensions.

The constant is `8^4 * 3^4 = 24^4 = 331776`. -/
theorem bourgainWeightedGaussianEnergy_le_scaledNearEnergy
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    bourgainWeightedGaussianEnergy X p a ≤
      331776 * bourgainWeightedScaledNearEnergy X p a := by
  classical
  let c : ι → Fin 4 → ℤ := fun i => bourgainScaledCell X (p i)
  have hgauss :
      bourgainWeightedGaussianEnergy X p a ≤
        4096 * ∑ i : ι, ∑ j : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j := by
    unfold bourgainWeightedGaussianEnergy
    calc
      (∑ i : ι, ∑ j : ι,
          Real.exp (-Real.pi * bourgainScaledSqDist X (p i) (p j)) *
            a i * a j)
          ≤ ∑ i : ι, ∑ j : ι,
              4096 *
                (bourgainFourCellKernel (c i) (c j) * a i * a j) := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            have hpw :=
              bourgainGaussianPairWeight_le_cellKernel X (p i) (p j)
            have haij : 0 ≤ a i * a j := mul_nonneg (ha i) (ha j)
            calc
              Real.exp
                    (-Real.pi * bourgainScaledSqDist X (p i) (p j)) *
                  a i * a j
                  ≤ (4096 * bourgainFourCellKernel (c i) (c j)) *
                      a i * a j := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_right hpw (ha i)) (ha j)
              _ = 4096 *
                    (bourgainFourCellKernel (c i) (c j) * a i * a j) := by
                    ring
      _ = 4096 * ∑ i : ι, ∑ j : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j := by
        simp_rw [Finset.mul_sum]
  have hcell :
      (∑ i : ι, ∑ j : ι,
          bourgainFourCellKernel (c i) (c j) * a i * a j) ≤
        81 * ∑ k ∈ Finset.univ.image c,
          (∑ i : ι with c i = k, a i) ^ (2 : ℕ) :=
    sum_bourgainFourCellKernel_le_cellMass a c
  have hsame :
      (∑ k ∈ Finset.univ.image c,
          (∑ i : ι with c i = k, a i) ^ (2 : ℕ)) ≤
        bourgainWeightedScaledNearEnergy X p a := by
    rw [sum_cellMass_sq_eq_sameCell]
    unfold bourgainWeightedScaledNearEnergy
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hc : c i = c j
    · have hnear :
          BourgainScaledNear X (p i) (p j) := by
        exact bourgainScaledNear_of_cell_eq hc
      simp [hc, hnear]
    · simp only [hc, ↓reduceIte]
      split_ifs
      · exact mul_nonneg (ha i) (ha j)
      · exact le_rfl
  calc
    bourgainWeightedGaussianEnergy X p a
        ≤ 4096 * ∑ i : ι, ∑ j : ι,
            bourgainFourCellKernel (c i) (c j) * a i * a j := hgauss
    _ ≤ 4096 * (81 * ∑ k ∈ Finset.univ.image c,
          (∑ i : ι with c i = k, a i) ^ (2 : ℕ)) := by
        gcongr
    _ ≤ 4096 * (81 * bourgainWeightedScaledNearEnergy X p a) := by
        gcongr
    _ = 331776 * bourgainWeightedScaledNearEnergy X p a := by ring

theorem bourgainScaledNear_sixfold_iff
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) (h h' : Fin 6 → Fin H) :
    BourgainScaledNear X
        (bourgainSixfoldMoment h) (bourgainSixfoldMoment h') ↔
      BourgainNearPair X h h' := by
  constructor
  · intro hnear j
    have hj := hnear j
    rw [abs_mul, abs_of_pos (hX j)] at hj
    apply (lt_div_iff₀ (mul_pos (by norm_num) (hX j))).2
    calc
      |bourgainSixfoldMoment h j - bourgainSixfoldMoment h' j| *
          (2 * X j)
          = 2 *
              (X j *
                |bourgainSixfoldMoment h j -
                  bourgainSixfoldMoment h' j|) := by ring
      _ < 2 * (1 / 2 : ℝ) := by gcongr
      _ = 1 := by norm_num
  · intro hnear j
    rw [abs_mul, abs_of_pos (hX j)]
    calc
      X j *
          |bourgainSixfoldMoment h j -
            bourgainSixfoldMoment h' j|
          < X j * (1 / (2 * X j)) :=
        mul_lt_mul_of_pos_left (hnear j) (hX j)
      _ = 1 / 2 := by field_simp [(hX j).ne']

/-- Gaussian spacing energy is bounded by the sharp first-spacing count.
This is the unconditional smooth-to-sharp clustering direction needed in
the double-large-sieve step. -/
theorem bourgainGaussianSpacingEnergy_le_firstSpacingCount
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) :
    bourgainGaussianSpacingEnergy H X ≤
      331776 * (bourgainFirstSpacingCount H X : ℝ) := by
  let p : (Fin 6 → Fin H) → BourgainPhaseSpace :=
    bourgainSixfoldMoment
  let a : (Fin 6 → Fin H) → ℝ := fun _ => 1
  have hcluster :=
    bourgainWeightedGaussianEnergy_le_scaledNearEnergy X p a
      (fun _ => by norm_num)
  have hgauss :
      bourgainWeightedGaussianEnergy X p a =
        bourgainGaussianSpacingEnergy H X := by
    simp [bourgainWeightedGaussianEnergy, bourgainGaussianSpacingEnergy,
      p, a]
  have hnear :
      bourgainWeightedScaledNearEnergy X p a =
        (bourgainFirstSpacingCount H X : ℝ) := by
    classical
    calc
      bourgainWeightedScaledNearEnergy X p a =
          ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
            if BourgainNearPair X h h' then (1 : ℝ) else 0 := by
        unfold bourgainWeightedScaledNearEnergy
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro h' hh'
        rw [bourgainScaledNear_sixfold_iff hX]
        simp [p, a]
      _ = ∑ q ∈
          ((Finset.univ : Finset (Fin 6 → Fin H)).product
            (Finset.univ : Finset (Fin 6 → Fin H))),
          if BourgainNearPair X q.1 q.2 then (1 : ℝ) else 0 := by
        simpa using
          (Finset.sum_product
            (Finset.univ : Finset (Fin 6 → Fin H))
            (Finset.univ : Finset (Fin 6 → Fin H))
            (fun q =>
              if BourgainNearPair X q.1 q.2 then (1 : ℝ) else 0)).symm
      _ = (bourgainFirstSpacingCount H X : ℝ) := by
        simp [bourgainFirstSpacingCount, Finset.sum_boole]
  rw [hgauss, hnear] at hcluster
  exact hcluster

end

end RHTower
