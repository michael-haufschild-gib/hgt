import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignedIncidenceForms
import Mathlib.Algebra.BigOperators.Fin

/-!
# Frustration is the local–global gap

Balanced forms are positive exactly when they are locally payable
(`BalancedIncidenceIsLocallyPayable`).  This module shows that balance is the dividing line.

* **Rank-one charges cannot be localized** (`not_locallyPayable_rankOneCoupling`).  The square
  `(Σ_i w_i f_i)²` with every `w_i ≠ 0` on three or more points is positive and admits no local
  allocation: an allocation would need `a_ij + a_ji ≥ 2 |w_i w_j|` on every overlap from budgets
  `w_i²`, i.e. `n (n − 1) ≤ n`.  A polar charge — the square of one linear functional — must be
  paid globally, never pair by pair.
* **The frustrated triangle** (`triangleCoupling κ`: unit budgets, overlap charge `κ` on all three
  pairs).  It is balanced iff `κ ≤ 0` (`triangle_isBalanced_iff`), positive iff `−½ ≤ κ ≤ 1`
  (`triangle_nonneg_iff`) and locally payable iff `|κ| ≤ ½` (`triangle_locallyPayable_iff`).  On the
  balanced side positivity and payment coincide at `κ = −½`; on the frustrated side the window
  `½ < κ ≤ 1` is positive and unpayable (`triangle_frustrated_gap`): frustration halves the
  capacity of local payment.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Rank-one charges -/

section RankOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one coupling `w_i w_j`: the square of the functional `f ↦ Σ_i w_i f_i`. -/
def rankOneCoupling (w : ι → ℝ) : ι → ι → ℝ := fun i j => w i * w j

omit [Fintype ι] [DecidableEq ι] in
theorem rankOneCoupling_isSymmetric (w : ι → ℝ) : IsSymmetricCoupling (rankOneCoupling w) :=
  fun i j => by simp only [rankOneCoupling]; ring

omit [DecidableEq ι] in
theorem incidenceEnergy_rankOneCoupling (w f : ι → ℝ) :
    incidenceEnergy (rankOneCoupling w) f = (∑ i, w i * f i) ^ 2 := by
  unfold incidenceEnergy rankOneCoupling
  rw [sq, sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
theorem incidenceEnergy_rankOneCoupling_nonneg (w f : ι → ℝ) :
    0 ≤ incidenceEnergy (rankOneCoupling w) f := by
  rw [incidenceEnergy_rankOneCoupling]
  exact sq_nonneg _

/-- **A rank-one charge on three or more points cannot be paid locally.** -/
theorem not_locallyPayable_rankOneCoupling {w : ι → ℝ} (hw : ∀ i, w i ≠ 0)
    (hcard : 3 ≤ Fintype.card ι) : ¬ LocallyPayable (rankOneCoupling w) := by
  rintro ⟨A⟩
  set n := Fintype.card ι with hn
  -- normalized shares `b_ij = a_ij / w_i²`
  set b : ι → ι → ℝ := fun i j => A.share i j / w i ^ 2 with hb
  have hw2 : ∀ i, 0 < w i ^ 2 := fun i => lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hw i)))
  have hb_nonneg : ∀ i j, 0 ≤ b i j := fun i j => div_nonneg (A.share_nonneg i j) (hw2 i).le
  have hb_pair : ∀ i j, i ≠ j → 2 ≤ b i j + b j i := by
    intro i j hij
    have hp := A.pays i j hij
    simp only [rankOneCoupling] at hp
    have hprod : 1 ≤ b i j * b j i := by
      simp only [hb]
      rw [div_mul_div_comm, le_div_iff₀ (mul_pos (hw2 i) (hw2 j))]
      nlinarith [hp]
    nlinarith [sq_nonneg (b i j - b j i), hb_nonneg i j, hb_nonneg j i]
  have hb_budget : ∀ i, ∑ j ∈ univ.erase i, b i j ≤ 1 := by
    intro i
    have h := A.within_budget i
    simp only [rankOneCoupling] at h
    simp only [hb, ← sum_div]
    rw [div_le_one (hw2 i)]
    simpa only [sq] using h
  -- total normalized lending is at most `n` but at least `n (n - 1)`
  have hupper : ∑ i, ∑ j ∈ univ.erase i, b i j ≤ n := by
    calc ∑ i, ∑ j ∈ univ.erase i, b i j ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum fun i _ => hb_budget i
      _ = n := by simp [hn]
  have hlower : (n : ℝ) * (n - 1) ≤ ∑ i, ∑ j ∈ univ.erase i, b i j := by
    have h2 : ∑ i, ∑ j ∈ univ.erase i, (b i j + b j i) =
        2 * ∑ i, ∑ j ∈ univ.erase i, b i j := by
      simp only [sum_add_distrib]
      rw [← sum_offDiag_swap b]
      ring
    have h3 : ∑ i, ∑ j ∈ univ.erase i, (2 : ℝ) ≤ ∑ i, ∑ j ∈ univ.erase i, (b i j + b j i) :=
      sum_le_sum fun i _ => sum_le_sum fun j hj => hb_pair i j (ne_of_mem_erase hj).symm
    have h4 : ∑ i : ι, ∑ _j ∈ univ.erase i, (2 : ℝ) = 2 * ((n : ℝ) * (n - 1)) := by
      simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul, ← hn]
      have h1 : 1 ≤ n := by omega
      push_cast [Nat.cast_sub h1]
      ring
    linarith
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hcard
  nlinarith

end RankOne

/-! ### The frustrated triangle -/

/-- The triangle with unit budgets and overlap charge `κ` on each of its three pairs. -/
def triangleCoupling (κ : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else κ

theorem triangleCoupling_isSymmetric (κ : ℝ) : IsSymmetricCoupling (triangleCoupling κ) := by
  intro i j
  simp only [triangleCoupling, eq_comm]

theorem incidenceEnergy_triangleCoupling (κ : ℝ) (f : Fin 3 → ℝ) :
    incidenceEnergy (triangleCoupling κ) f =
      f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + 2 * κ * (f 0 * f 1 + f 0 * f 2 + f 1 * f 2) := by
  simp only [incidenceEnergy, triangleCoupling, Fin.sum_univ_three]
  simp
  ring

/-- **Positivity window of the triangle**: `−½ ≤ κ ≤ 1`. -/
theorem triangle_nonneg_iff (κ : ℝ) :
    (∀ f, 0 ≤ incidenceEnergy (triangleCoupling κ) f) ↔ -1 / 2 ≤ κ ∧ κ ≤ 1 := by
  constructor
  · intro h
    have h1 := h fun _ => 1
    have h2 := h ![1, -1, 0]
    simp only [incidenceEnergy_triangleCoupling] at h1 h2
    simp at h2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩ f
    rw [incidenceEnergy_triangleCoupling]
    have key : f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + 2 * κ * (f 0 * f 1 + f 0 * f 2 + f 1 * f 2) =
        (1 + 2 * κ) / 3 * (f 0 + f 1 + f 2) ^ 2 +
          (1 - κ) / 3 * ((f 0 - f 1) ^ 2 + (f 0 - f 2) ^ 2 + (f 1 - f 2) ^ 2) := by ring
    rw [key]
    have ha : 0 ≤ (1 + 2 * κ) / 3 := by linarith
    have hb : 0 ≤ (1 - κ) / 3 := by linarith
    positivity

private theorem triangle_erase_sum (a : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    ∑ j ∈ univ.erase i, a i j = ∑ j, a i j - a i i :=
  sum_erase_eq_sub (mem_univ i)

/-- **Payment window of the triangle**: `|κ| ≤ ½`. -/
theorem triangle_locallyPayable_iff (κ : ℝ) :
    LocallyPayable (triangleCoupling κ) ↔ |κ| ≤ 1 / 2 := by
  constructor
  · rintro ⟨A⟩
    -- each overlap receives at least `2|κ|`; the three unit budgets lend at most `3`
    have hpair : ∀ i j : Fin 3, i ≠ j → 2 * |κ| ≤ A.share i j + A.share j i := by
      intro i j hij
      have hp := A.pays i j hij
      simp only [triangleCoupling, hij, if_false] at hp
      have h1 := A.share_nonneg i j
      have h2 := A.share_nonneg j i
      by_contra hlt
      have hlt := not_le.mp hlt
      have habs := abs_nonneg κ
      have hsq : |κ| ^ 2 = κ ^ 2 := sq_abs κ
      nlinarith [sq_nonneg (A.share i j - A.share j i)]
    have hb : ∀ i : Fin 3, ∑ j ∈ univ.erase i, A.share i j ≤ 1 := by
      intro i
      have := A.within_budget i
      simpa only [triangleCoupling, if_true] using this
    have b0 := hb 0
    have b1 := hb 1
    have b2 := hb 2
    simp only [triangle_erase_sum, Fin.sum_univ_three] at b0 b1 b2
    have p01 := hpair 0 1 (by decide)
    have p02 := hpair 0 2 (by decide)
    have p12 := hpair 1 2 (by decide)
    linarith
  · intro hκ
    have hκ2 : κ ^ 2 ≤ 1 / 2 * (1 / 2) := by
      have := abs_nonneg κ
      nlinarith [sq_abs κ]
    refine ⟨{ share := fun _ _ => 1 / 2
              share_nonneg := fun _ _ => by norm_num
              pays := fun i j hij => ?_
              within_budget := fun i => ?_ }⟩
    · simp only [triangleCoupling, hij, if_false]
      exact hκ2
    · simp only [triangleCoupling, if_true, sum_const, card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num

/-- **Balance of the triangle**: the triangle is balanced exactly when its overlaps are aligned. -/
theorem triangle_isBalanced_iff (κ : ℝ) : IsBalanced (triangleCoupling κ) ↔ κ ≤ 0 := by
  constructor
  · rintro ⟨s, hs, hz⟩
    by_contra hκ
    have hκ := not_le.mp hκ
    have h01 := hz 0 1 (by decide)
    have h02 := hz 0 2 (by decide)
    have h12 := hz 1 2 (by decide)
    simp only [switchCoupling, triangleCoupling] at h01 h02 h12
    simp at h01 h02 h12
    have a01 : s 0 * s 1 ≤ 0 := by nlinarith
    have a02 : s 0 * s 2 ≤ 0 := by nlinarith
    have a12 : s 1 * s 2 ≤ 0 := by nlinarith
    have hprod : (s 0 * s 1) * (s 0 * s 2) * (s 1 * s 2) = 1 := by
      have e : (s 0 * s 1) * (s 0 * s 2) * (s 1 * s 2) = s 0 ^ 2 * s 1 ^ 2 * s 2 ^ 2 := by ring
      rw [e, hs 0, hs 1, hs 2]
      norm_num
    have hle : (s 0 * s 1) * (s 0 * s 2) * (s 1 * s 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos a01 a02) a12
    linarith
  · intro hκ
    refine ⟨fun _ => 1, fun _ => by norm_num, fun i j hij => ?_⟩
    simp only [switchCoupling, triangleCoupling, hij, if_false]
    linarith

/-- **The frustration gap.**  For `½ < κ ≤ 1` the triangle is positive, frustrated and not locally
payable. -/
theorem triangle_frustrated_gap {κ : ℝ} (h1 : 1 / 2 < κ) (h2 : κ ≤ 1) :
    (∀ f, 0 ≤ incidenceEnergy (triangleCoupling κ) f) ∧ ¬ IsBalanced (triangleCoupling κ) ∧
      ¬ LocallyPayable (triangleCoupling κ) := by
  refine ⟨(triangle_nonneg_iff κ).mpr ⟨by linarith, h2⟩, fun hb => ?_, fun hp => ?_⟩
  · have := (triangle_isBalanced_iff κ).mp hb
    linarith
  · have := (triangle_locallyPayable_iff κ).mp hp
    rw [abs_of_pos (by linarith)] at this
    linarith

/-- On the balanced side the two windows meet: for `κ ≤ 0`, positivity is local payability. -/
theorem triangle_nonneg_iff_locallyPayable_of_nonpos {κ : ℝ} (hκ : κ ≤ 0) :
    (∀ f, 0 ≤ incidenceEnergy (triangleCoupling κ) f) ↔ LocallyPayable (triangleCoupling κ) := by
  rw [triangle_nonneg_iff, triangle_locallyPayable_iff, abs_of_nonpos hκ]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
