import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-! Frequency separation and coefficient counting for narrow affine-clock windows. -/

open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The two affine-clock branches at native scale `n+1`. -/
def criticalAffineBranch (shifted : Bool) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) + if shifted then 1 / 12 else 0

theorem criticalAffineBranch_bounds (shifted : Bool) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ criticalAffineBranch shifted n ∧
      criticalAffineBranch shifted n ≤ ((n + 1 : ℕ) : ℝ) + 1 / 12 := by
  cases shifted <;> simp only [criticalAffineBranch, Bool.false_eq_true,
    if_false, if_true, add_zero] <;> constructor <;> linarith

private theorem affine_ordered_gap {N δ p q x y : ℝ}
    (hN : 0 < N) (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + 1 ≤ q) (hsmall : (p + q) * δ ≤ 1 / 4)
    (hlarge : p + q ≤ N) (hx : x ≤ (1 + δ) * N + 1 / 12) (hy : N ≤ y) :
    N / 2 ≤ q * y - p * x := by
  have hpx := mul_le_mul_of_nonneg_left hx hp
  have hqy := mul_le_mul_of_nonneg_left hy hq
  have hpN : p ≤ N := by linarith
  have hpδ : p * δ ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right (by linarith : p ≤ p + q) hδ).trans hsmall
  have hδN := mul_le_mul_of_nonneg_right hpδ hN.le
  have hgap := mul_le_mul_of_nonneg_right hpq hN.le
  nlinarith only [hpx, hqy, hpN, hδN, hgap, hN]

/-- Unequal integer harmonics cannot resonate inside a sufficiently narrow relative window. -/
theorem criticalAffineBranch_difference_gap {N δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    {p q m n : ℕ} (hpq : p ≠ q)
    (hsmall : ((p : ℝ) + q) * δ ≤ 1 / 4) (hlarge : (p : ℝ) + q ≤ N)
    (hm : N ≤ ((m + 1 : ℕ) : ℝ) ∧ ((m + 1 : ℕ) : ℝ) ≤ (1 + δ) * N)
    (hn : N ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N)
    (i j : Bool) :
    N / 2 ≤ |(p : ℝ) * criticalAffineBranch i m - q * criticalAffineBranch j n| := by
  have hx := criticalAffineBranch_bounds i m
  have hy := criticalAffineBranch_bounds j n
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · have hcast : (p : ℝ) + 1 ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    have h := affine_ordered_gap (x := criticalAffineBranch i m)
      (y := criticalAffineBranch j n) hN hδ (Nat.cast_nonneg p) (Nat.cast_nonneg q)
      hcast hsmall hlarge (by linarith [hm.2]) (hn.1.trans hy.1)
    rw [abs_sub_comm]
    exact h.trans (le_abs_self _)
  · have hcast : (q : ℝ) + 1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    have h := affine_ordered_gap (x := criticalAffineBranch j n)
      (y := criticalAffineBranch i m) hN hδ (Nat.cast_nonneg q) (Nat.cast_nonneg p)
      hcast (by simpa only [add_comm] using hsmall)
      (by simpa only [add_comm] using hlarge) (by linarith [hn.2]) (hm.1.trans hx.1)
    exact h.trans (le_abs_self _)

/-- Every sum frequency is large, including the resonant harmonic pair. -/
theorem criticalAffineBranch_sum_gap {N : ℝ} (hN : 0 ≤ N)
    {p q m n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hm : N ≤ ((m + 1 : ℕ) : ℝ)) (hn : N ≤ ((n + 1 : ℕ) : ℝ))
    (i j : Bool) :
    2 * N ≤ (p : ℝ) * criticalAffineBranch i m + q * criticalAffineBranch j n := by
  have hx := hm.trans (criticalAffineBranch_bounds i m).1
  have hy := hn.trans (criticalAffineBranch_bounds j n).1
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx' := mul_le_mul_of_nonneg_right hp' (hN.trans hx)
  have hy' := mul_le_mul_of_nonneg_right hq' (hN.trans hy)
  linarith

/-- Native scales in a relative window form a one-separated set. -/
theorem card_le_critical_scale_window {N δ : ℝ} (hN : 0 ≤ N) (hδ : 0 ≤ δ)
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, N ≤ ((n + 1 : ℕ) : ℝ) ∧
      ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N) :
    (S.card : ℝ) ≤ δ * N + 1 := by
  classical
  let f : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  have hinj : Function.Injective f := by
    intro m n h
    have he : m + 1 = n + 1 := Nat.cast_injective h
    omega
  have hcount := card_le_of_separated_of_subset_Icc (L := 1)
    zero_lt_one (show N ≤ (1 + δ) * N by nlinarith [mul_nonneg hδ hN])
    (S.image f) (by
      intro x hx y hy hxy
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
      have hmn : m ≠ n := fun h => hxy (congrArg f h)
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have hcast : ((m + 1 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show m + 1 + 1 ≤ n + 1 by omega)
        rw [abs_sub_comm]
        exact (show (1 : ℝ) ≤ f n - f m by dsimp [f]; linarith).trans (le_abs_self _)
      · have hcast : ((n + 1 : ℕ) : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show n + 1 + 1 ≤ m + 1 by omega)
        exact (show (1 : ℝ) ≤ f m - f n by dsimp [f]; linarith).trans (le_abs_self _)) (by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      exact hS n hn)
  rw [Finset.card_image_of_injective S hinj] at hcount
  nlinarith only [hcount]

/-- Passing from entry bounds to square-norm bounds costs only the relative window width. -/
theorem sq_sum_abs_le_critical_scale_window {N δ : ℝ} (hN : 0 ≤ N) (hδ : 0 ≤ δ)
    (S : Finset ℕ) (b : ℕ → ℝ)
    (hS : ∀ n ∈ S, N ≤ ((n + 1 : ℕ) : ℝ) ∧
      ((n + 1 : ℕ) : ℝ) ≤ (1 + δ) * N) :
    (∑ n ∈ S, |b n|) ^ 2 ≤ (δ * N + 1) * ∑ n ∈ S, b n ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => |b n|)
  simp only [sq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_right (card_le_critical_scale_window hN hδ S hS)
    (Finset.sum_nonneg fun n hn => sq_nonneg (b n)))

end GaloisForLFunctions.ArithmeticPositivityTheory

