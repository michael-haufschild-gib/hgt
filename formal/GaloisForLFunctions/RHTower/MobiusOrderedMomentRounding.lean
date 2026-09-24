import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Ordered floor rounding for literal finite moment selection

For a sorted group of atoms, floor differences are literal zero-or-one selectors.
The variable-weight version permits different fractional coefficients from different
cofactor families. Its prefix discrepancy is in `[-1,0]`; summation by parts bounds
the discrepancy against every nondecreasing weight in `[0,1]` by one. When the
fractional total is an integer, it selects exactly that many atoms. This permits
one global rounding per actual Möbius sign in a physical block, independent of
the number of cofactor families.
-/

open Finset

namespace RHTower

theorem weighted_sum_abs_le_one_of_prefix_discrepancy
    (d w : ℕ → ℝ) (N : ℕ)
    (hprefix : ∀ k ≤ N, -1 ≤ ∑ i ∈ range k, d i ∧ ∑ i ∈ range k, d i ≤ 0)
    (hw0 : ∀ i < N, 0 ≤ w i)
    (hw1 : ∀ i < N, w i ≤ 1)
    (hwmono : ∀ i j, i ≤ j → j < N → w i ≤ w j) :
    |∑ i ∈ range N, w i * d i| ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN]
  have hNm : N - 1 < N := by omega
  let D : ℕ → ℝ := fun k => ∑ i ∈ range k, d i
  let T : ℝ := ∑ i ∈ range (N - 1), (w (i + 1) - w i) * D (i + 1)
  have hparts : (∑ i ∈ range N, w i * d i) = w (N - 1) * D N - T := by
    simpa only [D, T, smul_eq_mul] using Finset.sum_range_by_parts w d N
  have hdiff (i : ℕ) (hi : i ∈ range (N - 1)) : 0 ≤ w (i + 1) - w i := by
    have hiN : i + 1 < N := by have := mem_range.mp hi; omega
    exact sub_nonneg.mpr (hwmono i (i+1) (by omega) hiN)
  have hD (k : ℕ) (hk : k ≤ N) : -1 ≤ D k ∧ D k ≤ 0 := by
    simpa only [D] using hprefix k hk
  have hTupper : T ≤ 0 := by
    have h : 0 ≤ ∑ i ∈ range (N - 1),
        -((w (i + 1) - w i) * D (i + 1)) := by
      apply sum_nonneg
      intro i hi
      have hiN : i + 1 ≤ N := by have := mem_range.mp hi; omega
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos (hdiff i hi) (hD (i+1) hiN).2)
    rw [sum_neg_distrib] at h
    dsimp [T]
    linarith
  have htel (M : ℕ) : (∑ i ∈ range M, (w (i+1) - w i)) = w M - w 0 := by
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; linarith
  have hTlower : -(w (N - 1) - w 0) ≤ T := by
    calc
      -(w (N - 1) - w 0) =
          ∑ i ∈ range (N - 1), -(w (i+1) - w i) := by
            rw [sum_neg_distrib, htel]
      _ ≤ T := by
        dsimp [T]
        apply sum_le_sum
        intro i hi
        have hiN : i + 1 ≤ N := by have := mem_range.mp hi; omega
        have h := mul_le_mul_of_nonneg_left (hD (i+1) hiN).1 (hdiff i hi)
        nlinarith
  have hlast0 : 0 ≤ w (N - 1) := hw0 _ hNm
  have hlast1 : w (N - 1) ≤ 1 := hw1 _ hNm
  have hfirst : -w (N - 1) ≤ w (N - 1) * D N := by
    have h := mul_le_mul_of_nonneg_left (hD N le_rfl).1 hlast0
    nlinarith
  have hfirst0 : w (N - 1) * D N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlast0 (hD N le_rfl).2
  have hw00 : 0 ≤ w 0 := hw0 0 (by omega)
  rw [abs_le]
  constructor
  · rw [hparts]
    linarith
  · rw [hparts]
    linarith

noncomputable def floorPrefixSelector (lam : ℝ) (i : ℕ) : ℝ :=
  (⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ : ℝ) - (⌊(i : ℝ) * lam⌋₊ : ℝ)

theorem floorPrefixSelector_mem_unit {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (i : ℕ) : floorPrefixSelector lam i = 0 ∨ floorPrefixSelector lam i = 1 := by
  have hlow : (i : ℝ) * lam ≤ ((i + 1 : ℕ) : ℝ) * lam := by
    push_cast
    nlinarith
  have hhigh : ((i + 1 : ℕ) : ℝ) * lam ≤ (i : ℝ) * lam + 1 := by
    push_cast
    nlinarith
  have hflo : ⌊(i : ℝ) * lam⌋₊ ≤ ⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ :=
    Nat.floor_mono hlow
  have hfhi : ⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ ≤ ⌊(i : ℝ) * lam⌋₊ + 1 := by
    have h := Nat.floor_mono hhigh
    rwa [Nat.floor_add_one (mul_nonneg (Nat.cast_nonneg _) hlam0)] at h
  have hfloR : (⌊(i : ℝ) * lam⌋₊ : ℝ) ≤ (⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ : ℝ) := by
    exact_mod_cast hflo
  have hfhiR : (⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ : ℝ) ≤
      (⌊(i : ℝ) * lam⌋₊ : ℝ) + 1 := by
    exact_mod_cast hfhi
  have hz : 0 ≤ floorPrefixSelector lam i := by
    dsimp [floorPrefixSelector]
    linarith
  have ho : floorPrefixSelector lam i ≤ 1 := by
    dsimp [floorPrefixSelector]
    linarith
  have hint : ∃ n : ℕ, floorPrefixSelector lam i = n := by
    refine ⟨⌊((i + 1 : ℕ) : ℝ) * lam⌋₊ - ⌊(i : ℝ) * lam⌋₊, ?_⟩
    simp only [floorPrefixSelector]
    rw [Nat.cast_sub hflo]
  obtain ⟨n, hn⟩ := hint
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · left; simpa [hn0] using hn
  · right
    have hno : n ≤ 1 := by
      rw [hn] at ho
      exact_mod_cast ho
    have hn1 : n = 1 := by omega
    simpa [hn1] using hn

theorem sum_floorPrefixSelector (lam : ℝ) (k : ℕ) :
    ∑ i ∈ range k, floorPrefixSelector lam i = (⌊(k : ℝ) * lam⌋₊ : ℝ) := by
  induction k with
  | zero => simp [floorPrefixSelector]
  | succ k ih =>
      rw [sum_range_succ, ih]
      dsimp [floorPrefixSelector]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

theorem floorPrefixSelector_prefix_discrepancy {lam : ℝ} (hlam : 0 ≤ lam)
    (k : ℕ) :
    -1 ≤ ∑ i ∈ range k, (floorPrefixSelector lam i - lam) ∧
      ∑ i ∈ range k, (floorPrefixSelector lam i - lam) ≤ 0 := by
  have hfloorle : (⌊(k : ℝ) * lam⌋₊ : ℝ) ≤ (k : ℝ) * lam :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hlam)
  have hfloorlt : (k : ℝ) * lam < (⌊(k : ℝ) * lam⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hsum : ∑ i ∈ range k, (floorPrefixSelector lam i - lam) =
      (⌊(k : ℝ) * lam⌋₊ : ℝ) - (k : ℝ) * lam := by
    rw [sum_sub_distrib, sum_floorPrefixSelector]
    simp
  rw [hsum]
  constructor <;> linarith

theorem floorPrefixSelector_weighted_moment_bound
    {lam : ℝ} (hlam0 : 0 ≤ lam)
    (w : ℕ → ℝ) (N : ℕ)
    (hw0 : ∀ i < N, 0 ≤ w i)
    (hw1 : ∀ i < N, w i ≤ 1)
    (hwmono : ∀ i j, i ≤ j → j < N → w i ≤ w j) :
    |∑ i ∈ range N, w i * (floorPrefixSelector lam i - lam)| ≤ 1 :=
  weighted_sum_abs_le_one_of_prefix_discrepancy
    (fun i => floorPrefixSelector lam i - lam) w N
    (fun k _ => floorPrefixSelector_prefix_discrepancy hlam0 k) hw0 hw1 hwmono

noncomputable def cumulativeFractionalWeight (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, lam i

noncomputable def variableFloorSelector (lam : ℕ → ℝ) (i : ℕ) : ℝ :=
  (⌊cumulativeFractionalWeight lam (i + 1)⌋₊ : ℝ) -
    (⌊cumulativeFractionalWeight lam i⌋₊ : ℝ)

theorem variableFloorSelector_mem_unit {lam : ℕ → ℝ}
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1) (i : ℕ) :
    variableFloorSelector lam i = 0 ∨ variableFloorSelector lam i = 1 := by
  have hstep : cumulativeFractionalWeight lam (i + 1) =
      cumulativeFractionalWeight lam i + lam i := by
    simp [cumulativeFractionalWeight, sum_range_succ]
  have hA0 : 0 ≤ cumulativeFractionalWeight lam i := by
    unfold cumulativeFractionalWeight
    exact sum_nonneg fun j _ => hlam0 j
  have hlow : cumulativeFractionalWeight lam i ≤
      cumulativeFractionalWeight lam (i + 1) := by
    rw [hstep]
    linarith [hlam0 i]
  have hhigh : cumulativeFractionalWeight lam (i + 1) ≤
      cumulativeFractionalWeight lam i + 1 := by
    rw [hstep]
    linarith [hlam1 i]
  have hflo : ⌊cumulativeFractionalWeight lam i⌋₊ ≤
      ⌊cumulativeFractionalWeight lam (i + 1)⌋₊ := Nat.floor_mono hlow
  have hfhi : ⌊cumulativeFractionalWeight lam (i + 1)⌋₊ ≤
      ⌊cumulativeFractionalWeight lam i⌋₊ + 1 := by
    have h := Nat.floor_mono hhigh
    rwa [Nat.floor_add_one hA0] at h
  have hfloR : (⌊cumulativeFractionalWeight lam i⌋₊ : ℝ) ≤
      (⌊cumulativeFractionalWeight lam (i + 1)⌋₊ : ℝ) := by
    exact_mod_cast hflo
  have hfhiR : (⌊cumulativeFractionalWeight lam (i + 1)⌋₊ : ℝ) ≤
      (⌊cumulativeFractionalWeight lam i⌋₊ : ℝ) + 1 := by
    exact_mod_cast hfhi
  have ho : variableFloorSelector lam i ≤ 1 := by
    dsimp [variableFloorSelector]
    linarith
  have hint : ∃ n : ℕ, variableFloorSelector lam i = n := by
    refine ⟨⌊cumulativeFractionalWeight lam (i + 1)⌋₊ -
      ⌊cumulativeFractionalWeight lam i⌋₊, ?_⟩
    simp only [variableFloorSelector]
    rw [Nat.cast_sub hflo]
  obtain ⟨n, hn⟩ := hint
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · left; simpa [hn0] using hn
  · right
    have hno : n ≤ 1 := by
      rw [hn] at ho
      exact_mod_cast ho
    have hn1 : n = 1 := by omega
    simpa [hn1] using hn

theorem sum_variableFloorSelector (lam : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, variableFloorSelector lam i =
      (⌊cumulativeFractionalWeight lam k⌋₊ : ℝ) := by
  induction k with
  | zero => simp [variableFloorSelector, cumulativeFractionalWeight]
  | succ k ih =>
      rw [sum_range_succ, ih]
      dsimp [variableFloorSelector]
      linarith

theorem variableFloorSelector_prefix_discrepancy {lam : ℕ → ℝ}
    (hlam0 : ∀ i, 0 ≤ lam i) (k : ℕ) :
    -1 ≤ ∑ i ∈ range k, (variableFloorSelector lam i - lam i) ∧
      ∑ i ∈ range k, (variableFloorSelector lam i - lam i) ≤ 0 := by
  have hA0 : 0 ≤ cumulativeFractionalWeight lam k := by
    unfold cumulativeFractionalWeight
    exact sum_nonneg fun j _ => hlam0 j
  have hfloorle : (⌊cumulativeFractionalWeight lam k⌋₊ : ℝ) ≤
      cumulativeFractionalWeight lam k := Nat.floor_le hA0
  have hfloorlt : cumulativeFractionalWeight lam k <
      (⌊cumulativeFractionalWeight lam k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsum : ∑ i ∈ range k, (variableFloorSelector lam i - lam i) =
      (⌊cumulativeFractionalWeight lam k⌋₊ : ℝ) -
        cumulativeFractionalWeight lam k := by
    rw [sum_sub_distrib, sum_variableFloorSelector]
    rfl
  rw [hsum]
  constructor <;> linarith

theorem variableFloorSelector_weighted_moment_bound
    {lam : ℕ → ℝ} (hlam0 : ∀ i, 0 ≤ lam i)
    (w : ℕ → ℝ) (N : ℕ)
    (hw0 : ∀ i < N, 0 ≤ w i)
    (hw1 : ∀ i < N, w i ≤ 1)
    (hwmono : ∀ i j, i ≤ j → j < N → w i ≤ w j) :
    |∑ i ∈ range N, w i * (variableFloorSelector lam i - lam i)| ≤ 1 :=
  weighted_sum_abs_le_one_of_prefix_discrepancy
    (fun i => variableFloorSelector lam i - lam i) w N
    (fun k _ => variableFloorSelector_prefix_discrepancy hlam0 k) hw0 hw1 hwmono

theorem sum_variableFloorSelector_of_integer_total
    (lam : ℕ → ℝ) (N m : ℕ)
    (hm : cumulativeFractionalWeight lam N = (m : ℝ)) :
    ∑ i ∈ range N, variableFloorSelector lam i = m := by
  rw [sum_variableFloorSelector, hm, Nat.floor_natCast]

end RHTower
