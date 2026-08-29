import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma31PerronComparison

/-!
# Aligning a real short window with the natural Perron window

Matomäki--Teräväinen's Lemma 3.1 is a variance over a *real* centre `x`, while the Perron
comparison of `MatomakiTeravainenLemma31PerronComparison` is stated for the natural window
`(A, A+H]` with `A H : ℕ`.  The alignment is exact: the integers of the real window `(x, x+h]` are
precisely those of `(⌊x⌋, ⌊x+h⌋]`, so the coefficient sum over the real window *is* a
`perronWindowSum`, with no error at all; the only inexactness is that the natural width
`⌊x+h⌋ − ⌊x⌋` differs from `h` by less than one.

* `natWindow_eq_realWindow` — the integers of `(x, x+h]` are `Ioc ⌊x⌋ ⌊x+h⌋`;
* `sum_realWindow_eq_perronWindowSum` — the coefficient sum is exactly a natural window sum;
* `abs_natWidth_sub_le_one` — the natural width is within one of `h`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The natural numbers in the real window `(x, x+h]` are exactly `Ioc ⌊x⌋ ⌊x+h⌋`. -/
theorem natWindow_eq_realWindow {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (n : ℕ) :
    (n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊) ↔ (x < (n : ℝ) ∧ (n : ℝ) ≤ x + h) := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact (Nat.floor_lt hx).mp h1
    · exact (Nat.le_floor_iff (by linarith)).mp h2
  · rintro ⟨h1, h2⟩
    exact ⟨(Nat.floor_lt hx).mpr h1, (Nat.le_floor_iff (by linarith)).mpr h2⟩

/-- **The real window sum is exactly a natural window sum.** -/
theorem sum_realWindow_eq_perronWindowSum (c : ℕ → ℂ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h)
    {M : ℕ} (hM : ⌊x + h⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, c n)
      = perronWindowSum c M ⌊x⌋₊ (⌊x + h⌋₊ - ⌊x⌋₊) := by
  classical
  have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hsum : ⌊x⌋₊ + (⌊x + h⌋₊ - ⌊x⌋₊) = ⌊x + h⌋₊ := by omega
  have hminA : min M ⌊x⌋₊ = ⌊x⌋₊ := min_eq_right (le_trans hle hM)
  have hminB : min M (⌊x⌋₊ + (⌊x + h⌋₊ - ⌊x⌋₊)) = ⌊x + h⌋₊ := by
    rw [hsum]
    exact min_eq_right hM
  rw [perronWindowSum, hminA, hminB]
  have hIcc : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊x + h⌋₊ :=
    Finset.Icc_subset_Icc le_rfl hle
  rw [eq_sub_iff_add_eq, ← Finset.sum_union]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h1, le_trans h2 hle⟩
    · rintro ⟨h1, h2⟩
      by_cases hcase : ⌊x⌋₊ < n
      · exact Or.inl ⟨hcase, h2⟩
      · exact Or.inr ⟨h1, by omega⟩
  · refine Finset.disjoint_left.mpr ?_
    intro n hn hn'
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc] at hn'
    omega

/-- The natural width differs from the real width by less than one. -/
theorem abs_natWidth_sub_le_one {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    |((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) - h| ≤ 1 := by
  have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hcast : ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊x + h⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    rw [Nat.cast_sub hle]
  rw [hcast, abs_le]
  have h1 : (⌊x + h⌋₊ : ℝ) ≤ x + h := Nat.floor_le (by linarith)
  have h2 : x + h < (⌊x + h⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h4 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor <;> linarith

/-- **The two-window Perron comparison for real windows.**  Brick 26's natural-window identity,
transported to the real windows `(x, x+h]` and `(x, x+h₁]` that the variance of Lemma 3.1 runs
over.  The transport is exact: only the widths are replaced by their integer counterparts, and
`abs_natWidth_sub_le_one` bounds that replacement. -/
theorem norm_realWindowSum_compare_sub_integral_le
    {c : ℕ → ℂ} {M : ℕ} {K T x h h₁ : ℝ}
    (hK : ∀ n, ‖c n‖ ≤ K) (hT : 0 < T) (hx : 0 ≤ x) (hh : 0 ≤ h) (hh₁ : 0 ≤ h₁)
    (hM : ⌊x + h⌋₊ ≤ M) (hM₁ : ⌊x + h₁⌋₊ ≤ M) :
    ‖(∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, c n)
        - ((((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) : ℝ) : ℂ)
          * (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h₁⌋₊, c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            perronPoly c M 1 t * perronCompareKernel ((⌊x⌋₊ : ℝ) + 1 / 2)
              ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) t‖
      ≤ perronNearError K M ⌊x + h⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T
        + (((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          (perronNearError K M ⌊x + h₁⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T) := by
  classical
  have hleh : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hleh₁ : ⌊x⌋₊ ≤ ⌊x + h₁⌋₊ := Nat.floor_le_floor (by linarith)
  have hAH : ⌊x⌋₊ + (⌊x + h⌋₊ - ⌊x⌋₊) = ⌊x + h⌋₊ := by omega
  have hAH₁ : ⌊x⌋₊ + (⌊x + h₁⌋₊ - ⌊x⌋₊) = ⌊x + h₁⌋₊ := by omega
  rw [sum_realWindow_eq_perronWindowSum c hx hh hM,
    sum_realWindow_eq_perronWindowSum c hx hh₁ hM₁]
  have hbase := norm_perronWindowSum_compare_sub_integral_le (c := c) (M := M) (A := ⌊x⌋₊)
    (H := ⌊x + h⌋₊ - ⌊x⌋₊) (H₁ := ⌊x + h₁⌋₊ - ⌊x⌋₊) (K := K) (T := T) hK hT
  rw [hAH, hAH₁] at hbase
  exact hbase

end

end RHTower.Sieve
