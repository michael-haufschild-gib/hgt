import GaloisForLFunctions.RHTower.Sieve.SquarefreeTailTruncate
import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow

/-!
# Ingredients for the fibre squarefree mass
-/

namespace RHTower.Sieve

open Finset

/-- The truncation tail of a window, as a real number. -/
noncomputable def windowTail (t L R M : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (R + 1) M, ((#{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} : ℕ) : ℝ)

theorem windowTail_nonneg (t L R M : ℕ) : 0 ≤ windowTail t L R M :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **The tail grows with the window.** -/
theorem windowTail_mono {t L L' R M : ℕ} (hL : L ≤ L') :
    windowTail t L R M ≤ windowTail t L' R M := by
  classical
  refine Finset.sum_le_sum fun d _ => ?_
  have hsub : Finset.Ioc t (t + L) ⊆ Finset.Ioc t (t + L') :=
    Finset.Ioc_subset_Ioc_right (by omega)
  have : #{n ∈ Finset.Ioc t (t + L) | d ^ (2 : ℕ) ∣ n} ≤ #{n ∈ Finset.Ioc t (t + L') | d ^ (2 : ℕ) ∣ n} :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  exact_mod_cast this

/-- **Every fibre is short.**  The fibre above `a ≥ √x` has length at most `⌈h⌉ + 1`. -/
theorem fibreLen_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ} (ha : a ∈ outerBlock x h) :
    fibreLen x h a ≤ ⌈h⌉₊ + 1 := by
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hs0 hlow
  set P : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with hP
  set Q : ℕ := ⌈x / (a : ℝ)⌉₊ - 1 with hQ
  by_cases hPQ : P ≤ Q
  · have : fibreLen x h a = 0 := by
      rw [fibreLen, fibreStartIdx, ← hP, ← hQ]
      omega
    omega
  · have hlt : Q < P := by omega
    have hQ1 : 1 ≤ ⌈x / (a : ℝ)⌉₊ := by
      refine Nat.one_le_ceil_iff.2 ?_
      positivity
    have hQcast : (Q : ℝ) = (⌈x / (a : ℝ)⌉₊ : ℝ) - 1 := by
      rw [hQ, Nat.cast_sub hQ1]
      norm_num
    have hPle : (P : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := Nat.floor_le (by positivity)
    have hQge : x / (a : ℝ) - 1 ≤ (Q : ℝ) := by
      rw [hQcast]
      have := Nat.le_ceil (x / (a : ℝ))
      linarith
    have hgap : (P : ℝ) - (Q : ℝ) ≤ h + 1 := by
      have hval : (x + h * Real.sqrt x) / (a : ℝ) - x / (a : ℝ)
          = h * Real.sqrt x / (a : ℝ) := by
        field_simp
        ring
      have hdiv : h * Real.sqrt x / (a : ℝ) ≤ h := by
        rw [div_le_iff₀ ha0]
        nlinarith [hlow, hh, hs0]
      linarith [hPle, hQge, hval, hdiv]
    have hnat : (fibreLen x h a : ℝ) ≤ h + 1 := by
      have hcast : (fibreLen x h a : ℝ) = (P : ℝ) - (Q : ℝ) := by
        rw [fibreLen, fibreStartIdx, ← hP, ← hQ, Nat.cast_sub hlt.le]
      rw [hcast]
      exact hgap
    have hceil : h + 1 ≤ ((⌈h⌉₊ : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil h
      linarith
    have : (fibreLen x h a : ℝ) ≤ ((⌈h⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [hnat, hceil]
    exact_mod_cast this

end RHTower.Sieve
