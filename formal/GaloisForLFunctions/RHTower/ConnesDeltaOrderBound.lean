import GaloisForLFunctions.RHTower.ConnesDivisionDistribution

/-!
# Appendix I (28): the order bound on the delta coefficients

Appendix I (28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesDivisionDistribution` shows that `δ^{(k)}` solves `φ·α = 0` exactly when `k` is below the
order of the zero.  This file upgrades that to the statement Connes actually uses: in the delta
representation of a solution, *every* coefficient of index at least the order vanishes.  So the
solution space at a zero of order `n` is spanned by `δ, δ', …, δ^{(n-1)}` — the multiplicity
statement of Theorem III.1.
-/

open GaloisForLFunctions.HTGeometry Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Below the index `k`, the jet test `jetTest (k − n)` is annihilated by an order-`n` zero. -/
theorem connes_iteratedDeriv_mul_jetTest_lt {φ : ℝ → ℂ} {n k j : ℕ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hvanish : ∀ i, i < n → iteratedDeriv i φ 0 = 0)
    (hnk : n ≤ k) (hj : j < k) :
    iteratedDeriv j (fun x => φ x * (jetTest (k - n) : ℝ → ℂ) x) 0 = 0 := by
  have hφj : ContDiffAt ℝ (j : ℕ∞) φ 0 := (hφ.of_le (by exact_mod_cast le_top)).contDiffAt
  have hψj : ContDiffAt ℝ (j : ℕ∞) (jetTest (k - n) : ℝ → ℂ) 0 :=
    (((jetTest (k - n)).smooth').of_le (by exact_mod_cast le_top)).contDiffAt
  have hfun : (fun x => φ x * (jetTest (k - n) : ℝ → ℂ) x)
      = φ * (jetTest (k - n) : ℝ → ℂ) := rfl
  rw [hfun, iteratedDeriv_mul hφj hψj]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_jetTest_zero]
  by_cases hcase : j - i = k - n
  · rw [if_pos hcase, mul_one]
    have hin : i < n := by omega
    rw [hvanish i hin]
    ring
  · rw [if_neg hcase, mul_zero]

/-- **Appendix I (28), the order bound.**  If a delta combination solves `φ·α = 0` at a zero of
order `n`, all its coefficients of index `≥ n` vanish. -/
theorem connes_delta_coeffs_vanish_above_order {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {φ : ℝ → ℂ} {n M : ℕ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hvanish : ∀ i, i < n → iteratedDeriv i φ 0 = 0)
    (hnz : iteratedDeriv n φ 0 ≠ 0) (c : ℕ → X)
    (hker : ∀ ψ : SchwartzMap ℝ ℂ,
      ∑ j ∈ Finset.range (M + 1),
        (iteratedDeriv j (fun x => φ x * (ψ : ℝ → ℂ) x) 0) • c j = 0) :
    ∀ j, n ≤ j → j ≤ M → c j = 0 := by
  have key : ∀ d : ℕ, ∀ j : ℕ, n ≤ j → j ≤ M → M - j = d → c j = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hnj hjM hd
      have hsum := hker (jetTest (j - n))
      have hsingle : (∑ i ∈ Finset.range (M + 1),
            (iteratedDeriv i (fun x => φ x * (jetTest (j - n) : ℝ → ℂ) x) 0) • c i)
          = (iteratedDeriv j (fun x => φ x * (jetTest (j - n) : ℝ → ℂ) x) 0) • c j := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro i hi hij
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · rw [connes_iteratedDeriv_mul_jetTest_lt hφ hvanish hnj hlt, zero_smul]
          · have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hci : c i = 0 := ih (M - i) (by omega) i (by omega) hiM rfl
            rw [hci, smul_zero]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
      rw [hsingle, connes_iteratedDeriv_mul_ne_zero_of_le hφ hvanish hnj] at hsum
      have hscal : ((j.choose n : ℂ) * iteratedDeriv n φ 0) ≠ 0 := by
        refine mul_ne_zero ?_ hnz
        have hpos : 0 < j.choose n := Nat.choose_pos hnj
        exact_mod_cast hpos.ne'
      have h1 : ((j.choose n : ℂ) * iteratedDeriv n φ 0)⁻¹
          • (((j.choose n : ℂ) * iteratedDeriv n φ 0) • c j)
          = ((j.choose n : ℂ) * iteratedDeriv n φ 0)⁻¹ • (0 : X) := by
        rw [hsum]
      rw [smul_smul, inv_mul_cancel₀ hscal, one_smul, smul_zero] at h1
      exact h1
  intro j hnj hjM
  exact key (M - j) j hnj hjM rfl

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry Finset

/-- **Appendix I (28), the order bound, jet form.**  The same conclusion as
`connes_delta_coeffs_vanish_above_order`, but only the jet test functions are needed as input —
so no temperate-growth hypothesis on the multiplier is required anywhere. -/
theorem connes_delta_coeffs_vanish_above_order_jet {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {φ : ℝ → ℂ} {n M : ℕ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hvanish : ∀ i, i < n → iteratedDeriv i φ 0 = 0)
    (hnz : iteratedDeriv n φ 0 ≠ 0) (c : ℕ → X)
    (hker : ∀ m : ℕ,
      ∑ j ∈ Finset.range (M + 1),
        (iteratedDeriv j (fun x => φ x * (jetTest m : ℝ → ℂ) x) 0) • c j = 0) :
    ∀ j, n ≤ j → j ≤ M → c j = 0 := by
  have key : ∀ d : ℕ, ∀ j : ℕ, n ≤ j → j ≤ M → M - j = d → c j = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hnj hjM hd
      have hsum := hker (j - n)
      have hsingle : (∑ i ∈ Finset.range (M + 1),
            (iteratedDeriv i (fun x => φ x * (jetTest (j - n) : ℝ → ℂ) x) 0) • c i)
          = (iteratedDeriv j (fun x => φ x * (jetTest (j - n) : ℝ → ℂ) x) 0) • c j := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro i hi hij
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · rw [connes_iteratedDeriv_mul_jetTest_lt hφ hvanish hnj hlt, zero_smul]
          · have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hci : c i = 0 := ih (M - i) (by omega) i (by omega) hiM rfl
            rw [hci, smul_zero]
        · intro hmem
          exact absurd (Finset.mem_range.mpr (by omega)) hmem
      rw [hsingle, connes_iteratedDeriv_mul_ne_zero_of_le hφ hvanish hnj] at hsum
      have hscal : ((j.choose n : ℂ) * iteratedDeriv n φ 0) ≠ 0 := by
        refine mul_ne_zero ?_ hnz
        have hpos : 0 < j.choose n := Nat.choose_pos hnj
        exact_mod_cast hpos.ne'
      have h1 : ((j.choose n : ℂ) * iteratedDeriv n φ 0)⁻¹
          • (((j.choose n : ℂ) * iteratedDeriv n φ 0) • c j)
          = ((j.choose n : ℂ) * iteratedDeriv n φ 0)⁻¹ • (0 : X) := by
        rw [hsum]
      rw [smul_smul, inv_mul_cancel₀ hscal, one_smul, smul_zero] at h1
      exact h1
  intro j hnj hjM
  exact key (M - j) j hnj hjM rfl

end

end GaloisForLFunctions.RHTower
