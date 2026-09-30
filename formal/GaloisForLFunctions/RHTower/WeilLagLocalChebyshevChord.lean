import GaloisForLFunctions.RHTower.WeilLagQuadraticInterpolation
import GaloisForLFunctions.RHTower.SuzukiWeilLagTailBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Local signed Chebyshev work for the integer Weil lag

The barycentric lag chord cancels the shared Chebyshev-error tail. Its exact
prime-compensated defect is two finite signed integrals, unchanged after
subtracting any constant from the error. The resulting local upper-interpolation
law retains the actual prime data and does not assert a uniform work bound.
-/

open Real Set MeasureTheory

namespace RHTower

noncomputable section

private theorem lagChebyshevTail_sub_eq_local {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    weilLagChebyshevTail n - weilLagChebyshevTail m =
      ∫ t in Ioc (n : ℝ) m, chebyshevError t / t ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hi : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi (n : ℝ)) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hnR)
  have hsplit : weilLagChebyshevTail n =
      (∫ t in Ioc (n : ℝ) m, chebyshevError t / t ^ 2) + weilLagChebyshevTail m := by
    unfold weilLagChebyshevTail
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hnmR)),
      Ioc_union_Ioi_eq_Ioi hnmR]
  linarith only [hsplit]

/-- The exact prime-compensated chord defect is finite local signed Chebyshev work. -/
theorem lagPrimeChordDefect_eq_local_chebyshevWork {n k m : ℕ}
    (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    (u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
        lagPrimeChordCharge m n m u v =
      u * n * (∫ t in Ioc (n : ℝ) k, chebyshevError t / t ^ 2) -
        v * m * (∫ t in Ioc (k : ℝ) m, chebyshevError t / t ^ 2) := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  have h := sqrt_integerLag_chord_exact hn hnk hkm hu hv huv hmean
  rw [sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch k hk,
    sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch n hn,
    sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch m hm] at h
  rw [← lagChebyshevTail_sub_eq_local (by omega : 1 ≤ n) hnk,
    ← lagChebyshevTail_sub_eq_local (by omega : 1 ≤ k) hkm]
  have hmeanTail : (k : ℝ) * weilLagChebyshevTail k =
      (u * n + v * m) * weilLagChebyshevTail k := by rw [hmean]
  have hconst : u * Real.log (2 * π) + v * Real.log (2 * π) = Real.log (2 * π) := by
    calc _ = (u + v) * Real.log (2 * π) := by ring
      _ = _ := by rw [huv, one_mul]
  linarith only [h, hmeanTail, hconst]

private theorem lagIntegral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Ioc a b, 1 / t ^ 2) = 1 / a - 1 / b := by
  rw [← intervalIntegral.integral_of_le hab]
  have hz : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    have := h.1
    linarith
  have h := integral_zpow (a := a) (b := b) (n := (-2 : ℤ)) (Or.inr ⟨by omega, hz⟩)
  have hden : -((2 : ℤ) : ℝ) + 1 = -1 := by push_cast; ring
  simpa only [show (-2 : ℤ) + 1 = -1 by omega, zpow_neg, zpow_natCast, zpow_one, pow_one,
    Int.cast_neg, Int.cast_one, hden, div_neg, div_one, neg_sub, one_div] using! h

private theorem lagIntegrable_inv_sq {a b : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioc a b) := by
  have hc : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Icc a b) :=
    continuousOn_const.div ((continuous_id.pow 2).continuousOn) (by
      intro t ht
      have ht0 : 0 < t := (zero_lt_one.trans_le ha).trans_le ht.1
      positivity)
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem lagCentered_local_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in Ioc a b, (chebyshevError t - c) / t ^ 2) =
      (∫ t in Ioc a b, chebyshevError t / t ^ 2) - c * (1 / a - 1 / b) := by
  have he : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioc a b) :=
    integrableOn_chebyshevError_div_sq.mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha))
  have hc : IntegrableOn (fun t : ℝ => c * (1 / t ^ 2)) (Ioc a b) :=
    lagIntegrable_inv_sq ha |>.const_mul c
  have hfun : (fun t : ℝ => (chebyshevError t - c) / t ^ 2) =
      (fun t : ℝ => chebyshevError t / t ^ 2 - c * (1 / t ^ 2)) := by
    funext t
    ring
  rw [hfun, integral_sub he hc, integral_const_mul,
    lagIntegral_inv_sq (zero_lt_one.trans_le ha) hab]

/-- Subtracting any constant error level leaves the exact chord work unchanged. -/
theorem lagPrimeChordDefect_eq_centered_local_chebyshevWork {n k m : ℕ}
    (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) (c : ℝ) :
    (u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
        lagPrimeChordCharge m n m u v =
      u * n * (∫ t in Ioc (n : ℝ) k, (chebyshevError t - c) / t ^ 2) -
        v * m * (∫ t in Ioc (k : ℝ) m, (chebyshevError t - c) / t ^ 2) := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  rw [lagCentered_local_integral (by exact_mod_cast (by omega : 1 ≤ n))
    (by exact_mod_cast hnk), lagCentered_local_integral
    (by exact_mod_cast (by omega : 1 ≤ k)) (by exact_mod_cast hkm)]
  rw [lagPrimeChordDefect_eq_local_chebyshevWork hn hnk hkm hu hv huv hmean]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hcancel : u * n * (1 / (n : ℝ) - 1 / (k : ℝ)) -
      v * m * (1 / (k : ℝ) - 1 / (m : ℝ)) = 0 := by
    field_simp
    nlinarith only [hmean, huv]
  linear_combination c * hcancel

/-- Every actual lag has a local signed-work upper certificate at any constant error level. -/
theorem integerLag_local_chebyshev_upper_interpolation :
    ∀ n k m : ℕ, 2 ≤ n → n ≤ k → k ≤ m →
      ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v = 1 → (k : ℝ) = u * n + v * m →
        ∀ c : ℝ, integerLag k ≤ max 0 (max (integerLag n) (integerLag m)) +
          (u * n * (∫ t in Ioc (n : ℝ) k, (chebyshevError t - c) / t ^ 2) -
            v * m * (∫ t in Ioc (k : ℝ) m, (chebyshevError t - c) / t ^ 2)) / Real.sqrt k := by
  intro n k m hn hnk hkm u v hu hv huv hmean c
  have h := integerLag_chord_prime_ceiling hn hnk hkm hu hv huv hmean
    (le_max_left 0 (max (integerLag n) (integerLag m)))
    ((le_max_left (integerLag n) (integerLag m)).trans
      (le_max_right 0 (max (integerLag n) (integerLag m))))
    ((le_max_right (integerLag n) (integerLag m)).trans
      (le_max_right 0 (max (integerLag n) (integerLag m))))
  rw [lagPrimeChordDefect_eq_centered_local_chebyshevWork hn hnk hkm hu hv huv hmean c] at h
  exact h

end

end RHTower
