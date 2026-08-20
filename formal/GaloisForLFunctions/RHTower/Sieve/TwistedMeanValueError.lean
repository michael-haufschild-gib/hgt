import GaloisForLFunctions.RHTower.Sieve.TwistedOffDiagonalSum

/-!
# The twisted mean value theorem in error form

Combining the exact diagonal split with the harmonic off-diagonal row sum: for Dirichlet
polynomials supported in `[1, N]` and a twist by `(h/k)^{-it}` with `h, k ≤ y`, the window integral
differs from `U` times the diagonal `nk = mh` by at most

```text
4 · #s · C · N y · (1 + log #s),
```

`C` being any uniform bound on the coefficient products.  The bound is `U`-free: it is the exact
analogue of the classical mean value theorem for Dirichlet polynomials, with the twist folded into
the diagonal condition.
-/

open Finset Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

theorem norm_expInt_twisted_le_gap {m n h k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hk : 1 ≤ k) (hne : n * k ≠ m * h) {B : ℝ}
    (hB1 : ((n * k : ℕ) : ℝ) ≤ B) (hB2 : ((m * h : ℕ) : ℝ) ≤ B) (T U : ℝ) :
    ‖expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
      ≤ 2 * B / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)| := by
  have hnk : (0 : ℝ) < ((n * k : ℕ) : ℝ) := by
    have : 1 ≤ n * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hmh : (0 : ℝ) < ((m * h : ℕ) : ℝ) := by
    have : 1 ≤ m * h := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hfreq := twistedFreq_eq hm hn hh hk
  have hL : Real.log n - Real.log m + (Real.log k - Real.log h) ≠ 0 := by
    rw [hfreq]
    intro h0
    have hlog : Real.log ((n * k : ℕ) : ℝ) = Real.log ((m * h : ℕ) : ℝ) := by linarith
    have heq : ((n * k : ℕ) : ℝ) = ((m * h : ℕ) : ℝ) := by
      rw [← Real.exp_log hnk, ← Real.exp_log hmh, hlog]
    exact hne (by exact_mod_cast heq)
  refine le_trans (norm_expInt_le hL T U) ?_
  rw [hfreq]
  exact two_div_abs_log_twisted_le hm hn hh hk hne hB1 hB2

/-- **The twisted mean value theorem, error form.** -/
theorem twisted_meanValue_error (a b : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {h k : ℕ}
    (hh : 1 ≤ h) (hk : 1 ≤ k) (hs : ∀ n ∈ s, 1 ≤ n)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n ∈ s, ∀ j : ℕ, j = h ∨ j = k → ((n * j : ℕ) : ℝ) ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ∈ s, ∀ n ∈ s, ‖twistedCoeff a b σ m n‖ ≤ C) (T U : ℝ) :
    ‖(∫ t in T..(T + U), cdpoly a s σ t * (starRingEnd ℂ) (cdpoly b s σ t)
          * Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I))
        - (U : ℂ) * (∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h),
            twistedCoeff a b σ m n)‖
      ≤ 4 * (s.card : ℝ) * C * B * (1 + Real.log s.card) := by
  classical
  rw [twisted_meanValue_split a b s σ hh hk hs T U, add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) ?_
  have hrow : ∀ m ∈ s, ‖∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
      twistedCoeff a b σ m n
        * expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
      ≤ 4 * C * B * (1 + Real.log s.card) := by
    intro m hm
    have hm1 : 1 ≤ m := hs m hm
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
        ‖twistedCoeff a b σ m n
            * expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
          ≤ (2 * B * C) * ((1 : ℝ) / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)|) := by
      intro n hn
      obtain ⟨hns, hneq⟩ := Finset.mem_filter.mp hn
      rw [norm_mul]
      have hgap := norm_expInt_twisted_le_gap hm1 (hs n hns) hh hk hneq
        (hB n hns k (Or.inr rfl)) (hB m hm h (Or.inl rfl)) T U
      have hstep : ‖twistedCoeff a b σ m n‖
          * ‖expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
          ≤ C * (2 * B / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)|) :=
        mul_le_mul (hC m hm n hns) hgap (norm_nonneg _) hC0
      refine le_trans hstep (le_of_eq ?_)
      field_simp
      try ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsumrow := sum_inv_abs_twisted_row_le (s := s) (m := m) (h := h) (k := k) hk
    have hnn : (0 : ℝ) ≤ 2 * B * C := by positivity
    have := mul_le_mul_of_nonneg_left hsumrow hnn
    calc (2 * B * C)
          * ∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
              (1 : ℝ) / |((n * k : ℕ) : ℝ) - ((m * h : ℕ) : ℝ)|
        ≤ (2 * B * C) * (2 * (1 + Real.log s.card)) := this
      _ = 4 * C * B * (1 + Real.log s.card) := by ring
  refine le_trans (Finset.sum_le_sum hrow) (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end RHTower.Sieve

end
