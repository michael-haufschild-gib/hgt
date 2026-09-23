import GaloisForLFunctions.RHTower.TwistedDistanceTransfer
import GaloisForLFunctions.RHTower.Sieve.PerronAntitwistEscape
import GaloisForLFunctions.RHTower.Sieve.DampedSizePointwise

/-!
# The twisted Perron integral with its antitwist cell

Twisting a real multiplicative function by `n^{-iτ}` moves its trivial frequency to `-τ`.  Every cell of
the Perron range except the unit window there has effective frequency at least one in modulus, so the
Littlewood deficit gives it the damped Euler size `exp(-Δ/4)`; the antitwist window is charged the
trivial size, but the Perron kernel there is `y^σ/(|τ|−1)`, so its total cost is the escape term

```text
2·V_A·V_B·(trivial size)·y^σ/(|τ|−1).
```

This is the unconditional cellwise transfer: the ordinary cells carry a quarter of the deficit, and the
antitwist cell carries only its own Lorentzian weight.
-/

noncomputable section

namespace RHTower

open RHTower.Sieve Complex MeasureTheory Set

/-- The twisted real sequence is a bounded coprime-multiplicative sequence with value one at one. -/
theorem twistSeq_real_one {r : ℕ → ℝ} (hr1 : r 1 = 1) (τ : ℝ) :
    twistSeq (fun n => (r n : ℂ)) τ 1 = 1 :=
  twistSeq_one (by rw [hr1]; norm_num) τ

theorem twistSeq_real_coprime_mul {r : ℕ → ℝ} (hr1 : r 1 = 1)
    (hrmul : ∀ {m n : ℕ}, Nat.Coprime m n → r (m * n) = r m * r n) (τ : ℝ) {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    twistSeq (fun n => (r n : ℂ)) τ (m * n)
      = twistSeq (fun n => (r n : ℂ)) τ m * twistSeq (fun n => (r n : ℂ)) τ n := by
  refine twistSeq_coprime_mul (by rw [hr1]; norm_num) (fun {a b} hab => ?_) τ hmn
  rw [hrmul hab]
  push_cast
  ring

theorem norm_twistSeq_real_le_one {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1) (τ : ℝ) (n : ℕ) :
    ‖twistSeq (fun n => (r n : ℂ)) τ n‖ ≤ 1 := by
  refine norm_twistSeq_le_one (fun k => ?_) τ n
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hr k

/-- **(Z12) The damped size of the twisted truncated series on an ordinary cell.** -/
theorem norm_LSeries_truncSeq_twistSeq_le_damped_at {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1)
    (hr1 : r 1 = 1) (hrmul : ∀ {m n : ℕ}, Nat.Coprime m n → r (m * n) = r m * r n)
    {β x τ σ t : ℝ} (hβ : 0 < β) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hσ : 1 < σ) {L : ℕ} (hL : 1 ≤ L)
    (hcell : 1 ≤ |τ + t|) (hhorizon : 2 * |τ + t| ≤ x ^ β) :
    ‖LSeries (truncSeq (twistSeq (fun n => (r n : ℂ)) τ) L) ((σ : ℂ) + (t : ℝ) * I)‖
      ≤ dampedSize σ (Real.sqrt (littlewoodCellGap β x)) ⌊x⌋₊ L := by
  refine norm_LSeries_truncSeq_line_le_damped_at (twistSeq_real_one hr1 τ)
    (fun {m n} h => twistSeq_real_coprime_mul hr1 (fun {a b} hab => hrmul hab) τ h)
    (norm_twistSeq_real_le_one hr τ) hσ (one_le_floor_of_horizon hx hx0) (Real.sqrt_nonneg _)
    hL ?_
  refine Real.sqrt_le_sqrt ?_
  exact littlewoodCellGap_le_mulDistSqPair_twistSeq hr hβ hx hx0 (by linarith) (by linarith)

/-- **(Z11) The twisted triple Perron integral.**  All but the antitwist window is damped by a quarter
of the Littlewood deficit; the antitwist window costs only its own kernel weight `1/(|τ|−1)`. -/
theorem integral_symm_norm_perron_triple_twisted_le
    {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1) (hr1 : r 1 = 1)
    (hrmul : ∀ {m n : ℕ}, Nat.Coprime m n → r (m * n) = r m * r n)
    {A B : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ y t₀ VA VB QA κA QB κB β x τ : ℝ} {L : ℕ} (M : ℕ)
    (hσ : 1 < σ) (hy : 0 < y) (ht₀ : 1 ≤ t₀) (hL : 1 ≤ L) (hVA : 0 ≤ VA) (hVB : 0 ≤ VB)
    (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hmsA : ∀ U : ℝ, 1 ≤ U →
      (∫ z in Set.Icc (-U) U, ‖LSeries A ((σ : ℂ) + (z : ℝ) * I)‖ ^ (2 : ℕ)) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, 1 ≤ U →
      (∫ z in Set.Icc (-U) U, ‖LSeries B ((σ : ℂ) + (z : ℝ) * I)‖ ^ (2 : ℕ)) ≤ QB + κB * U)
    (hβ : 0 < β) (hx : zetaHorizonLogThreshold ≤ Real.log x) (hx0 : 0 < x)
    (hτ : 1 < |τ|) (hhorizon : 2 * (|τ| + t₀ * 2 ^ M) ≤ x ^ β)
    (hAb : ∀ t : ℝ, ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VA)
    (hBb : ∀ t : ℝ, ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VB) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries (truncSeq (twistSeq (fun n => (r n : ℂ)) τ) L) ((σ : ℂ) + (t : ℝ) * I)
            * ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ (2 * perronVerticalAffineProductBound σ y t₀
              (dampedSize σ (Real.sqrt (littlewoodCellGap β x)) ⌊x⌋₊ L) QA κA QB κB M
            + (dampedSize σ (Real.sqrt (littlewoodCellGap β x)) ⌊x⌋₊ L * y ^ σ / σ)
                * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)))
          + 2 * (VA * VB * (dampedSize σ 0 ⌊x⌋₊ L * (y ^ σ / (|τ| - 1)))) := by
  have hz1 : 1 ≤ ⌊x⌋₊ := one_le_floor_of_horizon hx hx0
  have hf1 := twistSeq_real_one hr1 τ
  have hfmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      twistSeq (fun n => (r n : ℂ)) τ (m * n)
        = twistSeq (fun n => (r n : ℂ)) τ m * twistSeq (fun n => (r n : ℂ)) τ n :=
    fun {m n} h => twistSeq_real_coprime_mul hr1 (fun {a b} hab => hrmul hab) τ h
  have hfbdd := norm_twistSeq_real_le_one hr τ
  have hFc : Continuous fun t : ℝ =>
      LSeries (truncSeq (twistSeq (fun n => (r n : ℂ)) τ) L) ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support (s := Finset.Icc 1 L) (by simp)
      (fun n hn => truncSeq_support hn) σ
  have habsneg : |(-τ : ℝ)| = |τ| := abs_neg τ
  have hmain := integral_symm_norm_perron_triple_punctured_affine_le
    (A := A) (B := B) (f := truncSeq (twistSeq (fun n => (r n : ℂ)) τ) L)
    hA0 hAsupp hB0 hBsupp (σ := σ) (x := y) (t₀ := t₀)
    (V := dampedSize σ (Real.sqrt (littlewoodCellGap β x)) ⌊x⌋₊ L)
    (Vtr := dampedSize σ 0 ⌊x⌋₊ L) (VA := VA) (VB := VB) (c := -τ)
    (by linarith) hy ht₀ (dampedSize_nonneg hσ _ _) (dampedSize_nonneg hσ _ _) hVA hVB
    hQA hκA hQB hκB hFc hmsA hmsB M (by rw [habsneg]; exact hτ) ?_ ?_ hAb hBb
  · rw [habsneg] at hmain
    exact hmain
  · intro t ht hcell
    have hcell' : 1 ≤ |τ + t| := by
      have hswap : |t - -τ| = |τ + t| := by
        rw [sub_neg_eq_add, add_comm]
      rw [hswap] at hcell
      exact hcell
    have hupper : 2 * |τ + t| ≤ x ^ β := by
      have h1 : |τ + t| ≤ |τ| + |t| := abs_add_le τ t
      linarith
    exact norm_LSeries_truncSeq_twistSeq_le_damped_at hr hr1 (fun {a b} hab => hrmul hab)
      hβ hx hx0 hσ hL hcell' hupper
  · intro t
    exact norm_LSeries_truncSeq_line_le_trivial_size hf1 (fun {a b} hab => hfmul hab) hfbdd
      hσ hz1 hL t

end RHTower

end
