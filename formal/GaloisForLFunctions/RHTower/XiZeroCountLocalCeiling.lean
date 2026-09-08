import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.MontgomeryZeroSumWindow

/-!
# The sharp local ceiling and the block-length law

The Riemann–von Mangoldt count with logarithmic remainder,
`|N(T) − (T/2π) log(T/2πe) − 7/8| ≤ C log T`, gives a sharp ceiling on the number of zeros in any
ordinate window: for `t ≥ T₀` and `H ≥ 0`,

`N(t+H) − N(t) ≤ (H/2π) log(t+H) + 2C log(t+H)`,

by convexity of `u log u`.  Consequently a set of zero copies whose ordinates lie in an interval
of length `H` has at most that many elements, and a **block** — `L` copies whose ordinates span at
most `(1−ε)(L−1)` mean gaps `2π/log(t+H)` — has `L ≤ 2C log(t+H)/ε`.  Sub-mean-gap clustering of
zeros therefore cannot persist beyond `O(log T/ε)` zeros: the evader class of the isolation
dichotomy consists of short blocks only.
-/

open Set

namespace RHTower

noncomputable section

/-- Convexity of `u log u`: `b log b − a log a ≤ (b − a)(log b + 1)` for `0 < a ≤ b`. -/
theorem mul_log_sub_mul_log_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b * Real.log b - a * Real.log a ≤ (b - a) * (Real.log b + 1) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hx : 0 < a / b := div_pos ha hb
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  rw [Real.log_div ha.ne' hb.ne', inv_div] at h1
  have h2 : a * (Real.log a - Real.log b) ≥ a * (1 - b / a) := mul_le_mul_of_nonneg_left h1 ha.le
  have h3 : a * (1 - b / a) = a - b := by field_simp
  nlinarith

/-- Increment of the smooth Riemann–von Mangoldt main term over a window of length `H`. -/
theorem routeKSmoothRVMCount_add_sub_le {t H : ℝ} (ht : 0 < t) (hH : 0 ≤ H) :
    routeKSmoothRVMCount (t + H) - routeKSmoothRVMCount t
      ≤ H / (2 * Real.pi) * Real.log (t + H) := by
  have htH : 0 < t + H := by linarith
  rw [routeKSmoothRVMCount_sub_eq ht htH]
  have hB : Real.log routeKRVMBase = Real.log (2 * Real.pi) + 1 := by
    rw [routeKRVMBase, Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have hconv := mul_log_sub_mul_log_le ht (by linarith : t ≤ t + H)
  have hlog2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hB, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hHH : (t + H - t) = H := by ring
  rw [hHH] at hconv
  rw [hHH]
  have hR : H / (2 * Real.pi) * Real.log (t + H) * (2 * Real.pi) = H * Real.log (t + H) := by
    field_simp
  rw [hR]
  have := mul_nonneg hH hlog2π
  linarith

/-- **Sharp local ceiling, count form.**  There are `C, T₀` with
`N(t+H) − N(t) ≤ (H/2π) log(t+H) + 2C log(t+H)` for all `t ≥ T₀`, `H ≥ 0`. -/
theorem exists_xiZeroCount_window_le :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ H : ℝ, 0 ≤ H →
      ((xiZeroCount (t + H) : ℝ) - (xiZeroCount t : ℝ))
        ≤ H / (2 * Real.pi) * Real.log (t + H) + 2 * C * Real.log (t + H) := by
  obtain ⟨C, hC, T₀, hT₀, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C, hC, T₀, hT₀, fun t ht H hH => ?_⟩
  have ht0 : 0 < t := by linarith
  have htH : T₀ ≤ t + H := by linarith
  have h1 := hrem t ht
  have h2 := hrem (t + H) htH
  have hlog : Real.log t ≤ Real.log (t + H) := Real.log_le_log ht0 (by linarith)
  have hsmooth := routeKSmoothRVMCount_add_sub_le ht0 hH
  have h1' := (abs_le.mp h1).2
  have h1'' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).2
  have h2'' := (abs_le.mp h2).1
  nlinarith [hC.le, hlog]

/-- A finite set of zero copies with ordinates in `(t, t+H]` (`t ≥ 0`) has at most
`N(t+H) − N(t)` elements. -/
theorem card_le_xiZeroCount_sub {t H : ℝ} (ht : 0 ≤ t) (hH : 0 ≤ H) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, t < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ t + H) :
    (F.card : ℤ) ≤ xiZeroCount (t + H) - xiZeroCount t := by
  classical
  set S₁ := xiSupportsPos t with hS₁
  set S₂ := xiSupportsPos (t + H) with hS₂
  have hsub : S₁ ⊆ S₂ := by
    intro ρ hρ
    rw [hS₁, mem_xiSupportsPos] at hρ
    rw [hS₂, mem_xiSupportsPos]
    exact ⟨hρ.1.trans (by linarith), hρ.2⟩
  have hcount : xiZeroCount (t + H) - xiZeroCount t =
      ∑ ρ ∈ S₂ \ S₁, (xiSupportMultiplicity ρ : ℤ) := by
    rw [xiZeroCount_eq_pos_sum (by linarith), xiZeroCount_eq_pos_sum ht, ← hS₁, ← hS₂,
      ← Finset.sum_sdiff hsub]
    ring
  rw [hcount]
  -- `F` sits inside the sigma-finset over the new supports
  have hFsub : F ⊆ (S₂ \ S₁).sigma (fun ρ => (Finset.univ : Finset (Fin (xiSupportMultiplicity ρ)))) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hF q hq
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_sdiff, hS₂, hS₁, mem_xiSupportsPos, mem_xiSupportsPos]
    have hpos : 0 < (q.1 : ℂ).im := by linarith
    refine ⟨⟨by rw [abs_of_pos hpos]; exact h2, hpos⟩, ?_⟩
    rintro ⟨h3, -⟩
    rw [abs_of_pos hpos] at h3
    linarith
  have hcard := Finset.card_le_card hFsub
  rw [Finset.card_sigma] at hcard
  have hsum : (∑ a ∈ S₂ \ S₁, (Finset.univ : Finset (Fin (xiSupportMultiplicity a))).card) =
      ∑ a ∈ S₂ \ S₁, xiSupportMultiplicity a :=
    Finset.sum_congr rfl fun a _ => Finset.card_fin _
  exact_mod_cast hcard.trans hsum.le

/-- **Sharp local ceiling, card form.**  Zero copies with ordinates in a window `(t, t+H]` number
at most `(H/2π) log(t+H) + 2C log(t+H)`. -/
theorem exists_card_window_le :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ H : ℝ, 0 ≤ H →
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, t < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ t + H) →
      (F.card : ℝ) ≤ H / (2 * Real.pi) * Real.log (t + H) + 2 * C * Real.log (t + H) := by
  obtain ⟨C, hC, T₀, hT₀, hceil⟩ := exists_xiZeroCount_window_le
  refine ⟨C, hC, T₀, hT₀, fun t ht H hH F hF => ?_⟩
  have h1 := card_le_xiZeroCount_sub (by linarith) hH F hF
  have h1' : (F.card : ℝ) ≤ (xiZeroCount (t + H) : ℝ) - (xiZeroCount t : ℝ) := by
    exact_mod_cast h1
  exact h1'.trans (hceil t ht H hH)

/-- **Block-length law.**  A set of `L` zero copies whose ordinates lie in `(t, t+H]` with
`H ≤ (1−ε)(L−1)·2π/log(t+H)` (sub-mean-gap spacing) satisfies `L ≤ 2C log(t+H)/ε`. -/
theorem exists_card_block_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ H : ℝ, 0 ≤ H →
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, t < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ t + H) →
      H * Real.log (t + H) ≤ (1 - ε) * ((F.card : ℝ) - 1) * (2 * Real.pi) →
      (F.card : ℝ) ≤ 2 * C * Real.log (t + H) / ε := by
  obtain ⟨C, hC, T₀, hT₀, hceil⟩ := exists_card_window_le
  refine ⟨C, hC, T₀, hT₀, fun t ht H hH F hF hblock => ?_⟩
  have h1 := hceil t ht H hH F hF
  have hlogpos : 0 < Real.log (t + H) := Real.log_pos (by linarith)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hmain : H / (2 * Real.pi) * Real.log (t + H) ≤ (1 - ε) * ((F.card : ℝ) - 1) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
    linarith
  have hL : (F.card : ℝ) ≤ (1 - ε) * ((F.card : ℝ) - 1) + 2 * C * Real.log (t + H) := by
    linarith
  rw [le_div_iff₀ hε]
  nlinarith [hε1, Nat.cast_nonneg (α := ℝ) F.card]

end

end RHTower
