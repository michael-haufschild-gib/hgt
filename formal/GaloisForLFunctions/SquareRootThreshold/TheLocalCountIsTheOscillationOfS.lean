import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.ZeroCountRemainderNotIntegrable

/-!
# The local zero count is the oscillation of `S`

Write `N(T)` for the zero count (`xiZeroCount`), `M(T) = (T/2π) log(T/2πe) + 7/8` for its smooth main
term (`routeKSmoothRVMCount`) and `S = N − M` for the remainder (`rvmRemainder`).

* **Window bound** (`card_le_window_main_add_oscillation`).  A set of zero copies with ordinates in
  `(t, t + H]`, `t > 0`, has at most `(H/2π) log(t + H) + S(t + H) − S(t)` elements.
* **Equivalence of the two families** (`rvmRemainder_oscillation_le_of_window_le`,
  `window_le_of_rvmRemainder_oscillation_le`).  For `T₀ ≥ 2πe`, the local count
  `N(t + H) − N(t) ≤ C(H log(t + H) + 1)` for all `t ≥ T₀`, `0 ≤ H` implies the same bound for
  `S(t + H) − S(t)`, and the bound for `S` with `C` implies the local count with `C + 1/(2π)`.

So a count `≪ r log t + 1` of the zeros with ordinate within `r` of `t`, at every scale `r` — the
input that makes heat detection linear in the depth — is exactly a one-sided bound
`S(t + H) − S(t) ≪ H log t + 1` on the short-scale oscillation of `S`.  The unit-window count is the
case `H ≍ 1`; `S` itself is unbounded (`SquareRootThreshold.rvmRemainder_unbounded`).
-/

namespace RHTower

noncomputable section

/-- **Window bound.**  A set of zero copies with ordinates in `(t, t + H]`, `t > 0`, `H ≥ 0`, has at
most `(H/2π) log(t + H) + S(t + H) − S(t)` elements. -/
theorem card_le_window_main_add_oscillation {t H : ℝ} (ht : 0 < t) (hH : 0 ≤ H)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, t < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ t + H) :
    (F.card : ℝ) ≤ H / (2 * Real.pi) * Real.log (t + H) + (rvmRemainder (t + H) - rvmRemainder t) := by
  have h := card_le_xiZeroCount_sub ht.le hH F hF
  have h' : (F.card : ℝ) ≤ (xiZeroCount (t + H) : ℝ) - (xiZeroCount t : ℝ) := by exact_mod_cast h
  have hM := routeKSmoothRVMCount_add_sub_le ht hH
  unfold rvmRemainder zeroCountReal
  linarith

/-- The main term is nondecreasing beyond `2πe`. -/
theorem routeKSmoothRVMCount_mono_of_base_le {t t' : ℝ} (ht : routeKRVMBase ≤ t) (htt : t ≤ t') :
    routeKSmoothRVMCount t ≤ routeKSmoothRVMCount t' := by
  have hB : 0 < routeKRVMBase := by have := one_le_routeKRVMBase; linarith
  have ht0 : 0 < t := lt_of_lt_of_le hB ht
  have hl : 0 ≤ Real.log (t / routeKRVMBase) :=
    Real.log_nonneg (by rw [le_div_iff₀ hB]; linarith)
  have hll : Real.log (t / routeKRVMBase) ≤ Real.log (t' / routeKRVMBase) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right htt hB.le)
  unfold routeKSmoothRVMCount
  have h1 : t / (2 * Real.pi) ≤ t' / (2 * Real.pi) := div_le_div_of_nonneg_right htt (by positivity)
  have := mul_le_mul h1 hll hl (div_nonneg (by linarith) (by positivity))
  linarith

/-- **A local count bounds the oscillation of `S`.**  For `T₀ ≥ 2πe`, if
`N(t + H) − N(t) ≤ C(H log(t + H) + 1)` for all `t ≥ T₀` and `H ≥ 0`, then
`S(t + H) − S(t) ≤ C(H log(t + H) + 1)` on the same range. -/
theorem rvmRemainder_oscillation_le_of_window_le {C T₀ : ℝ} (hT₀ : routeKRVMBase ≤ T₀)
    (hwin : ∀ t : ℝ, T₀ ≤ t → ∀ H : ℝ, 0 ≤ H →
      (xiZeroCount (t + H) : ℝ) - (xiZeroCount t : ℝ) ≤ C * (H * Real.log (t + H) + 1))
    {t H : ℝ} (ht : T₀ ≤ t) (hH : 0 ≤ H) :
    rvmRemainder (t + H) - rvmRemainder t ≤ C * (H * Real.log (t + H) + 1) := by
  have hM := routeKSmoothRVMCount_mono_of_base_le (hT₀.trans ht) (show t ≤ t + H by linarith)
  have hw := hwin t ht H hH
  unfold rvmRemainder zeroCountReal
  linarith

/-- **An oscillation bound for `S` gives the local count.**  If
`S(t + H) − S(t) ≤ C(H log(t + H) + 1)` for all `t ≥ T₀ ≥ 1` and `H ≥ 0`, then
`N(t + H) − N(t) ≤ (C + 1/(2π))(H log(t + H) + 1)` on the same range. -/
theorem window_le_of_rvmRemainder_oscillation_le {C T₀ : ℝ} (hT₀ : 1 ≤ T₀)
    (hosc : ∀ t : ℝ, T₀ ≤ t → ∀ H : ℝ, 0 ≤ H →
      rvmRemainder (t + H) - rvmRemainder t ≤ C * (H * Real.log (t + H) + 1))
    {t H : ℝ} (ht : T₀ ≤ t) (hH : 0 ≤ H) :
    (xiZeroCount (t + H) : ℝ) - (xiZeroCount t : ℝ)
      ≤ (C + 1 / (2 * Real.pi)) * (H * Real.log (t + H) + 1) := by
  have ht0 : 0 < t := by linarith
  have hM := routeKSmoothRVMCount_add_sub_le ht0 hH
  have hS := hosc t ht H hH
  have hlog : 0 ≤ Real.log (t + H) := Real.log_nonneg (by linarith)
  have hπ : 0 < 2 * Real.pi := by positivity
  have e : H / (2 * Real.pi) * Real.log (t + H) = 1 / (2 * Real.pi) * (H * Real.log (t + H)) := by
    ring
  have h1 : 0 ≤ 1 / (2 * Real.pi) := by positivity
  unfold rvmRemainder zeroCountReal at hS
  nlinarith [mul_nonneg hH hlog]

end

end RHTower

