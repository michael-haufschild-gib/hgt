import GaloisForLFunctions.HTGeometry.UnimodularLevelInterlacing
import GaloisForLFunctions.RHTower.SuzukiCoalescingRealAxisPhase

/-!
# The real-axis phase of a fragmented carrier, and its Clark level count

The countermodel carrier is an anchor chart times an `N`-fold repeated pole.  Along the real axis
its phase is the sum of the two continuous half-plane phases,

`Φ(x) = polePhase 0 c x + N · polePhase u v x`,

strictly increasing because both summands are.  The anchor contributes a nonnegative gain and each
copy of the pole contributes a full turn less a deficit proportional to its depth, so

`Φ(β) - Φ(α) ≥ 2πN - 2Nv (1/(β-u) + 1/(u-α))`

whenever the foot `u` lies inside `[α, β]`.  Feeding that gain to the monotone level count makes
both antipodal Clark levels appear `N - O(1)` times in the interval, strictly interlacing, with the
loss controlled by `N v` alone — the depth budget, not the number of factors.
-/

noncomputable section

namespace RHTower

open Complex Real Set GaloisForLFunctions.HTGeometry

/-- The composite real-axis phase of an anchor times an `N`-fold pole. -/
def suzukiFragmentPhase (c u v : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  polePhase 0 c x + (N : ℝ) * polePhase u v x

theorem continuous_suzukiFragmentPhase {c v : ℝ} (hc : 0 < c) (hv : 0 < v) (u : ℝ) (N : ℕ) :
    Continuous (suzukiFragmentPhase c u v N) := by
  unfold suzukiFragmentPhase
  exact (continuous_polePhase 0 hc).add ((continuous_polePhase u hv).const_smul (N : ℝ))

theorem strictMono_suzukiFragmentPhase {c v : ℝ} (hc : 0 < c) (hv : 0 < v) (u : ℝ) (N : ℕ) :
    StrictMono (suzukiFragmentPhase c u v N) := by
  unfold suzukiFragmentPhase
  exact (strictMono_polePhase 0 hc).add_monotone
    ((strictMono_polePhase u hv).monotone.const_mul (Nat.cast_nonneg N))

/-- **`(42)`.**  A full turn per pole, less a deficit proportional to the depth budget `N v`. -/
theorem suzukiFragmentPhase_gain_ge {c u v α β : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hα : α < u) (hβ : u < β) (N : ℕ) :
    2 * π * N - 2 * (N : ℝ) * v * (1 / (β - u) + 1 / (u - α))
      ≤ suzukiFragmentPhase c u v N β - suzukiFragmentPhase c u v N α := by
  have hanchor : polePhase 0 c α ≤ polePhase 0 c β :=
    (strictMono_polePhase 0 hc).monotone (by linarith)
  have hpole := polePhase_nsmul_gain_ge (u := u) (v := v) (α := α) (β := β) N hv hα hβ
  unfold suzukiFragmentPhase
  have hexpand : (N : ℝ) * polePhase u v β - (N : ℝ) * polePhase u v α
      = (N : ℝ) * (polePhase u v β - polePhase u v α) := by ring
  linarith [hexpand]

/-- **`(38)`.**  Both antipodal Clark levels of the fragmented carrier are attained `M + 1` and `M`
times in `[α, β]`, strictly interlacing, for any `M` the phase gain can pay for.  Combined with
`(42)` this gives `N - O(1)` crossings of each level with the loss governed by the depth budget. -/
theorem exists_interlacing_suzukiFragment_levels {c u v α β : ℝ} (hc : 0 < c) (hv : 0 < v)
    (hα : α < u) (hβ : u < β) (N : ℕ) {M : ℕ}
    (hM : 2 * π * M ≤ 2 * π * N - 2 * (N : ℝ) * v * (1 / (β - u) + 1 / (u - α))) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ M, x k ∈ Icc α β ∧
        Complex.exp ((suzukiFragmentPhase c u v N (x k) : ℂ) * I)
          = Complex.exp ((suzukiFragmentPhase c u v N α : ℂ) * I)) ∧
      (∀ k, k < M → x' k ∈ Icc α β ∧
        Complex.exp ((suzukiFragmentPhase c u v N (x' k) : ℂ) * I)
          = -Complex.exp ((suzukiFragmentPhase c u v N α : ℂ) * I)) ∧
      (∀ k, k < M → x k < x' k ∧ x' k < x (k + 1)) := by
  have hαβ : α ≤ β := le_of_lt (lt_trans hα hβ)
  have hmono := strictMono_suzukiFragmentPhase hc hv u N
  have hgain := suzukiFragmentPhase_gain_ge hc hv hα hβ N
  refine exists_interlacing_levels_of_phase_gain hαβ
    (continuous_suzukiFragmentPhase hc hv u N).continuousOn
    (hmono.strictMonoOn _) ?_
  linarith

end RHTower
