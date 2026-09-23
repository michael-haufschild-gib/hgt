import GaloisForLFunctions.HTGeometry.TunableAbsorptionSum
import GaloisForLFunctions.HTGeometry.NevanlinnaEntire

/-!
# The kernel sum with a tunable leading constant

The absorption estimate with leading constant `1 + ε` survives the passage to the full series: once
both kernel roots are known to be bounded, every partial sum at `w` is bounded by `(1+ε)` times the
whole series at `z` plus a term of order `‖w − z‖²`.

Letting `w → z` and then `ε → 0` makes the kernel sum upper semicontinuous, which — with lower
semicontinuity free from its being a supremum of continuous partial sums — is continuity.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The kernel series written with norms rather than `normSq`. -/
theorem summable_normSq_eq_norm (s : ℕ → ℝ) (v : ℂ) :
    (fun k => Complex.normSq (monicOrthoC s k v) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      = fun k => ‖monicOrthoC s k v‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) := by
  funext k
  rw [← Complex.sq_norm]

/-- **The tunable bound for the whole kernel series.** -/
theorem tsum_kernel_le_tunable (h : PositiveMomentForm s) (z w : ℂ) {e : ℝ} (he : 0 < e)
    {Sw S P : ℝ} (hSw : ∀ N, kernelRoot s (fun j => monicOrthoC s j w) N ≤ Sw)
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P) :
    ∑' k, ‖monicOrthoC s k w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k)
      ≤ (1 + e) * (∑' k, ‖monicOrthoC s k z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s k) (monicOrtho s k))
        + 4 * (1 + e⁻¹) *
            (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            Sw ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
  have hpos : ∀ k, 0 < momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun k => monicOrtho_inner_self_pos h k
  have hnn : ∀ (v : ℂ) (k : ℕ),
      0 ≤ ‖monicOrthoC s k v‖ ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun v k => div_nonneg (sq_nonneg _) (hpos k).le
  have hsumw : Summable fun k => ‖monicOrthoC s k w‖ ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    have := summable_of_kernelRoot_le h w hSw
    rwa [summable_normSq_eq_norm s w] at this
  have hsumz : Summable fun k => ‖monicOrthoC s k z‖ ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    have := summable_of_kernelRoot_le h z hS
    rwa [summable_normSq_eq_norm s z] at this
  have hzle : ∀ N : ℕ, kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)
      ≤ ∑' k, ‖monicOrthoC s k z‖ ^ (2 : ℕ) / momentInner s (monicOrtho s k) (monicOrtho s k) := by
    intro N
    rw [kernelRoot_sq h]
    exact hsumz.sum_le_tsum _ fun k _ => hnn z k
  have hrhs_nonneg : 0 ≤ (1 + e) * (∑' k, ‖monicOrthoC s k z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      + 4 * (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          Sw ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
    have h1 : 0 ≤ ∑' k, ‖monicOrthoC s k z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) :=
      tsum_nonneg fun k => hnn z k
    have h2 : (0:ℝ) ≤ 1 + e := by linarith
    have h3 : (0:ℝ) ≤ 1 + e⁻¹ := by positivity
    have h4 : (0:ℝ) ≤ 4 * (1 + e⁻¹) *
        (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
        Sw ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by positivity
    nlinarith [mul_nonneg h2 h1]
  refine hsumw.tsum_le_of_sum_le fun t => ?_
  obtain ⟨n, hn⟩ := t.exists_nat_subset_range
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hn fun k _ _ => hnn w k) ?_
  rcases n with _ | N
  · simpa using hrhs_nonneg
  · have hstep := kernelRoot_sq_le_absorption_tunable h N z w he
    have hKw : kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) ≤ Sw ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hSw N) 2
    have hKz : kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hS N) 2
    have hPz : kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) ≤ P ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hP N) 2
    have htail : 4 * (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ) *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ)
        ≤ 4 * (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          Sw ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
      have hc : (0:ℝ) ≤ 4 * (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) := by positivity
      gcongr
    have hlead : (1 + e) * kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ)
        ≤ (1 + e) * ∑' k, ‖monicOrthoC s k z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s k) (monicOrtho s k) :=
      mul_le_mul_of_nonneg_left (hzle N) (by linarith)
    rw [← kernelRoot_sq h (fun j => monicOrthoC s j w) N]
    linarith [hstep, htail, hlead]

end HTGeometry
