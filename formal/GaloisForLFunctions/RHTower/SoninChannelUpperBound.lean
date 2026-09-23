import GaloisForLFunctions.RHTower.SoninFourierChannelBound

/-!
# A step multiplier is no larger than its largest coefficient

The exact energy identity bounds the channel from above as well as below: the layers are orthogonal
and their total mass is at most the vector's, so the channel norm never exceeds the largest layer
logarithm below the tower height.

Together with the lower bound this pins the frequency-side contribution to the size of the
logarithm of the outer tower radius — the completion it could supply grows only logarithmically.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- A shell projection is a contraction. -/
theorem norm_evenIndicatorLayer_apply_le {s t : ℝ} (hst : s ≤ t) (u : evenSubspace) :
    ‖evenIndicatorLayer s t u‖ ≤ ‖u‖ := by
  have hidem : evenIndicatorLayer s t (evenIndicatorLayer s t u) = evenIndicatorLayer s t u := by
    have h := DFunLike.congr_fun (evenIndicatorLayer_mul_self hst) u
    simpa using h
  have hself : ⟪evenIndicatorLayer s t u, evenIndicatorLayer s t u⟫_ℂ =
      ⟪u, evenIndicatorLayer s t u⟫_ℂ := by
    have h := ContinuousLinearMap.adjoint_inner_right (evenIndicatorLayer s t) u
      (evenIndicatorLayer s t u)
    rw [adjoint_evenIndicatorLayer, hidem] at h
    exact h.symm
  have hnorm : ‖evenIndicatorLayer s t u‖ ^ (2 : ℕ) ≤ ‖u‖ * ‖evenIndicatorLayer s t u‖ := by
    have hre : ‖evenIndicatorLayer s t u‖ ^ (2 : ℕ) = ‖(⟪u, evenIndicatorLayer s t u⟫_ℂ)‖ := by
      rw [← hself]
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hre]
    exact norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (evenIndicatorLayer s t u)) with hzero | hpos
  · rw [← hzero]
    exact norm_nonneg u
  · nlinarith

/-- **Upper bound.**  The channel norm is at most the largest layer logarithm below the height. -/
theorem norm_evenLogShellChannel_apply_le (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ)
    (u : evenSubspace) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ k, k < n → |Real.log (logShellRadius a r k)| ≤ M) :
    ‖evenLogShellChannel a r n u‖ ≤ M * ‖u‖ := by
  classical
  have hmass : ∑ k ∈ Finset.range n,
      ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) =
      ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u‖ ^ (2 : ℕ) := by
    have hsum := DFunLike.congr_fun (sum_evenIndicatorLayer (fun k => logShellRadius a r k) n) u
    rw [sum_apply] at hsum
    have hpy := norm_sum_sq_of_pairwise_inner_eq_zero (𝕜 := ℂ) (Finset.range n)
      (fun k => evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u)
      (fun i _ k _ hik => inner_layer_apply_eq_zero_of_ne a r ha hr u hik)
    rw [← hpy, hsum]
    rfl
  have htotal : ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u‖ ≤ ‖u‖ :=
    norm_evenIndicatorLayer_apply_le (logShellRadius_mono ha hr (Nat.zero_le n)) u
  have hsq : ‖evenLogShellChannel a r n u‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by
    rw [norm_sq_evenLogShellChannel_apply a r ha hr n u]
    have hterm : ∀ k ∈ Finset.range n,
        |Real.log (logShellRadius a r k)| ^ (2 : ℕ) *
            ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) ≤
          M ^ (2 : ℕ) * ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) := by
      intro k hk
      have hle := hM k (Finset.mem_range.mp hk)
      have habs0 : (0 : ℝ) ≤ |Real.log (logShellRadius a r k)| := abs_nonneg _
      have hsq' : |Real.log (logShellRadius a r k)| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hsq' (by positivity)
    calc ∑ k ∈ Finset.range n, |Real.log (logShellRadius a r k)| ^ (2 : ℕ) *
            ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ)
        ≤ ∑ k ∈ Finset.range n, M ^ (2 : ℕ) *
            ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ (2 : ℕ) :=
          Finset.sum_le_sum hterm
      _ = M ^ (2 : ℕ) * ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u‖ ^ (2 : ℕ) := by
          rw [← Finset.mul_sum, hmass]
      _ ≤ M ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) := by
          have hsq2 := mul_self_le_mul_self (norm_nonneg
            (evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r n) u)) htotal
          nlinarith [sq_nonneg M, hsq2]
  nlinarith [norm_nonneg (evenLogShellChannel a r n u), norm_nonneg u,
    mul_nonneg hM0 (norm_nonneg u)]

/-- **Upper bound in the frequency variable.** -/
theorem norm_evenFourierLogShellChannel_apply_le (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ)
    (w : evenSubspace) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ k, k < n → |Real.log (logShellRadius a r k)| ≤ M) :
    ‖evenFourierLogShellChannel a r n w‖ ≤ M * ‖w‖ := by
  rw [norm_evenFourierLogShellChannel_apply]
  have h := norm_evenLogShellChannel_apply_le a r ha hr n (evenFourierTransform w) M hM0 hM
  rwa [evenFourierTransform_isometry] at h

end RHTower
