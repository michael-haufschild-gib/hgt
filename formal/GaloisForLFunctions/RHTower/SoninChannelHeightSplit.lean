import GaloisForLFunctions.RHTower.SoninChannelUpperBound

/-!
# Splitting the channel at a shell index

The exact energy identity is a sum over shells, so it splits at any index: below the cut the layer
logarithms are bounded and the layers carry at most the vector's own mass, while above the cut the
sum is whatever the vector's mass in the outer shells makes it.

This separates the two things a tall tower can do.  The shells the vector actually meets contribute
their logarithm times its mass; the shells beyond contribute their (larger) logarithms times only the
mass the vector leaves out there.  A vector whose outer mass decays fast enough therefore sees a
channel bounded independently of the tower's height.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- **Bessel bound for the tower's layers.**  The layers of a tower are orthogonal and their total
mass is that of a single cutoff difference, hence at most the vector's own. -/
theorem sum_norm_sq_evenIndicatorLayer_le (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (m : ℕ)
    (u : evenSubspace) :
    ∑ k ∈ Finset.range m,
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
      ‖u‖ ^ 2 := by
  classical
  have hsum := DFunLike.congr_fun (sum_evenIndicatorLayer (fun k => logShellRadius a r k) m) u
  rw [sum_apply] at hsum
  have hpy := norm_sum_sq_of_pairwise_inner_eq_zero (𝕜 := ℂ) (Finset.range m)
    (fun k => evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u)
    (fun i _ k _ hik => inner_layer_apply_eq_zero_of_ne a r ha hr u hik)
  have hmass : ∑ k ∈ Finset.range m,
      ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 =
      ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r m) u‖ ^ 2 := by
    rw [← hpy, hsum]
    rfl
  rw [hmass]
  have htotal : ‖evenIndicatorLayer (logShellRadius a r 0) (logShellRadius a r m) u‖ ≤ ‖u‖ :=
    norm_evenIndicatorLayer_apply_le (logShellRadius_mono ha hr (Nat.zero_le m)) u
  rw [pow_two, pow_two]
  exact mul_self_le_mul_self (norm_nonneg _) htotal

/-- The shells below the cut contribute at most the bound squared times the vector's mass. -/
theorem sum_range_logShellRadius_weight_le (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (m : ℕ)
    (u : evenSubspace) (M : ℝ) (hM : ∀ k, k < m → |Real.log (logShellRadius a r k)| ≤ M) :
    ∑ k ∈ Finset.range m, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
      M ^ 2 * ‖u‖ ^ 2 := by
  classical
  have hterm : ∀ k ∈ Finset.range m,
      |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤
        M ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 := by
    intro k hk
    have hle := hM k (Finset.mem_range.mp hk)
    have habs0 : (0 : ℝ) ≤ |Real.log (logShellRadius a r k)| := abs_nonneg _
    have hsq : |Real.log (logShellRadius a r k)| ^ 2 ≤ M ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  calc ∑ k ∈ Finset.range m, |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2
      ≤ ∑ k ∈ Finset.range m, M ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = M ^ 2 * ∑ k ∈ Finset.range m,
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 := by
        rw [← Finset.mul_sum]
    _ ≤ M ^ 2 * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_norm_sq_evenIndicatorLayer_le a r ha hr m u) (sq_nonneg M)

/-- **The channel splits at a shell index.**  Below the cut only the bound on the layer logarithms
and the vector's mass enter; above it, the outer shells' own weighted mass. -/
theorem norm_sq_evenLogShellChannel_apply_le_split (a r : ℝ) (ha : 0 < a) (hr : 1 < r)
    (n K : ℕ) (u : evenSubspace) (M : ℝ)
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M) :
    ‖evenLogShellChannel a r n u‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 +
      ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 := by
  classical
  rw [norm_sq_evenLogShellChannel_apply a r ha hr n u]
  rcases le_total K n with hKn | hnK
  · have hsplit : ∑ k ∈ Finset.range n, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 =
        (∑ k ∈ Finset.range K, |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2) +
        ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
          ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le K) hKn).symm
    rw [hsplit]
    have := sum_range_logShellRadius_weight_le a r ha hr K u M hM
    linarith
  · have hempty : Finset.Ico K n = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, add_zero]
    exact sum_range_logShellRadius_weight_le a r ha hr n u M
      (fun k hk => hM k (lt_of_lt_of_le hk hnK))

/-- **Height-independent channel bound.**  A bound on the layer logarithms below the cut and a bound
on the weighted outer mass together bound the channel, with no reference to the tower's height beyond
the outer sum. -/
theorem norm_evenLogShellChannel_apply_le_of_tail (a r : ℝ) (ha : 0 < a) (hr : 1 < r)
    (n K : ℕ) (u : evenSubspace) (M E : ℝ)
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (htail : ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1)) u‖ ^ 2 ≤ E) :
    ‖evenLogShellChannel a r n u‖ ≤ Real.sqrt (M ^ 2 * ‖u‖ ^ 2 + E) := by
  have hsplit := norm_sq_evenLogShellChannel_apply_le_split a r ha hr n K u M hM
  have hsq : ‖evenLogShellChannel a r n u‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 + E := by linarith
  have hmono := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at hmono

/-- **Height-independent bound in the frequency variable.** -/
theorem norm_evenFourierLogShellChannel_apply_le_of_tail (a r : ℝ) (ha : 0 < a) (hr : 1 < r)
    (n K : ℕ) (w : evenSubspace) (M E : ℝ)
    (hM : ∀ k, k < K → |Real.log (logShellRadius a r k)| ≤ M)
    (htail : ∑ k ∈ Finset.Ico K n, |Real.log (logShellRadius a r k)| ^ 2 *
        ‖evenIndicatorLayer (logShellRadius a r k) (logShellRadius a r (k + 1))
          (evenFourierTransform w)‖ ^ 2 ≤ E) :
    ‖evenFourierLogShellChannel a r n w‖ ≤ Real.sqrt (M ^ 2 * ‖w‖ ^ 2 + E) := by
  rw [norm_evenFourierLogShellChannel_apply]
  have h := norm_evenLogShellChannel_apply_le_of_tail a r ha hr n K (evenFourierTransform w) M E
    hM htail
  rwa [evenFourierTransform_isometry] at h

end RHTower

