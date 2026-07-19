import GaloisForLFunctions.RHTower.ConstrainedProlateGroundDistanceCCM
import GaloisForLFunctions.RHTower.SecularVectorRawDefect

/-!
# Scale ratios of the CCM Fuchs family

Within the CCM family `d_j(λ) = A_j λ^{8j+1} e^{−4πλ²}` any lower scale is negligible against a
higher one, because the exponentials cancel and a positive power of `λ` remains.  Specialized to
the reference scale `d_{k+1}`, this is one of the two inputs the raw-defect chain consumes.
-/

open Filter

noncomputable section

namespace RHTower

/-- **Lower CCM scales are negligible against the reference scale `d_{k+1}`.** -/
theorem ccmFuchsScale_div_tendsto_zero {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {j k : ℕ} (hjk : j ≤ k) :
    Tendsto (fun lam : ℝ => ccmFuchsScale A lam j / ccmFuchsScale A lam (k + 1))
      atTop (nhds 0) := by
  have h := fuchsRate_div_tendsto_zero (hA (k + 1)) (hA j) (4 * j)
    (k := 4 * (k + 1) - 4 * j) (by omega)
  rw [show 4 * j + (4 * (k + 1) - 4 * j) = 4 * (k + 1) from by omega] at h
  exact h

/-- The reference scale is eventually nonzero. -/
theorem ccmFuchsScale_ne_zero {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) (j : ℕ) :
    ∀ᶠ lam : ℝ in atTop, ccmFuchsScale A lam j ≠ 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact ne_of_gt (fuchsRate_pos (hA j) _ hlam)

/-! ## Positivity and separation derived from the ratio limits -/

/-- A quantity comparable to a positive reference with positive limiting proportion is eventually
positive. -/
theorem eventually_pos_of_div_tendsto_pos {M B : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hB : ∀ᶠ lam : ℝ in atTop, 0 < B lam)
    (h : Tendsto (fun lam => M lam / B lam) atTop (nhds θ)) :
    ∀ᶠ lam : ℝ in atTop, 0 < M lam := by
  filter_upwards [hB, h.eventually (eventually_gt_nhds (by linarith : θ / 2 < θ))]
    with lam hBpos hratio
  have : 0 < M lam / B lam := lt_trans (by linarith) hratio
  exact (div_pos_iff.mp this).elim (fun hp => hp.1) (fun hn => absurd hBpos (by linarith [hn.2]))

/-- **Strict domination from a vanishing ratio.**  Sharpens the nonvanishing statement: a quantity
negligible against a positive reference is eventually strictly below it. -/
theorem eventually_lt_of_div_tendsto_zero {D M : ℝ → ℝ}
    (hM : ∀ᶠ lam : ℝ in atTop, 0 < M lam)
    (h : Tendsto (fun lam => D lam / M lam) atTop (nhds 0)) :
    ∀ᶠ lam : ℝ in atTop, D lam < M lam := by
  filter_upwards [hM, h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with lam hMpos hratio
  have := (div_lt_iff₀ hMpos).mp hratio
  linarith

/-- A quantity negligible against a positive reference is eventually strictly below it, so their
difference never vanishes. -/
theorem eventually_sub_ne_zero_of_div_tendsto_zero {D M : ℝ → ℝ}
    (hM : ∀ᶠ lam : ℝ in atTop, 0 < M lam)
    (h : Tendsto (fun lam => D lam / M lam) atTop (nhds 0)) :
    ∀ᶠ lam : ℝ in atTop, D lam - M lam ≠ 0 := by
  filter_upwards [eventually_lt_of_div_tendsto_zero hM h] with lam hlt
  exact ne_of_lt (by linarith)

/-- **Strict domination from a limiting proportion below one.**  If the root sits at a fraction
`θ < 1` of the reference scale, it is eventually strictly below it. -/
theorem eventually_lt_of_div_tendsto_lt_one {M B : ℝ → ℝ} {θ : ℝ} (hθ : θ < 1)
    (hB : ∀ᶠ lam : ℝ in atTop, 0 < B lam)
    (h : Tendsto (fun lam => M lam / B lam) atTop (nhds θ)) :
    ∀ᶠ lam : ℝ in atTop, M lam < B lam := by
  filter_upwards [hB, h.eventually (eventually_lt_nhds hθ)] with lam hBpos hratio
  have := (div_lt_iff₀ hBpos).mp hratio
  linarith

end RHTower

end
