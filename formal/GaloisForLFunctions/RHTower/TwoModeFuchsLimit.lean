import GaloisForLFunctions.RHTower.ProlateSecularEquation
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Two-mode ground leakage under the Fuchs rate model: the 8/11 limit

The constrained two-mode ground leakage is the secular root
`μ = (ℓ₀²·d₁ + ℓ₁²·d₀)/(ℓ₀² + ℓ₁²)`, a strict convex combination of the two mode leakages.
When the leakages follow the Fuchs rates — `d₀` at index `n`, `d₁` at index `n+k` with `k ≥ 1` —
the lower rate is negligible against the higher one (`fuchsRate_div_tendsto_zero`), so the ratio
`μ/d₁` converges to the pure weight `ℓ₀²/(ℓ₀² + ℓ₁²)`
(`twoModeSecularRoot_fuchs_ratio_tendsto`).

With the Connes–Consani–Moscovici seed weights `ℓ₀ = 2^(1/4)`, `ℓ₁ = √3·2^(−5/4)` and the radial
index step `k = 4`, the weight is exactly `8/11`: the constrained ground leakage is
asymptotically `8/11` of the second-mode leakage (`ccm_twoMode_ground_leakage_ratio`).
-/

open Filter

namespace RHTower

/-- The secular root normalized by the dominant leakage is an affine function of the leakage
ratio `d₀/d₁`. -/
theorem twoModeSecularRoot_div (d₀ d₁ ℓ₀ ℓ₁ : ℝ) (hd₁ : d₁ ≠ 0) (hl : ℓ₀ ^ 2 + ℓ₁ ^ 2 ≠ 0) :
    GaloisForLFunctions.twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ / d₁
      = (ℓ₀ ^ 2 + ℓ₁ ^ 2 * (d₀ / d₁)) / (ℓ₀ ^ 2 + ℓ₁ ^ 2) := by
  unfold GaloisForLFunctions.twoModeSecularRoot
  field_simp

/-- **Fuchs-rate limit of the two-mode ground leakage.**  When the two mode leakages follow
Fuchs rates of strictly increasing index, the normalized secular root converges to the pure
weight of the dominated mode: `μ/d₁ → ℓ₀²/(ℓ₀² + ℓ₁²)`. -/
theorem twoModeSecularRoot_fuchs_ratio_tendsto {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (n : ℕ) {k : ℕ} (hk : k ≠ 0) {ℓ₀ ℓ₁ : ℝ} (hl : ℓ₀ ^ 2 + ℓ₁ ^ 2 ≠ 0) :
    Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ n lam) (fuchsRate A₁ (n + k) lam) ℓ₀ ℓ₁
          / fuchsRate A₁ (n + k) lam)
      atTop (nhds (ℓ₀ ^ 2 / (ℓ₀ ^ 2 + ℓ₁ ^ 2))) := by
  have hq := fuchsRate_div_tendsto_zero hA₁ hA₀ n hk
  have hlim : Tendsto (fun lam : ℝ =>
      (ℓ₀ ^ 2 + ℓ₁ ^ 2 * (fuchsRate A₀ n lam / fuchsRate A₁ (n + k) lam))
        / (ℓ₀ ^ 2 + ℓ₁ ^ 2))
      atTop (nhds (ℓ₀ ^ 2 / (ℓ₀ ^ 2 + ℓ₁ ^ 2))) := by
    have h1 := (hq.const_mul (ℓ₁ ^ 2)).const_add (ℓ₀ ^ 2)
    have h2 := h1.div_const (ℓ₀ ^ 2 + ℓ₁ ^ 2)
    simpa using h2
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  rw [twoModeSecularRoot_div _ _ _ _ (fuchsRate_pos hA₁ (n + k) hlam).ne' hl]

/-- **The Connes–Consani–Moscovici 8/11 law.**  With the CCM seed weights `ℓ₀ = 2^(1/4)`,
`ℓ₁ = √3·2^(−5/4)` and the radial Fuchs index step `4`, the constrained two-mode ground leakage
is asymptotically `8/11` of the dominant second-mode leakage. -/
theorem ccm_twoMode_ground_leakage_ratio {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot (fuchsRate A₀ 0 lam) (fuchsRate A₁ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))
          / fuchsRate A₁ 4 lam)
      atTop (nhds (8 / 11)) := by
  have hl : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2
      + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 ≠ 0 := by positivity
  have h := twoModeSecularRoot_fuchs_ratio_tendsto hA₀ hA₁ 0 (k := 4) (by norm_num) hl
  rw [GaloisForLFunctions.ccm_groundState_weight_eq] at h
  simpa using h

end RHTower

namespace RHTower

/-- **The CCM 3/11 gap law.**  The constrained spectral gap of the two-mode ground state —
the distance from the ground leakage to the dominant mode leakage — is asymptotically `3/11`
of the dominant leakage: the complementary constant to the `8/11` ground ratio. -/
theorem ccm_twoMode_ground_gap_ratio {A₀ A₁ : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) :
    Filter.Tendsto (fun lam : ℝ =>
        (fuchsRate A₁ 4 lam - GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ 0 lam) (fuchsRate A₁ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))
          / fuchsRate A₁ 4 lam)
      Filter.atTop (nhds (3 / 11)) := by
  have h8 := ccm_twoMode_ground_leakage_ratio hA₀ hA₁
  have hone : Filter.Tendsto (fun lam : ℝ =>
      1 - GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₀ 0 lam) (fuchsRate A₁ 4 lam)
          ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))
        / fuchsRate A₁ 4 lam)
      Filter.atTop (nhds (1 - 8 / 11)) :=
    Filter.Tendsto.sub tendsto_const_nhds h8
  have h311 : (1 : ℝ) - 8 / 11 = 3 / 11 := by norm_num
  rw [h311] at hone
  refine hone.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd1 : fuchsRate A₁ 4 lam ≠ 0 := (fuchsRate_pos hA₁ 4 hlam).ne'
  field_simp

end RHTower
