import GaloisForLFunctions.RHTower.ProlateSecularEquation
import GaloisForLFunctions.RHTower.FuchsProlateScale
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast

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

/-- A positive denominator turns convergence of a quotient into every strict sub-limit being
an eventual multiplicative lower bound for the numerator. -/
theorem eventually_const_mul_le_of_tendsto_div_atTop
    {a b : ℝ → ℝ} {L c : ℝ}
    (h : Tendsto (fun x => a x / b x) atTop (nhds L))
    (hb : ∀ᶠ x in atTop, 0 < b x) (hc : c < L) :
    ∀ᶠ x in atTop, c * b x ≤ a x := by
  have hevent : ∀ᶠ x in atTop, c < a x / b x :=
    h.eventually (eventually_gt_nhds hc)
  filter_upwards [hevent, hb] with x hx hbx
  exact ((lt_div_iff₀ hbx).mp hx).le

/-- If `a / b` tends to zero and `b` is eventually positive, then `a` is eventually smaller than
every positive constant multiple of `b`. -/
theorem eventually_lt_const_mul_of_tendsto_div_zero_atTop
    {a b : ℝ → ℝ} {c : ℝ}
    (h : Tendsto (fun x => a x / b x) atTop (nhds 0))
    (hb : ∀ᶠ x in atTop, 0 < b x) (hc : 0 < c) :
    ∀ᶠ x in atTop, a x < c * b x := by
  have hevent : ∀ᶠ x in atTop, a x / b x < c :=
    h.eventually (eventually_lt_nhds hc)
  filter_upwards [hevent, hb] with x hx hbx
  exact (div_lt_iff₀ hbx).mp hx

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

/-- Every constant strictly below `3/11` is an eventual lower bound for the normalized CCM
two-mode gap.  This is the quantified inequality form of `ccm_twoMode_ground_gap_ratio`. -/
theorem ccm_twoMode_ground_gap_eventually_ge
    {A₀ A₁ c : ℝ} (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hc : c < 3 / 11) :
    ∀ᶠ lam : ℝ in Filter.atTop,
      c * fuchsRate A₁ 4 lam ≤
        fuchsRate A₁ 4 lam - GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₀ 0 lam) (fuchsRate A₁ 4 lam)
          ((2 : ℝ) ^ ((1 : ℝ) / 4))
          (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) := by
  apply eventually_const_mul_le_of_tendsto_div_atTop
    (ccm_twoMode_ground_gap_ratio hA₀ hA₁)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact fuchsRate_pos hA₁ 4 hlam
  exact hc

/-- The squared Hermite coordinates of the negative Fourier sector are proportional to `8` and
`5`, so the lower-mode weight is exactly `8/13`.  The common scaling is immaterial to the secular
root. -/
theorem ccm_negativeSector_twoMode_weight_eq :
    (Real.sqrt 8) ^ 2 / ((Real.sqrt 8) ^ 2 + (Real.sqrt 5) ^ 2) = (8 : ℝ) / 13 := by
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

/-- The negative-sector two-mode secular root is positive at every positive aperture in the
Fuchs-rate model. -/
theorem ccm_negativeSector_twoModeSecularRoot_pos
    {A₂ A₆ lam : ℝ} (hA₂ : 0 < A₂) (hA₆ : 0 < A₆) (hlam : 0 < lam) :
    0 < GaloisForLFunctions.twoModeSecularRoot
      (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) := by
  have hs8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  unfold GaloisForLFunctions.twoModeSecularRoot
  exact div_pos
    (add_pos
      (mul_pos (pow_pos hs8 2) (fuchsRate_pos hA₆ 6 hlam))
      (mul_pos (pow_pos hs5 2) (fuchsRate_pos hA₂ 2 hlam)))
    (add_pos (pow_pos hs8 2) (pow_pos hs5 2))

/-- **The negative-sector `8/13` law.**  For the `h₂`--`h₆` Hermite contrast and Fuchs
indices `2` and `6`, the constrained two-mode ground leakage is asymptotically `8/13` of the
dominant second-mode leakage. -/
theorem ccm_negativeSector_twoMode_ground_leakage_ratio
    {A₂ A₆ : ℝ} (hA₂ : 0 < A₂) (hA₆ : 0 < A₆) :
    Filter.Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam)
            (Real.sqrt 8) (Real.sqrt 5)
          / fuchsRate A₆ 6 lam)
      Filter.atTop (nhds (8 / 13)) := by
  have hl : (Real.sqrt 8) ^ 2 + (Real.sqrt 5) ^ 2 ≠ 0 := by positivity
  have h := twoModeSecularRoot_fuchs_ratio_tendsto hA₂ hA₆ 2 (k := 4) (by norm_num) hl
  rw [ccm_negativeSector_twoMode_weight_eq] at h
  simpa using h

/-- **The negative-sector `5/13` gap law.**  The distance from the `h₂`--`h₆` two-mode
ground leakage to the dominant leakage is asymptotically the complementary fraction `5/13`. -/
theorem ccm_negativeSector_twoMode_ground_gap_ratio
    {A₂ A₆ : ℝ} (hA₂ : 0 < A₂) (hA₆ : 0 < A₆) :
    Filter.Tendsto (fun lam : ℝ =>
        (fuchsRate A₆ 6 lam - GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam)
            (Real.sqrt 8) (Real.sqrt 5)) / fuchsRate A₆ 6 lam)
      Filter.atTop (nhds (5 / 13)) := by
  have h8 := ccm_negativeSector_twoMode_ground_leakage_ratio hA₂ hA₆
  have h : Filter.Tendsto (fun lam : ℝ =>
      1 - GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) /
        fuchsRate A₆ 6 lam)
      Filter.atTop (nhds ((1 : ℝ) - 8 / 13)) := tendsto_const_nhds.sub h8
  have h513 : (1 : ℝ) - 8 / 13 = 5 / 13 := by norm_num
  rw [h513] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd₆ : fuchsRate A₆ 6 lam ≠ 0 := (fuchsRate_pos hA₆ 6 hlam).ne'
  field_simp

/-- Every constant strictly below `5/13` is an eventual lower bound for the negative-sector
two-mode gap after scaling by its dominant Fuchs leakage. -/
theorem ccm_negativeSector_twoMode_ground_gap_eventually_ge
    {A₂ A₆ c : ℝ} (hA₂ : 0 < A₂) (hA₆ : 0 < A₆) (hc : c < 5 / 13) :
    ∀ᶠ lam : ℝ in Filter.atTop,
      c * fuchsRate A₆ 6 lam ≤
        fuchsRate A₆ 6 lam - GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) := by
  apply eventually_const_mul_le_of_tendsto_div_atTop
    (ccm_negativeSector_twoMode_ground_gap_ratio hA₂ hA₆)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact fuchsRate_pos hA₆ 6 hlam
  exact hc

/-- **Two-mode Fourier-parity separation.**  In the exact Fuchs-rate model, the positive-sector
`h₀`--`h₄` constrained floor is negligible compared with the negative-sector `h₂`--`h₆`
floor.  This is the limit form of the card's `λ⁻⁴` parity separation. -/
theorem ccm_twoMode_parity_floor_ratio_tendsto_zero
    {A₀ A₂ A₄ A₆ : ℝ}
    (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hA₄ : 0 < A₄) (hA₆ : 0 < A₆) :
    Filter.Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ 0 lam) (fuchsRate A₄ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) /
          GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5))
      Filter.atTop (nhds 0) := by
  have hp := ccm_twoMode_ground_leakage_ratio hA₀ hA₄
  have hn := ccm_negativeSector_twoMode_ground_leakage_ratio hA₂ hA₆
  have hs := fuchsRate_div_tendsto_zero hA₆ hA₄ 4 (k := 2) (by norm_num)
  have h := (hp.mul hs).div hn (by norm_num)
  norm_num only [mul_zero, zero_div] at h
  have hlim : Filter.Tendsto (fun lam : ℝ =>
      ((GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ 0 lam) (fuchsRate A₄ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) /
          fuchsRate A₄ 4 lam) * (fuchsRate A₄ 4 lam / fuchsRate A₆ 6 lam)) /
        (GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) /
          fuchsRate A₆ 6 lam))
      Filter.atTop (nhds 0) := by
    simpa only [Pi.mul_apply, Pi.div_apply, Nat.reduceAdd] using! h
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd₄ : fuchsRate A₄ 4 lam ≠ 0 := (fuchsRate_pos hA₄ 4 hlam).ne'
  have hd₆ : fuchsRate A₆ 6 lam ≠ 0 := (fuchsRate_pos hA₆ 6 hlam).ne'
  have hμm : GaloisForLFunctions.twoModeSecularRoot
      (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) ≠ 0 :=
    (ccm_negativeSector_twoModeSecularRoot_pos hA₂ hA₆ hlam).ne'
  field_simp

/-- **Quantified two-mode parity separation.**  Every positive multiple of the negative-sector
floor eventually strictly dominates the positive-sector floor. -/
theorem ccm_twoMode_parity_floor_eventually_lt_mul
    {A₀ A₂ A₄ A₆ c : ℝ}
    (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hA₄ : 0 < A₄) (hA₆ : 0 < A₆)
    (hc : 0 < c) :
    ∀ᶠ lam : ℝ in Filter.atTop,
      GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₀ 0 lam) (fuchsRate A₄ 4 lam)
          ((2 : ℝ) ^ ((1 : ℝ) / 4))
          (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) <
        c * GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) := by
  apply eventually_lt_const_mul_of_tendsto_div_zero_atTop
    (ccm_twoMode_parity_floor_ratio_tendsto_zero hA₀ hA₂ hA₄ hA₆)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact ccm_negativeSector_twoModeSecularRoot_pos hA₂ hA₆ hlam
  exact hc

/-- **Sharp two-mode Fourier-parity scale.**  Multiplying the positive/negative floor ratio by
`λ⁴` exposes the exact Fuchs-model coefficient `13 A₄ / (11 A₆)`. -/
theorem ccm_twoMode_parity_floor_scaled_ratio
    {A₀ A₂ A₄ A₆ : ℝ}
    (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hA₄ : 0 < A₄) (hA₆ : 0 < A₆) :
    Filter.Tendsto (fun lam : ℝ => lam ^ 4 *
        GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ 0 lam) (fuchsRate A₄ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) /
          GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5))
      Filter.atTop (nhds (13 * A₄ / (11 * A₆))) := by
  have hp := ccm_twoMode_ground_leakage_ratio hA₀ hA₄
  have hn := ccm_negativeSector_twoMode_ground_leakage_ratio hA₂ hA₆
  have hs : Filter.Tendsto (fun lam : ℝ =>
      lam ^ 4 * fuchsRate A₄ 4 lam / fuchsRate A₆ 6 lam)
      Filter.atTop (nhds (A₄ / A₆)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
    unfold fuchsRate
    have he : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
    field_simp [hA₄.ne', hA₆.ne', hlam.ne', he]
    ring
  have h := (hp.mul hs).div hn (by norm_num)
  have hc : ((8 : ℝ) / 11 * (A₄ / A₆)) / (8 / 13) = 13 * A₄ / (11 * A₆) := by
    field_simp [hA₆.ne']
  rw [hc] at h
  have hlim : Filter.Tendsto (fun lam : ℝ =>
      ((GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₀ 0 lam) (fuchsRate A₄ 4 lam)
            ((2 : ℝ) ^ ((1 : ℝ) / 4)) (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) /
          fuchsRate A₄ 4 lam) *
        (lam ^ 4 * fuchsRate A₄ 4 lam / fuchsRate A₆ 6 lam)) /
        (GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) /
          fuchsRate A₆ 6 lam))
      Filter.atTop (nhds (13 * A₄ / (11 * A₆))) := by
    simpa only [Pi.mul_apply, Pi.div_apply] using! h
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd₄ : fuchsRate A₄ 4 lam ≠ 0 := (fuchsRate_pos hA₄ 4 hlam).ne'
  have hd₆ : fuchsRate A₆ 6 lam ≠ 0 := (fuchsRate_pos hA₆ 6 hlam).ne'
  have hμm : GaloisForLFunctions.twoModeSecularRoot
      (fuchsRate A₂ 2 lam) (fuchsRate A₆ 6 lam) (Real.sqrt 8) (Real.sqrt 5) ≠ 0 :=
    (ccm_negativeSector_twoModeSecularRoot_pos hA₂ hA₆ hlam).ne'
  field_simp

/-- The aggregated head coordinate and the next Hermite coordinate recover exactly the fixed-mode
secular weight `θₖ = Qₖ/Qₖ₊₁`. -/
theorem constrainedProlateHermiteTheta_eq_square_ratio (k : ℕ) :
    (Real.sqrt (constrainedProlateHermiteSquareSum k)) ^ 2 /
        ((Real.sqrt (constrainedProlateHermiteSquareSum k)) ^ 2 +
          constrainedProlateHermiteCoordinate (k + 1) ^ 2) =
      constrainedProlateHermiteTheta k := by
  rw [Real.sq_sqrt (constrainedProlateHermiteSquareSum_pos k).le,
    constrainedProlateHermiteCoordinate_sq,
    constrainedProlateHermiteSquareSum_eq,
    constrainedProlateHermiteTheta,
    constrainedProlateHermiteWeightSum_succ]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

/-- **All-depth two-mode Fuchs ladder.**  At every fixed depth `k`, aggregating the first `k+1`
Hermite coordinates into one head mode gives normalized ground leakage converging to the exact
card constant `θₖ`. -/
theorem constrainedProlate_fixedMode_twoMode_fuchs_ratio
    {Aₖ Aₖ₁ : ℝ} (hAₖ : 0 < Aₖ) (hAₖ₁ : 0 < Aₖ₁) (k : ℕ) :
    Filter.Tendsto (fun lam : ℝ =>
        GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate Aₖ (4 * k) lam) (fuchsRate Aₖ₁ (4 * (k + 1)) lam)
            (Real.sqrt (constrainedProlateHermiteSquareSum k))
            (constrainedProlateHermiteCoordinate (k + 1)) /
          fuchsRate Aₖ₁ (4 * (k + 1)) lam)
      Filter.atTop (nhds (constrainedProlateHermiteTheta k)) := by
  have hl : (Real.sqrt (constrainedProlateHermiteSquareSum k)) ^ 2 +
      constrainedProlateHermiteCoordinate (k + 1) ^ 2 ≠ 0 := by
    exact (add_pos
      (pow_pos (Real.sqrt_pos.2 (constrainedProlateHermiteSquareSum_pos k)) 2)
      (pow_pos (constrainedProlateHermiteCoordinate_pos (k + 1)) 2)).ne'
  have h := twoModeSecularRoot_fuchs_ratio_tendsto hAₖ hAₖ₁ (4 * k)
    (k := 4) (by norm_num) hl
  rw [constrainedProlateHermiteTheta_eq_square_ratio] at h
  simpa [Nat.mul_add] using h

/-- The complementary all-depth two-mode spectral gap converges to `1 - θₖ`. -/
theorem constrainedProlate_fixedMode_twoMode_fuchs_gap_ratio
    {Aₖ Aₖ₁ : ℝ} (hAₖ : 0 < Aₖ) (hAₖ₁ : 0 < Aₖ₁) (k : ℕ) :
    Filter.Tendsto (fun lam : ℝ =>
        (fuchsRate Aₖ₁ (4 * (k + 1)) lam -
          GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate Aₖ (4 * k) lam) (fuchsRate Aₖ₁ (4 * (k + 1)) lam)
            (Real.sqrt (constrainedProlateHermiteSquareSum k))
            (constrainedProlateHermiteCoordinate (k + 1))) /
          fuchsRate Aₖ₁ (4 * (k + 1)) lam)
      Filter.atTop (nhds (1 - constrainedProlateHermiteTheta k)) := by
  have htheta := constrainedProlate_fixedMode_twoMode_fuchs_ratio hAₖ hAₖ₁ k
  have h : Filter.Tendsto (fun lam : ℝ =>
      1 - GaloisForLFunctions.twoModeSecularRoot
          (fuchsRate Aₖ (4 * k) lam) (fuchsRate Aₖ₁ (4 * (k + 1)) lam)
          (Real.sqrt (constrainedProlateHermiteSquareSum k))
          (constrainedProlateHermiteCoordinate (k + 1)) /
        fuchsRate Aₖ₁ (4 * (k + 1)) lam)
      Filter.atTop (nhds (1 - constrainedProlateHermiteTheta k)) := tendsto_const_nhds.sub htheta
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hd : fuchsRate Aₖ₁ (4 * (k + 1)) lam ≠ 0 :=
    (fuchsRate_pos hAₖ₁ (4 * (k + 1)) hlam).ne'
  field_simp

/-- Every constant strictly below `1 - θₖ` is an eventual lower bound for the all-depth
two-mode Fuchs gap.  This is the quantified inequality form of
`constrainedProlate_fixedMode_twoMode_fuchs_gap_ratio`. -/
theorem constrainedProlate_fixedMode_twoMode_fuchs_gap_eventually_ge
    {Aₖ Aₖ₁ c : ℝ} (hAₖ : 0 < Aₖ) (hAₖ₁ : 0 < Aₖ₁)
    (k : ℕ) (hc : c < 1 - constrainedProlateHermiteTheta k) :
    ∀ᶠ lam in Filter.atTop,
      c * fuchsRate Aₖ₁ (4 * (k + 1)) lam ≤
        fuchsRate Aₖ₁ (4 * (k + 1)) lam -
          GaloisForLFunctions.twoModeSecularRoot
            (fuchsRate Aₖ (4 * k) lam)
            (fuchsRate Aₖ₁ (4 * (k + 1)) lam)
            (Real.sqrt (constrainedProlateHermiteSquareSum k))
            (constrainedProlateHermiteCoordinate (k + 1)) := by
  apply eventually_const_mul_le_of_tendsto_div_atTop
    (constrainedProlate_fixedMode_twoMode_fuchs_gap_ratio hAₖ hAₖ₁ k)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with lam hlam
  exact fuchsRate_pos hAₖ₁ (4 * (k + 1)) hlam
  exact hc

end RHTower
