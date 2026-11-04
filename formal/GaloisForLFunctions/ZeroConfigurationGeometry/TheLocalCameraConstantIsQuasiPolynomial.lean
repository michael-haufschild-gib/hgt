import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatedPointsAreSeenByTheLocalCamera

/-!
# The local camera constant is quasi-polynomial

The local camera at height `X` (`one_add_pow_le_of_isolated_cancellation_of_bump`) uses isolating
windows at spacing `H = 2/D` for a cluster of density `D`, count error `C₀` and isolation `η`. For
`ζ` at height `X` all three move with `X`: `D ≍ log X`, `C₀ ≍ log X`, `η ≍ 1/log X`. Here the window
constants are bounded in terms of `D` alone. Fix `ℓ ≥ 0` and let `|C₀| ≤ ℓD`, `η ≥ 1/D`, `D ≥ 1`,
and `σ = ℓ/2 + 6`. Then:

* the filled lattice has slack `windowSlack ≤ σ` (`windowSlack_localSlack_le`);
* the near/far constant is `≤ nfRate σ · D (1 + log D)` (`nearFarConst_two_mul_inv_le`);
* the growth exponent is `windowExponent ≤ 6σ(1 + σ) D` (`windowExponent_le`);
* `log windowGrowth ≤ growthRate ℓ · D (1 + log D)` (`log_windowGrowth_le`);
* `log (1/windowFloor) ≤ floorRate ℓ · D (1 + log D)²` (`log_inv_windowFloor_le`), and for every
  `0 < η ≤ 1`, `log (1/windowFloor) ≤ floorRate ℓ · D (1 + log D)(1 + log D + log(1/η))`
  (`log_inv_windowFloor_le_of_le_one`).

For `D ≍ log X` the windows grow like `X^{O(log log X)}` and their floor is `X^{−O((log log X)²)}`.
The floor decides: it is the price of `log X` neighbours, each displaced by a bounded multiple of
the mean spacing, at distance `≍ 1/log X` from the target.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The slack bound `ℓ/2 + 6` of a cluster with count error `≤ ℓD`. -/
def slackBound (ℓ : ℝ) : ℝ := ℓ / 2 + 6

/-- The rate of the near/far constant at spacing `2/D` and slack `≤ σ`. -/
def nfRate (σ : ℝ) : ℝ := 4 + 4 * (1 + σ) * (2 + Real.log (2 * σ + 9))

/-- The rate of `log windowGrowth`. -/
def growthRate (ℓ : ℝ) : ℝ :=
  1 + π * (2 + slackBound ℓ) * (1 + 2 * slackBound ℓ) / 2 + π / 4 +
    3 * slackBound ℓ * nfRate (slackBound ℓ)

/-- The rate of `log (1/windowFloor)`. -/
def floorRate (ℓ : ℝ) : ℝ :=
  2 + (1 + slackBound ℓ) ^ 2 +
    6 * slackBound ℓ * (1 + (1 + slackBound ℓ) ^ 2) * nfRate (slackBound ℓ)

theorem latDelta_two_mul_inv {D : ℝ} (hD : 1 ≤ D) : latDelta (2 * D⁻¹) = D⁻¹ := by
  rw [latDelta, show 2 * D⁻¹ / 2 = D⁻¹ by ring]
  exact min_eq_right (inv_le_one_of_one_le₀ hD)

theorem localSlack_nonneg {D C₀ : ℝ} (hD : 0 < D) : 0 ≤ localSlack D C₀ := by
  unfold localSlack; positivity

theorem windowSlack_localSlack_nonneg {D C₀ : ℝ} (hD : 0 < D) :
    0 ≤ windowSlack (2 * D⁻¹) (localSlack D C₀) := by
  have := localSlack_nonneg (C₀ := C₀) hD
  unfold windowSlack; positivity

theorem windowSlack_localSlack_le {D C₀ ℓ : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D) :
    windowSlack (2 * D⁻¹) (localSlack D C₀) ≤ slackBound ℓ := by
  have hD0 : 0 < D := by linarith
  have hinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hinv0 : 0 < D⁻¹ := inv_pos.mpr hD0
  have h1 : |C₀| * D⁻¹ ≤ ℓ := by
    calc |C₀| * D⁻¹ ≤ ℓ * D * D⁻¹ := mul_le_mul_of_nonneg_right hC hinv0.le
      _ = ℓ := by field_simp
  unfold windowSlack localSlack slackBound
  linarith

/-- **The near/far constant at spacing `2/D`.** -/
theorem nearFarConst_two_mul_inv_le {D L σ : ℝ} (hD : 1 ≤ D) (hL0 : 0 ≤ L) (hLσ : L ≤ σ) :
    nearFarConst (2 * D⁻¹) L ≤ nfRate σ * D * (1 + Real.log D) := by
  have hD0 : 0 < D := by linarith
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hσ0 : 0 ≤ σ := hL0.trans hLσ
  have hlσ : 0 ≤ Real.log (2 * σ + 9) := Real.log_nonneg (by linarith)
  have e3 : 4 * (L + 2) / (2 * D⁻¹) = 2 * (L + 2) * D := by field_simp; ring
  obtain ⟨lg, hlg⟩ : ∃ lg, lg = Real.log (4 * (L + 2) / (2 * D⁻¹) + 5) := ⟨_, rfl⟩
  have hlog : lg ≤ Real.log (2 * σ + 9) + Real.log D := by
    rw [hlg, ← Real.log_mul (by positivity) hD0.ne', e3]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlg0 : 0 ≤ lg := by
    rw [hlg, e3]
    exact Real.log_nonneg (by nlinarith)
  rw [nearFarConst, latDelta_two_mul_inv hD, ← hlg, show 4 / (2 * D⁻¹) = 2 * D by field_simp; ring,
    show 1 / D⁻¹ = D by field_simp, show (1 + lg) / (2 * D⁻¹) = (1 + lg) * D / 2 by field_simp,
    nfRate]
  have step : 4 * (1 + L) * (D + (1 + lg) * D / 2) ≤
      4 * (1 + σ) * (D + (1 + (Real.log (2 * σ + 9) + Real.log D)) * D / 2) := by
    have h1 : (1 + lg) * D ≤ (1 + (Real.log (2 * σ + 9) + Real.log D)) * D :=
      mul_le_mul_of_nonneg_right (by linarith) hD0.le
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hA : (0 : ℝ) ≤ 1 + σ := by linarith
  nlinarith [mul_nonneg hA hD0.le, mul_nonneg (mul_nonneg hA hD0.le) hlσ, mul_nonneg hD0.le hlD,
    mul_nonneg (mul_nonneg hA hD0.le) hlD,
    mul_nonneg (mul_nonneg (mul_nonneg hA hD0.le) hlσ) hlD]

/-- **The growth exponent at spacing `2/D`.** -/
theorem windowExponent_le {D C₀ ℓ : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D) :
    windowExponent (2 * D⁻¹) (localSlack D C₀) ≤
      6 * slackBound ℓ * (1 + slackBound ℓ) * D := by
  have hD0 : 0 < D := by linarith
  have hS := windowSlack_localSlack_le hD hC
  have hS0 := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨S, hSdef⟩ : ∃ S, S = windowSlack (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  rw [← hSdef] at hS hS0
  rw [windowExponent, ← hSdef, show 4 * (1 + S) / (2 * D⁻¹) = 2 * (1 + S) * D by field_simp; ring]
  have h1 : S * (1 + S) ≤ slackBound ℓ * (1 + slackBound ℓ) :=
    mul_le_mul hS (by linarith) (by linarith) (by linarith)
  nlinarith

theorem log_nearestConstStrip_le {D L σ : ℝ} (hD : 1 ≤ D) (hL0 : 0 ≤ L) (hLσ : L ≤ σ) :
    Real.log (nearestConstStrip (2 * D⁻¹) L) ≤
      Real.log D + π * (2 + σ) * (1 + 2 * σ) / 2 + π * D / 4 := by
  have hD0 : 0 < D := by linarith
  have hinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hσ0 : 0 ≤ σ := hL0.trans hLσ
  rw [nearestConstStrip, show π / (2 * D⁻¹) = π * D / 2 by field_simp,
    show 2 * D⁻¹ / 2 = D⁻¹ by ring, show π / (2 * (2 * D⁻¹)) = π * D / 4 by field_simp; ring,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have h1 : (D⁻¹ + 1 / 2 + L) * (1 + 2 * L) ≤ (2 + σ) * (1 + 2 * σ) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have h2 : π * D / 2 * ((D⁻¹ + 1 / 2 + L) * (1 + 2 * L)) ≤ π * D / 2 * ((2 + σ) * (1 + 2 * σ)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hin : π * D / 2 * (D⁻¹ + 1 / 2 + L) * (1 + 2 * L) + 1 ≤
      D * (π * (2 + σ) * (1 + 2 * σ) / 2 + 1) := by
    nlinarith
  have hc : 0 < π * (2 + σ) * (1 + 2 * σ) / 2 + 1 := by positivity
  calc Real.log (π * D / 2 * (D⁻¹ + 1 / 2 + L) * (1 + 2 * L) + 1) + π * D / 4
      ≤ Real.log (D * (π * (2 + σ) * (1 + 2 * σ) / 2 + 1)) + π * D / 4 := by
        gcongr
    _ = Real.log D + Real.log (π * (2 + σ) * (1 + 2 * σ) / 2 + 1) + π * D / 4 := by
        rw [Real.log_mul hD0.ne' hc.ne']
    _ ≤ Real.log D + π * (2 + σ) * (1 + 2 * σ) / 2 + π * D / 4 := by
        have := Real.log_le_sub_one_of_pos hc
        linarith

/-- **The growth of the isolating windows.** -/
theorem log_windowGrowth_le {D C₀ ℓ : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D) :
    Real.log (windowGrowth (2 * D⁻¹) (localSlack D C₀)) ≤ growthRate ℓ * D * (1 + Real.log D) := by
  have hD0 : 0 < D := by linarith
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hS := windowSlack_localSlack_le hD hC
  have hS0 := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨S, hSdef⟩ : ∃ S, S = windowSlack (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  rw [← hSdef] at hS hS0
  have hσ0 : 0 ≤ slackBound ℓ := hS0.trans hS
  have hncs := log_nearestConstStrip_le hD hS0 hS
  have hnf := nearFarConst_two_mul_inv_le hD hS0 hS
  have hncs0 : 0 < nearestConstStrip (2 * D⁻¹) S := by
    rw [nearestConstStrip]
    exact mul_pos (by positivity) (Real.exp_pos _)
  rw [windowGrowth, ← hSdef, Real.log_mul hncs0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hnfr : 0 ≤ nfRate (slackBound ℓ) := by
    unfold nfRate
    have : 0 ≤ Real.log (2 * slackBound ℓ + 9) := Real.log_nonneg (by linarith)
    positivity
  have h3 : 3 * S * nearFarConst (2 * D⁻¹) S ≤
      3 * slackBound ℓ * (nfRate (slackBound ℓ) * D * (1 + Real.log D)) := by
    have hnf0 : 0 ≤ nearFarConst (2 * D⁻¹) S := by
      rw [nearFarConst, latDelta_two_mul_inv hD]
      have : 0 ≤ Real.log (4 * (S + 2) / (2 * D⁻¹) + 5) := Real.log_nonneg (by
        have : 0 ≤ 4 * (S + 2) / (2 * D⁻¹) := by positivity
        linarith)
      positivity
    exact mul_le_mul (by linarith) hnf hnf0 (by positivity)
  have hDl : 1 ≤ D * (1 + Real.log D) := by nlinarith
  have hlogD : Real.log D ≤ D * (1 + Real.log D) := by nlinarith
  have hc1 : 0 ≤ π * (2 + slackBound ℓ) * (1 + 2 * slackBound ℓ) / 2 := by positivity
  rw [growthRate]
  linarith [hncs, h3, hlogD, mul_le_mul_of_nonneg_left hDl hc1,
    mul_nonneg (mul_nonneg Real.pi_pos.le hD0.le) hlD]

/-- **The floor of the isolating windows.** -/
theorem log_inv_windowFloor_le {D C₀ ℓ η : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D) (hη : D⁻¹ ≤ η) :
    Real.log (windowFloor (2 * D⁻¹) (localSlack D C₀) η)⁻¹ ≤
      floorRate ℓ * D * (1 + Real.log D) ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hinv0 : 0 < D⁻¹ := inv_pos.mpr hD0
  have hS := windowSlack_localSlack_le hD hC
  have hS0 := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨S, hSdef⟩ : ∃ S, S = windowSlack (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  rw [← hSdef] at hS hS0
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = slackBound ℓ := ⟨_, rfl⟩
  rw [← hσ] at hS
  have hσ0 : 0 ≤ σ := hS0.trans hS
  have hmin : min η (2 * D⁻¹ / 2) = D⁻¹ := by
    rw [show 2 * D⁻¹ / 2 = D⁻¹ by ring]; exact min_eq_right hη
  -- the factor floor
  have hiso : Real.log (1 / isoConst S D⁻¹) ≤ Real.log D + (1 + σ) ^ 2 := by
    have e : 1 / isoConst S D⁻¹ = D * ((D⁻¹ + S) * (1 + S)) := by
      rw [isoConst, one_div_div, div_eq_mul_inv, inv_inv, mul_comm]
    rw [e, Real.log_mul hD0.ne' (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < (D⁻¹ + S) * (1 + S))
    have h2 : (D⁻¹ + S) * (1 + S) ≤ (1 + σ) ^ 2 := by nlinarith
    linarith
  have hiso0 : 0 ≤ Real.log (1 / isoConst S D⁻¹) := by
    have hc1 : isoConst S D⁻¹ ≤ 1 := isoConst_le_one hS0 hinv0
    have hc0 : 0 < isoConst S D⁻¹ := isoConst_pos hS0 hinv0
    exact Real.log_nonneg (by rw [le_div_iff₀ hc0]; linarith)
  have hrate : isoRate S D⁻¹ ≤ 6 * σ * ((1 + (1 + σ) ^ 2) * (1 + Real.log D)) := by
    rw [isoRate]
    have : 1 + Real.log (1 / isoConst S D⁻¹) ≤ (1 + (1 + σ) ^ 2) * (1 + Real.log D) := by
      nlinarith [mul_nonneg (sq_nonneg (1 + σ)) hlD]
    exact mul_le_mul (by linarith) this (by linarith) (by positivity)
  have hrate0 : 0 ≤ isoRate S D⁻¹ := by
    rw [isoRate]; positivity
  have hnf := nearFarConst_two_mul_inv_le hD hS0 hS
  have hnf0 : 0 ≤ nearFarConst (2 * D⁻¹) S := by
    rw [nearFarConst, latDelta_two_mul_inv hD]
    have : 0 ≤ Real.log (4 * (S + 2) / (2 * D⁻¹) + 5) := Real.log_nonneg (by
      have : 0 ≤ 4 * (S + 2) / (2 * D⁻¹) := by positivity
      linarith)
    positivity
  have hnfr : 0 ≤ nfRate σ := by
    unfold nfRate
    have : 0 ≤ Real.log (2 * σ + 9) := Real.log_nonneg (by linarith)
    positivity
  have hprod : isoRate S D⁻¹ * nearFarConst (2 * D⁻¹) S ≤
      6 * σ * (1 + (1 + σ) ^ 2) * nfRate σ * D * (1 + Real.log D) ^ 2 := by
    calc isoRate S D⁻¹ * nearFarConst (2 * D⁻¹) S
        ≤ 6 * σ * ((1 + (1 + σ) ^ 2) * (1 + Real.log D)) * (nfRate σ * D * (1 + Real.log D)) :=
          mul_le_mul hrate hnf hnf0 (by positivity)
      _ = _ := by ring
  have hc0 : 0 < isoConst S D⁻¹ := isoConst_pos hS0 hinv0
  rw [windowFloor, ← hSdef, hmin]
  have e : (1 / 2 * (isoConst S D⁻¹ * Real.exp (-(isoRate S D⁻¹ * nearFarConst (2 * D⁻¹) S))))⁻¹ =
      2 * (1 / isoConst S D⁻¹) * Real.exp (isoRate S D⁻¹ * nearFarConst (2 * D⁻¹) S) := by
    rw [Real.exp_neg]; field_simp
  rw [e, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by norm_num) (by positivity)]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hDl : 1 ≤ D * (1 + Real.log D) ^ 2 := by nlinarith [mul_nonneg hD0.le hlD]
  have hlogD : Real.log D ≤ D * (1 + Real.log D) ^ 2 := by
    nlinarith [mul_nonneg hD0.le hlD, mul_nonneg (mul_nonneg hD0.le hlD) hlD]
  rw [floorRate, ← hσ]
  nlinarith [mul_le_mul_of_nonneg_left hDl (sq_nonneg (1 + σ)), Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

/-- **The floor at small isolation.** For `0 < η ≤ 1` the isolation radius enters only through
`log(1/η)`: `log (1/windowFloor) ≤ floorRate ℓ · D (1 + log D)(1 + log D + log(1/η))`. -/
theorem log_inv_windowFloor_le_of_le_one {D C₀ ℓ η : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D)
    (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Real.log (windowFloor (2 * D⁻¹) (localSlack D C₀) η)⁻¹ ≤
      floorRate ℓ * D * (1 + Real.log D) * (1 + Real.log D + Real.log (1 / η)) := by
  have hD0 : 0 < D := by linarith
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hinv : D⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hinv0 : 0 < D⁻¹ := inv_pos.mpr hD0
  have hlη : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hS := windowSlack_localSlack_le hD hC
  have hS0 := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨S, hSdef⟩ : ∃ S, S = windowSlack (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  rw [← hSdef] at hS hS0
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = slackBound ℓ := ⟨_, rfl⟩
  rw [← hσ] at hS
  have hσ0 : 0 ≤ σ := hS0.trans hS
  obtain ⟨η', hη'⟩ : ∃ η', η' = min η (2 * D⁻¹ / 2) := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; exact lt_min hη0 (by positivity)
  have hη'1 : η' ≤ 1 := by rw [hη']; exact (min_le_left _ _).trans hη1
  have hη'low : η * D⁻¹ ≤ η' := by
    rw [hη', show 2 * D⁻¹ / 2 = D⁻¹ by ring]
    exact le_min (by nlinarith) (by nlinarith)
  obtain ⟨ℒ, hℒ⟩ : ∃ ℒ, ℒ = Real.log D + Real.log (1 / η) := ⟨_, rfl⟩
  have hℒ0 : 0 ≤ ℒ := by rw [hℒ]; positivity
  have hlη' : Real.log (1 / η') ≤ ℒ := by
    rw [hℒ, ← Real.log_mul hD0.ne' (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hη'0]
    calc (1 : ℝ) = D * (1 / η) * (η * D⁻¹) := by field_simp
      _ ≤ D * (1 / η) * η' := mul_le_mul_of_nonneg_left hη'low (by positivity)
  have hiso : Real.log (1 / isoConst S η') ≤ ℒ + (1 + σ) ^ 2 := by
    have e : 1 / isoConst S η' = 1 / η' * ((η' + S) * (1 + S)) := by
      rw [isoConst]; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < (η' + S) * (1 + S))
    have h2 : (η' + S) * (1 + S) ≤ (1 + σ) ^ 2 := by nlinarith
    linarith
  have hrate : isoRate S η' ≤ 6 * σ * ((1 + (1 + σ) ^ 2) * (1 + ℒ)) := by
    rw [isoRate]
    have : 1 + Real.log (1 / isoConst S η') ≤ (1 + (1 + σ) ^ 2) * (1 + ℒ) := by
      nlinarith [mul_nonneg (sq_nonneg (1 + σ)) hℒ0]
    exact mul_le_mul (by linarith) this (by
      have hc1 : isoConst S η' ≤ 1 := isoConst_le_one hS0 hη'0
      have hc0 : 0 < isoConst S η' := isoConst_pos hS0 hη'0
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / isoConst S η' by
        rw [le_div_iff₀ hc0]; linarith)
      linarith) (by positivity)
  have hrate0 : 0 ≤ isoRate S η' := by
    rw [isoRate]
    have hc1 : isoConst S η' ≤ 1 := isoConst_le_one hS0 hη'0
    have hc0 : 0 < isoConst S η' := isoConst_pos hS0 hη'0
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / isoConst S η' by rw [le_div_iff₀ hc0]; linarith)
    positivity
  have hnf := nearFarConst_two_mul_inv_le hD hS0 hS
  have hnf0 : 0 ≤ nearFarConst (2 * D⁻¹) S := by
    rw [nearFarConst, latDelta_two_mul_inv hD]
    have : 0 ≤ Real.log (4 * (S + 2) / (2 * D⁻¹) + 5) := Real.log_nonneg (by
      have : 0 ≤ 4 * (S + 2) / (2 * D⁻¹) := by positivity
      linarith)
    positivity
  have hnfr : 0 ≤ nfRate σ := by
    unfold nfRate
    have : 0 ≤ Real.log (2 * σ + 9) := Real.log_nonneg (by linarith)
    positivity
  have hprod : isoRate S η' * nearFarConst (2 * D⁻¹) S ≤
      6 * σ * (1 + (1 + σ) ^ 2) * nfRate σ * (D * (1 + Real.log D) * (1 + ℒ)) := by
    calc isoRate S η' * nearFarConst (2 * D⁻¹) S
        ≤ 6 * σ * ((1 + (1 + σ) ^ 2) * (1 + ℒ)) * (nfRate σ * D * (1 + Real.log D)) :=
          mul_le_mul hrate hnf hnf0 (by positivity)
      _ = _ := by ring
  have hc0 : 0 < isoConst S η' := isoConst_pos hS0 hη'0
  rw [windowFloor, ← hSdef, ← hη']
  have e : (1 / 2 * (isoConst S η' * Real.exp (-(isoRate S η' * nearFarConst (2 * D⁻¹) S))))⁻¹ =
      2 * (1 / isoConst S η') * Real.exp (isoRate S η' * nearFarConst (2 * D⁻¹) S) := by
    rw [Real.exp_neg]; field_simp
  rw [e, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by norm_num) (by positivity)]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hT : 1 ≤ D * (1 + Real.log D) := by nlinarith
  have hT1 : 1 + ℒ ≤ D * (1 + Real.log D) * (1 + ℒ) := le_mul_of_one_le_left (by linarith) hT
  have hℒ' : 1 + Real.log D + Real.log (1 / η) = 1 + ℒ := by rw [hℒ]; ring
  rw [floorRate, ← hσ, hℒ']
  have hA : (2 + (1 + σ) ^ 2) * (1 + ℒ) ≤ (2 + (1 + σ) ^ 2) * (D * (1 + Real.log D) * (1 + ℒ)) :=
    mul_le_mul_of_nonneg_left hT1 (by positivity)
  nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2), mul_nonneg (sq_nonneg (1 + σ)) hℒ0]

end GaloisForLFunctions.ZeroConfigurationGeometry
