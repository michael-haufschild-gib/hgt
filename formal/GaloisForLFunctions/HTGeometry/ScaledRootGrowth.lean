import GaloisForLFunctions.HTGeometry.OscillatingRootLimsup

/-!
# Root growth along a rescaled index

A shift lattice of degree `d` reaches the index `k` after `k/d` steps, so its
root exponents are `1/(a m + b)` rather than `1/m`.  Rescaling the exponent does
not change the root growth: writing `u^{1/(am+b)} = (u^{1/m})^{m/(am+b)}` and
noting `m/(am+b) → 1/a`, a sequence whose `m`-th roots tend to one has rescaled
roots tending to one as well, and the bounded-plus-frequently-non-degenerate
criterion for a root `limsup` of one transfers verbatim.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section Rescaling

variable {a b : ℕ}

theorem scaled_denom_pos (ha : 0 < a) {m : ℕ} (hm : 0 < m) :
    (0 : ℝ) < ((a * m + b : ℕ) : ℝ) := by
  have : 0 < a * m + b := by
    have : 0 < a * m := Nat.mul_pos ha hm
    omega
  exact_mod_cast this

/-- The rescaling ratio tends to the reciprocal of the scale. -/
theorem tendsto_scaleRatio (ha : 0 < a) :
    Tendsto (fun m : ℕ => (m : ℝ) / ((a * m + b : ℕ) : ℝ)) atTop (𝓝 (1 / (a : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hden : Tendsto (fun m : ℕ => (a : ℝ) + (b : ℝ) / (m : ℝ)) atTop
      (𝓝 ((a : ℝ) + 0)) := by
    refine tendsto_const_nhds.add ?_
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [add_zero] at hden
  have hlim : Tendsto (fun m : ℕ => 1 / ((a : ℝ) + (b : ℝ) / (m : ℝ))) atTop
      (𝓝 (1 / (a : ℝ))) := tendsto_const_nhds.div hden haR.ne'
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : ((a * m + b : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) + (b : ℝ) := by push_cast; ring
  rw [hcast]
  field_simp

/-- **A root limit survives the rescaling of the exponent.** -/
theorem tendsto_rpow_scaled_of_tendsto_rpow_inv {u : ℕ → ℝ} (hu : ∀ m, 0 ≤ u m)
    (h : Tendsto (fun m : ℕ => (u m) ^ (1 / (m : ℝ))) atTop (𝓝 1)) (ha : 0 < a) :
    Tendsto (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop (𝓝 1) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hp : Tendsto (fun m : ℕ => (m : ℝ) / ((a * m + b : ℕ) : ℝ)) atTop
      (𝓝 (1 / (a : ℝ))) := tendsto_scaleRatio ha
  have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) ((1 : ℝ), 1 / (a : ℝ)) :=
    Real.continuousAt_rpow _ (by norm_num)
  have hcomp := hcont.tendsto.comp (h.prodMk_nhds hp)
  rw [Real.one_rpow] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < ((a * m + b : ℕ) : ℝ) := scaled_denom_pos ha hm
  rw [Function.comp_apply, ← Real.rpow_mul (hu m)]
  congr 1
  field_simp

/-- A positive constant is invisible to the rescaled root. -/
theorem tendsto_const_rpow_scaled {C : ℝ} (hC : 0 < C) (ha : 0 < a) :
    Tendsto (fun m : ℕ => C ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop (𝓝 1) :=
  tendsto_rpow_scaled_of_tendsto_rpow_inv (fun _ => hC.le)
    (tendsto_const_rpow_inv_nat hC) ha

/-- A polynomial envelope is invisible to the rescaled root. -/
theorem tendsto_rpow_scaled_of_polynomial_bounds {u : ℕ → ℝ} {C₁ C₂ B : ℝ}
    (hu : ∀ m, 0 ≤ u m) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hlb : ∀ᶠ m : ℕ in atTop, C₁ * (m : ℝ) ^ (-B) ≤ u m)
    (hub : ∀ᶠ m : ℕ in atTop, u m ≤ C₂ * (m : ℝ) ^ B) (ha : 0 < a) :
    Tendsto (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop (𝓝 1) :=
  tendsto_rpow_scaled_of_tendsto_rpow_inv hu
    (tendsto_rpow_inv_of_polynomial_bounds hC₁ hC₂ hlb hub) ha

end Rescaling

section ScaledLimsup

variable {u : ℕ → ℝ} {a b : ℕ}

theorem rpow_scaled_le_const {C : ℝ} (hnn : ∀ m, 0 ≤ u m) (hub : ∀ m, u m ≤ C)
    (ha : 0 < a) (m : ℕ) :
    (u m) ^ (1 / ((a * m + b : ℕ) : ℝ)) ≤ C ^ (1 / ((a * m + b : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hden : (0 : ℝ) < ((a * 0 + b : ℕ) : ℝ) := by
        have : 0 < a * 0 + b := by omega
        exact_mod_cast this
      exact Real.rpow_le_rpow (hnn 0) (hub 0) (by positivity)
  · have hden : (0 : ℝ) < ((a * m + b : ℕ) : ℝ) := scaled_denom_pos ha hm
    exact Real.rpow_le_rpow (hnn m) (hub m) (by positivity)

theorem isBoundedUnder_rpow_scaled {C : ℝ} (hC : 0 < C) (hnn : ∀ m, 0 ≤ u m)
    (hub : ∀ m, u m ≤ C) (ha : 0 < a) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) := by
  have hconv := tendsto_const_rpow_scaled (a := a) (b := b) hC ha
  refine ⟨2, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [hconv.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with m hm
  exact le_of_lt (lt_of_le_of_lt (rpow_scaled_le_const hnn hub ha m) hm)

/-- **The rescaled root `limsup` of a bounded, frequently non-degenerate factor is
one.** -/
theorem limsup_rpow_scaled_eq_one {C c₀ : ℝ} (hC : 0 < C) (hc₀ : 0 < c₀)
    (hnn : ∀ m, 0 ≤ u m) (hub : ∀ m, u m ≤ C)
    (hlb : ∃ᶠ m in atTop, c₀ ≤ u m) (ha : 0 < a) :
    limsup (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop = 1 := by
  have hbdd := isBoundedUnder_rpow_scaled (a := a) (b := b) hC hnn hub ha
  have hlow : IsBoundedUnder (· ≥ ·) atTop
      (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with m
    exact Real.rpow_nonneg (hnn m) _
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) := hlow.isCoboundedUnder_le
  refine le_antisymm ?_ ?_
  · have hle : limsup (fun m : ℕ => (u m) ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop
        ≤ limsup (fun m : ℕ => C ^ (1 / ((a * m + b : ℕ) : ℝ))) atTop :=
      limsup_le_limsup (Filter.Eventually.of_forall
        (rpow_scaled_le_const hnn hub ha)) hcob
        (tendsto_const_rpow_scaled (a := a) (b := b) hC ha).isBoundedUnder_le
    rwa [(tendsto_const_rpow_scaled (a := a) (b := b) hC ha).limsup_eq] at hle
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨t, ht1, ht2⟩ := exists_between hcon
    have hev : ∀ᶠ m : ℕ in atTop, t < c₀ ^ (1 / ((a * m + b : ℕ) : ℝ)) :=
      (tendsto_const_rpow_scaled (a := a) (b := b) hc₀ ha).eventually_const_lt ht2
    have hfreq : ∃ᶠ m : ℕ in atTop,
        t ≤ (u m) ^ (1 / ((a * m + b : ℕ) : ℝ)) := by
      refine ((hlb.and_eventually hev).and_eventually (eventually_gt_atTop 0)).mono
        fun m hm => ?_
      obtain ⟨⟨hu1, hu2⟩, hmpos⟩ := hm
      have hden : (0 : ℝ) < ((a * m + b : ℕ) : ℝ) := scaled_denom_pos ha hmpos
      exact le_trans hu2.le (Real.rpow_le_rpow hc₀.le hu1 (by positivity))
    exact absurd (le_limsup_of_frequently_le hfreq hbdd) (not_le.mpr ht1)

end ScaledLimsup

end GaloisForLFunctions.HTGeometry
