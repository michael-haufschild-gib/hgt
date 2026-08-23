import GaloisForLFunctions.RHTower.SteinhausRatePositive

/-!
# The rate function is strictly increasing and convex

Any tilt whose value is within `ε` of the supremum must itself be at least that value, because
`λq − Λ_α(λ) ≤ λ`.  Moving `q` up therefore gains at least that much, which makes the rate
strictly increasing.  Convexity is immediate: the rate is a supremum of affine functions of `q`.
-/

open Set

namespace HTGeometry

noncomputable section

/-- **The rate function is strictly increasing on `[0, 1)`.** -/
theorem rvRate_strictMono {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (h12 : q₁ < q₂) (hq₂ : q₂ < 1) :
    rvRate α q₁ < rvRate α q₂ := by
  have hq₁1 : q₁ < 1 := lt_trans h12 hq₂
  rcases eq_or_lt_of_le hq₁ with hzero | hpos
  · rw [← hzero, rvRate_zero hα]
    exact rvRate_pos h0 hα (by linarith) hq₂
  · have hIpos : 0 < rvRate α q₁ := rvRate_pos h0 hα hpos hq₁1
    set d : ℝ := q₂ - q₁ with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have hd1 : d ≤ 1 := by rw [hd]; linarith
    set ε : ℝ := rvRate α q₁ * d / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; positivity
    have hlt : rvRate α q₁ - ε < sSup (rvLegendreSet α q₁) := by
      have h : sSup (rvLegendreSet α q₁) = rvRate α q₁ := rfl
      rw [h]
      linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup (rvLegendreSet_nonempty α q₁) hlt
    obtain ⟨lam, hlam, rfl⟩ := hy
    have hcum := rvCumulant_nonneg α lam
    have hlamge : rvRate α q₁ - ε < lam := by
      have hle : lam * q₁ - rvCumulant α lam ≤ lam := by
        nlinarith [hlam, hcum, hq₁1]
      linarith
    have hstep := le_rvRate hα hq₂ hlam
    have hid : lam * q₂ - rvCumulant α lam
        = (lam * q₁ - rvCumulant α lam) + lam * d := by rw [hd]; ring
    rw [hid] at hstep
    have hgain : lam * d > (rvRate α q₁ - ε) * d :=
      mul_lt_mul_of_pos_right hlamge hd0
    have hfinal : rvRate α q₁ < (rvRate α q₁ - ε) + (rvRate α q₁ - ε) * d := by
      rw [hε]
      nlinarith [hIpos, hd0, hd1]
    linarith [hstep, hylt, hgain, hfinal]

/-- **The rate function is convex.** -/
theorem rvRate_convex {α : ℝ} (hα : α < 1) {q₁ q₂ t : ℝ} (hq₁ : q₁ < 1) (hq₂ : q₂ < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rvRate α (t * q₁ + (1 - t) * q₂) ≤ t * rvRate α q₁ + (1 - t) * rvRate α q₂ := by
  refine csSup_le (rvLegendreSet_nonempty α _) ?_
  rintro y ⟨lam, hlam, rfl⟩
  have h1 := le_rvRate hα hq₁ hlam
  have h2 := le_rvRate hα hq₂ hlam
  have hid : lam * (t * q₁ + (1 - t) * q₂) - rvCumulant α lam
      = t * (lam * q₁ - rvCumulant α lam) + (1 - t) * (lam * q₂ - rvCumulant α lam) := by
    ring
  rw [hid]
  have hA := mul_le_mul_of_nonneg_left h1 ht0
  have hB := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - t)
  linarith

/-- **The rate function is convex on the whole half line below `1`.** -/
theorem convexOn_rvRate {α : ℝ} (hα : α < 1) : ConvexOn ℝ (Set.Iio (1 : ℝ)) (rvRate α) := by
  refine ⟨convex_Iio 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  have hmain := rvRate_convex (α := α) (q₁ := x) (q₂ := y) (t := a) hα hx hy ha (by linarith)
  rw [hb']
  simpa using hmain

/-- **The rate function is continuous below `1`.**  This is part `3`'s continuity claim. -/
theorem continuousOn_rvRate {α : ℝ} (hα : α < 1) :
    ContinuousOn (rvRate α) (Set.Iio (1 : ℝ)) :=
  ConvexOn.continuousOn isOpen_Iio (convexOn_rvRate hα)

end

end HTGeometry
