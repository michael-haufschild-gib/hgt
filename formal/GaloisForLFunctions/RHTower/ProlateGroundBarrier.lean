import GaloisForLFunctions.RHTower.ProlateInteriorMassLower
import GaloisForLFunctions.RHTower.ProlateTurningLayer

/-!
# A radial Riccati barrier valid at every separation

The elementary barrier `c sqrt(1-s) y / sqrt(1-y²)` is a Riccati subsolution on the whole positive
half-band only when `c·s ≥ 4`: at `y = 0` its derivative is `c sqrt(1-s)` while the Riccati slack
there is exactly `c² s`, so the comparison is marginal precisely when `c·s` approaches `1` — which
is the ground index of the prolate ladder.

Lifting the barrier by the constant `2 sqrt c` repairs this with no hypothesis on `c·s` at all.
The lift changes neither the derivative nor the leading behaviour, and it adds `K² = 4c` to the
Riccati slack, which dominates `c sqrt(1-s) / sqrt(1-y²)³ ≤ 2 sqrt 2 · c` throughout the region
`y² ≤ 1/2` where the tail term `2y B/(1-y²)` cannot carry the derivative.  For `y² ≥ 1/2` the tail
term alone already suffices.

The lift costs one additive `2 sqrt c` in every downstream flux constant, hence a factor
`exp(4 sqrt c · w / (1 - b²))` in the window-mass bound: for the window width `w = 1/c` used by the
leakage estimate that factor is bounded, so the ground index obeys the same explicit upper leakage
bound as every excited index.
-/

noncomputable section

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- The elementary radial barrier lifted by `2 sqrt c`. -/
def prolateShiftedBarrier (c s y : ℝ) : ℝ := prolateRadialBarrier c s y + 2 * Real.sqrt c

theorem prolateRadialBarrier_le_shiftedBarrier {c s y : ℝ} :
    prolateRadialBarrier c s y ≤ prolateShiftedBarrier c s y := by
  have h : (0 : ℝ) ≤ 2 * Real.sqrt c := by positivity
  rw [prolateShiftedBarrier]
  linarith

theorem hasDerivAt_prolateShiftedBarrier {c s y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (prolateShiftedBarrier c s)
      (c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ)) y := by
  have h := (hasDerivAt_prolateRadialBarrier (c := c) (s := s) hy).add_const (2 * Real.sqrt c)
  exact h

theorem continuousOn_prolateShiftedBarrier {c s a b : ℝ}
    (hp : ∀ y ∈ Icc a b, 0 < 1 - y ^ (2 : ℕ)) :
    ContinuousOn (prolateShiftedBarrier c s) (Icc a b) :=
  (continuousOn_prolateRadialBarrier hp).add continuousOn_const

theorem prolateRadialBarrier_nonneg {c s y : ℝ} (hc : 0 ≤ c) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ prolateRadialBarrier c s y := by
  have hd : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have hr : (0 : ℝ) < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hd
  have hk : (0 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  rw [prolateRadialBarrier]
  positivity

/-- **The lifted barrier is a Riccati subsolution at every separation.**  No lower bound on `c·s`
is used: below the half-band midpoint the added constant contributes `4c` to the slack, which
already dominates the derivative `c sqrt(1-s)/sqrt(1-y²)³`, and above it the transport term
`2y B/(1-y²)` carries the derivative by itself. -/
theorem prolateShiftedBarrier_subsolution {c s y : ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ) ≤
      prolateShiftedBarrier c s y ^ (2 : ℕ) +
        (2 * y / (1 - y ^ (2 : ℕ))) * prolateShiftedBarrier c s y -
          (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hd : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  set r : ℝ := Real.sqrt (1 - y ^ (2 : ℕ)) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 hd
  have hrsq : r ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) := Real.sq_sqrt hd.le
  set κ : ℝ := Real.sqrt (1 - s) with hκ_def
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκsq : κ ^ (2 : ℕ) = 1 - s := Real.sq_sqrt (by linarith)
  have hκ1 : κ ≤ 1 := by nlinarith
  set P : ℝ := prolateRadialBarrier c s y with hP_def
  have hPval : P = c * κ * y / r := by rw [hP_def, prolateRadialBarrier]
  have hP0 : 0 ≤ P := by rw [hPval]; positivity
  set K : ℝ := 2 * Real.sqrt c with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hKsq : K ^ (2 : ℕ) = 4 * c := by
    rw [hK_def, mul_pow, Real.sq_sqrt hc.le]; ring
  set B : ℝ := 2 * y / (1 - y ^ (2 : ℕ)) with hB_def
  have hB0 : 0 ≤ B := by rw [hB_def]; positivity
  -- the exact Riccati identity of the unlifted barrier
  have hPsq : P ^ (2 : ℕ) = c ^ (2 : ℕ) * (1 - s) * y ^ (2 : ℕ) / (1 - y ^ (2 : ℕ)) := by
    rw [hPval, div_pow, hrsq]
    congr 1
    rw [mul_pow, mul_pow, hκsq]
  have hPq : P ^ (2 : ℕ) - (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) = c ^ (2 : ℕ) * s := by
    rw [hPsq, div_sub_div_same, div_eq_iff (ne_of_gt hd)]
    ring
  have hexpand : prolateShiftedBarrier c s y ^ (2 : ℕ) +
        B * prolateShiftedBarrier c s y -
          (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ))
      = c ^ (2 : ℕ) * s + (B * P + K ^ (2 : ℕ) + 2 * P * K + B * K) := by
    have hsplit : prolateShiftedBarrier c s y = P + K := rfl
    rw [hsplit]
    have hring : (P + K) ^ (2 : ℕ) + B * (P + K) -
        (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ))
        = (P ^ (2 : ℕ) - (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
          + (B * P + K ^ (2 : ℕ) + 2 * P * K + B * K) := by ring
    rw [hring, hPq]
  rw [hexpand]
  have hcs0 : (0 : ℝ) ≤ c ^ (2 : ℕ) * s := by positivity
  have hBP : 0 ≤ B * P := mul_nonneg hB0 hP0
  have hPK : 0 ≤ 2 * P * K := by positivity
  have hBK : 0 ≤ B * K := mul_nonneg hB0 hK0
  by_cases hhalf : (1 : ℝ) / 2 ≤ y ^ (2 : ℕ)
  · -- the transport term alone carries the derivative
    have hr3 : r ^ (3 : ℕ) = (1 - y ^ (2 : ℕ)) * r := by rw [← hrsq]; ring
    have hBPval : B * P = 2 * c * κ * y ^ (2 : ℕ) / r ^ (3 : ℕ) := by
      rw [hB_def, hPval, hr3]
      field_simp
    have hnum : c * κ ≤ 2 * c * κ * y ^ (2 : ℕ) := by nlinarith [mul_nonneg hc.le hκ0]
    have h3 : (0 : ℝ) < r ^ (3 : ℕ) := pow_pos hr 3
    have hkey : c * κ / r ^ (3 : ℕ) ≤ B * P := by
      rw [hBPval, ← sub_nonneg, ← sub_div]
      exact div_nonneg (by linarith) h3.le
    linarith
  · -- the lift alone carries the derivative
    have hy2 : y ^ (2 : ℕ) < 1 / 2 := lt_of_not_ge hhalf
    have hr710 : (7 : ℝ) / 10 ≤ r := by nlinarith [hr.le]
    have hr3ge : (343 : ℝ) / 1000 ≤ r ^ (3 : ℕ) := by nlinarith [hr.le]
    have hkey : c * κ / r ^ (3 : ℕ) ≤ K ^ (2 : ℕ) := by
      rw [hKsq, div_le_iff₀ (pow_pos hr 3)]
      nlinarith [hc.le, hκ0, hκ1]
    linarith

/-- Backward Riccati comparison using the lifted radial barrier. -/
theorem prolateLogDeriv_le_shiftedBarrier
    {c s a b : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hinit : prolateLogDeriv Φ b ≤ prolateShiftedBarrier c s b) :
    ∀ y ∈ Icc a b, prolateLogDeriv Φ y ≤ prolateShiftedBarrier c s y := by
  have hp : ∀ y ∈ Icc a b, 0 < 1 - y ^ (2 : ℕ) := by
    intro y hy
    nlinarith [ha, hy.1, hy.2, hb]
  refine HTGeometry.riccati_le_of_le_of_subsolution
    (u := prolateLogDeriv Φ) (U := prolateShiftedBarrier c s)
    (u' := fun y => (prolateLogDeriv Φ y) ^ (2 : ℕ) +
      (2 * y / (1 - y ^ (2 : ℕ))) * prolateLogDeriv Φ y -
        (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    (U' := fun y => c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ))
    (bcoef := fun y => 2 * y / (1 - y ^ (2 : ℕ)))
    (q := fun y => (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    hab (continuousOn_prolateLogDeriv hsm fun y hy => ne_of_gt (hpos y hy))
    (continuousOn_prolateShiftedBarrier hp) ?_ ?_ ?_ ?_ ?_ hinit
  · intro y hy
    have hymem : y ∈ Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hyband : y ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> nlinarith [ha, hy.1, hy.2, hb]
    exact hasDerivAt_prolateLogDeriv hsm heig hyband (ne_of_gt (hpos y hymem))
  · intro y hy
    have hyband : y ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> nlinarith [ha, hy.1, hy.2, hb]
    exact hasDerivAt_prolateShiftedBarrier hyband
  · have hnum : ContinuousOn (fun y : ℝ => 2 * y) (Icc a b) := by fun_prop
    have hden : ContinuousOn (fun y : ℝ => 1 - y ^ (2 : ℕ)) (Icc a b) := by fun_prop
    exact hnum.div hden fun y hy => ne_of_gt (hp y hy)
  · intro _ _
    rfl
  · intro y hy
    have hypos : y ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ha hy.1, lt_trans hy.2 hb⟩
    exact prolateShiftedBarrier_subsolution hc hs0 hs1 hypos

/-- The endpoint-normalized logarithmic derivative lies below the lifted barrier, at every
separation. -/
theorem prolateLogDeriv_le_shiftedBarrier_of_endpoint_normalized
    {c s a : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hpos : ∀ y ∈ Icc a 1, 0 < Φ y) :
    prolateLogDeriv Φ a ≤ prolateShiftedBarrier c s a := by
  have hab : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), a ≤ b :=
    mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ha1)
  have hb1 : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), b < 1 := self_mem_nhdsWithin
  have hinit := eventually_prolateLogDeriv_le_radialBarrier_at_one hc hs0 hs1 hsm hΦ1
  obtain ⟨b, habb, hb, hterminal⟩ := (hab.and (hb1.and hinit)).exists
  exact prolateLogDeriv_le_shiftedBarrier hc hs0 hs1.le hsm heig
    habb ha0 hb (fun y hy => hpos y ⟨hy.1, hy.2.trans hb.le⟩)
    (hterminal.trans prolateRadialBarrier_le_shiftedBarrier)
    a ⟨le_rfl, habb⟩

/-- Two-sided band bound for the logarithmic derivative, at every separation. -/
theorem abs_prolateLogDeriv_le_shiftedBand {c s α : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hα0 : 0 < α) (hα1 : α < 1) (hsα : s < α ^ (2 : ℕ))
    (hpos : ∀ u ∈ Icc α 1, 0 < Φ u) :
    |prolateLogDeriv Φ α| ≤ prolateShiftedBarrier c s α + 6 / (1 - α) := by
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hupper : prolateLogDeriv Φ α ≤ prolateShiftedBarrier c s α :=
    prolateLogDeriv_le_shiftedBarrier_of_endpoint_normalized hc hs0 hs1 hα0 hα1 hsm heig hΦ1 hpos
  have hcχ : (0 : ℝ) ≤ c ^ (2 : ℕ) + -(s * c ^ (2 : ℕ)) := by nlinarith [sq_nonneg c]
  have hturn : ∀ u ∈ Icc α 1, (0 : ℝ) ≤ -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * u ^ (2 : ℕ) := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hα0.le hu.1
    have hsq : α ^ (2 : ℕ) ≤ u ^ (2 : ℕ) := by nlinarith [hu.1, hα0]
    nlinarith [mul_nonneg (sq_nonneg c) (by linarith : (0 : ℝ) ≤ u ^ (2 : ℕ) - s)]
  have hQ0 : (0 : ℝ) < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * α ^ (2 : ℕ) := by
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsα)]
  have hlower := prolateWKB_sub_six_div_le_prolateLogDeriv (c := c) (χ := -(s * c ^ (2 : ℕ)))
    hsm heig hcχ hα0.le hα1 hpos hturn hQ0
  have hWnn : (0 : ℝ) ≤ prolateWKB c (-(s * c ^ (2 : ℕ))) α := Real.sqrt_nonneg _
  have hbar : (0 : ℝ) ≤ prolateShiftedBarrier c s α := by
    have h := prolateRadialBarrier_nonneg (c := c) (s := s) (y := α) hc.le hα0.le hα1
    have h2 : (0 : ℝ) ≤ 2 * Real.sqrt c := by positivity
    rw [prolateShiftedBarrier]
    linarith
  have hsix : (0 : ℝ) < 6 / (1 - α) := by positivity
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The flux of a band mode is bounded by the lifted barrier times the value.** -/
theorem prolateFlux_sq_le_shiftedBand {c s t : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (ht0 : 0 < t) (ht1 : t < 1) (hst : s < t ^ (2 : ℕ))
    (hpos : ∀ u ∈ Icc t 1, 0 < Φ u) :
    prolateFlux Φ t ^ (2 : ℕ)
      ≤ ((1 - t ^ (2 : ℕ)) * (prolateShiftedBarrier c s t + 6 / (1 - t))) ^ (2 : ℕ) * Φ t ^ (2 : ℕ) := by
  have hB := abs_prolateLogDeriv_le_shiftedBand hc hs0 hs1 hsm heig hΦ1 ht0 ht1 hst hpos
  have hΦt : 0 < Φ t := hpos t ⟨le_rfl, ht1.le⟩
  have hderiv : |deriv Φ t| ≤ (prolateShiftedBarrier c s t + 6 / (1 - t)) * Φ t := by
    rw [prolateLogDeriv, abs_neg, abs_div, abs_of_pos hΦt, div_le_iff₀ hΦt] at hB
    exact hB
  have hBnn : (0 : ℝ) ≤ (prolateShiftedBarrier c s t + 6 / (1 - t)) * Φ t :=
    le_trans (abs_nonneg _) hderiv
  have hsq : deriv Φ t ^ (2 : ℕ) ≤ ((prolateShiftedBarrier c s t + 6 / (1 - t)) * Φ t) ^ (2 : ℕ) := by
    have := sq_abs (deriv Φ t)
    nlinarith [hderiv, abs_nonneg (deriv Φ t), this]
  rw [prolateFlux, mul_pow]
  nlinarith [hsq, sq_nonneg (1 - t ^ (2 : ℕ)),
    mul_pow (prolateShiftedBarrier c s t + 6 / (1 - t)) (Φ t) 2]

/-- The uniform lifted barrier constant on a window of the band. -/
theorem one_sub_sq_mul_shiftedBand_barrier_le {c s t b : ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (htb : t ≤ b) (hb1 : b < 1) :
    (1 - t ^ (2 : ℕ)) * (prolateShiftedBarrier c s t + 6 / (1 - t))
      ≤ c * b + 12 + 2 * Real.sqrt c := by
  have hbase := one_sub_sq_mul_band_barrier_le hc hs0 ht0 htb hb1
  have ht1 : t < 1 := lt_of_le_of_lt htb hb1
  have hw : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
  have hw1 : (0 : ℝ) ≤ 1 - t ^ (2 : ℕ) := hw.le
  have hwle : (1 : ℝ) - t ^ (2 : ℕ) ≤ 1 := by nlinarith
  have hsc : (0 : ℝ) ≤ 2 * Real.sqrt c := by positivity
  have hsplit : (1 - t ^ (2 : ℕ)) * (prolateShiftedBarrier c s t + 6 / (1 - t))
      = (1 - t ^ (2 : ℕ)) * (prolateRadialBarrier c s t + 6 / (1 - t))
        + (1 - t ^ (2 : ℕ)) * (2 * Real.sqrt c) := by
    rw [prolateShiftedBarrier]; ring
  have hlift : (1 - t ^ (2 : ℕ)) * (2 * Real.sqrt c) ≤ 2 * Real.sqrt c := by nlinarith
  rw [hsplit]
  linarith

/-! ## The window and aperture mass, with an arbitrary flux constant -/

/-- **The interior mass from below on a band window, for any uniform flux constant.** -/
theorem prolate_window_mass_lower_of_fluxConst {M y₀ b : ℝ} {Φ : ℝ → ℝ}
    (hM : 0 ≤ M) (hy00 : 0 < y₀) (hy0b : y₀ ≤ b) (hb1 : b < 1)
    (hd1 : Differentiable ℝ Φ)
    (hpos : ∀ u ∈ Icc y₀ 1, 0 < Φ u)
    (hfluxM : ∀ t ∈ Icc y₀ b, prolateFlux Φ t ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * Φ t ^ (2 : ℕ)) :
    (b - y₀) * (Φ y₀ * Real.exp (-(M * (b - y₀) / (1 - b ^ (2 : ℕ))))) ^ (2 : ℕ)
      ≤ ∫ t in y₀..b, Φ t ^ (2 : ℕ) := by
  have hMsqrt : Real.sqrt (M ^ (2 : ℕ)) = M := Real.sqrt_sq hM
  have hposwin : ∀ t ∈ Icc y₀ b, 0 < Φ t := fun t ht =>
    hpos t ⟨ht.1, le_trans ht.2 hb1.le⟩
  have hmain := mass_lower_of_fluxBound (Φ := Φ) (K := M ^ (2 : ℕ)) (sq_nonneg M) hy0b hb1
    (by linarith) hd1 hposwin hfluxM
  rw [hMsqrt] at hmain
  refine le_trans ?_ hmain
  have hbw : (0 : ℝ) < 1 - b ^ (2 : ℕ) := by
    have hb0 : (0 : ℝ) ≤ b := le_trans hy00.le hy0b
    nlinarith
  have hJ : (∫ t in y₀..b, M / (1 - t ^ (2 : ℕ))) ≤ M * (b - y₀) / (1 - b ^ (2 : ℕ)) := by
    have hcont : ContinuousOn (fun t : ℝ => M / (1 - t ^ (2 : ℕ))) (Icc y₀ b) := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
      have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
      intro hcon
      nlinarith [hcon]
    have hpoint : ∀ t ∈ Icc y₀ b, M / (1 - t ^ (2 : ℕ)) ≤ M / (1 - b ^ (2 : ℕ)) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
      have hw : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
      have hmono : 1 - b ^ (2 : ℕ) ≤ 1 - t ^ (2 : ℕ) := by nlinarith [ht.2, ht0.le]
      exact div_le_div_of_nonneg_left hM hbw hmono
    have hcontu : ContinuousOn (fun t : ℝ => M / (1 - t ^ (2 : ℕ))) (uIcc y₀ b) := by
      rwa [uIcc_of_le hy0b]
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy0b
      (hcontu.intervalIntegrable)
      ((continuous_const : Continuous fun _ : ℝ => M / (1 - b ^ (2 : ℕ))).intervalIntegrable y₀ b)
      hpoint
    calc (∫ t in y₀..b, M / (1 - t ^ (2 : ℕ)))
        ≤ ∫ _t in y₀..b, M / (1 - b ^ (2 : ℕ)) := hmono
      _ = M * (b - y₀) / (1 - b ^ (2 : ℕ)) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]
          field_simp
  have hexp : Real.exp (-(M * (b - y₀) / (1 - b ^ (2 : ℕ))))
      ≤ Real.exp (-∫ t in y₀..b, M / (1 - t ^ (2 : ℕ))) :=
    Real.exp_le_exp.2 (by linarith)
  have hΦy0 : 0 < Φ y₀ := hpos y₀ ⟨le_rfl, by linarith⟩
  have hprod : (Φ y₀ * Real.exp (-(M * (b - y₀) / (1 - b ^ (2 : ℕ))))) ^ (2 : ℕ)
      ≤ (Φ y₀ * Real.exp (-∫ t in y₀..b, M / (1 - t ^ (2 : ℕ)))) ^ (2 : ℕ) := by
    have h1 : Φ y₀ * Real.exp (-(M * (b - y₀) / (1 - b ^ (2 : ℕ))))
        ≤ Φ y₀ * Real.exp (-∫ t in y₀..b, M / (1 - t ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hexp hΦy0.le
    have h2 : (0 : ℝ) ≤ Φ y₀ * Real.exp (-(M * (b - y₀) / (1 - b ^ (2 : ℕ)))) := by positivity
    exact pow_le_pow_left₀ h2 h1 2
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

/-- **The aperture mass from below at every separation.**  Only the lifted barrier is used, so no
lower bound on `c·s` appears; the price is the additive `2 sqrt c` in the transport constant. -/
theorem prolate_aperture_mass_lower_shifted {c s y₀ b : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hy00 : 0 < y₀) (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0b : y₀ ≤ b) (hb1 : b < 1)
    (hpos : ∀ u ∈ Icc y₀ 1, 0 < Φ u) :
    (b - y₀) * (Φ y₀ *
        Real.exp (-((c * b + 12 + 2 * Real.sqrt c) * (b - y₀) / (1 - b ^ (2 : ℕ))))) ^ (2 : ℕ)
      ≤ ∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hb0 : (0 : ℝ) ≤ b := le_trans hy00.le hy0b
  have hMnn : (0 : ℝ) ≤ c * b + 12 + 2 * Real.sqrt c := by positivity
  have hflux : ∀ t ∈ Icc y₀ b,
      prolateFlux Φ t ^ (2 : ℕ) ≤ (c * b + 12 + 2 * Real.sqrt c) ^ (2 : ℕ) * Φ t ^ (2 : ℕ) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    have hst : s < t ^ (2 : ℕ) := by nlinarith [ht.1, hy00]
    have hpost : ∀ u ∈ Icc t 1, 0 < Φ u := fun u hu =>
      hpos u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hb := prolateFlux_sq_le_shiftedBand hc hs0 hs1 hsm heig hΦ1 ht0 ht1 hst hpost
    have hunif := one_sub_sq_mul_shiftedBand_barrier_le (c := c) (s := s) (t := t) (b := b)
      hc hs0 ht0.le ht.2 hb1
    have hnn : (0 : ℝ) ≤ (1 - t ^ (2 : ℕ)) * (prolateShiftedBarrier c s t + 6 / (1 - t)) := by
      have hw : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
      have hw1 : (0 : ℝ) < 1 - t := by linarith
      have hbar : (0 : ℝ) ≤ prolateShiftedBarrier c s t := by
        have h := prolateRadialBarrier_nonneg (c := c) (s := s) (y := t) hc.le ht0.le ht1
        have h2 : (0 : ℝ) ≤ 2 * Real.sqrt c := by positivity
        rw [prolateShiftedBarrier]; linarith
      have : (0 : ℝ) < 6 / (1 - t) := by positivity
      positivity
    have hsq : ((1 - t ^ (2 : ℕ)) * (prolateShiftedBarrier c s t + 6 / (1 - t))) ^ (2 : ℕ)
        ≤ (c * b + 12 + 2 * Real.sqrt c) ^ (2 : ℕ) := by
      nlinarith [hunif, hnn, hMnn]
    nlinarith [hb, hsq, sq_nonneg (Φ t)]
  have hwin := prolate_window_mass_lower_of_fluxConst hMnn hy00 hy0b hb1 hd1 hpos hflux
  have hcont : Continuous fun y : ℝ => Φ y ^ (2 : ℕ) := hsm.continuous.pow 2
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => Φ y ^ (2 : ℕ)) MeasureTheory.volume u v :=
    fun u v => hcont.intervalIntegrable u v
  have hy0ge : (-1 : ℝ) ≤ y₀ := by linarith
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun y : ℝ => Φ y ^ (2 : ℕ)) (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := y₀) (c := b)
    (hint _ _) (hint _ _)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun y : ℝ => Φ y ^ (2 : ℕ)) (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := b) (c := (1 : ℝ))
    (hint _ _) (hint _ _)
  have hleft : (0 : ℝ) ≤ ∫ y in (-1 : ℝ)..y₀, Φ y ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hy0ge fun _ _ => sq_nonneg _
  have hright : (0 : ℝ) ≤ ∫ y in b..(1 : ℝ), Φ y ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg hb1.le fun _ _ => sq_nonneg _
  linarith [hwin, hleft, hright, hadd1, hadd2]

end GaloisForLFunctions.RHTower

end
