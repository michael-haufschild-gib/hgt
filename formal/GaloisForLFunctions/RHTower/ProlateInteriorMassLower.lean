import GaloisForLFunctions.RHTower.ProlateBandAmplitudeAnchor
import GaloisForLFunctions.RHTower.ProlateBandFluxEnergy

/-!
# The interior mass from below, at the matching point

The flux `(1 − y²)Phi'` of a band mode is bounded by the value there: the two barriers already
available trap the logarithmic derivative, and multiplying by `1 − y²` gives

```text
(1 − t²)|Phi'/Phi|  ≤  c sqrt(1−s) t sqrt(1 − t²) + 6(1 + t)  ≤  c b + 12       (t ≤ b) .
```

Feeding that constant into the corpus's flux-driven mass bound produces, for any window
`[y₀, b]` inside the band,

```text
(b − y₀) · (Phi(y₀) · exp(−(c b + 12)(b − y₀)/(1 − b²)))²  ≤  ∫_{y₀}^{b} Phi² .
```

At the standard matching point `y₀ = 2 sqrt s` the barrier constant is `c b + 12 = O(sqrt c)` for a
fixed mode, so a window of width `1/(c b + 12)` costs a bounded exponential and contributes
`Phi(y₀)²/(c b + 12)` — the true order of the aperture mass.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The flux of a band mode is bounded by the barrier times the value.** -/
theorem prolateFlux_sq_le_band {c s t : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1) (ht0 : 0 < t) (ht1 : t < 1) (hst : s < t ^ 2)
    (hpos : ∀ u ∈ Icc t 1, 0 < Φ u) :
    prolateFlux Φ t ^ 2
      ≤ ((1 - t ^ 2) * (prolateRadialBarrier c s t + 6 / (1 - t))) ^ 2 * Φ t ^ 2 := by
  have hB := abs_prolateLogDeriv_le_band hc hs0 hs1 hcs hsm heig hΦ1 ht0 ht1 hst hpos
  have hΦt : 0 < Φ t := hpos t ⟨le_rfl, ht1.le⟩
  have hderiv : |deriv Φ t| ≤ (prolateRadialBarrier c s t + 6 / (1 - t)) * Φ t := by
    rw [prolateLogDeriv, abs_neg, abs_div, abs_of_pos hΦt, div_le_iff₀ hΦt] at hB
    exact hB
  have hBnn : (0 : ℝ) ≤ (prolateRadialBarrier c s t + 6 / (1 - t)) * Φ t :=
    le_trans (abs_nonneg _) hderiv
  have hsq : deriv Φ t ^ 2 ≤ ((prolateRadialBarrier c s t + 6 / (1 - t)) * Φ t) ^ 2 := by
    have := sq_abs (deriv Φ t)
    nlinarith [hderiv, abs_nonneg (deriv Φ t), this]
  rw [prolateFlux, mul_pow]
  nlinarith [hsq, sq_nonneg (1 - t ^ 2), mul_pow (prolateRadialBarrier c s t + 6 / (1 - t)) (Φ t) 2]

/-- The uniform barrier constant on a window of the band. -/
theorem one_sub_sq_mul_band_barrier_le {c s t b : ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (htb : t ≤ b) (hb1 : b < 1) :
    (1 - t ^ 2) * (prolateRadialBarrier c s t + 6 / (1 - t)) ≤ c * b + 12 := by
  have ht1 : t < 1 := lt_of_le_of_lt htb hb1
  have hw : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hw1 : (0 : ℝ) < 1 - t := by linarith
  have hsqrtw : (0 : ℝ) < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hw
  have hsqrtsnn : (0 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hsqrts : Real.sqrt (1 - s) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) - s ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  -- the barrier part
  have hbar : (1 - t ^ 2) * prolateRadialBarrier c s t ≤ c * b := by
    obtain ⟨S, hS0, hS2, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S ^ 2 = 1 - t ^ 2 ∧
        Real.sqrt (1 - t ^ 2) = S := ⟨Real.sqrt (1 - t ^ 2), hsqrtw, Real.sq_sqrt hw.le, rfl⟩
    have hS1 : S ≤ 1 := by nlinarith [hS2, hS0, sq_nonneg t]
    rw [prolateRadialBarrier, hSeq, ← hS2]
    have hval : S ^ 2 * (c * Real.sqrt (1 - s) * t / S) = c * Real.sqrt (1 - s) * t * S := by
      field_simp
    rw [hval]
    have h1 : c * Real.sqrt (1 - s) * t * S ≤ c * t := by
      nlinarith [hc.le, ht0, hsqrtsnn, hS0.le, hsqrts, hS1,
        mul_nonneg (mul_nonneg hc.le hsqrtsnn) ht0, mul_nonneg hc.le ht0]
    nlinarith [h1, hc.le, htb]
  -- the correction part
  have hcorr : (1 - t ^ 2) * (6 / (1 - t)) ≤ 12 := by
    have hval : (1 - t ^ 2) * (6 / (1 - t)) = 6 * (1 + t) := by
      field_simp
      ring
    rw [hval]
    linarith
  have hsplit : (1 - t ^ 2) * (prolateRadialBarrier c s t + 6 / (1 - t))
      = (1 - t ^ 2) * prolateRadialBarrier c s t + (1 - t ^ 2) * (6 / (1 - t)) := by ring
  rw [hsplit]
  linarith

/-- **The interior mass from below on a band window.** -/
theorem prolate_window_mass_lower {c s y₀ b : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1) (hy00 : 0 < y₀) (hsy0 : s < y₀ ^ 2) (hy0b : y₀ ≤ b) (hb1 : b < 1)
    (hpos : ∀ u ∈ Icc y₀ 1, 0 < Φ u) :
    (b - y₀) * (Φ y₀ * Real.exp (-((c * b + 12) * (b - y₀) / (1 - b ^ 2)))) ^ 2
      ≤ ∫ t in y₀..b, Φ t ^ 2 := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hKnn : (0 : ℝ) ≤ (c * b + 12) ^ 2 := sq_nonneg _
  have hKsqrt : Real.sqrt ((c * b + 12) ^ 2) = c * b + 12 := by
    refine Real.sqrt_sq ?_
    have : (0 : ℝ) ≤ c * b := by
      have : (0 : ℝ) ≤ b := le_trans hy00.le hy0b
      positivity
    linarith
  have hposwin : ∀ t ∈ Icc y₀ b, 0 < Φ t := fun t ht =>
    hpos t ⟨ht.1, le_trans ht.2 hb1.le⟩
  have hflux : ∀ t ∈ Icc y₀ b, prolateFlux Φ t ^ 2 ≤ (c * b + 12) ^ 2 * Φ t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    have hst : s < t ^ 2 := by nlinarith [ht.1, hy00]
    have hpost : ∀ u ∈ Icc t 1, 0 < Φ u := fun u hu =>
      hpos u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hb := prolateFlux_sq_le_band hc hs0 hs1 hcs hsm heig hΦ1 ht0 ht1 hst hpost
    have hunif := one_sub_sq_mul_band_barrier_le (c := c) (s := s) (t := t) (b := b)
      hc hs0 ht0.le ht.2 hb1
    have hnn : (0 : ℝ) ≤ (1 - t ^ 2) * (prolateRadialBarrier c s t + 6 / (1 - t)) := by
      have hw : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
      have hw1 : (0 : ℝ) < 1 - t := by linarith
      have hbar : (0 : ℝ) ≤ prolateRadialBarrier c s t := by
        rw [prolateRadialBarrier]
        have h3 : (0 : ℝ) < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hw
        have h4 : (0 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
        positivity
      have : (0 : ℝ) < 6 / (1 - t) := by positivity
      positivity
    have hsq : ((1 - t ^ 2) * (prolateRadialBarrier c s t + 6 / (1 - t))) ^ 2
        ≤ (c * b + 12) ^ 2 := by
      have hnn2 : (0 : ℝ) ≤ c * b + 12 := le_trans hnn hunif
      nlinarith [hunif, hnn, hnn2]
    nlinarith [hb, hsq, sq_nonneg (Φ t)]
  have hmain := mass_lower_of_fluxBound (Φ := Φ) (K := (c * b + 12) ^ 2) hKnn hy0b hb1
    (by linarith) hd1 hposwin hflux
  rw [hKsqrt] at hmain
  refine le_trans ?_ hmain
  have hJ : (∫ t in y₀..b, (c * b + 12) / (1 - t ^ 2))
      ≤ (c * b + 12) * (b - y₀) / (1 - b ^ 2) := by
    have hbw : (0 : ℝ) < 1 - b ^ 2 := by
      have : (0 : ℝ) ≤ b := le_trans hy00.le hy0b
      nlinarith
    have hnn2 : (0 : ℝ) ≤ c * b + 12 := by
      have : (0 : ℝ) ≤ c * b := by
        have : (0 : ℝ) ≤ b := le_trans hy00.le hy0b
        positivity
      linarith
    have hcont : ContinuousOn (fun t : ℝ => (c * b + 12) / (1 - t ^ 2)) (Icc y₀ b) := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
      have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
      intro hcon
      nlinarith [hcon]
    have hpoint : ∀ t ∈ Icc y₀ b, (c * b + 12) / (1 - t ^ 2) ≤ (c * b + 12) / (1 - b ^ 2) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hy00 ht.1
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
      have hw : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
      have hmono : 1 - b ^ 2 ≤ 1 - t ^ 2 := by nlinarith [ht.2, ht0.le]
      exact div_le_div_of_nonneg_left hnn2 hbw hmono
    have hcontu : ContinuousOn (fun t : ℝ => (c * b + 12) / (1 - t ^ 2)) (uIcc y₀ b) := by
      rwa [uIcc_of_le hy0b]
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy0b
      (hcontu.intervalIntegrable)
      ((continuous_const : Continuous fun _ : ℝ => (c * b + 12) / (1 - b ^ 2)).intervalIntegrable
        y₀ b) hpoint
    calc (∫ t in y₀..b, (c * b + 12) / (1 - t ^ 2))
        ≤ ∫ _t in y₀..b, (c * b + 12) / (1 - b ^ 2) := hmono
      _ = (c * b + 12) * (b - y₀) / (1 - b ^ 2) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]
          field_simp
  have hexp : Real.exp (-((c * b + 12) * (b - y₀) / (1 - b ^ 2)))
      ≤ Real.exp (-∫ t in y₀..b, (c * b + 12) / (1 - t ^ 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have hΦy0 : 0 < Φ y₀ := hpos y₀ ⟨le_rfl, by linarith⟩
  have hprod : (Φ y₀ * Real.exp (-((c * b + 12) * (b - y₀) / (1 - b ^ 2)))) ^ 2
      ≤ (Φ y₀ * Real.exp (-∫ t in y₀..b, (c * b + 12) / (1 - t ^ 2))) ^ 2 := by
    have h1 : Φ y₀ * Real.exp (-((c * b + 12) * (b - y₀) / (1 - b ^ 2)))
        ≤ Φ y₀ * Real.exp (-∫ t in y₀..b, (c * b + 12) / (1 - t ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp hΦy0.le
    have h2 : (0 : ℝ) ≤ Φ y₀ * Real.exp (-((c * b + 12) * (b - y₀) / (1 - b ^ 2))) := by
      positivity
    exact pow_le_pow_left₀ h2 h1 2
  exact mul_le_mul_of_nonneg_left hprod (by linarith)

end GaloisForLFunctions.RHTower

end
