import GaloisForLFunctions.HTGeometry.SturmAmplitudeEnvelope
import GaloisForLFunctions.RHTower.BandBarrierRatio

/-!
# Transporting the prolate amplitude across the forbidden band

The angular prolate equation is `((1 − y²)Phi')' + c²(s − y²)Phi = 0`.  On the band `y² > s` the
potential is negative, and the scale

```text
K(y) = −Q(y) p(y) = c² (y² − s)(1 − y²)
```

is positive.  At that scale the amplitude `G = Phi² + ((1−y²)Phi')²/K` has

```text
1/p − Q/K = 2/(1 − y²) ,      sqrt K · (2/(1 − y²)) = 2 c sqrt((y² − s)/(1 − y²)) = 2 c P(y) ,
```

so the amplitude's logarithmic derivative is bounded by *exactly twice the WKB rate* plus the
logarithmic variation of the scale, and the latter is a sum of two logarithms:

```text
|K'|/K  ≤  2y/(y² − s) + 2y/(1 − y²) .
```

Integrating, the transport across any window of the band costs the sharp exponential `e^{2cΞ}` times
the *ratio of the scales* — one power of `(α²−s)(1−y₀²) / ((y₀²−s)(1−α²))`, not a power of the
exponential.  This is what lets an endpoint bound reach the turning layer without the loss the crude
radial barrier incurs.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The band scale `−Q p` of the angular prolate equation. -/
def prolateBandScale (c s : ℝ) (y : ℝ) : ℝ := c ^ (2 : ℕ) * (y ^ (2 : ℕ) - s) * (1 - y ^ (2 : ℕ))

/-- Its derivative. -/
def prolateBandScaleDeriv (c s : ℝ) (y : ℝ) : ℝ :=
  c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ)) + (y ^ (2 : ℕ) - s) * (-(2 * y)))

/-- The prolate amplitude at the band scale. -/
def prolateBandAmplitude (c s : ℝ) (Φ DΦ : ℝ → ℝ) (y : ℝ) : ℝ :=
  sturmAmplitudeVar (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (prolateBandScale c s) y

/-- The majorant of the amplitude's logarithmic derivative: twice the WKB rate plus the two
logarithmic derivatives of the scale. -/
def prolateBandMajorant (c s : ℝ) (y : ℝ) : ℝ :=
  2 * c * prolateWKBProfile s y + 2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))

theorem hasDerivAt_prolateBandScale (c s y : ℝ) :
    HasDerivAt (prolateBandScale c s) (prolateBandScaleDeriv c s y) y := by
  have h1 : HasDerivAt (fun t : ℝ => c ^ (2 : ℕ) * (t ^ (2 : ℕ) - s)) (c ^ (2 : ℕ) * (2 * y)) y := by
    have := ((hasDerivAt_pow 2 y).sub_const s).const_mul (c ^ (2 : ℕ))
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ (2 : ℕ)) (-(2 * y)) y := by
    have := (hasDerivAt_pow 2 y).const_sub 1
    refine this.congr_deriv ?_
    push_cast
    ring
  have h := h1.mul h2
  refine h.congr_deriv ?_
  rw [prolateBandScaleDeriv]
  ring

theorem prolateBandScale_pos {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    0 < prolateBandScale c s y := by
  rw [prolateBandScale]
  have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  positivity

/-! ## The pointwise majorant -/

/-- At the band scale the drift term is exactly `2/(1 − y²)`. -/
theorem prolateBand_drift_eq {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    1 / (1 - y ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) / prolateBandScale c s y = 2 / (1 - y ^ (2 : ℕ)) := by
  have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  rw [prolateBandScale]
  field_simp
  ring

/-- The scaled WKB rate is exactly twice the profile. -/
theorem sqrt_prolateBandScale_mul {c s y : ℝ} (hc : 0 < c) (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    Real.sqrt (prolateBandScale c s y) * (2 / (1 - y ^ (2 : ℕ))) = 2 * c * prolateWKBProfile s y := by
  have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  have hK : prolateBandScale c s y = c ^ (2 : ℕ) * ((y ^ (2 : ℕ) - s) * (1 - y ^ (2 : ℕ))) := by
    rw [prolateBandScale]; ring
  rw [hK, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, prolateWKBProfile]
  have hsplit : Real.sqrt ((y ^ (2 : ℕ) - s) * (1 - y ^ (2 : ℕ)))
      = Real.sqrt (y ^ (2 : ℕ) - s) * Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_mul h1.le _
  have hdiv : Real.sqrt ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))
      = Real.sqrt (y ^ (2 : ℕ) - s) / Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_div' _ h2.le
  have hs2 : Real.sqrt (1 - y ^ (2 : ℕ)) * Real.sqrt (1 - y ^ (2 : ℕ)) = 1 - y ^ (2 : ℕ) :=
    Real.mul_self_sqrt h2.le
  have hs2pos : (0 : ℝ) < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 h2
  rw [hsplit, hdiv]
  field_simp
  nlinarith [hs2, hs2pos]

/-- The logarithmic variation of the scale splits into two elementary logarithmic derivatives. -/
theorem abs_prolateBandScaleDeriv_div_le {c s y : ℝ} (hc : 0 < c) (hy0 : 0 ≤ y)
    (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    |prolateBandScaleDeriv c s y| / prolateBandScale c s y
      ≤ 2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ)) := by
  have h1 : (0 : ℝ) < y ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have hKpos : 0 < prolateBandScale c s y := prolateBandScale_pos hc hsy hy
  have habs : |prolateBandScaleDeriv c s y|
      ≤ c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ)) + (y ^ (2 : ℕ) - s) * (2 * y)) := by
    rw [prolateBandScaleDeriv]
    have hval : c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ)) + (y ^ (2 : ℕ) - s) * (-(2 * y)))
        = c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ))) - c ^ (2 : ℕ) * ((y ^ (2 : ℕ) - s) * (2 * y)) := by ring
    rw [hval]
    have hA : (0 : ℝ) ≤ c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ))) := by positivity
    have hB : (0 : ℝ) ≤ c ^ (2 : ℕ) * ((y ^ (2 : ℕ) - s) * (2 * y)) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hstep : |prolateBandScaleDeriv c s y| / prolateBandScale c s y
      ≤ (c ^ (2 : ℕ) * (2 * y * (1 - y ^ (2 : ℕ)) + (y ^ (2 : ℕ) - s) * (2 * y))) / prolateBandScale c s y := by
    gcongr
  refine le_trans hstep (le_of_eq ?_)
  rw [prolateBandScale]
  field_simp

/-- **The pointwise bound on the amplitude's logarithmic derivative.** -/
theorem prolateBand_majorant_bound {c s y : ℝ} (hc : 0 < c) (hy0 : 0 ≤ y)
    (hsy : s < y ^ (2 : ℕ)) (hy : y ^ (2 : ℕ) < 1) :
    Real.sqrt (prolateBandScale c s y)
        * |1 / (1 - y ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) / prolateBandScale c s y|
      + |prolateBandScaleDeriv c s y| / prolateBandScale c s y
      ≤ prolateBandMajorant c s y := by
  have h2 : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by linarith
  have hdrift := prolateBand_drift_eq hc hsy hy
  have habs : |1 / (1 - y ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) / prolateBandScale c s y|
      = 2 / (1 - y ^ (2 : ℕ)) := by
    rw [hdrift, abs_of_pos (by positivity)]
  rw [habs, sqrt_prolateBandScale_mul hc hsy hy, prolateBandMajorant]
  have := abs_prolateBandScaleDeriv_div_le hc hy0 hsy hy
  linarith

/-! ## The accumulated majorant -/

theorem continuousOn_prolateBandMajorant {c s y₀ α : ℝ} (hy0 : 0 ≤ y₀) (hsy0 : s < y₀ ^ (2 : ℕ))
    (hα1 : α < 1) :
    ContinuousOn (prolateBandMajorant c s) (Icc y₀ α) := by
  have hmem : ∀ y ∈ Icc y₀ α, s < y ^ (2 : ℕ) ∧ y ^ (2 : ℕ) < 1 := by
    intro y hy
    have hy0' : 0 ≤ y := le_trans hy0 hy.1
    have hsq : y₀ ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hy.1, hy0]
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hα1
    exact ⟨by linarith, by nlinarith⟩
  have hprof : ContinuousOn (prolateWKBProfile s) (Icc y₀ α) := by
    show ContinuousOn (fun y : ℝ => Real.sqrt ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))) (Icc y₀ α)
    refine Real.continuous_sqrt.comp_continuousOn
      (ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_)
    have := (hmem y hy).2
    intro hcon
    linarith
  have h1 : ContinuousOn (fun y : ℝ => 2 * y / (y ^ (2 : ℕ) - s)) (Icc y₀ α) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
    have := (hmem y hy).1
    intro hcon
    linarith [hcon]
  have h2 : ContinuousOn (fun y : ℝ => 2 * y / (1 - y ^ (2 : ℕ))) (Icc y₀ α) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
    have := (hmem y hy).2
    intro hcon
    linarith [hcon]
  show ContinuousOn (fun y : ℝ =>
    2 * c * prolateWKBProfile s y + 2 * y / (y ^ (2 : ℕ) - s) + 2 * y / (1 - y ^ (2 : ℕ))) (Icc y₀ α)
  exact ((continuousOn_const.mul hprof).add h1).add h2

/-- **The accumulated majorant is the sharp action plus the logarithm of the scale ratio.** -/
theorem integral_prolateBandMajorant {c s y₀ α : ℝ} (hy0 : 0 ≤ y₀)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0α : y₀ ≤ α) (hα1 : α < 1) :
    (∫ t in y₀..α, prolateBandMajorant c s t)
      = 2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
        + (Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s))
        + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ))) := by
  have hmem : ∀ y ∈ uIcc y₀ α, s < y ^ (2 : ℕ) ∧ y ^ (2 : ℕ) < 1 ∧ 0 ≤ y := by
    intro y hy
    rw [uIcc_of_le hy0α] at hy
    have hy0' : 0 ≤ y := le_trans hy0 hy.1
    have hsq : y₀ ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hy.1, hy0]
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hα1
    exact ⟨by linarith, by nlinarith, hy0'⟩
  have hcont := continuousOn_prolateBandMajorant (c := c) hy0 hsy0 hα1
  -- the three pieces
  have hprofc : ContinuousOn (fun t : ℝ => 2 * c * prolateWKBProfile s t) (uIcc y₀ α) := by
    rw [uIcc_of_le hy0α]
    have hprof : ContinuousOn (prolateWKBProfile s) (Icc y₀ α) := by
      show ContinuousOn (fun y : ℝ => Real.sqrt ((y ^ (2 : ℕ) - s) / (1 - y ^ (2 : ℕ)))) (Icc y₀ α)
      refine Real.continuous_sqrt.comp_continuousOn
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_)
      have h := (hmem y (by rw [uIcc_of_le hy0α]; exact hy)).2.1
      intro hcon
      linarith
    exact continuousOn_const.mul hprof
  have h1c : ContinuousOn (fun t : ℝ => 2 * t / (t ^ (2 : ℕ) - s)) (uIcc y₀ α) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
    have h := (hmem y hy).1
    intro hcon
    linarith [hcon]
  have h2c : ContinuousOn (fun t : ℝ => 2 * t / (1 - t ^ (2 : ℕ))) (uIcc y₀ α) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_
    have h := (hmem y hy).2.1
    intro hcon
    linarith [hcon]
  have e1 : (∫ t in y₀..α, (2 * c * prolateWKBProfile s t + 2 * t / (t ^ (2 : ℕ) - s)))
      = (∫ t in y₀..α, 2 * c * prolateWKBProfile s t) + ∫ t in y₀..α, 2 * t / (t ^ (2 : ℕ) - s) :=
    intervalIntegral.integral_add hprofc.intervalIntegrable h1c.intervalIntegrable
  have e2 : (∫ t in y₀..α, ((2 * c * prolateWKBProfile s t + 2 * t / (t ^ (2 : ℕ) - s))
        + 2 * t / (1 - t ^ (2 : ℕ))))
      = (∫ t in y₀..α, (2 * c * prolateWKBProfile s t + 2 * t / (t ^ (2 : ℕ) - s)))
        + ∫ t in y₀..α, 2 * t / (1 - t ^ (2 : ℕ)) :=
    intervalIntegral.integral_add ((hprofc.add h1c).intervalIntegrable) h2c.intervalIntegrable
  have hsplit : (∫ t in y₀..α, prolateBandMajorant c s t)
      = (∫ t in y₀..α, 2 * c * prolateWKBProfile s t)
        + (∫ t in y₀..α, 2 * t / (t ^ (2 : ℕ) - s))
        + ∫ t in y₀..α, 2 * t / (1 - t ^ (2 : ℕ)) := by
    show (∫ t in y₀..α, ((2 * c * prolateWKBProfile s t + 2 * t / (t ^ (2 : ℕ) - s))
        + 2 * t / (1 - t ^ (2 : ℕ))))
      = (∫ t in y₀..α, 2 * c * prolateWKBProfile s t)
        + (∫ t in y₀..α, 2 * t / (t ^ (2 : ℕ) - s))
        + ∫ t in y₀..α, 2 * t / (1 - t ^ (2 : ℕ))
    rw [e2, e1]
  rw [hsplit]
  congr 1
  · congr 1
    · rw [intervalIntegral.integral_const_mul,
        ← bandEndpointPhase_sub_eq_integral hy0 hy0α hα1 hsy0.le]
    · -- the first logarithm
      have hprim : ∀ t ∈ uIcc y₀ α,
          HasDerivAt (fun z : ℝ => Real.log (z ^ (2 : ℕ) - s)) (2 * t / (t ^ (2 : ℕ) - s)) t := by
        intro t ht
        have hne : t ^ (2 : ℕ) - s ≠ 0 := by
          have := (hmem t ht).1
          intro hcon
          linarith [hcon]
        have hd : HasDerivAt (fun z : ℝ => z ^ (2 : ℕ) - s) (2 * t) t := by
          have := (hasDerivAt_pow 2 t).sub_const s
          refine this.congr_deriv ?_
          push_cast
          ring
        exact hd.log hne
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim h1c.intervalIntegrable]
  · -- the second logarithm
    have hprim : ∀ t ∈ uIcc y₀ α,
        HasDerivAt (fun z : ℝ => -Real.log (1 - z ^ (2 : ℕ))) (2 * t / (1 - t ^ (2 : ℕ))) t := by
      intro t ht
      have hne : (1 : ℝ) - t ^ (2 : ℕ) ≠ 0 := by
        have := (hmem t ht).2.1
        intro hcon
        linarith [hcon]
      have hd : HasDerivAt (fun z : ℝ => 1 - z ^ (2 : ℕ)) (-(2 * t)) t := by
        have := (hasDerivAt_pow 2 t).const_sub 1
        refine this.congr_deriv ?_
        push_cast
        ring
      have h := (hd.log hne).neg
      refine h.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim h2c.intervalIntegrable]
    ring

/-! ## The transport -/

/-- **The amplitude transport across a window of the forbidden band.**  The cost is the sharp
exponential of twice the WKB action, times the ratio of the band scales. -/
theorem prolateBand_amplitude_le {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hy0 : 0 ≤ y₀) (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (hΦ : ∀ y ∈ Icc y₀ α, HasDerivAt Φ (DΦ y) y)
    (hflux : ∀ y ∈ Icc y₀ α, HasDerivAt (fun t => (1 - t ^ (2 : ℕ)) * DΦ t)
      (-(c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) * Φ y)) y)
    (hpos : ∀ y ∈ Icc y₀ α, Φ y ≠ 0) :
    prolateBandAmplitude c s Φ DΦ y₀
      ≤ prolateBandAmplitude c s Φ DΦ α
        * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
            + (Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s))
            + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ)))) := by
  have hmem : ∀ y ∈ Icc y₀ α, s < y ^ (2 : ℕ) ∧ y ^ (2 : ℕ) < 1 ∧ 0 ≤ y := by
    intro y hy
    have hy0' : 0 ≤ y := le_trans hy0 hy.1
    have hsq : y₀ ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith [hy.1, hy0]
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 hα1
    exact ⟨by linarith, by nlinarith, hy0'⟩
  have hKpos : ∀ y ∈ Icc y₀ α, 0 < prolateBandScale c s y := fun y hy =>
    prolateBandScale_pos hc (hmem y hy).1 (hmem y hy).2.1
  have hp : ∀ y ∈ Icc y₀ α, (1 : ℝ) - y ^ (2 : ℕ) ≠ 0 := by
    intro y hy
    have := (hmem y hy).2.1
    intro hcon
    linarith [hcon]
  have hGpos : ∀ y ∈ Icc y₀ α, 0 < prolateBandAmplitude c s Φ DΦ y := by
    intro y hy
    rw [prolateBandAmplitude, sturmAmplitudeVar]
    have h1 : 0 < Φ y ^ (2 : ℕ) := by
      have := hpos y hy
      positivity
    have h2 : 0 ≤ ((1 - y ^ (2 : ℕ)) * DΦ y) ^ (2 : ℕ) / prolateBandScale c s y := by
      have := (hKpos y hy).le
      positivity
    linarith
  have hbound : ∀ y ∈ Icc y₀ α,
      Real.sqrt (prolateBandScale c s y)
          * |1 / (1 - y ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - y ^ (2 : ℕ)) / prolateBandScale c s y|
        + |prolateBandScaleDeriv c s y| / prolateBandScale c s y
        ≤ prolateBandMajorant c s y := fun y hy =>
    prolateBand_majorant_bound hc (hmem y hy).2.2 (hmem y hy).1 (hmem y hy).2.1
  have henv := sturmAmplitudeVar_envelope (p := fun t : ℝ => 1 - t ^ (2 : ℕ))
    (Q := fun t : ℝ => c ^ (2 : ℕ) * (s - t ^ (2 : ℕ))) (R := Φ) (DR := DΦ)
    (K := prolateBandScale c s) (DK := prolateBandScaleDeriv c s)
    (m := prolateBandMajorant c s) hy0α hKpos hp hΦ hflux
    (fun y _ => hasDerivAt_prolateBandScale c s y) hGpos
    (continuousOn_prolateBandMajorant hy0 hsy0 hα1) hbound
  rw [← integral_prolateBandMajorant (c := c) hy0 hsy0 hy0α hα1]
  exact henv.1

end GaloisForLFunctions.RHTower

end
