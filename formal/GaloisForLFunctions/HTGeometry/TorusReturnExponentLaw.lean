import GaloisForLFunctions.HTGeometry.CompletedTimeSmallBall

/-!
# The local return exponent of a phase torus

A family of return targets squeezed between two balls whose radii are proportional to `ε` has Haar
measure of exact order `ε` to the torus dimension, with explicit two-sided constants coming from
the two proportionality factors.  Consequently the logarithmic return exponent

`log m (S ε) / log ε → dim`

is exactly the dimension of the presenting torus, with no rationality or embedding hypothesis on
the target family beyond the ball sandwich.
-/

open Filter MeasureTheory Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A two-sided power sandwich pins the logarithmic exponent. -/
theorem tendsto_log_div_log_of_power_sandwich {m : ℝ → ℝ} {c₁ c₂ : ℝ} {k : ℕ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c₁ * ε ^ k ≤ m ε)
    (hhigh : ∀ᶠ ε in 𝓝[>] (0 : ℝ), m ε ≤ c₂ * ε ^ k) :
    Tendsto (fun ε => Real.log (m ε) / Real.log ε) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
  have hmem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) 1 := eventually_of_mem hIoo fun _ h => h
  have hlogneg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log ε < 0 := by
    filter_upwards [hmem] with ε hε
    exact Real.log_neg hε.1 hε.2
  have hlogTop : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] (0 : ℝ)) atTop := by
    exact Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hquot : ∀ c : ℝ, Tendsto (fun ε : ℝ => Real.log c / Real.log ε + (k : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ))) := by
    intro c
    have hzero : Tendsto (fun ε : ℝ => (-Real.log c) / (-Real.log ε))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds.div_atTop hlogTop
    have hEq : (fun ε : ℝ => (-Real.log c) / (-Real.log ε))
        = fun ε : ℝ => Real.log c / Real.log ε := by
      funext ε
      rw [neg_div_neg_eq]
    rw [hEq] at hzero
    simpa using hzero.add (tendsto_const_nhds (x := (k : ℝ)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hquot c₂) (hquot c₁) ?_ ?_
  · filter_upwards [hmem, hlogneg, hlow, hhigh] with ε hε hlog hl hh
    have hpow : (0 : ℝ) < ε ^ k := pow_pos hε.1 k
    have hmpos : 0 < m ε := lt_of_lt_of_le (by positivity) hl
    have hupper : Real.log (m ε) ≤ Real.log c₂ + (k : ℝ) * Real.log ε := by
      calc Real.log (m ε) ≤ Real.log (c₂ * ε ^ k) := Real.log_le_log hmpos hh
        _ = Real.log c₂ + (k : ℝ) * Real.log ε := by
            rw [Real.log_mul (ne_of_gt hc₂) (ne_of_gt hpow), Real.log_pow]
    rw [div_add' _ _ _ (ne_of_lt hlog), div_le_div_right_of_neg hlog]
    linarith
  · filter_upwards [hmem, hlogneg, hlow] with ε hε hlog hl
    have hpow : (0 : ℝ) < ε ^ k := pow_pos hε.1 k
    have hlower : Real.log c₁ + (k : ℝ) * Real.log ε ≤ Real.log (m ε) := by
      calc Real.log c₁ + (k : ℝ) * Real.log ε
          = Real.log (c₁ * ε ^ k) := by
            rw [Real.log_mul (ne_of_gt hc₁) (ne_of_gt hpow), Real.log_pow]
        _ ≤ Real.log (m ε) := Real.log_le_log (by positivity) hl
    rw [div_add' _ _ _ (ne_of_lt hlog), div_le_div_right_of_neg hlog]
    linarith

variable {k : Type*} [Fintype k]

/-- Haar measure of a small ball in a phase torus, as a real number. -/
theorem toReal_finiteTorusHaar_ball (x : UnitAddTorus k) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) :
    ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (ball x ε)).toReal
      = (2 * ε) ^ Fintype.card k := by
  rw [finiteTorusHaarProbabilityMeasure_ball x hε hε', ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]

/-- **Local return-volume law.**  A target family squeezed between balls of radii `a * ε` and
`b * ε` has Haar measure between `(2a)^dim ε^dim` and `(2b)^dim ε^dim` for all small `ε`. -/
theorem finiteTorusHaar_return_sandwich (x : UnitAddTorus k) (S : ℝ → Set (UnitAddTorus k))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h₁ : ∀ ε, 0 < ε → ball x (a * ε) ⊆ S ε)
    (h₂ : ∀ ε, 0 < ε → S ε ⊆ ball x (b * ε)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (2 * a) ^ Fintype.card k * ε ^ Fintype.card k ≤
          ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (S ε)).toReal ∧
        ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (S ε)).toReal ≤
          (2 * b) ^ Fintype.card k * ε ^ Fintype.card k := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hIoo : Set.Ioo (0 : ℝ) (1 / (2 * b)) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [eventually_of_mem hIoo fun _ h => h] with ε hε
  have hεpos : 0 < ε := hε.1
  have hbε : b * ε ≤ 1 / 2 := by
    have := hε.2
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have haε : a * ε ≤ 1 / 2 := le_trans (by nlinarith) hbε
  have hlow := measure_mono
    (μ := (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))) (h₁ ε hεpos)
  have hhigh := measure_mono
    (μ := (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))) (h₂ ε hεpos)
  have hfinS : (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (S ε) ≠ ⊤ :=
    measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _
  have hfinB : ∀ r : ℝ,
      (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (ball x r) ≠ ⊤ :=
    fun _ => measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _
  constructor
  · have := (ENNReal.toReal_le_toReal (hfinB (a * ε)) hfinS).mpr hlow
    rw [toReal_finiteTorusHaar_ball x (by positivity) haε] at this
    calc (2 * a) ^ Fintype.card k * ε ^ Fintype.card k
        = (2 * (a * ε)) ^ Fintype.card k := by rw [← mul_pow]; ring_nf
      _ ≤ _ := this
  · have := (ENNReal.toReal_le_toReal hfinS (hfinB (b * ε))).mpr hhigh
    rw [toReal_finiteTorusHaar_ball x (by positivity) hbε] at this
    calc ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (S ε)).toReal
        ≤ (2 * (b * ε)) ^ Fintype.card k := this
      _ = (2 * b) ^ Fintype.card k * ε ^ Fintype.card k := by rw [← mul_pow]; ring_nf

/-- **Local return exponent of a phase torus.**  For a target family squeezed between balls of
radii proportional to `ε`, the logarithmic Haar return exponent is exactly the torus dimension. -/
theorem tendsto_log_finiteTorusHaar_return_div_log (x : UnitAddTorus k)
    (S : ℝ → Set (UnitAddTorus k)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h₁ : ∀ ε, 0 < ε → ball x (a * ε) ⊆ S ε)
    (h₂ : ∀ ε, 0 < ε → S ε ⊆ ball x (b * ε)) :
    Tendsto (fun ε => Real.log
        ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) (S ε)).toReal /
      Real.log ε) (𝓝[>] 0) (𝓝 (Fintype.card k : ℝ)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsand := finiteTorusHaar_return_sandwich x S ha hab h₁ h₂
  refine tendsto_log_div_log_of_power_sandwich (c₁ := (2 * a) ^ Fintype.card k)
    (c₂ := (2 * b) ^ Fintype.card k) (by positivity) (by positivity) ?_ ?_
  · filter_upwards [hsand] with ε hε
    exact hε.1
  · filter_upwards [hsand] with ε hε
    exact hε.2

end

end GaloisForLFunctions.HTGeometry
