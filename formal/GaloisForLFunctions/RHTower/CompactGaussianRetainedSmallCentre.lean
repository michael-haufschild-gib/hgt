import GaloisForLFunctions.RHTower.CompactGaussianRetainedEnvelope

open Complex Filter Topology Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- A measurable retained-coordinate event controlling the entire compact background. -/
def compactGaussianRetainedSmallCentreEvent (c : ℂ) (r R : ℝ) (N L : ℕ)
    (S : Finset ℕ) (ε : ℝ) : Set Omega :=
  {ω | compactGaussianRetainedDiscEnvelope c r R N L S ω < ENNReal.ofReal ε}

theorem measurableSet_compactGaussianRetainedSmallCentreEvent (c : ℂ) (r R : ℝ)
    {N : ℕ} (hN : 0 < N) (L : ℕ) (S : Finset ℕ) (ε : ℝ) :
    MeasurableSet (compactGaussianRetainedSmallCentreEvent c r R N L S ε) :=
  measurableSet_lt (measurable_compactGaussianRetainedDiscEnvelope c r R hN L S) measurable_const

/-- Small-centre selection depends only on the retained coordinates. -/
theorem compactGaussianRetainedSmallCentreEvent_congr_retained (c : ℂ) (r R : ℝ)
    (N L : ℕ) (S : Finset ℕ) (ε : ℝ) {ω ξ : Omega} (h : ∀ p ∈ S, ω p = ξ p) :
    ω ∈ compactGaussianRetainedSmallCentreEvent c r R N L S ε ↔
      ξ ∈ compactGaussianRetainedSmallCentreEvent c r R N L S ε := by
  simp only [compactGaussianRetainedSmallCentreEvent, mem_setOf_eq,
    compactGaussianRetainedDiscEnvelope_congr_retained c r R N L S h]

/-- Every selected phase has the prescribed small background on the whole disc. -/
theorem norm_compactGaussianRetainedCarrier_lt_of_mem_smallCentre
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) {N : ℕ} (hN : 0 < N)
    (L : ℕ) (S : Finset ℕ) {ε : ℝ} (hε : 0 < ε) {ω : Omega}
    (hω : ω ∈ compactGaussianRetainedSmallCentreEvent c r R N L S ε)
    {s : ℂ} (hs : s ∈ closedBall c r) : ‖compactGaussianRetainedCarrier s N L S ω‖ < ε :=
  (ENNReal.ofReal_lt_ofReal_iff hε).mp
    ((norm_le_compactGaussianRetainedDiscEnvelope c hr hrR hN L S ω hs).trans_lt hω)

/-- The discarded original mass tends to zero uniformly over every retained set
and independent polynomial cutoff. -/
theorem eventually_measureReal_compactGaussianRetainedSmallCentre_compl_le
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ,
      steinhausMeasure.real (compactGaussianRetainedSmallCentreEvent c r R N L S ε)ᶜ ≤ δ := by
  filter_upwards [eventually_lintegral_compactGaussianRetainedDiscEnvelope_le
    c hr hrR hc0 hc1 (mul_pos hδ hε), eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro L S
  let G := compactGaussianRetainedDiscEnvelope c r R N L S
  have hGm : Measurable G := measurable_compactGaussianRetainedDiscEnvelope c r R hN L S
  have hbad : steinhausMeasure {ω | ENNReal.ofReal ε ≤ G ω} ≤ ENNReal.ofReal δ := by
    calc
      _ ≤ (∫⁻ ω, G ω ∂steinhausMeasure) / ENNReal.ofReal ε :=
        meas_ge_le_lintegral_div hGm.aemeasurable
          (ENNReal.ofReal_ne_zero_iff.mpr hε) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (δ * ε) / ENNReal.ofReal ε :=
        ENNReal.div_le_div_right (hmean L S) _
      _ = _ := by rw [← ENNReal.ofReal_div_of_pos hε, mul_div_cancel_right₀ δ hε.ne']
  have hcomp : (compactGaussianRetainedSmallCentreEvent c r R N L S ε)ᶜ =
      {ω | ENNReal.ofReal ε ≤ G ω} := by
    ext ω
    simp only [compactGaussianRetainedSmallCentreEvent, mem_compl_iff, mem_setOf_eq, not_lt, G]
  rw [hcomp]
  simpa only [Measure.real, ENNReal.toReal_ofReal hδ.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad

/-- Every prescribed event of fixed positive mass retains half that mass with
the complete compact normalized background small. -/
theorem eventually_compactGaussianRetainedSmallCentre_inter_mass
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1)
    {ε m : ℝ} (hε : 0 < ε) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ,
      ∀ E : Set Omega, m ≤ steinhausMeasure.real E →
        m / 2 ≤ steinhausMeasure.real
          (E ∩ compactGaussianRetainedSmallCentreEvent c r R N L S ε) := by
  filter_upwards [eventually_measureReal_compactGaussianRetainedSmallCentre_compl_le
    c hr hrR hc0 hc1 hε (half_pos hm)] with N hN
  intro L S E hE
  have hbad := hN L S
  have hdiff := le_measureReal_sdiff (μ := steinhausMeasure) (s₁ := E)
    (s₂ := (compactGaussianRetainedSmallCentreEvent c r R N L S ε)ᶜ)
  rw [Set.sdiff_compl] at hdiff
  linarith

end RHTower
