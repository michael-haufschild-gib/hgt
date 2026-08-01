import GaloisForLFunctions.HTGeometry.StripThreeLinesTransfer
import GaloisForLFunctions.HTGeometry.StripHullSeparation
import GaloisForLFunctions.HTGeometry.VerticalPhaseRank
import GaloisForLFunctions.HTGeometry.LineStripCarrier

/-!
# The line carrier and the strip carrier are the same

The translation pseudometric of the line restriction is dominated by that of the substrip translate
curve, and — by the three-lines bound — a small line distance forces a small substrip distance.  So
the identity of the translation parameter is uniformly continuous both ways, and the two phase
carriers are uniformly equivalent: a statement about the carrier of the strip curve, where jets make
sense, is a statement about the carrier of the line restriction, where the rank bound lives.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **A small line distance forces a small substrip distance.** -/
theorem uniformContinuous_bohrLine_to_strip {σ R r r' : ℝ} (hr0 : 0 ≤ r) (hrr' : r < r')
    (hr'R : r' < R) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ t : ℝ, f t = F ((σ : ℂ) + (t : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) :
    UniformContinuous (fun t : BohrLine f => (BohrLine.of Gb t.val)) := by
  classical
  have hcontOn : ContinuousOn F (closedStrip σ r') :=
    (hF.mono (closedStrip_subset_verticalStrip hr'R)).continuousOn
  obtain ⟨M, hM⟩ := exists_bound_of_isStripAlmostPeriodicOn hcontOn (hap r' hr'R)
  have hM1 : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ max M 1 := fun z hz => (hM z hz).trans (le_max_left _ _)
  have hMpos : (0 : ℝ) < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ :=
    exists_delta_strip_of_line hr0 hrr' hr'R hMpos hF hM1 (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun {s t} hst => ?_⟩
  have hline : ∀ x : ℝ, ‖F ((σ : ℂ) + ((x + s.val : ℝ) : ℂ) * Complex.I)
      - F ((σ : ℂ) + ((x + t.val : ℝ) : ℂ) * Complex.I)‖ ≤ δ := by
    intro x
    have hd : dist (translateBC s.val f) (translateBC t.val f) < δ := hst
    have hpt := BoundedContinuousFunction.dist_coe_le_dist
      (f := translateBC s.val f) (g := translateBC t.val f) x
    have hval : dist (f (x + s.val)) (f (x + t.val)) ≤ δ := by
      simpa using hpt.trans hd.le
    rw [hf, hf] at hval
    simpa [dist_eq_norm] using hval
  have hstrip : ∀ z ∈ closedStrip σ r,
      ‖F (z + (s.val : ℂ) * Complex.I) - F (z + (t.val : ℂ) * Complex.I)‖ ≤ ε / 2 :=
    hδp s.val t.val hline
  have hGbdist : dist (Gb s.val) (Gb t.val) ≤ ε / 2 := by
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun z => ?_
    rw [hGb, hGb, dist_eq_norm]
    exact hstrip (z : ℂ) z.2
  have hfinal : dist (translateBC s.val Gb) (translateBC t.val Gb) ≤ ε / 2 := by
    rw [← dist_stripCurve_eq hGb]
    exact hGbdist
  have : dist (BohrLine.of Gb s.val) (BohrLine.of Gb t.val) ≤ ε / 2 := hfinal
  linarith [this]

/-- **The two translation uniformities agree.** -/
noncomputable def stripLineUniformEquiv {σ R r r' : ℝ} (hr0 : 0 ≤ r) (hrr' : r < r')
    (hr'R : r' < R) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ t : ℝ, f t = F ((σ : ℂ) + (t : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) :
    BohrLine f ≃ᵤ BohrLine Gb where
  toFun t := BohrLine.of Gb t.val
  invFun t := BohrLine.of f t.val
  left_inv _ := rfl
  right_inv _ := rfl
  uniformContinuous_toFun := uniformContinuous_bohrLine_to_strip hr0 hrr' hr'R hF hap hf hGb
  uniformContinuous_invFun := by
    have hlip : LipschitzWith 1 (fun t : BohrLine Gb => BohrLine.of f t.val) := by
      refine LipschitzWith.of_dist_le_mul fun s t => ?_
      have h := dist_line_le_dist_strip hr0 hf hGb s.val t.val
      simpa [BohrLine.dist_eq] using h
    exact hlip.uniformContinuous

/-- **The line carrier and the strip carrier are uniformly equivalent.** -/
noncomputable def stripLineHullEquiv {σ R r r' : ℝ} (hr0 : 0 ≤ r) (hrr' : r < r')
    (hr'R : r' < R) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ t : ℝ, f t = F ((σ : ℂ) + (t : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) :
    BohrHull f ≃ᵤ BohrHull Gb :=
  UniformSpace.Completion.mapEquiv (stripLineUniformEquiv hr0 hrr' hr'R hF hap hf hGb)

end GaloisForLFunctions
