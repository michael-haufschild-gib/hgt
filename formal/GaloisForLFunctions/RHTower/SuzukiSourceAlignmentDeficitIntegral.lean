import GaloisForLFunctions.RHTower.SuzukiSourceAlignmentSlack

/-!
# The bottom-edge deficits as integrals of nonnegative weights

The two source deficits are the gap between the edge resolvent value and the actual resolvent
moment of the source spectral measure.  Because both measures are probability measures, that gap is
itself an integral,

`1/(1-r) - ∫ (1+t)⁻¹ dμ_e = ∫ (t+r)/[(1-r)(1+t)] dμ_e`,
`∫ (1-t)⁻¹ dμ_o - 1/(1+r) = ∫ (t+r)/[(1-t)(1+r)] dμ_o`,

of a weight that is nonnegative on the spectrum.  The pointwise edge comparisons then bound the
Rayleigh quotient of the shifted contraction by the deficit, and vanishing deficit forces the
measure onto the edge point.

Everything here is the integral half of the slack law: the pointwise inequalities are already
available, and what is added is their passage through the integral for a probability measure
supported in `[-r, 1]`.
-/

open MeasureTheory

noncomputable section

namespace RHTower

variable {μ : Measure ℝ}

/-- The even resolvent weight. -/
def evenResolvent (t : ℝ) : ℝ := 1 / (1 + t)

/-- The odd resolvent weight. -/
def oddResolvent (t : ℝ) : ℝ := 1 / (1 - t)

/-- The even bottom-edge weight. -/
def evenEdgeWeight (r t : ℝ) : ℝ := (t + r) / ((1 - r) * (1 + t))

/-- The odd bottom-edge weight. -/
def oddEdgeWeight (r t : ℝ) : ℝ := (t + r) / ((1 - t) * (1 + r))

/-! ## Integrability on a spectrum contained in `[-r, 1]` -/

theorem integrable_id_of_edgeSupport [IsProbabilityMeasure μ] {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1) : Integrable (fun t : ℝ => t) μ := by
  refine (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
  filter_upwards [hsupp] with t ht
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [ht.1], ht.2⟩

theorem integrable_evenResolvent [IsProbabilityMeasure μ] {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1) : Integrable evenResolvent μ := by
  refine (integrable_const (1 / (1 - r))).mono'
    ((measurable_const.div (measurable_const.add measurable_id)).aestronglyMeasurable) ?_
  filter_upwards [hsupp] with t ht
  have h1t : (0 : ℝ) < 1 + t := by linarith [ht.1]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rw [evenResolvent, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_le_div_iff₀ h1t h1r]
  linarith [ht.1]

/-! ## The deficits are integrals of the edge weights -/

/-- **`(245)`, even half.** -/
theorem evenDeficit_eq [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1) :
    1 / (1 - r) - ∫ t, evenResolvent t ∂μ = ∫ t, evenEdgeWeight r t ∂μ := by
  have hint := integrable_evenResolvent hr0 hr1 hsupp
  have hconst : Integrable (fun _ : ℝ => 1 / (1 - r)) μ := integrable_const _
  have hsub : ∫ t, ((1 / (1 - r)) - evenResolvent t) ∂μ
      = 1 / (1 - r) - ∫ t, evenResolvent t ∂μ := by
    rw [integral_sub hconst hint, integral_const]
    simp
  rw [← hsub]
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with t ht
  have h1t : (0 : ℝ) < 1 + t := by linarith [ht.1]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rw [evenResolvent, evenEdgeWeight]
  field_simp
  ring

/-- **`(245)`, odd half.**  Finiteness of the odd energy is the integrability input. -/
theorem oddDeficit_eq [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t < 1) (hint : Integrable oddResolvent μ) :
    (∫ t, oddResolvent t ∂μ) - 1 / (1 + r) = ∫ t, oddEdgeWeight r t ∂μ := by
  have hconst : Integrable (fun _ : ℝ => 1 / (1 + r)) μ := integrable_const _
  have hsub : ∫ t, (oddResolvent t - 1 / (1 + r)) ∂μ
      = (∫ t, oddResolvent t ∂μ) - 1 / (1 + r) := by
    rw [integral_sub hint hconst, integral_const]
    simp
  rw [← hsub]
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with t ht
  have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have h1r : (0 : ℝ) < 1 + r := by linarith
  rw [oddResolvent, oddEdgeWeight]
  field_simp
  ring

theorem integrable_evenEdgeWeight [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1) : Integrable (evenEdgeWeight r) μ := by
  refine ((integrable_const (1 / (1 - r))).sub (integrable_evenResolvent hr0 hr1 hsupp)).congr ?_
  filter_upwards [hsupp] with t ht
  have h1t : (0 : ℝ) < 1 + t := by linarith [ht.1]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  simp only [Pi.sub_apply, evenResolvent, evenEdgeWeight]
  field_simp
  ring

theorem integrable_oddEdgeWeight [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t < 1) (hint : Integrable oddResolvent μ) :
    Integrable (oddEdgeWeight r) μ := by
  refine (hint.sub (integrable_const (1 / (1 + r)))).congr ?_
  filter_upwards [hsupp] with t ht
  have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have h1r : (0 : ℝ) < 1 + r := by linarith
  simp only [Pi.sub_apply, oddResolvent, oddEdgeWeight]
  field_simp
  ring

/-! ## `(248)`: the shifted Rayleigh quotient is dominated by the deficit -/

/-- **`(248)`, even half.** -/
theorem edgeIntegral_le_evenDeficit [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1) :
    ∫ t, (t + r) ∂μ ≤ 2 * (1 - r) * ∫ t, evenEdgeWeight r t ∂μ := by
  have hid := integrable_id_of_edgeSupport hr0 hr1 hsupp
  have hw := integrable_evenEdgeWeight hr0 hr1 hsupp
  have hmono : ∫ t, (t + r) ∂μ ≤ ∫ t, (2 * (1 - r) * evenEdgeWeight r t) ∂μ := by
    refine integral_mono_ae (hid.add (integrable_const r)) (hw.const_mul _) ?_
    filter_upwards [hsupp] with t ht
    exact edge_le_even_weight hr1 ht.1 ht.2
  rwa [integral_const_mul] at hmono

/-- **`(248)`, odd half.** -/
theorem edgeIntegral_le_oddDeficit [IsProbabilityMeasure μ] {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t < 1) (hint : Integrable oddResolvent μ) :
    ∫ t, (t + r) ∂μ ≤ (1 + r) ^ 2 * ∫ t, oddEdgeWeight r t ∂μ := by
  have hsupp' : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1 := by
    filter_upwards [hsupp] with t ht
    exact ⟨ht.1, ht.2.le⟩
  have hid := integrable_id_of_edgeSupport hr0 hr1 hsupp'
  have hw := integrable_oddEdgeWeight hr0 hsupp hint
  have hmono : ∫ t, (t + r) ∂μ ≤ ∫ t, ((1 + r) ^ 2 * oddEdgeWeight r t) ∂μ := by
    refine integral_mono_ae (hid.add (integrable_const r)) (hw.const_mul _) ?_
    filter_upwards [hsupp] with t ht
    exact edge_le_odd_weight hr0 ht.1 ht.2
  rwa [integral_const_mul] at hmono

/-! ## `(250)`: the prime surplus of the source profile -/

/-- **`(250)`**: an upper bound for the deficit is a lower bound for the negated Rayleigh
quotient, which is the finite-prime surplus of the profile. -/
theorem neg_rayleigh_ge_of_deficit [IsProbabilityMeasure μ] {r Δ S c : ℝ} (hc : 0 ≤ c) (hΔS : Δ ≤ S) (hint : Integrable (fun t : ℝ => t) μ)
    (hedge : ∫ t, (t + r) ∂μ ≤ c * Δ) :
    r - c * S ≤ -∫ t, t ∂μ := by
  have hsplit : ∫ t, (t + r) ∂μ = (∫ t, t ∂μ) + r := by
    rw [integral_add hint (integrable_const r), integral_const]
    simp
  have hmono : c * Δ ≤ c * S := by nlinarith
  linarith [hedge, hsplit]

/-! ## `(251)`: a vanishing deficit collapses the measure onto the edge -/

/-- **`(251)`, even half.** -/
theorem ae_eq_edge_of_evenDeficit_eq_zero [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t ≤ 1)
    (hzero : ∫ t, evenEdgeWeight r t ∂μ = 0) : ∀ᵐ t ∂μ, t = -r := by
  have hnn : 0 ≤ᵐ[μ] evenEdgeWeight r := by
    filter_upwards [hsupp] with t ht
    have h1t : (0 : ℝ) < 1 + t := by linarith [ht.1]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have htr : (0 : ℝ) ≤ t + r := by linarith [ht.1]
    rw [evenEdgeWeight]
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (integrable_evenEdgeWeight hr0 hr1 hsupp)).mp hzero
  filter_upwards [hsupp, hae] with t ht hw
  have h1t : (0 : ℝ) < 1 + t := by linarith [ht.1]
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have : (t + r) / ((1 - r) * (1 + t)) = 0 := hw
  have hnum : t + r = 0 := by
    field_simp at this
    linarith
  linarith

/-- **`(251)`, odd half.** -/
theorem ae_eq_edge_of_oddDeficit_eq_zero [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 ≤ r) (hsupp : ∀ᵐ t ∂μ, -r ≤ t ∧ t < 1) (hint : Integrable oddResolvent μ)
    (hzero : ∫ t, oddEdgeWeight r t ∂μ = 0) : ∀ᵐ t ∂μ, t = -r := by
  have hnn : 0 ≤ᵐ[μ] oddEdgeWeight r := by
    filter_upwards [hsupp] with t ht
    have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have htr : (0 : ℝ) ≤ t + r := by linarith [ht.1]
    rw [oddEdgeWeight]
    positivity
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (integrable_oddEdgeWeight hr0 hsupp hint)).mp hzero
  filter_upwards [hsupp, hae] with t ht hw
  have h1t : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have : (t + r) / ((1 - t) * (1 + r)) = 0 := hw
  have hnum : t + r = 0 := by
    field_simp at this
    linarith
  linarith

end RHTower
