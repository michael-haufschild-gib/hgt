import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The zero-edge capacity slack and the hazard peak

Subtracting the transport integral from the logarithmic length of the probe interval leaves a
manifestly nonnegative integrand, `(1 - v_o) + v_e`, because both posterior hardnesses lie in
`[0,1]`.  That is the capacity-slack identity, and its nonnegativity immediately bounds the probe
ratio below by the transported factor.

The hazard has an exact product form: the difference of the two normalized second moments is a
double integral of `(u - t)` against a positive kernel, because

`1/[(t+s)²(u+s)] - 1/[(u+s)²(t+s)] = (u-t)/[(t+s)²(u+s)²]`.

Finally a mean-value comparison turns a lower bound for the transport integral into a lower bound
for the peak of the hazard, which is the card's diverging supremum.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(330)`: the capacity-slack identity -/

/-- **`(330)`: the logarithmic probe length minus the transported factor is the slack integral.** -/
theorem capacitySlack_eq {ve vo : ℝ → ℝ} {r ε T : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hg : IntervalIntegrable (fun s => (vo s - ve s) / s) volume r ε)
    (htrans : (∫ s in r..ε, (vo s - ve s) / s) = T) :
    Real.log (ε / r) - T = ∫ s in r..ε, ((1 - vo s) + ve s) / s := by
  have h0 : (0 : ℝ) ∉ Set.uIcc r ε := by
    rw [Set.uIcc_of_le hrε.le]
    intro h
    exact absurd h.1 (by linarith)
  have hone : IntervalIntegrable (fun s : ℝ => 1 / s) volume r ε := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro s hs
    rw [Set.uIcc_of_le hrε.le] at hs
    exact ne_of_gt (lt_of_lt_of_le hr hs.1)
  have hcongr : (∫ s in r..ε, ((1 - vo s) + ve s) / s)
      = ∫ s in r..ε, (1 / s - (vo s - ve s) / s) := by
    refine intervalIntegral.integral_congr ?_
    intro s _
    simp only
    ring
  rw [hcongr, intervalIntegral.integral_sub hone hg, htrans, integral_one_div h0]

/-- **`(330)`, nonnegativity: both posterior hardnesses lie in `[0,1]`.** -/
theorem capacitySlack_nonneg {ve vo : ℝ → ℝ} {r ε : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hint : IntervalIntegrable (fun s => ((1 - vo s) + ve s) / s) volume r ε)
    (hvo1 : ∀ s ∈ Set.Icc r ε, vo s ≤ 1) (hve0 : ∀ s ∈ Set.Icc r ε, 0 ≤ ve s) :
    0 ≤ ∫ s in r..ε, ((1 - vo s) + ve s) / s := by
  have hzero : (∫ s in r..ε, (0 : ℝ)) ≤ ∫ s in r..ε, ((1 - vo s) + ve s) / s := by
    refine intervalIntegral.integral_mono_on hrε.le intervalIntegrable_const hint ?_
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hr hs.1
    have h1 : 0 ≤ (1 - vo s) + ve s := by
      have := hvo1 s hs
      have := hve0 s hs
      linarith
    positivity
  simpa using hzero

/-- **`(331)`: nonnegative slack bounds the probe ratio below by the transported factor.** -/
theorem log_ratio_ge_of_slack {r ε T : ℝ} (hslack : 0 ≤ Real.log (ε / r) - T) :
    T ≤ Real.log (ε / r) := by linarith

/-- **`(331)`, exponentiated form.** -/
theorem ratio_ge_of_log_le {r ε R : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (h : Real.log R ≤ Real.log (ε / r)) (hR : 0 < R) : R ≤ ε / r := by
  have hdiv : (0 : ℝ) < ε / r := div_pos hε hr
  exact (Real.log_le_log_iff hR hdiv).mp h

/-! ## `(333)`: the Jordan numerator -/

/-- **`(333)`: the hazard numerator is a difference of the two spectral points against a positive
kernel.** -/
theorem hazard_kernel_identity {t u s : ℝ} (ht : 0 < t + s) (hu : 0 < u + s) :
    1 / ((t + s) ^ 2 * (u + s)) - 1 / ((u + s) ^ 2 * (t + s))
      = (u - t) / ((t + s) ^ 2 * (u + s) ^ 2) := by
  field_simp
  ring

/-! ## `(334)`: the hazard peak -/

/-- **`(334)`: a lower bound for the transport integral is a lower bound for the hazard peak.** -/
theorem le_sup_of_integral_ge {f : ℝ → ℝ} {r ε c M : ℝ} (hrε : r < ε)
    (hint : IntervalIntegrable f volume r ε)
    (hbound : ∀ s ∈ Set.Icc r ε, f s ≤ M) (hge : c ≤ ∫ s in r..ε, f s) :
    c ≤ M * (ε - r) := by
  have hle : (∫ s in r..ε, f s) ≤ ∫ _s in r..ε, M :=
    intervalIntegral.integral_mono_on hrε.le hint intervalIntegrable_const hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  linarith [hge, hle]

/-! ## `(336)`: the sharpness model -/

/-- **`(336)`: the two-atom model realises the transported factor exactly.** -/
theorem sharpnessModel_factor {R η r : ℝ} (hr : 0 < r) (hη : 0 ≤ η) (hR : 0 < R) :
    (r / (η * r + r)) / (r / ((R * (1 + η) - 1) * r + r)) = R := by
  have h1 : (0 : ℝ) < 1 + η := by linarith
  have h2 : (0 : ℝ) < R * (1 + η) := by positivity
  have hden1 : η * r + r = (1 + η) * r := by ring
  have hden2 : (R * (1 + η) - 1) * r + r = R * (1 + η) * r := by ring
  rw [hden1, hden2]
  field_simp

end GaloisForLFunctions.RHTower
