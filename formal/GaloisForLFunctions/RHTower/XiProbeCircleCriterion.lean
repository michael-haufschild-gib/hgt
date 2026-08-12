import GaloisForLFunctions.RHTower.GaussHodgeWeilPositivityCone

/-!
# The probe-circle criterion and the smearing law

Two exact laws of the budget-probe chart.

*The smearing law*: every divisor copy's probe response is a probe-smeared on-line response —
with `γ = Re α` and `b = Im α`, the budget mass at probe `c` is the average of the on-line
profile `2x/(γ² + x²)` at the displaced probes `c ∓ b`.  An off-line copy answers every probe
exactly like an on-line copy under probe displacement below the strip half-width: finite probe
data cannot resolve the critical line by sampling.

*The probe-circle criterion*: in the pole coordinate `x = (c − i·ᾱ)⁻¹` the on-line condition is
the circle relation `Re x = c·|x|²` — the image of the critical axis under the probe inversion.
For every real probe `c`, the Riemann hypothesis is equivalent to every divisor copy's probe
coordinate lying on the circle.  The relation is quadratic Hermitian in the atoms, while all
prime-side ray-jet data are holomorphic moments — the criterion localizes RH in the exact gap
between holomorphic and Hermitian divisor data.
-/

open Complex

namespace RHTower

noncomputable section

/-- The on-line probe profile: the budget mass a critical-line copy of height `γ` deposits at
probe `x`. -/
def xiOnLineProbeProfile (γ x : ℝ) : ℝ :=
  2 * x / (γ ^ 2 + x ^ 2)

/-- **The smearing law**: every copy's budget mass is the average of the on-line profile at
the two displaced probes `c ∓ b`.  Off-line copies are probe-displaced on-line copies. -/
theorem xiBudgetMassAt_eq_online_smear (c : ℝ) (q : XiZeroCopy) :
    xiBudgetMassAt c q =
      (xiOnLineProbeProfile (xiSpectralPoint q).re (c - (xiSpectralPoint q).im) +
        xiOnLineProbeProfile (xiSpectralPoint q).re (c + (xiSpectralPoint q).im)) / 2 := by
  rw [xiBudgetMassAt, xiOnLineProbeProfile, xiOnLineProbeProfile]
  ring

/-- On-line copies deposit exactly the on-line profile. -/
theorem xiBudgetMassAt_eq_online_of_im_eq_zero {q : XiZeroCopy}
    (hb : (xiSpectralPoint q).im = 0) (c : ℝ) :
    xiBudgetMassAt c q = xiOnLineProbeProfile (xiSpectralPoint q).re c := by
  rw [xiBudgetMassAt_eq_online_smear, hb, sub_zero, add_zero]
  ring

/-- The probe coordinate of a divisor copy: the reciprocal offset of the probe from the copy's
response pole `i·ᾱ`. -/
def xiProbeCoordinate (c : ℝ) (q : XiZeroCopy) : ℂ :=
  ((c : ℂ) - I * (starRingEnd ℂ) (xiSpectralPoint q))⁻¹

theorem xiProbeCoordinate_denom_re (c : ℝ) (q : XiZeroCopy) :
    ((c : ℂ) - I * (starRingEnd ℂ) (xiSpectralPoint q)).re =
      c - (xiSpectralPoint q).im := by
  simp [Complex.sub_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]

theorem xiProbeCoordinate_denom_im (c : ℝ) (q : XiZeroCopy) :
    ((c : ℂ) - I * (starRingEnd ℂ) (xiSpectralPoint q)).im =
      -(xiSpectralPoint q).re := by
  simp [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]

theorem xiProbeCoordinate_denom_ne_zero (c : ℝ) (q : XiZeroCopy) :
    ((c : ℂ) - I * (starRingEnd ℂ) (xiSpectralPoint q)) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [xiProbeCoordinate_denom_im, Complex.zero_im, neg_eq_zero] at him
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  rw [him] at hg
  norm_num at hg

/-- **The circle law**: a copy's probe coordinate satisfies the circle relation
`Re x = c·|x|²` exactly when the copy lies on the critical line. -/
theorem xiProbeCoordinate_circle_iff (c : ℝ) (q : XiZeroCopy) :
    (xiProbeCoordinate c q).re =
      c * Complex.normSq (xiProbeCoordinate c q) ↔ (xiSpectralPoint q).im = 0 := by
  set w : ℂ := (c : ℂ) - I * (starRingEnd ℂ) (xiSpectralPoint q) with hw
  have hwne : w ≠ 0 := xiProbeCoordinate_denom_ne_zero c q
  have hnormSqpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  have hre : (xiProbeCoordinate c q).re = w.re / Complex.normSq w := by
    rw [xiProbeCoordinate, ← hw, Complex.inv_re]
  have hns : Complex.normSq (xiProbeCoordinate c q) = (Complex.normSq w)⁻¹ := by
    rw [xiProbeCoordinate, ← hw, Complex.normSq_inv]
  rw [hre, hns]
  constructor
  · intro h
    have h2 : w.re = c := by
      field_simp at h
      exact h
    have h3 := xiProbeCoordinate_denom_re c q
    rw [← hw] at h3
    rw [h3] at h2
    linarith
  · intro hb
    have h3 := xiProbeCoordinate_denom_re c q
    rw [← hw, hb, sub_zero] at h3
    rw [h3]
    field_simp

/-- **The probe-circle criterion**: at every real probe, the Riemann hypothesis is equivalent
to every divisor copy's probe coordinate lying on the probe circle.  The relation is quadratic
Hermitian in the divisor atoms, while all ray-jet data are holomorphic moments: the criterion
places RH exactly in the holomorphic–Hermitian gap. -/
theorem riemannHypothesis_iff_forall_probeCoordinate_circle (c : ℝ) :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy,
      (xiProbeCoordinate c q).re = c * Complex.normSq (xiProbeCoordinate c q) := by
  constructor
  · intro hRH q
    rw [xiProbeCoordinate_circle_iff]
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht, Complex.ofReal_im]
  · intro h
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    have hb : (xiSpectralPoint q).im = 0 := (xiProbeCoordinate_circle_iff c q).mp (h q)
    have h1 : (xiSpectralPoint q ^ 2).im = 0 := by
      rw [sq, Complex.mul_im, hb]
      ring
    rw [h1] at hq
    exact lt_irrefl 0 hq

end

end RHTower
