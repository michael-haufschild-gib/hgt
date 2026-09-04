import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction

/-!
# Bombieri–Yoshida for the constrained restricted Weil form

**Theorem.**  If the pole-vanishing (constrained) ground energy of the CCM restricted Weil form is
nonnegative at every aperture, then the Riemann hypothesis holds
(`riemannHypothesis_of_polarGroundEnergy_nonneg`).

The proof assembles the translate multiplier (`SuzukiPolarTranslateMultiplier`), the twisted
two-bump limit (`SuzukiWeightedScrewTwoBumpLimit`), the weighted Widder–Landau engine
(`WeightedScrewLandauEngine`) and the pole contradiction (`WeightedScrewPoleContradiction`) with the
polar spectral weights `W_q = M(γ_q)²`, `M(γ) = (cos γ − 1)(cos γ − cosh(1/2))` (`h = 1`).  The weights
are bounded, depend only on `γ_q²`, and are nonzero at every off-line copy because `cos γ = 1` and
`cos γ = cosh(1/2)` force `Im γ ∈ {0, ±1/2}`.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- `(cos(γh) − 1)(cos(γh) − cosh(h/2)) ≠ 0` for `0 < |Im γ| < 1/2` and `h > 0`. -/
theorem polarMultiplierSpectral_ne_zero {h : ℝ} (hh : 0 < h) {γ : ℂ} (him : γ.im ≠ 0)
    (hstrip : |γ.im| < 1 / 2) : polarMultiplierSpectral h γ ≠ 0 := by
  unfold polarMultiplierSpectral
  refine mul_ne_zero ?_ ?_
  · intro hc
    rw [sub_eq_zero, ← Complex.cos_zero] at hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_cos_iff.mp hc
    rcases hk with hk | hk
    · have hi := congrArg Complex.im hk
      simp [Complex.mul_im] at hi
      rcases hi with hi | hi
      · exact him hi
      · exact hh.ne' hi
    · have hi := congrArg Complex.im hk
      simp [Complex.mul_im] at hi
      rcases hi with hi | hi
      · exact him hi
      · exact hh.ne' hi
  · intro hc
    rw [sub_eq_zero] at hc
    have hcosh : (Real.cosh (h / 2) : ℂ) = Complex.cos (((h / 2 : ℝ) : ℂ) * I) := by
      rw [Complex.cos_mul_I, Complex.ofReal_cosh]
    rw [hcosh] at hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_cos_iff.mp hc
    rcases hk with hk | hk
    · have hi := congrArg Complex.im hk
      simp [Complex.mul_im] at hi
      -- `h/2 = γ.im * h` gives `γ.im = 1/2`
      have : γ.im = 1 / 2 := by
        field_simp at hi ⊢
        nlinarith [hi, hh]
      rw [this, abs_of_pos (by norm_num)] at hstrip
      linarith
    · have hi := congrArg Complex.im hk
      simp [Complex.mul_im] at hi
      have : γ.im = -1 / 2 := by
        field_simp at hi ⊢
        nlinarith [hi, hh]
      rw [this] at hstrip
      norm_num at hstrip

theorem polarSpectralWeight_ne_zero {h : ℝ} (hh : 0 < h) (q : XiZeroCopy)
    (him : (xiSpectralPoint q).im ≠ 0) : polarSpectralWeight h q ≠ 0 :=
  pow_ne_zero 2 (polarMultiplierSpectral_ne_zero hh him (abs_xiSpectralPoint_im_lt_half q))

theorem polarSpectralWeight_of_eq (h : ℝ) {q q' : XiZeroCopy}
    (hq : xiSpectralPoint q' = xiSpectralPoint q) :
    polarSpectralWeight h q' = polarSpectralWeight h q := by
  unfold polarSpectralWeight
  rw [hq]

theorem polarSpectralWeight_of_neg (h : ℝ) {q q' : XiZeroCopy}
    (hq : xiSpectralPoint q' = -xiSpectralPoint q) :
    polarSpectralWeight h q' = polarSpectralWeight h q := by
  unfold polarSpectralWeight polarMultiplierSpectral
  rw [hq, neg_mul, Complex.cos_neg]

/-- **Bombieri–Yoshida for the constrained restricted Weil form.**  Nonnegativity of the
pole-vanishing ground energy at every aperture forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_polarGroundEnergy_nonneg
    (hμ : ∀ A : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilPolarGroundEnergy A) :
    RiemannHypothesis := by
  have hh : (0 : ℝ) < 1 := one_pos
  exact riemannHypothesis_of_weighted_positive (polarSpectralWeight 1)
    (C := polarSymbolBound 1 ^ 2) (by positivity) (norm_polarSpectralWeight_le hh.le)
    (fun q q' hq => polarSpectralWeight_of_eq 1 hq)
    (fun q q' hq => polarSpectralWeight_of_neg 1 hq)
    (fun q him => polarSpectralWeight_ne_zero hh q him)
    (fun t _ => weightedXiScrewDivisor_polar_re_nonneg hμ hh t)
    (fun t => weightedXiScrewDivisor_polar_im 1 t)

/-- The strict form. -/
theorem riemannHypothesis_of_polarGroundEnergy_pos
    (hμ : ∀ A : SuzukiPositiveAperture, 0 < ccmRestrictedWeilPolarGroundEnergy A) :
    RiemannHypothesis :=
  riemannHypothesis_of_polarGroundEnergy_nonneg fun A => (hμ A).le

end

end RHTower
