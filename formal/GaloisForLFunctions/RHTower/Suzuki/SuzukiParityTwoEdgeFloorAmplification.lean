import GaloisForLFunctions.RHTower.CCM.CCMInwardRegularizationFloor

/-!
# Suzuki parity two-edge complementarity and odd-floor amplification

The symmetric and antisymmetric fixed-width boundary packets have diagonal Xi--Weil energies
whose sum is independent of aperture.  The identity is exact: the two growing edge squares cancel
and only the cross-edge trace remains.  Existing two-sided transverse oscillation of the symmetric
packet therefore transfers to the antisymmetric packet with the opposite sign.

Inward regularization then gives the sharp variational bridge to the odd restricted-Weil floor.
Under false RH that floor has the same cofinal subcritical-power amplification already known for
the unrestricted floor.  No RH assumption enters any identity or regularization theorem.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-! ## The sharp antisymmetric edge packet -/

/-- Bilateral transform of the antisymmetric fixed-width two-edge packet
`1_[a-L,a] - 1_[-a,-a+L]`. -/
def rectangularOddTwoEdgeTransform (L a : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w -
    Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)

/-- The odd edge transform respects Schwarz conjugation. -/
theorem rectangularOddTwoEdgeTransform_conj (L a : ℝ) (w : ℂ) :
    (starRingEnd ℂ) (rectangularOddTwoEdgeTransform L a w) =
      rectangularOddTwoEdgeTransform L a ((starRingEnd ℂ) w) := by
  rw [rectangularOddTwoEdgeTransform, rectangularOddTwoEdgeTransform]
  simp only [map_sub, map_mul, map_neg, rectangularWindowAmplitude_conj]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  congr 1 <;> simp

/-- Reflection of the transform variable reverses the antisymmetric edge packet. -/
theorem rectangularOddTwoEdgeTransform_neg (L a : ℝ) (w : ℂ) :
    rectangularOddTwoEdgeTransform L a (-w) =
      -rectangularOddTwoEdgeTransform L a w := by
  rw [rectangularOddTwoEdgeTransform, rectangularOddTwoEdgeTransform]
  simp only [neg_neg]
  ring

/-- Odd two-edge transform in the centered Xi spectral coordinate. -/
def xiRectangularOddTwoEdgeTransform (L a : ℝ) (z : ℂ) : ℂ :=
  rectangularOddTwoEdgeTransform L a (I * z)

/-- The Xi--Weil involution acts by minus one on the real odd edge transform. -/
theorem xiWeilSharp_xiRectangularOddTwoEdgeTransform (L a : ℝ) (z : ℂ) :
    xiWeilSharp (xiRectangularOddTwoEdgeTransform L a) z =
      -xiRectangularOddTwoEdgeTransform L a z := by
  rw [xiWeilSharp, xiRectangularOddTwoEdgeTransform,
    rectangularOddTwoEdgeTransform_conj]
  rw [show (starRingEnd ℂ) (I * (starRingEnd ℂ) z) = -(I * z) by simp]
  exact rectangularOddTwoEdgeTransform_neg L a (I * z)

private theorem parity_real_mul_re_le_abs_half {c : ℝ} {w : ℂ}
    (hw : |w.re| ≤ (1 / 2 : ℝ)) :
    ((c : ℂ) * w).re ≤ |c| / 2 := by
  rw [Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    c * w.re ≤ |c * w.re| := le_abs_self _
    _ = |c| * |w.re| := abs_mul c w.re
    _ ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left hw (abs_nonneg c)
    _ = |c| / 2 := by ring

/-- Uniform reciprocal-height bound for the sharp odd edge transform. -/
theorem norm_rectangularOddTwoEdgeTransform_le
    (L a : ℝ) {w : ℂ} (hw : w ≠ 0) (hwre : |w.re| ≤ (1 / 2 : ℝ)) :
    ‖rectangularOddTwoEdgeTransform L a w‖ ≤
      (2 * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) / ‖w‖ := by
  have hA := norm_rectangularWindowAmplitude_le L hw hwre
  have hAnRaw := norm_rectangularWindowAmplitude_le L (neg_ne_zero.mpr hw) (by simpa using hwre)
  have hAn : ‖rectangularWindowAmplitude L (-w)‖ ≤
      (1 + Real.exp (|L| / 2)) / ‖w‖ := by
    simpa only [norm_neg] using hAnRaw
  have he : ‖Complex.exp ((a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (parity_real_mul_re_le_abs_half hwre)
  have hen : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    have h := parity_real_mul_re_le_abs_half (c := -a) hwre
    simpa only [ofReal_neg, neg_mul, abs_neg] using Real.exp_le_exp.mpr h
  rw [rectangularOddTwoEdgeTransform]
  calc
    ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w -
        Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)‖ ≤
        ‖Complex.exp ((a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L w‖ +
          ‖Complex.exp (-(a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L (-w)‖ := by
      simpa only [norm_mul] using norm_sub_le
        (Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w)
        (Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w))
    _ ≤ Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) +
        Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) := by
      gcongr
    _ = _ := by ring

/-- Pointwise reciprocal-square majorant for the sharp odd Xi transform. -/
theorem xiRectangularOddTwoEdgeTransform_square_le
    (L a : ℝ) (q : XiZeroCopy) :
    ‖xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q)‖ ^ 2 ≤
      (2 * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let C : ℝ := 2 * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  have hbound : ‖xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q)‖ ≤
      C / ‖xiSpectralPoint q‖ := by
    rw [xiRectangularOddTwoEdgeTransform]
    have h := norm_rectangularOddTwoEdgeTransform_le L a hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))
    rw [norm_mul, norm_I, one_mul] at h
    exact h
  calc
    ‖xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q)‖ ^ 2 ≤
        (C / ‖xiSpectralPoint q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp

/-- Every sharp odd two-edge profile is square-summable on the Xi divisor. -/
theorem xiRectangularOddTwoEdgeTransform_squareSummable (L a : ℝ) :
    XiWeilSquareSummable (xiRectangularOddTwoEdgeTransform L a) := by
  let C : ℝ := 2 * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  apply Summable.of_nonneg_of_le
  · intro q
    positivity
  · intro q
    exact xiRectangularOddTwoEdgeTransform_square_le L a q
  · exact xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)

/-- Odd diagonal polarization is minus the sum of squared odd transform values. -/
theorem xiWeilPolarization_oddRectangular_eq_neg_tsum_sq (L a : ℝ) :
    xiWeilPolarization (xiRectangularOddTwoEdgeTransform L a)
        (xiRectangularOddTwoEdgeTransform L a) =
      ∑' q : XiZeroCopy,
        -(xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q) ^ 2) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp_xiRectangularOddTwoEdgeTransform]
  ring

/-- Squared odd transform values are absolutely summable. -/
theorem xiRectangularOddTwoEdgeTransform_sq_summable (L a : ℝ) :
    Summable (fun q : XiZeroCopy =>
      xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q) ^ 2) := by
  apply Summable.of_norm
  simpa only [norm_pow] using!
    (xiRectangularOddTwoEdgeTransform_squareSummable L a)

/-! ## Aperture-independent parity trace -/

/-- Cross-edge trace term left after adding the even and odd diagonal energies. -/
def xiRectangularParityTraceTerm (L : ℝ) (q : XiZeroCopy) : ℂ :=
  4 * rectangularWindowAmplitude L (I * xiSpectralPoint q) *
    rectangularWindowAmplitude L (-(I * xiSpectralPoint q))

/-- Even plus odd energy equals the cross-edge term, pointwise on every Xi divisor copy. -/
theorem xiRectangular_even_sq_sub_odd_sq_eq_traceTerm
    (L a : ℝ) (q : XiZeroCopy) :
    xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 -
        xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 =
      xiRectangularParityTraceTerm L q := by
  let w : ℂ := I * xiSpectralPoint q
  let R : ℂ := Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w
  let S : ℂ := Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w)
  have heven : xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) = R + S := by
    rfl
  have hodd : xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q) = R - S := by
    rfl
  rw [heven, hodd]
  calc
    (R + S) ^ 2 - (R - S) ^ 2 = 4 * R * S := by ring
    _ = 4 * (Complex.exp ((a : ℂ) * w) * Complex.exp (-(a : ℂ) * w)) *
          (rectangularWindowAmplitude L w * rectangularWindowAmplitude L (-w)) := by
      dsimp only [R, S]
      ring
    _ = xiRectangularParityTraceTerm L q := by
      have hexp : Complex.exp ((a : ℂ) * w) * Complex.exp (-(a : ℂ) * w) = 1 := by
        calc
          Complex.exp ((a : ℂ) * w) * Complex.exp (-(a : ℂ) * w) =
              Complex.exp (((a : ℂ) * w) + (-(a : ℂ) * w)) :=
            (Complex.exp_add _ _).symm
          _ = 1 := by rw [show ((a : ℂ) * w) + (-(a : ℂ) * w) = 0 by ring,
            Complex.exp_zero]
      rw [hexp]
      simp [xiRectangularParityTraceTerm, w]
      ring

/-- The aperture-independent cross-edge trace is absolutely summable. -/
theorem xiRectangularParityTraceTerm_summable (L : ℝ) :
    Summable (xiRectangularParityTraceTerm L) := by
  have hdiff := (xiRectangularTwoEdgeTransform_sq_summable L 0).sub
    (xiRectangularOddTwoEdgeTransform_sq_summable L 0)
  exact hdiff.congr fun q => xiRectangular_even_sq_sub_odd_sq_eq_traceTerm L 0 q

/-- Aperture-independent total parity trace carried by one fixed-width edge profile. -/
def xiRectangularParityTrace (L : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiRectangularParityTraceTerm L q

/-- **Parity complementarity.** Even and odd diagonal Xi--Weil energies have constant sum. -/
theorem xiWeilPolarization_even_add_odd_eq_parityTrace (L a : ℝ) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) +
      xiWeilPolarization (xiRectangularOddTwoEdgeTransform L a)
        (xiRectangularOddTwoEdgeTransform L a) =
      xiRectangularParityTrace L := by
  rw [xiWeilPolarization_rectangular_eq_tsum_sq,
    xiWeilPolarization_oddRectangular_eq_neg_tsum_sq]
  have heven := xiRectangularTwoEdgeTransform_sq_summable L a
  have hodd := (xiRectangularOddTwoEdgeTransform_sq_summable L a).neg
  rw [← heven.tsum_add hodd]
  unfold xiRectangularParityTrace
  apply tsum_congr
  intro q
  rw [← xiRectangular_even_sq_sub_odd_sq_eq_traceTerm L a q]
  ring

/-- The parity trace is real because it is a sum of two Hermitian diagonal energies. -/
theorem xiRectangularParityTrace_im_eq_zero (L : ℝ) :
    (xiRectangularParityTrace L).im = 0 := by
  rw [← xiWeilPolarization_even_add_odd_eq_parityTrace L 0]
  simp only [add_im, xiWeilPolarization_diagonal_im_eq_zero, add_zero]

/-- Directly observable odd fixed-width Weil energy at logarithmic aperture. -/
def xiRectangularOddWeilLogCoefficient (L : ℝ) (n : ℕ) : ℂ :=
  xiWeilPolarization
    (xiRectangularOddTwoEdgeTransform L (Real.log n / 2))
    (xiRectangularOddTwoEdgeTransform L (Real.log n / 2))

/-- Sampled even and odd energies retain the same aperture-independent parity trace. -/
theorem xiRectangularWeilLogCoefficient_add_odd_eq_parityTrace (L : ℝ) (n : ℕ) :
    xiRectangularWeilLogCoefficient L n +
      xiRectangularOddWeilLogCoefficient L n =
      xiRectangularParityTrace L := by
  exact xiWeilPolarization_even_add_odd_eq_parityTrace L (Real.log n / 2)

/-- False RH forces negative odd-parity excursions below every subcritical power scale. -/
theorem not_riemannHypothesis_implies_oddRectangular_weil_cofinally_unbounded_below_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiRectangularOddWeilLogCoefficient L n).re <
        -(C * (n : ℝ) ^ alpha) := by
  intro C hC N0
  let K : ℝ := (xiRectangularParityTrace L).re
  obtain ⟨n, hn0, hLa, heven⟩ :=
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_above_power
      hL halpha0 hRH halpha (C + |K|) (add_nonneg hC (abs_nonneg K)) N0
  refine ⟨n, hn0, hLa, ?_⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hLa
    linarith
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn_ne)
  have hpow : 1 ≤ (n : ℝ) ^ alpha := Real.one_le_rpow hn_one halpha0
  have hid := congrArg Complex.re
    (xiRectangularWeilLogCoefficient_add_odd_eq_parityTrace L n)
  simp only [add_re] at hid
  have hKpow : K ≤ |K| * (n : ℝ) ^ alpha := by
    calc
      K ≤ |K| := le_abs_self K
      _ ≤ |K| * (n : ℝ) ^ alpha := by
        nlinarith [abs_nonneg K]
  dsimp only [K] at heven hid hKpow ⊢
  nlinarith

/-- False RH also forces positive odd-parity excursions above every subcritical power scale. -/
theorem not_riemannHypothesis_implies_oddRectangular_weil_cofinally_unbounded_above_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      C * (n : ℝ) ^ alpha <
        (xiRectangularOddWeilLogCoefficient L n).re := by
  intro C hC N0
  let K : ℝ := (xiRectangularParityTrace L).re
  obtain ⟨n, hn0, hLa, heven⟩ :=
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below_power
      hL halpha0 hRH halpha (C + |K|) (add_nonneg hC (abs_nonneg K)) N0
  refine ⟨n, hn0, hLa, ?_⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hLa
    linarith
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn_ne)
  have hpow : 1 ≤ (n : ℝ) ^ alpha := Real.one_le_rpow hn_one halpha0
  have hid := congrArg Complex.re
    (xiRectangularWeilLogCoefficient_add_odd_eq_parityTrace L n)
  simp only [add_re] at hid
  have hKpow : -|K| * (n : ℝ) ^ alpha ≤ K := by
    calc
      -|K| * (n : ℝ) ^ alpha ≤ -|K| := by
        nlinarith [abs_nonneg K]
      _ ≤ K := neg_abs_le K
  dsimp only [K] at heven hid hKpow ⊢
  nlinarith

/-! ## Inward regularization in the odd parity sector -/

/-- Transform of two inward-smoothed edges with the antisymmetric sign. -/
def inwardRegularizedOddTwoEdgeTransform (L a epsilon : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
      inwardEdgeRegularizationFactor epsilon w -
    Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
      inwardEdgeRegularizationFactor epsilon (-w)

theorem tendsto_inwardRegularizedOddTwoEdgeTransform_zero (L a : ℝ) (w : ℂ) :
    Tendsto (fun epsilon : ℝ => inwardRegularizedOddTwoEdgeTransform L a epsilon w)
      (𝓝 0) (𝓝 (rectangularOddTwoEdgeTransform L a w)) := by
  have hw := tendsto_inwardEdgeRegularizationFactor_zero w
  have hn := tendsto_inwardEdgeRegularizationFactor_zero (-w)
  simpa [inwardRegularizedOddTwoEdgeTransform, rectangularOddTwoEdgeTransform] using
    ((tendsto_const_nhds.mul tendsto_const_nhds).mul hw).sub
      ((tendsto_const_nhds.mul tendsto_const_nhds).mul hn)

/-- Uniform reciprocal-height bound for every odd inward smoothing scale. -/
theorem norm_inwardRegularizedOddTwoEdgeTransform_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    {w : ℂ} (hw0 : w ≠ 0) (hw : |w.re| ≤ 1 / 2) :
    ‖inwardRegularizedOddTwoEdgeTransform L a epsilon w‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) / ‖w‖ := by
  have hA := norm_rectangularWindowAmplitude_le L hw0 hw
  have hAnRaw := norm_rectangularWindowAmplitude_le L (neg_ne_zero.mpr hw0) (by simpa using hw)
  have hAn : ‖rectangularWindowAmplitude L (-w)‖ ≤
      (1 + Real.exp (|L| / 2)) / ‖w‖ := by
    simpa only [norm_neg] using hAnRaw
  have hm := norm_inwardEdgeRegularizationFactor_le hepsilon0 hepsilon1 hw
  have hmn := norm_inwardEdgeRegularizationFactor_le (w := -w)
    hepsilon0 hepsilon1 (by simpa using hw)
  have he : ‖Complex.exp ((a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (parity_real_mul_re_le_abs_half hw)
  have hen : ‖Complex.exp (-(a : ℂ) * w)‖ ≤ Real.exp (|a| / 2) := by
    rw [Complex.norm_exp]
    have h := parity_real_mul_re_le_abs_half (c := -a) hw
    simpa only [ofReal_neg, neg_mul, abs_neg] using Real.exp_le_exp.mpr h
  rw [inwardRegularizedOddTwoEdgeTransform]
  calc
    ‖Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
          inwardEdgeRegularizationFactor epsilon w -
        Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
          inwardEdgeRegularizationFactor epsilon (-w)‖ ≤
        ‖Complex.exp ((a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L w‖ *
            ‖inwardEdgeRegularizationFactor epsilon w‖ +
          ‖Complex.exp (-(a : ℂ) * w)‖ * ‖rectangularWindowAmplitude L (-w)‖ *
            ‖inwardEdgeRegularizationFactor epsilon (-w)‖ := by
      simpa only [norm_mul] using norm_sub_le
        (Complex.exp ((a : ℂ) * w) * rectangularWindowAmplitude L w *
          inwardEdgeRegularizationFactor epsilon w)
        (Complex.exp (-(a : ℂ) * w) * rectangularWindowAmplitude L (-w) *
          inwardEdgeRegularizationFactor epsilon (-w))
    _ ≤ Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) * Real.exp (1 / 2) +
        Real.exp (|a| / 2) * ((1 + Real.exp (|L| / 2)) / ‖w‖) * Real.exp (1 / 2) := by
      gcongr
    _ = _ := by ring

def inwardRegularizedXiOddTwoEdgeTransform (L a epsilon : ℝ) (z : ℂ) : ℂ :=
  inwardRegularizedOddTwoEdgeTransform L a epsilon (I * z)

theorem tendsto_inwardRegularizedXiOddTwoEdgeTransform_zero (L a : ℝ) (z : ℂ) :
    Tendsto (fun epsilon : ℝ => inwardRegularizedXiOddTwoEdgeTransform L a epsilon z)
      (𝓝 0) (𝓝 (xiRectangularOddTwoEdgeTransform L a z)) := by
  exact tendsto_inwardRegularizedOddTwoEdgeTransform_zero L a (I * z)

theorem norm_inwardRegularizedXiOddTwoEdgeTransform_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (q : XiZeroCopy) :
    ‖inwardRegularizedXiOddTwoEdgeTransform L a epsilon (xiSpectralPoint q)‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) /
        ‖xiSpectralPoint q‖ := by
  have hz : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  simpa only [inwardRegularizedXiOddTwoEdgeTransform, norm_mul, norm_I, one_mul] using
    norm_inwardRegularizedOddTwoEdgeTransform_le L a hepsilon0 hepsilon1 hz
      (le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q))

theorem norm_inwardRegularizedXiOddTwoEdgePolarizationTerm_le
    (L a : ℝ) {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (q : XiZeroCopy) :
    ‖inwardRegularizedXiOddTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
        xiWeilSharp (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
          (xiSpectralPoint q)‖ ≤
      (2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let C : ℝ := 2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  have hq := norm_inwardRegularizedXiOddTwoEdgeTransform_le L a hepsilon0 hepsilon1 q
  have hqc := norm_inwardRegularizedXiOddTwoEdgeTransform_le L a hepsilon0 hepsilon1
    (xiZeroCopyLineConjEquiv q)
  have hsharp :
      ‖xiWeilSharp (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
          (xiSpectralPoint q)‖ ≤ C / ‖xiSpectralPoint q‖ := by
    rw [xiWeilSharp, norm_conj, ← xiSpectralPoint_lineConj]
    simpa only [C, xiSpectralPoint_lineConj, norm_conj] using hqc
  change ‖_ * _‖ ≤ C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)
  rw [norm_mul]
  calc
    _ ≤ (C / ‖xiSpectralPoint q‖) * (C / ‖xiSpectralPoint q‖) :=
      mul_le_mul hq hsharp (norm_nonneg _) (by positivity)
    _ = C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- Dominated convergence for the actual odd multiplicity-exact Xi--Weil energy. -/
theorem tendsto_xiWeilPolarization_inwardRegularizedOdd_zero (L a : ℝ) :
    Tendsto
      (fun epsilon : ℝ => xiWeilPolarization
        (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
        (inwardRegularizedXiOddTwoEdgeTransform L a epsilon))
      (𝓝[>] 0)
      (𝓝 (xiWeilPolarization
        (xiRectangularOddTwoEdgeTransform L a)
        (xiRectangularOddTwoEdgeTransform L a))) := by
  let C : ℝ := 2 * Real.exp (1 / 2) * (1 + Real.exp (|L| / 2)) * Real.exp (|a| / 2)
  have hsum : Summable (fun q : XiZeroCopy => C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left (C ^ 2)
  have hpoint (q : XiZeroCopy) : Tendsto
      (fun epsilon : ℝ =>
        inwardRegularizedXiOddTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
          xiWeilSharp (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
            (xiSpectralPoint q))
      (𝓝[>] 0)
      (𝓝 (xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q) *
        xiWeilSharp (xiRectangularOddTwoEdgeTransform L a) (xiSpectralPoint q))) := by
    have hleft : Tendsto
        (fun epsilon : ℝ =>
          inwardRegularizedXiOddTwoEdgeTransform L a epsilon (xiSpectralPoint q))
        (𝓝[>] 0) (𝓝 (xiRectangularOddTwoEdgeTransform L a (xiSpectralPoint q))) :=
      (tendsto_inwardRegularizedXiOddTwoEdgeTransform_zero
        L a (xiSpectralPoint q)).mono_left inf_le_left
    have hright0 : Tendsto
        (fun epsilon : ℝ => inwardRegularizedXiOddTwoEdgeTransform L a epsilon
          ((starRingEnd ℂ) (xiSpectralPoint q)))
        (𝓝[>] 0) (𝓝 (xiRectangularOddTwoEdgeTransform L a
          ((starRingEnd ℂ) (xiSpectralPoint q)))) :=
      (tendsto_inwardRegularizedXiOddTwoEdgeTransform_zero
        L a ((starRingEnd ℂ) (xiSpectralPoint q))).mono_left inf_le_left
    have hright := Complex.continuous_conj.continuousAt.tendsto.comp hright0
    simpa only [xiWeilSharp] using! hleft.mul hright
  have hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, ∀ q : XiZeroCopy,
      ‖inwardRegularizedXiOddTwoEdgeTransform L a epsilon (xiSpectralPoint q) *
          xiWeilSharp (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
            (xiSpectralPoint q)‖ ≤
        C ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have hupper : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon < 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (show ∀ᶠ epsilon : ℝ in 𝓝 0, epsilon < 1 from
          Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hupper] with epsilon he0 he1
    intro q
    exact norm_inwardRegularizedXiOddTwoEdgePolarizationTerm_le L a he0.le he1.le q
  simpa only [xiWeilPolarization] using
    tendsto_tsum_of_dominated_convergence hsum hpoint hbound

/-- Lossless variational passage from odd inward trials to the sharp odd value. -/
theorem sharp_xiOddWeilPolarization_ge_two_mul_length_mul_floor
    {L : ℝ} (hL : 0 < L) (a lambda : ℝ)
    (hvariational : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)
          (inwardRegularizedXiOddTwoEdgeTransform L a epsilon)).re) :
    2 * L * lambda ≤
      (xiWeilPolarization
        (xiRectangularOddTwoEdgeTransform L a)
        (xiRectangularOddTwoEdgeTransform L a)).re := by
  have hleft : Tendsto
      (fun epsilon : ℝ => lambda * inwardRegularizedTwoEdgeSquaredMass L epsilon)
      (𝓝[>] 0) (𝓝 (2 * L * lambda)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      tendsto_const_nhds.mul (tendsto_inwardRegularizedTwoEdgeSquaredMass_zero hL)
  have hright := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_xiWeilPolarization_inwardRegularizedOdd_zero L a)
  exact le_of_tendsto_of_tendsto hleft hright hvariational

/-- Negative magnitude of the sampled odd restricted-Weil floor. -/
def inwardRestrictedWeilOddNegativeFloor (lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  (lambda n)⁻

/-- **Odd-floor amplification.** False RH forces the negative odd restricted-Weil floor above
every subcritical transverse power at arbitrarily late logarithmic apertures. -/
theorem not_riemannHypothesis_implies_inwardRestrictedWeilOddFloor_cofinally_exceeds_power
    {L alpha : ℝ} (hL : 0 < L) (halpha0 : 0 ≤ alpha)
    (hRH : ¬RiemannHypothesis) (halpha : alpha < xiRightTransverseSup)
    {lambda : ℕ → ℝ}
    (hvariational : ∀ n : ℕ, ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      lambda n * inwardRegularizedTwoEdgeSquaredMass L epsilon ≤
        (xiWeilPolarization
          (inwardRegularizedXiOddTwoEdgeTransform L (Real.log n / 2) epsilon)
          (inwardRegularizedXiOddTwoEdgeTransform L (Real.log n / 2) epsilon)).re) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        C * (n : ℝ) ^ alpha < inwardRestrictedWeilOddNegativeFloor lambda n := by
  intro C hC N0
  obtain ⟨n, hn0, hLa, hodd⟩ :=
    not_riemannHypothesis_implies_oddRectangular_weil_cofinally_unbounded_below_power
      hL halpha0 hRH halpha (2 * L * C) (by positivity) N0
  have hsharp := sharp_xiOddWeilPolarization_ge_two_mul_length_mul_floor
    hL (Real.log n / 2) (lambda n) (hvariational n)
  refine ⟨n, hn0, hLa, ?_⟩
  rw [inwardRestrictedWeilOddNegativeFloor, negPart_def]
  apply lt_of_lt_of_le (b := -lambda n)
  · have hpow0 : 0 ≤ (n : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg n) alpha
    dsimp only [xiRectangularOddWeilLogCoefficient] at hodd
    nlinarith
  · exact le_max_left _ _

end

end RHTower
