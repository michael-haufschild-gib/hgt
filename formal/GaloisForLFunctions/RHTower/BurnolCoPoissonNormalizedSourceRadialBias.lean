import GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalWindowIncidence
import GaloisForLFunctions.RHTower.CothInfra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Radial bias of normalized co-Poisson sources

The centered endpoint modulus is strictly increasing on positive horizontal
rays. Applied to the literal completed Mellin jets at an unchanged Xi divisor,
this gives a strict quantitative bias between the two normalized Hilbert
sources. Fourier transport retains both jet factors, and vanishing of the
normalized real polarization is exactly critical-line placement.
-/

open Real Set Complex
namespace RHTower
noncomputable section


/-- Strict hyperbolic endpoint inequality. -/
theorem burnolWindow_two_cosh_sub_one_lt_mul_sinh {a : ℝ} (ha : 0 < a) :
    2 * (Real.cosh a - 1) < a * Real.sinh a := by
  have hh : 0 < a / 2 := by positivity
  have hp := mul_pos (Real.sinh_pos_iff.mpr hh)
    (sub_pos.mpr (sinh_lt_mul_cosh hh))
  have he : 2 * (a / 2) = a := by ring
  have hs := Real.sinh_two_mul (x := a / 2)
  have hc := Real.cosh_two_mul (x := a / 2)
  rw [he] at hs hc
  rw [hs, hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq (a / 2)]

/-- The derivative numerator of the centered endpoint modulus is strictly positive. -/
theorem burnolWindow_cosh_cos_derivativeNumerator_pos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    0 < (a ^ (2 : ℕ) + b ^ (2 : ℕ)) * Real.sinh a - 2 * a * (Real.cosh a - Real.cos b) := by
  have hfirst := mul_pos ha
    (sub_pos.mpr (burnolWindow_two_cosh_sub_one_lt_mul_sinh ha))
  have hsecond := mul_nonneg (sq_nonneg b)
    (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr ha.le))
  have hcos := mul_nonneg ha.le
    (sub_nonneg.mpr (Real.one_sub_sq_div_two_le_cos (x := b)))
  nlinarith

/-- Removing the elementary exponential factor leaves a strictly increasing
endpoint modulus on every positive horizontal ray. -/
theorem burnolWindow_cosh_cos_quotient_strictMonoOn (b : ℝ) :
    StrictMonoOn (fun a : ℝ => (Real.cosh a - Real.cos b) / (a ^ (2 : ℕ) + b ^ (2 : ℕ)))
      (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro a ha
    have ha0 : 0 < a := ha
    have hd : a ^ (2 : ℕ) + b ^ (2 : ℕ) ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg b] : 0 < a^(2 : ℕ)+b^(2 : ℕ))
    exact ((Real.continuous_cosh.continuousAt.sub continuousAt_const).div
      ((continuousAt_id.pow 2).add continuousAt_const) hd).continuousWithinAt
  · intro a ha
    rw [interior_Ioi] at ha
    have ha0 : 0 < a := ha
    have hd : a ^ (2 : ℕ) + b ^ (2 : ℕ) ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg b] : 0 < a^(2 : ℕ)+b^(2 : ℕ))
    have hder : HasDerivAt
        (fun a : ℝ => (Real.cosh a - Real.cos b) / (a ^ (2 : ℕ) + b ^ (2 : ℕ)))
        (((a ^ (2 : ℕ) + b ^ (2 : ℕ)) * Real.sinh a - 2 * a * (Real.cosh a - Real.cos b)) /
          (a ^ (2 : ℕ) + b ^ (2 : ℕ)) ^ (2 : ℕ)) a := by
      apply (((Real.hasDerivAt_cosh a).sub_const (Real.cos b)).div
        (((hasDerivAt_id a).pow 2).add_const (b ^ (2 : ℕ))) hd).congr_deriv
      simp only [Pi.pow_apply, id_eq]
      ring
    rw [hder.deriv]
    exact div_pos (burnolWindow_cosh_cos_derivativeNumerator_pos ha b) (sq_pos_of_ne_zero hd)

/-- Exact squared modulus of the unit-length complex endpoint gauge. -/
theorem burnolWindow_norm_endpointGauge_sq (z : ℂ) :
    ‖(Complex.exp z - 1) / z‖ ^ (2 : ℕ) =
      2 * Real.exp z.re * ((Real.cosh z.re - Real.cos z.im) / (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ))) := by
  rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_sub,
    ← Complex.sq_norm (Complex.exp z), Complex.norm_exp]
  simp only [map_one, mul_one, Complex.exp_re]
  rw [Complex.normSq_apply]
  have he : Real.exp z.re * Real.exp (-z.re) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hn : Real.exp z.re ^ (2 : ℕ) + 1 - 2 * (Real.exp z.re * Real.cos z.im) =
      2 * Real.exp z.re * (Real.cosh z.re - Real.cos z.im) := by
    rw [Real.cosh_eq]
    nlinarith
  rw [hn]
  ring

/-- Positive horizontal motion increases the squared endpoint modulus
strictly faster than its elementary exponential factor. -/
theorem burnolWindow_endpointGauge_sq_strict_growth
    {z w : ℂ} (hz : 0 < z.re) (hzw : z.re < w.re) (hi : z.im = w.im) :
    Real.exp (w.re - z.re) * ‖(Complex.exp z - 1) / z‖ ^ (2 : ℕ) <
      ‖(Complex.exp w - 1) / w‖ ^ (2 : ℕ) := by
  have hw : 0 < w.re := hz.trans hzw
  have hq := burnolWindow_cosh_cos_quotient_strictMonoOn z.im hz hw hzw
  rw [hi] at hq
  rw [burnolWindow_norm_endpointGauge_sq, burnolWindow_norm_endpointGauge_sq, hi]
  have he : Real.exp (w.re - z.re) * Real.exp z.re = Real.exp w.re := by
    rw [← Real.exp_add, sub_add_cancel]
  have hp := mul_lt_mul_of_pos_left hq (by positivity : 0 < 2 * Real.exp w.re)
  calc
    _ = 2 * (Real.exp (w.re - z.re) * Real.exp z.re) *
        ((Real.cosh z.re - Real.cos w.im) / (z.re ^ (2 : ℕ) + w.im ^ (2 : ℕ))) := by ring
    _ = 2 * Real.exp w.re *
        ((Real.cosh z.re - Real.cos w.im) / (z.re ^ (2 : ℕ) + w.im ^ (2 : ℕ))) := by rw [he]
    _ < _ := hp

/-- Exact rescaling from arbitrary positive window length to the unit gauge. -/
theorem burnolWindow_norm_endpointGauge_scaled_sq
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.re) :
    ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) =
      L ^ (2 : ℕ) * ‖(Complex.exp ((L : ℂ) * z) - 1) / ((L : ℂ) * z)‖ ^ (2 : ℕ) := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hzc : z ≠ 0 := by intro h; simp [h] at hz
  have he : (Complex.exp ((L : ℂ) * z) - 1) / z =
      (L : ℂ) * ((Complex.exp ((L : ℂ) * z) - 1) / ((L : ℂ) * z)) := by
    field_simp
  rw [he, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]

/-- The normalization bias is quantitative at every positive physical window length. -/
theorem burnolWindow_endpointGauge_scaled_sq_strict_growth
    {L : ℝ} (hL : 0 < L) {z w : ℂ}
    (hz : 0 < z.re) (hzw : z.re < w.re) (hi : z.im = w.im) :
    Real.exp (L * (w.re - z.re)) *
        ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) <
      ‖(Complex.exp ((L : ℂ) * w) - 1) / w‖ ^ (2 : ℕ) := by
  have hr (v : ℂ) : ((L : ℂ) * v).re = L * v.re := by simp
  have him : ((L : ℂ) * z).im = ((L : ℂ) * w).im := by simp [hi]
  have hs := burnolWindow_endpointGauge_sq_strict_growth
    (z := (L : ℂ) * z) (w := (L : ℂ) * w)
    (by rw [hr]; exact mul_pos hL hz)
    (by rw [hr, hr]; exact mul_lt_mul_of_pos_left hzw hL) him
  rw [hr, hr, ← mul_sub] at hs
  rw [burnolWindow_norm_endpointGauge_scaled_sq hL hz,
    burnolWindow_norm_endpointGauge_scaled_sq hL (hz.trans hzw)]
  nlinarith [mul_lt_mul_of_pos_left hs (sq_pos_of_pos hL)]

/-- Complex conjugation of the gauge changes no squared amplitude. -/
theorem burnolWindow_endpointGauge_conj_sq (L : ℝ) (z : ℂ) :
    ‖(Complex.exp ((L : ℂ) * starRingEnd ℂ z) - 1) / starRingEnd ℂ z‖ ^ (2 : ℕ) =
      ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) := by
  have he : (Complex.exp ((L : ℂ) * starRingEnd ℂ z) - 1) / starRingEnd ℂ z =
      starRingEnd ℂ ((Complex.exp ((L : ℂ) * z) - 1) / z) := by
    simp only [map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal]
  rw [he, Complex.norm_conj]

/-- Strict ordering of endpoint amplitudes along a positive horizontal ray. -/
theorem burnolWindow_endpointGauge_scaled_sq_lt
    {L : ℝ} (hL : 0 < L) {z w : ℂ}
    (hz : 0 < z.re) (hzw : z.re < w.re) (hi : z.im = w.im) :
    ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) <
      ‖(Complex.exp ((L : ℂ) * w) - 1) / w‖ ^ (2 : ℕ) := by
  have he : 1 ≤ Real.exp (L * (w.re - z.re)) :=
    Real.one_le_exp (mul_nonneg hL.le (sub_nonneg.mpr hzw.le))
  have hmul := mul_le_mul_of_nonneg_right he
    (sq_nonneg ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖)
  simp only [one_mul] at hmul
  exact hmul.trans_lt (burnolWindow_endpointGauge_scaled_sq_strict_growth hL hz hzw hi)

/-- Equal reflected endpoint amplitudes occur precisely at the center of the open strip. -/
theorem burnolWindow_endpointGauge_reflection_sq_eq_iff
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    (‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) =
      ‖(Complex.exp ((L : ℂ) * (1 - z)) - 1) / (1 - z)‖ ^ (2 : ℕ)) ↔ z.re = 1 / 2 := by
  let w := starRingEnd ℂ (1 - z)
  have hwre : w.re = 1 - z.re := by simp [w]
  have hwim : w.im = z.im := by simp [w]
  have hw0 : 0 < w.re := by rw [hwre]; linarith
  have hnorm := burnolWindow_endpointGauge_conj_sq L (1 - z)
  change ‖(Complex.exp ((L : ℂ) * w) - 1) / w‖ ^ (2 : ℕ) = _ at hnorm
  rw [← hnorm]
  constructor
  · intro heq
    rcases lt_trichotomy z.re w.re with hlt | he | hgt
    · exact False.elim ((ne_of_lt (burnolWindow_endpointGauge_scaled_sq_lt
        hL hz0 hlt hwim.symm)) heq)
    · rw [hwre] at he
      linarith
    · exact False.elim ((ne_of_lt (burnolWindow_endpointGauge_scaled_sq_lt
        hL hw0 hgt hwim)) heq.symm)
  · intro hline
    have he : z = w := by
      apply Complex.ext
      · rw [hwre, hline]; ring
      · exact hwim.symm
    rw [he]

/-- The literal first nonzero Gamma-completed jet of the original window. -/
def burnolWindowCompletedTopJet (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : ℂ :=
  iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
    (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ)

/-- The same-order literal jet of its actual Fourier partner, at the original divisor. -/
def burnolWindowFourierCompletedTopJet (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : ℂ :=
  iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
    (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le) (rho : ℂ)

/-- Both source normalization factors are nonzero at every actual Xi divisor. -/
theorem burnolWindowCompletedTopJets_ne_zero
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolWindowCompletedTopJet L hL rho ≠ 0 ∧
      burnolWindowFourierCompletedTopJet L hL rho ≠ 0 := by
  exact ⟨iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_ne_zero L hL rho,
    iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation_ne_zero hL rho⟩

/-- Equality of the two actual completed normalization amplitudes is already
exact critical-line placement. -/
theorem burnolWindowCompletedTopJets_norm_eq_iff
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    ‖burnolWindowCompletedTopJet L hL rho‖ =
      ‖burnolWindowFourierCompletedTopJet L hL rho‖ ↔ (rho : ℂ).re = 1 / 2 := by
  have hC : mellinCompletionFactor (rho : ℂ) *
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) ≠ 0 :=
    mul_ne_zero (mellinCompletionFactor_ne_zero (xi_divisor_support_re_mem_open_unit rho).1)
      (iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    burnolWindowCompletedTopJet, burnolWindowFourierCompletedTopJet,
    iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq hL,
    iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hL rho le_rfl,
    norm_mul (mellinCompletionFactor (rho : ℂ) *
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ)),
    norm_mul (mellinCompletionFactor (rho : ℂ) *
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ)),
    mul_pow, mul_pow,
    mul_right_inj' (pow_ne_zero 2 (norm_ne_zero_iff.mpr hC))]
  exact burnolWindow_endpointGauge_reflection_sq_eq_iff hL
    (xi_divisor_support_re_mem_open_unit rho).1 (xi_divisor_support_re_mem_open_unit rho).2

/-- On the strict right half of the strip, the actual normalization bias
exceeds the physical exponential gain, with the original conormal retained. -/
theorem burnolWindowCompletedTopJets_strict_radial_bias
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) (hr : 1 / 2 < (rho : ℂ).re) :
    Real.exp (L * (2 * (rho : ℂ).re - 1)) *
        ‖burnolWindowFourierCompletedTopJet L hL rho‖ ^ (2 : ℕ) <
      ‖burnolWindowCompletedTopJet L hL rho‖ ^ (2 : ℕ) := by
  let z : ℂ := starRingEnd ℂ (1 - (rho : ℂ))
  have hzre : z.re = 1 - (rho : ℂ).re := by simp [z]
  have hzim : z.im = (rho : ℂ).im := by simp [z]
  have hz0 : 0 < z.re := by rw [hzre]; linarith [(xi_divisor_support_re_mem_open_unit rho).2]
  have hzr : z.re < (rho : ℂ).re := by rw [hzre]; linarith
  have hs := burnolWindow_endpointGauge_scaled_sq_strict_growth hL hz0 hzr hzim
  have hnorm := burnolWindow_endpointGauge_conj_sq L (1 - (rho : ℂ))
  change ‖(Complex.exp ((L : ℂ) * z) - 1) / z‖ ^ (2 : ℕ) = _ at hnorm
  rw [hnorm, hzre, show (rho : ℂ).re - (1 - (rho : ℂ).re) =
    2 * (rho : ℂ).re - 1 by ring] at hs
  have hC : mellinCompletionFactor (rho : ℂ) *
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho) riemannZeta (rho : ℂ) ≠ 0 :=
    mul_ne_zero (mellinCompletionFactor_ne_zero (xi_divisor_support_re_mem_open_unit rho).1)
      (iteratedDeriv_riemannZeta_ne_zero_at_burnolCoPoissonXiConormalOrder rho)
  rw [burnolWindowCompletedTopJet, burnolWindowFourierCompletedTopJet,
    iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq hL,
    iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hL rho le_rfl,
    norm_mul, norm_mul, mul_pow, mul_pow]
  have hp := mul_lt_mul_of_pos_left hs (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hC))
  simp only [norm_mul, mul_pow] at hp ⊢
  nlinarith

/-- The actual original source normalized by its first nonzero completed jet. -/
def burnolJetNormalizedWindowSource
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : evenSubspace :=
  (burnolWindowCompletedTopJet L hL rho)⁻¹ •
    coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith))

/-- The actual Fourier source normalized by its own first nonzero completed jet. -/
def burnolJetNormalizedFourierWindowSource
    (L : ℝ) (hL : 0 < L) (rho : XiDivisorSupport) : evenSubspace :=
  (burnolWindowFourierCompletedTopJet L hL rho)⁻¹ •
    soninCosineUnitary (coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith)))

/-- The literal normalized source relation retains both conormal factors. -/
theorem burnolJetNormalizedWindowSource_weighted_fourier
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    burnolWindowCompletedTopJet L hL rho •
        soninCosineUnitary (burnolJetNormalizedWindowSource L hL rho) =
      burnolWindowFourierCompletedTopJet L hL rho •
        burnolJetNormalizedFourierWindowSource L hL rho := by
  obtain ⟨hJ, hK⟩ := burnolWindowCompletedTopJets_ne_zero hL rho
  simp only [burnolJetNormalizedWindowSource, burnolJetNormalizedFourierWindowSource,
    map_smul, smul_smul, mul_inv_cancel₀ hJ, mul_inv_cancel₀ hK, one_smul]

/-- Actual source norms divide by their respective conormal amplitudes. -/
theorem burnolJetNormalizedWindowSource_norms
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    let f := coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith : -L ≤ 0))
    ‖burnolJetNormalizedWindowSource L hL rho‖ =
        ‖f‖ / ‖burnolWindowCompletedTopJet L hL rho‖ ∧
      ‖burnolJetNormalizedFourierWindowSource L hL rho‖ =
        ‖f‖ / ‖burnolWindowFourierCompletedTopJet L hL rho‖ := by
  dsimp only
  constructor
  · simp only [burnolJetNormalizedWindowSource, norm_smul, norm_inv, div_eq_mul_inv]
    ring
  · simp only [burnolJetNormalizedFourierWindowSource, norm_smul, norm_inv,
      soninCosineUnitary.norm_map, div_eq_mul_inv]
    ring

/-- Hilbert norm preservation after the two actual jet normalizations is
already exactly the critical-line condition. -/
theorem burnolJetNormalizedWindowSource_norm_eq_iff
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    ‖burnolJetNormalizedWindowSource L hL rho‖ =
      ‖burnolJetNormalizedFourierWindowSource L hL rho‖ ↔ (rho : ℂ).re = 1 / 2 := by
  have hf := coPoissonSubWindowEven_ne_zero (Real.exp_pos (-L))
    (Real.exp_lt_one_iff.mpr (by linarith : -L < 0))
  have hfn := norm_ne_zero_iff.mpr hf
  obtain ⟨hX, hY⟩ := burnolJetNormalizedWindowSource_norms hL rho
  rw [hX, hY, div_eq_mul_inv, div_eq_mul_inv, mul_right_inj' hfn, inv_inj]
  exact burnolWindowCompletedTopJets_norm_eq_iff hL rho

/-- Strict quantitative Hilbert energy bias of the actual normalized source pair. -/
theorem burnolJetNormalizedWindowSource_strict_radial_bias
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) (hr : 1 / 2 < (rho : ℂ).re) :
    Real.exp (L * (2 * (rho : ℂ).re - 1)) *
        ‖burnolJetNormalizedWindowSource L hL rho‖ ^ (2 : ℕ) <
      ‖burnolJetNormalizedFourierWindowSource L hL rho‖ ^ (2 : ℕ) := by
  have hf := coPoissonSubWindowEven_ne_zero (Real.exp_pos (-L))
    (Real.exp_lt_one_iff.mpr (by linarith : -L < 0))
  have hfpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hf)
  obtain ⟨hJ, hK⟩ := burnolWindowCompletedTopJets_ne_zero hL rho
  have hJpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hJ)
  have hKpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hK)
  obtain ⟨hX, hY⟩ := burnolJetNormalizedWindowSource_norms hL rho
  rw [hX, hY, div_pow, div_pow, ← mul_div_assoc,
    div_lt_div_iff₀ hJpos hKpos]
  have hs := mul_lt_mul_of_pos_left
    (burnolWindowCompletedTopJets_strict_radial_bias hL rho hr) hfpos
  nlinarith

open scoped InnerProductSpace

/-- The actual real polarized pairing after jet normalization vanishes
exactly on the critical line. -/
theorem burnolJetNormalizedWindowSource_real_polarization_eq_zero_iff
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    (⟪burnolJetNormalizedWindowSource L hL rho +
        burnolJetNormalizedFourierWindowSource L hL rho,
      burnolJetNormalizedWindowSource L hL rho -
        burnolJetNormalizedFourierWindowSource L hL rho⟫_ℂ).re = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  letI : InnerProductSpace ℝ evenSubspace := InnerProductSpace.rclikeToReal ℂ evenSubspace
  exact (real_inner_add_sub_eq_zero_iff
    (burnolJetNormalizedWindowSource L hL rho)
    (burnolJetNormalizedFourierWindowSource L hL rho)).trans
      (burnolJetNormalizedWindowSource_norm_eq_iff hL rho)

/-- Before normalization, Fourier unitarity gives literal real orthogonality
for the same original source at every logarithmic window length. -/
theorem burnolWindowSource_real_fourier_polarization_zero
    {L : ℝ} (hL : 0 < L) :
    let f := coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith : -L ≤ 0))
    (⟪f + soninCosineUnitary f, f - soninCosineUnitary f⟫_ℂ).re = 0 := by
  letI : InnerProductSpace ℝ evenSubspace := InnerProductSpace.rclikeToReal ℂ evenSubspace
  let f := coPoissonSubWindowEven (Real.exp_pos (-L))
    (Real.exp_le_one_iff.mpr (by linarith : -L ≤ 0))
  exact (real_inner_add_sub_eq_zero_iff f (soninCosineUnitary f)).2
    (soninCosineUnitary.norm_map f).symm

end
end RHTower
