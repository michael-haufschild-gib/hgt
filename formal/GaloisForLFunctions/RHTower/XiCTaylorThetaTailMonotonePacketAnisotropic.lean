import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMonotonePacketCurrent

/-!
# Anisotropic sublinearity of the recombined critical theta-tail packet

The monotone-profile contraction bounds the complete finite critical translate packet by the
squared norm of its final sum, without expanding or estimating any off-diagonal Hermitian cross
term.  Since an anisotropic mesh converges to a point of positive centered imaginary part, the
coefficient `2 / Im z` is bounded while the mesh scale grows linearly.  The resulting estimate is
uniform in the packet depth, which may therefore be chosen separately at every mesh point.

This module deliberately stops at the recombined packet value.  Replacing that value by the
canonical Xi Taylor section requires an additional exact source identity; a packetwise norm
comparison would lose the cancellations in the Taylor denominator.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Value of the complete finite critical logarithmic translate packet. -/
def criticalLogPhaseTailPacketValue (L : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    criticalLogPhaseCoefficient L j z *
      thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z

/-- Spectral derivative of the complete finite critical logarithmic translate packet. -/
def criticalLogPhaseTailPacketDerivative (L : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N,
    (criticalLogPhaseCoefficient L j z *
        thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
      criticalLogPhaseCoefficientDerivative L j z *
        thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)

/-- Oriented current of the complete finite critical logarithmic translate packet. -/
def criticalLogPhaseTailPacketCurrent (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  (criticalLogPhaseTailPacketDerivative L N z *
    (starRingEnd ℂ) (criticalLogPhaseTailPacketValue L N z)).im

/-- Pointwise aggregate current bound, stated in terms of the named final packet value. -/
theorem criticalLogPhaseTailPacketCurrent_le_two_div_im
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 < z.im) (N : ℕ) :
    criticalLogPhaseTailPacketCurrent L N z ≤
      (2 / z.im) * Complex.normSq (criticalLogPhaseTailPacketValue L N z) := by
  simpa only [criticalLogPhaseTailPacketCurrent, criticalLogPhaseTailPacketDerivative,
    criticalLogPhaseTailPacketValue] using
      criticalLogPhase_tail_packetCurrent_le_two_div_im hL hz N

/-- At positive depth the negative derivative of the recombined source profile is strictly
positive on the positive half-line. -/
theorem neg_criticalLogPhaseTranslatedDensityProfileDerivative_pos
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    0 < -criticalLogPhaseTranslatedDensityProfileDerivative L N t := by
  rw [neg_pos]
  unfold criticalLogPhaseTranslatedDensityProfileDerivative
  apply Finset.sum_neg
  · intro j _hj
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      (thetaCuspTailSecondDensityAtom_deriv_neg Nat.zero_lt_one
        (add_nonneg ht (mul_nonneg (Nat.cast_nonneg j) hL)))
  · exact ⟨0, Finset.mem_range.mpr hN⟩

/-- The completion integrand has strictly positive real part at every positive source point. -/
theorem positiveTailCompletion_profileIntegrand_re_pos
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : 0 < t) :
    0 < ((((
        -criticalLogPhaseTranslatedDensityProfileDerivative L N t : ℝ) : ℂ) *
      (1 - spectralTranslationPhase t z)).re) := by
  have hh : 0 < -criticalLogPhaseTranslatedDensityProfileDerivative L N t :=
    neg_criticalLogPhaseTranslatedDensityProfileDerivative_pos hL hN ht.le
  have hphase : (spectralTranslationPhase t z).re < 1 := by
    calc
      (spectralTranslationPhase t z).re ≤
          ‖spectralTranslationPhase t z‖ := Complex.re_le_norm _
      _ = Real.exp (-t * z.im) :=
        norm_spectralTranslationPhase_eq_exp_neg_mul_im t z
      _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_re, one_re]
  simpa only [sub_zero] using mul_pos hh (sub_pos.mpr hphase)

/-- The positive-tail completion of a nonempty recombined packet lies in the open right
half-plane.  This is the strict form of the contraction mechanism. -/
theorem positiveTailCompletion_neg_profileDerivative_re_pos
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) :
    0 < (positiveTailCompletion
      (fun t : ℝ => -criticalLogPhaseTranslatedDensityProfileDerivative L N t) z).re := by
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  let f : ℝ → ℂ := fun t =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have hf : Integrable f mu := by
    simpa only [f, h, mu] using
      integrableOn_neg_profileDerivative_mul_one_sub_phase hL N hz.le
  have hfre : Integrable (fun t => (f t).re) mu := hf.re
  have hnonneg : 0 ≤ᵐ[mu] fun t => (f t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (positiveTailCompletion_profileIntegrand_re_pos hL hN hz ht).le
  have hsupp : Ioi (0 : ℝ) ⊆ Function.support (fun t => (f t).re) := by
    intro t ht
    exact Function.mem_support.mpr
      (ne_of_gt (positiveTailCompletion_profileIntegrand_re_pos hL hN hz ht))
  have hmuPos : 0 < mu (Ioi (0 : ℝ)) := by
    simp [mu]
  have hsuppPos : 0 < mu (Function.support (fun t => (f t).re)) :=
    lt_of_lt_of_le hmuPos (measure_mono hsupp)
  have hintPos : 0 < ∫ t, (f t).re ∂mu :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hfre).2 hsuppPos
  have hre : (∫ t, (f t).re ∂mu) = (∫ t, f t ∂mu).re :=
    integral_re hf
  rw [hre] at hintPos
  simpa only [positiveTailCompletion, f, h, mu] using hintPos

/-- Every nonempty complete critical translate packet is zero-free in the open upper half-plane.
The proof uses the strict right-half-plane completion, not root data. -/
theorem criticalLogPhaseTailPacketValue_ne_zero
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) :
    criticalLogPhaseTailPacketValue L N z ≠ 0 := by
  let h : ℝ → ℝ := fun t =>
    -criticalLogPhaseTranslatedDensityProfileDerivative L N t
  have hpos := positiveTailCompletion_neg_profileDerivative_re_pos hL hN hz
  have hcompletion := positiveTailCompletion_neg_profileDerivative_eq hL N hz.le
  intro hzero
  have hzero' :
      (∑ j ∈ Finset.range N,
        criticalLogPhaseCoefficient L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z) = 0 := by
    simpa only [criticalLogPhaseTailPacketValue] using hzero
  have hvalue := criticalLogPhase_tail_packet_eq_translatedProfile hL hz.le N
  have hintegral :
      (∫ t : ℝ in Ioi 0,
        (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
          spectralTranslationPhase t z) = 0 := by
    rw [← hvalue]
    exact hzero'
  rw [hintegral] at hcompletion
  have : positiveTailCompletion h z = 0 := by
    simpa only [h, mul_zero] using hcompletion
  rw [this] at hpos
  simp only [zero_re, lt_self_iff_false] at hpos

/-- On any sequence whose imaginary parts converge to a positive limit, the complete packet
current is sublinear relative to the squared norm of its final sum.  The estimate is uniform in
the depth schedule `N`; in particular all internal off-diagonal currents remain recombined. -/
theorem eventually_criticalLogPhaseTailPacketCurrent_le_scaled_normSq
    {z : ℕ → ℂ} {eta : ℝ}
    (hz : Tendsto (fun n : ℕ => (z n).im) atTop (nhds eta))
    (heta : 0 < eta) {L : ℝ} (hL : 0 ≤ L) (N : ℕ → ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      criticalLogPhaseTailPacketCurrent L (N n) (z n) ≤
        (epsilon * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) := by
  have himLower : ∀ᶠ n : ℕ in atTop, eta / 2 < (z n).im :=
    hz.eventually (eventually_gt_nhds (by linarith))
  have hnat : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscale : ∀ᶠ n : ℕ in atTop,
      4 / eta < epsilon * (((n + 1 : ℕ) : ℝ)) := by
    have hgrow := hnat.atTop_mul_const hepsilon
    have hevent := hgrow.eventually_gt_atTop (4 / eta)
    simpa only [mul_comm] using hevent
  filter_upwards [himLower, hscale] with n him hn
  have himPos : 0 < (z n).im := (half_pos heta).trans him
  have hcoefficient : 2 / (z n).im ≤ 4 / eta := by
    calc
      2 / (z n).im ≤ 2 / (eta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (half_pos heta) him.le
      _ = 4 / eta := by field_simp; ring
  calc
    criticalLogPhaseTailPacketCurrent L (N n) (z n) ≤
        (2 / (z n).im) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      criticalLogPhaseTailPacketCurrent_le_two_div_im hL himPos (N n)
    _ ≤ (4 / eta) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      mul_le_mul_of_nonneg_right hcoefficient (Complex.normSq_nonneg _)
    _ ≤ (epsilon * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      mul_le_mul_of_nonneg_right hn.le (Complex.normSq_nonneg _)

/-- Strict sublinear form for a positive depth schedule.  Zero-freeness of the final recombined
packet value is proved above, so strictness does not assume the desired denominator property. -/
theorem eventually_criticalLogPhaseTailPacketCurrent_lt_scaled_normSq
    {z : ℕ → ℂ} {eta : ℝ}
    (hz : Tendsto (fun n : ℕ => (z n).im) atTop (nhds eta))
    (heta : 0 < eta) {L : ℝ} (hL : 0 ≤ L) (N : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      criticalLogPhaseTailPacketCurrent L (N n) (z n) <
        (epsilon * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) := by
  have himLower : ∀ᶠ n : ℕ in atTop, eta / 2 < (z n).im :=
    hz.eventually (eventually_gt_nhds (by linarith))
  have hnat : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hscale : ∀ᶠ n : ℕ in atTop,
      4 / eta < epsilon * (((n + 1 : ℕ) : ℝ)) := by
    have hgrow := hnat.atTop_mul_const hepsilon
    have hevent := hgrow.eventually_gt_atTop (4 / eta)
    simpa only [mul_comm] using hevent
  filter_upwards [himLower, hscale] with n him hn
  have himPos : 0 < (z n).im := (half_pos heta).trans him
  have hcoefficient : 2 / (z n).im ≤ 4 / eta := by
    calc
      2 / (z n).im ≤ 2 / (eta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (half_pos heta) him.le
      _ = 4 / eta := by field_simp; ring
  have hvaluePos :
      0 < Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) := by
    rw [Complex.normSq_pos]
    exact criticalLogPhaseTailPacketValue_ne_zero hL (hN n) himPos
  calc
    criticalLogPhaseTailPacketCurrent L (N n) (z n) ≤
        (2 / (z n).im) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      criticalLogPhaseTailPacketCurrent_le_two_div_im hL himPos (N n)
    _ ≤ (4 / eta) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      mul_le_mul_of_nonneg_right hcoefficient hvaluePos.le
    _ < (epsilon * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (criticalLogPhaseTailPacketValue L (N n) (z n)) :=
      mul_lt_mul_of_pos_right hn hvaluePos

end

end RHTower
