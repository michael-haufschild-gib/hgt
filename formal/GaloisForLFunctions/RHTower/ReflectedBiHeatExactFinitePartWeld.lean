import GaloisForLFunctions.RHTower.ReflectedBiHeatFullWindowSingularFinitePart
import GaloisForLFunctions.RHTower.ReflectedBiHeatPhaseFinitePartExpansion
import GaloisForLFunctions.RHTower.ReflectedBiHeatRegulatorRemainderContinuity
import GaloisForLFunctions.RHTower.PolarizedAdditiveHeatSharpPrincipal
import GaloisForLFunctions.RHTower.HeatMomentParameterContinuity

/-!
# Exact reflected bi-heat finite-part weld

This module identifies the canonical row-subtraction finite part with the exact five-channel
Jonquière phase finite part.  The proof compares the two descriptions at positive real regulator,
then passes to the regulator origin using the pole-filled singular derivative and continuity of
the two cross moments, regular product, and sharp remainder.
-/

open Complex Filter Set Topology MeasureTheory Metric

namespace RHTower

noncomputable section

theorem star_jonquiereLead_conj (b : ℂ) :
    (starRingEnd ℂ) (jonquiereLead ((starRingEnd ℂ) b)) =
      jonquiereLeadNeg b := by
  rw [jonquiereLead, jonquiereLeadNeg, map_mul,
    ← Complex.Gamma_conj, ← Complex.exp_conj]
  congr 1
  · simp
  · simp
    rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
      exact map_ofNat (starRingEnd ℂ) 2]

theorem star_jonquiereLeadNeg_conj (b : ℂ) :
    (starRingEnd ℂ) (jonquiereLeadNeg ((starRingEnd ℂ) b)) =
      jonquiereLead b := by
  rw [jonquiereLead, jonquiereLeadNeg, map_mul,
    ← Complex.Gamma_conj, ← Complex.exp_conj]
  congr 1
  · simp
  · simp
    rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
      exact map_ofNat (starRingEnd ℂ) 2]

/-- The polarized leading coefficient becomes the reflected Gamma coefficient under complementary
symmetric regulation. -/
theorem polarizedHeatLeadingCoefficient_reflected (z epsilon : ℂ) :
    polarizedHeatLeadingCoefficient (z + epsilon / 2)
        ((starRingEnd ℂ) (1 - z + epsilon / 2)) =
      reflectedGammaCoefficient z epsilon := by
  have hcos :
      Complex.cos ((Real.pi : ℂ) * (1 - 2 * z) / 2) =
        (Complex.exp ((Real.pi : ℂ) * I * (1 - (z + epsilon / 2)) / 2) *
              Complex.exp (-(Real.pi : ℂ) * I *
                (1 - (1 - z + epsilon / 2)) / 2) +
            Complex.exp (-(Real.pi : ℂ) * I *
                (1 - (z + epsilon / 2)) / 2) *
              Complex.exp ((Real.pi : ℂ) * I *
                (1 - (1 - z + epsilon / 2)) / 2)) / 2 := by
    rw [Complex.cos, ← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> ring_nf
  have hshift :
      Complex.cos ((Real.pi : ℂ) * (1 - 2 * z) / 2) =
        Complex.sin ((Real.pi : ℂ) * z) := by
    rw [show ((Real.pi : ℂ) * (1 - 2 * z) / 2) =
      (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * z by ring]
    exact Complex.cos_pi_div_two_sub _
  rw [polarizedHeatLeadingCoefficient,
    star_jonquiereLead_conj, star_jonquiereLeadNeg_conj]
  simp only [jonquiereLead, jonquiereLeadNeg]
  rw [reflectedGammaCoefficient]
  rw [show 1 - (z + epsilon / 2) =
      (1 - z) + epsilon * (-(1 / 2)) by ring,
    show 1 - (1 - z + epsilon / 2) =
      z + epsilon * (-(1 / 2)) by ring]
  rw [← hshift, hcos]
  ring

/-- Exact four principal channels at positive real symmetric regulator. -/
noncomputable def reflectedBiHeatRegulatedPrincipal
    (P : ReflectedBiHeatRegulator) (epsilon : ℝ) : ℂ :=
  reflectedGammaCoefficient P.z (epsilon : ℂ) *
      heatMoment P.x ((epsilon : ℂ) - 1) +
    ((jonquiereLead (P.z + (epsilon : ℂ) / 2) +
        jonquiereLeadNeg (P.z + (epsilon : ℂ) / 2)) / 2 *
      riemannZeta (1 - P.z + (epsilon : ℂ) / 2)) *
        heatMoment P.x (P.z - 1 + (epsilon : ℂ) / 2) +
    (riemannZeta (P.z + (epsilon : ℂ) / 2) *
      ((jonquiereLead (1 - P.z + (epsilon : ℂ) / 2) +
        jonquiereLeadNeg (1 - P.z + (epsilon : ℂ) / 2)) / 2)) *
        heatMoment P.x (-P.z + (epsilon : ℂ) / 2) +
    riemannZeta (P.z + (epsilon : ℂ) / 2) *
      riemannZeta (1 - P.z + (epsilon : ℂ) / 2)

theorem polarizedHeatPrincipal_reflected_eq
    (P : ReflectedBiHeatRegulator) (epsilon : ℝ) :
    polarizedHeatPrincipal (P.z + (epsilon : ℂ) / 2)
        ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x =
      reflectedBiHeatRegulatedPrincipal P epsilon := by
  rw [polarizedHeatPrincipal, reflectedBiHeatRegulatedPrincipal,
    polarizedHeatLeadingCoefficient_reflected]
  rw [star_jonquiereLead_conj, star_jonquiereLeadNeg_conj,
    riemannZeta_conj]
  simp only [Complex.conj_conj]
  rw [show P.z + (epsilon : ℂ) / 2 +
        (1 - P.z + (epsilon : ℂ) / 2) - 2 =
      (epsilon : ℂ) - 1 by ring,
    show P.z + (epsilon : ℂ) / 2 - 1 =
      P.z - 1 + (epsilon : ℂ) / 2 by ring,
    show 1 - P.z + (epsilon : ℂ) / 2 - 1 =
      -P.z + (epsilon : ℂ) / 2 by ring]
  ring

/-- Exact phase-side finite part after replacing the Gaussian singular anomaly by the canonical
full-window singular finite part. -/
noncomputable def reflectedBiHeatExactPhaseFinitePart
    (P : ReflectedBiHeatRegulator) : ℂ :=
  reflectedFullWindowSingularFinitePart P +
    reflectedBiHeatLeftRawCoefficient P.z * heatMoment P.x (P.z - 1) +
    reflectedBiHeatRightRawCoefficient P.z * heatMoment P.x (-P.z) +
    riemannZeta P.z * riemannZeta (1 - P.z) +
    reflectedBiHeatSharpRemainder P P.x

/-- A complex derivative restricts to the same difference quotient on the positive real ray. -/
theorem hasDerivAt_tendsto_ofReal_slope_zero_right
    {f : ℂ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    Tendsto (fun x : ℝ => (f (x : ℂ) - f 0) / (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 f') := by
  have hofReal : Tendsto (fun x : ℝ => (x : ℂ))
      (𝓝[>] (0 : ℝ)) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact hx.ne'
  have hslope := h.tendsto_slope_zero.comp hofReal
  simpa [Function.comp_def, div_eq_inv_mul, mul_comm] using hslope

/-- The exact full-window singular channel, after subtraction of its theta residue, converges to
the derivative-defined finite part. -/
theorem tendsto_reflectedFullWindowSingular_sub_thetaPole
    (P : ReflectedBiHeatRegulator) :
    Tendsto (fun epsilon : ℝ =>
      reflectedGammaCoefficient P.z (epsilon : ℂ) *
          heatMoment P.x ((epsilon : ℂ) - 1) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedFullWindowSingularFinitePart P)) := by
  have hslope := hasDerivAt_tendsto_ofReal_slope_zero_right
    (differentiableAt_reflectedFullWindowSingularPoleUnit_zero P).hasDerivAt
  rw [← reflectedFullWindowSingularFinitePart] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  have hepsilon0 : 0 < epsilon := hepsilon
  rw [reflectedFullWindowSingularPoleUnit_eq_mul P (by simpa using hepsilon0),
    reflectedFullWindowSingularPoleUnit_zero]
  field_simp [hepsilon0.ne']

/-- The exact principal phase channels, together with the sharp remainder, have the canonical
full-window finite part at regulator zero. -/
theorem tendsto_reflectedBiHeatRegulatedPrincipal_sub_thetaPole
    (P : ReflectedBiHeatRegulator) :
    Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatRegulatedPrincipal P epsilon +
          polarizedHeatSharpRemainder
            (P.z + (epsilon : ℂ) / 2)
            ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatExactPhaseFinitePart P)) := by
  have hsOrder : Tendsto (fun epsilon : ℝ => P.z + (epsilon : ℂ) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 P.z) := by
    have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add (hepsilon.div_const 2)
  have hrOrder : Tendsto (fun epsilon : ℝ => 1 - P.z + (epsilon : ℂ) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - P.z)) := by
    have hepsilon : Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.add (hepsilon.div_const 2) :
      Tendsto (fun epsilon : ℝ => (1 - P.z) + (epsilon : ℂ) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 - P.z) + 0 / 2)))
  have hr₀ : 0 < (1 - P.z).re := by simp; linarith [P.z_re_lt_one]
  have hr₁ : (1 - P.z).re < 1 := by simp; linarith [P.z_re_pos]
  have hzetaS : Tendsto (fun epsilon : ℝ =>
      riemannZeta (P.z + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (riemannZeta P.z)) := by
    exact ((differentiableAt_riemannZeta (by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
      linarith [P.z_re_lt_one])).continuousAt.tendsto).comp hsOrder
  have hzetaR : Tendsto (fun epsilon : ℝ =>
      riemannZeta (1 - P.z + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (riemannZeta (1 - P.z))) := by
    exact ((differentiableAt_riemannZeta (by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
      linarith [P.z_re_pos])).continuousAt.tendsto).comp hrOrder
  have hleadS :=
    (continuousAt_jonquiereLead_of_openStrip P.z_re_pos P.z_re_lt_one).tendsto.comp
      hsOrder
  have hleadNegS :=
    (continuousAt_jonquiereLeadNeg_of_openStrip P.z_re_pos P.z_re_lt_one).tendsto.comp
      hsOrder
  have hleadR :=
    (continuousAt_jonquiereLead_of_openStrip hr₀ hr₁).tendsto.comp hrOrder
  have hleadNegR :=
    (continuousAt_jonquiereLeadNeg_of_openStrip hr₀ hr₁).tendsto.comp hrOrder
  have hleftCoeff : Tendsto (fun epsilon : ℝ =>
      ((jonquiereLead (P.z + (epsilon : ℂ) / 2) +
          jonquiereLeadNeg (P.z + (epsilon : ℂ) / 2)) / 2) *
        riemannZeta (1 - P.z + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatLeftRawCoefficient P.z)) := by
    simpa [reflectedBiHeatLeftRawCoefficient] using
      ((hleadS.add hleadNegS).div_const 2).mul hzetaR
  have hrightCoeff : Tendsto (fun epsilon : ℝ =>
      riemannZeta (P.z + (epsilon : ℂ) / 2) *
        ((jonquiereLead (1 - P.z + (epsilon : ℂ) / 2) +
          jonquiereLeadNeg (1 - P.z + (epsilon : ℂ) / 2)) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatRightRawCoefficient P.z)) := by
    simpa [reflectedBiHeatRightRawCoefficient] using
      hzetaS.mul ((hleadR.add hleadNegR).div_const 2)
  have hleftMoment : Tendsto (fun epsilon : ℝ =>
      heatMoment P.x (P.z - 1 + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (heatMoment P.x (P.z - 1))) := by
    exact tendsto_heatMoment_add_real_half (by simp; linarith [P.z_re_pos]) P.x_pos
  have hrightMoment : Tendsto (fun epsilon : ℝ =>
      heatMoment P.x (-P.z + (epsilon : ℂ) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (heatMoment P.x (-P.z))) := by
    exact tendsto_heatMoment_add_real_half (by simp; linarith [P.z_re_lt_one]) P.x_pos
  have hsingular := tendsto_reflectedFullWindowSingular_sub_thetaPole P
  have hleft := hleftCoeff.mul hleftMoment
  have hright := hrightCoeff.mul hrightMoment
  have hregular := hzetaS.mul hzetaR
  have hremainder := tendsto_reflectedBiHeatSharpRemainder_realRegulator P
  have hsum := ((((hsingular.add hleft).add hright).add hregular).add hremainder)
  have hsum' : Tendsto (fun epsilon : ℝ =>
      (reflectedGammaCoefficient P.z (epsilon : ℂ) *
          heatMoment P.x ((epsilon : ℂ) - 1) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ)) +
      (((jonquiereLead (P.z + (epsilon : ℂ) / 2) +
          jonquiereLeadNeg (P.z + (epsilon : ℂ) / 2)) / 2 *
        riemannZeta (1 - P.z + (epsilon : ℂ) / 2)) *
          heatMoment P.x (P.z - 1 + (epsilon : ℂ) / 2)) +
      ((riemannZeta (P.z + (epsilon : ℂ) / 2) *
        ((jonquiereLead (1 - P.z + (epsilon : ℂ) / 2) +
          jonquiereLeadNeg (1 - P.z + (epsilon : ℂ) / 2)) / 2)) *
          heatMoment P.x (-P.z + (epsilon : ℂ) / 2)) +
      riemannZeta (P.z + (epsilon : ℂ) / 2) *
        riemannZeta (1 - P.z + (epsilon : ℂ) / 2) +
      polarizedHeatSharpRemainder
        (P.z + (epsilon : ℂ) / 2)
        ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x)
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatExactPhaseFinitePart P)) := by
    simpa [reflectedBiHeatExactPhaseFinitePart] using hsum
  refine hsum'.congr' ?_
  filter_upwards with epsilon
  rw [reflectedBiHeatRegulatedPrincipal]
  ring

/-- At every sufficiently small positive real regulator, the row sum is exactly the regulated
principal phase model plus its sharp subtracted remainder. -/
theorem reflectedBiHeatPairSum_eq_regulatedPrincipal_add_remainder
    (P : ReflectedBiHeatRegulator) {epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hzLeft : epsilon / 2 < P.z.re)
    (hzRight : P.z.re < 1 - epsilon / 2) :
    reflectedBiHeatPairSum P.toDatum (epsilon : ℂ) =
      reflectedBiHeatRegulatedPrincipal P epsilon +
        polarizedHeatSharpRemainder
          (P.z + (epsilon : ℂ) / 2)
          ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x := by
  let Q : ReflectedBiHeatPositiveSlice :=
    { delta := epsilon
      x := P.x
      delta_pos := hepsilon0
      delta_lt_one := hepsilon1
      x_pos := P.x_pos }
  have hz : P.z ∈ Q.domain := by
    exact ⟨by simpa [Q] using hzLeft, by simpa [Q] using hzRight⟩
  have hleft₀ : 0 < (Q.leftOrder P.z).re := by
    rw [ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re]
    linarith [hepsilon0, P.z_re_pos]
  have hleft₁ : (Q.leftOrder P.z).re < 1 := by
    rw [ReflectedBiHeatPositiveSlice.leftOrder]
    norm_num [Complex.add_re, Complex.div_re]
    linarith [hzRight]
  have hright₀ : 0 < (Q.rightOrder P.z).re := by
    rw [ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
    linarith [hepsilon0, P.z_re_lt_one]
  have hright₁ : (Q.rightOrder P.z).re < 1 := by
    rw [ReflectedBiHeatPositiveSlice.rightOrder]
    norm_num [Complex.sub_re, Complex.add_re, Complex.div_re]
    linarith [hzLeft]
  have hsum : 1 < (Q.leftOrder P.z).re +
      ((starRingEnd ℂ) (Q.rightOrder P.z)).re := by
    simp only [Complex.conj_re]
    rw [← Complex.add_re, Q.leftOrder_add_rightOrder]
    norm_num [Q]
    linarith
  have hpairFixed : reflectedBiHeatPairSum P.toDatum (epsilon : ℂ) =
      reflectedBiHeatFixedRegulatorSum Q P.z := by
    rw [reflectedBiHeatPairSum, reflectedBiHeatFixedRegulatorSum]
    calc
      (∑' p : ℕ × ℕ,
          asymmetricHeatPairTerm (P.toDatum.leftOrder (epsilon : ℂ))
            (P.toDatum.rightOrder (epsilon : ℂ)) P.toDatum.x p) =
          ∑' p : ℕ × ℕ,
            asymmetricHeatPairTerm (Q.leftOrder P.z) (Q.rightOrder P.z) Q.x p := by
              apply tsum_congr
              intro p
              rfl
      _ = ∑' q : (ℕ × ℕ) ⊕ (ℕ × ℕ),
          asymmetricHeatPairTerm (Q.leftOrder P.z) (Q.rightOrder P.z) Q.x
            (upperLowerNatPairEquiv q) := by
              exact (Equiv.tsum_eq upperLowerNatPairEquiv
                (asymmetricHeatPairTerm (Q.leftOrder P.z) (Q.rightOrder P.z) Q.x)).symm
      _ = _ := by rfl
  calc
    reflectedBiHeatPairSum P.toDatum (epsilon : ℂ) =
        reflectedBiHeatFixedRegulatorSum Q P.z := hpairFixed
    _ = reflectedBiHeatFixedRegulatorPhaseEnergy Q P.z :=
      (reflectedBiHeatFixedRegulatorPhaseEnergy_eq_sum Q hz).symm
    _ = polarizedHeatEnergy (Q.leftOrder P.z)
        ((starRingEnd ℂ) (Q.rightOrder P.z)) Q.x :=
      reflectedBiHeatFixedRegulatorPhaseEnergy_eq_polarized Q P.z hright₀
    _ = polarizedHeatPrincipal (Q.leftOrder P.z)
          ((starRingEnd ℂ) (Q.rightOrder P.z)) Q.x +
        polarizedHeatSharpRemainder (Q.leftOrder P.z)
          ((starRingEnd ℂ) (Q.rightOrder P.z)) Q.x :=
      polarizedHeatEnergy_eq_principal_add_sharpRemainder
        hleft₀ hleft₁ (by simpa using hright₀) (by simpa using hright₁) hsum P.x_pos
    _ = _ := by
      rw [show Q.leftOrder P.z = P.z + (epsilon : ℂ) / 2 by rfl,
        show Q.rightOrder P.z = 1 - P.z + (epsilon : ℂ) / 2 by rfl,
        polarizedHeatPrincipal_reflected_eq]

/-- Canonical row subtraction and exact phase finite-part extraction give the same value. -/
theorem reflectedBiHeatFinitePart_eq_exactPhase
    (P : ReflectedBiHeatRegulator) :
    reflectedBiHeatFinitePart P.toDatum = reflectedBiHeatExactPhaseFinitePart P := by
  have hrow := tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P.toDatum
  have hphase := tendsto_reflectedBiHeatRegulatedPrincipal_sub_thetaPole P
  have heq : (fun epsilon : ℝ =>
      reflectedBiHeatPairSum P.toDatum (epsilon : ℂ) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun epsilon : ℝ =>
        reflectedBiHeatRegulatedPrincipal P epsilon +
            polarizedHeatSharpRemainder
              (P.z + (epsilon : ℂ) / 2)
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x -
          ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
      Ioo_mem_nhdsGT (by linarith [P.z_re_pos] : (0 : ℝ) < 2 * P.z.re),
      Ioo_mem_nhdsGT (by linarith [P.z_re_lt_one] :
        (0 : ℝ) < 2 * (1 - P.z.re))]
        with epsilon hepsilon hepsilonOne hzLeft hzRight
    rw [reflectedBiHeatPairSum_eq_regulatedPrincipal_add_remainder P
      hepsilon hepsilonOne.2 (by linarith [hzLeft.2]) (by linarith [hzRight.2])]
  have hrow' : Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatRegulatedPrincipal P epsilon +
            polarizedHeatSharpRemainder
              (P.z + (epsilon : ℂ) / 2)
              ((starRingEnd ℂ) (1 - P.z + (epsilon : ℂ) / 2)) P.x -
          ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatFinitePart P.toDatum)) :=
    hrow.congr' heq
  exact tendsto_nhds_unique hrow' hphase

/-- The exact phase finite part differs from the Gaussian phase model by the explicit
exponentially small full-window correction. -/
theorem reflectedBiHeatExactPhaseFinitePart_eq_phase_add_correction
    (P : ReflectedBiHeatRegulator) (hx1 : P.x ≤ 1)
    (hxUpper : P.x ≤ Real.pi / 4) :
    reflectedBiHeatExactPhaseFinitePart P =
      reflectedBiHeatPhaseFinitePart P P.x +
        reflectedFullWindowSingularCorrection P.z P.x := by
  rw [reflectedBiHeatExactPhaseFinitePart,
    reflectedFullWindowSingularFinitePart_eq_gaussian_add_explicitCorrection
      P hx1 hxUpper,
    ← reflectedBiHeatAnomaly_eq_singularFinitePart P,
    reflectedBiHeatPhaseFinitePart]
  ring

/-- Canonical row finite part at a variable positive aperture, extended by zero away from the
positive ray solely to state a right-neighborhood limit. -/
noncomputable def reflectedBiHeatCanonicalFinitePartAt
    (P : ReflectedBiHeatRegulator) (x : ℝ) : ℂ :=
  if hx : 0 < x then
    reflectedBiHeatFinitePart
      ({ z := P.z
         x := x
         z_re_pos := P.z_re_pos
         z_re_lt_one := P.z_re_lt_one
         x_pos := hx } : ReflectedBiHeatDatum)
  else 0

theorem reflectedBiHeatCanonicalFinitePartAt_eq_phase_add_correction
    (P : ReflectedBiHeatRegulator) {x : ℝ} (hx : 0 < x)
    (hx1 : x ≤ 1) (hxUpper : x ≤ Real.pi / 4) :
    reflectedBiHeatCanonicalFinitePartAt P x =
      reflectedBiHeatPhaseFinitePart P x +
        reflectedFullWindowSingularCorrection P.z x := by
  let Px : ReflectedBiHeatRegulator :=
    { z := P.z
      epsilon := P.epsilon
      x := x
      z_re_pos := P.z_re_pos
      z_re_lt_one := P.z_re_lt_one
      epsilon_re_pos := P.epsilon_re_pos
      x_pos := hx }
  rw [reflectedBiHeatCanonicalFinitePartAt, dif_pos hx]
  change reflectedBiHeatFinitePart Px.toDatum = _
  rw [reflectedBiHeatFinitePart_eq_exactPhase Px,
    reflectedBiHeatExactPhaseFinitePart_eq_phase_add_correction Px hx1 hxUpper]
  rfl

/-- The actual canonical row finite part has the card's complete small-aperture expansion. -/
theorem tendsto_reflectedBiHeatCanonicalFinitePart_sub_cardExpansion
    (P : ReflectedBiHeatRegulator) :
    Tendsto (fun x : ℝ =>
      reflectedBiHeatCanonicalFinitePartAt P x - reflectedBiHeatCardExpansion P x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hphase := tendsto_reflectedBiHeatPhaseFinitePart_sub_cardExpansion P
  have hcorrection := tendsto_reflectedFullWindowSingularCorrection_zero P.z
  have hsum := hphase.add hcorrection
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
    Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 4)]
      with x hx hx1 hxUpper
  rw [reflectedBiHeatCanonicalFinitePartAt_eq_phase_add_correction
    P hx hx1.2.le hxUpper.2.le]
  ring

/-- Premise-free exact finite-part weld and actual row-expansion capstone. -/
theorem reflectedBiHeatExactFinitePartWeld_capstone :
    ∀ P : ReflectedBiHeatRegulator,
      reflectedBiHeatFinitePart P.toDatum = reflectedBiHeatExactPhaseFinitePart P ∧
      Tendsto (fun x : ℝ =>
        reflectedBiHeatCanonicalFinitePartAt P x - reflectedBiHeatCardExpansion P x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro P
  exact ⟨reflectedBiHeatFinitePart_eq_exactPhase P,
    tendsto_reflectedBiHeatCanonicalFinitePart_sub_cardExpansion P⟩

end

end RHTower
