import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicSecondDerivativeEdge
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicOuterResponseKrein

/-!
# Corner-renormalized BM second-harmonic second derivative

The exact horizon-regular second jet splits into forbidden and normalizable AdS branches. The
normalizable branch has a non-integrable second-derivative corner, so subtracting only its leading
square-root asymptotic cannot define the third-order radial source. This module subtracts the full
normalizable branch, evaluates the remaining endpoint as an explicit hypergeometric coefficient,
and proves that finite part is nonzero on every Xi fibre.

This is a coefficient-level input for the augmented third-order Einstein--Teukolsky source; it does
not identify the complete cubic source.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact second-jet connection of the regular horizon solution into the two AdS branches. -/
theorem d4BMPlusPlusRegularAdSConnection_secondDerivative
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ) =
      d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
          d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z +
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
          d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  let A := d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi
  let B := d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi
  let R := d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)
  let Rd := d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ)
  let Rdd := d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ)
  let S := d4BMPlusPlusAdSForbiddenSolution n chi z
  let Sd := d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z
  let Sdd := d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z
  let V := d4BMPlusPlusAdSNormalizableSolution n chi z
  let Vd := d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z
  let Vdd := d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z
  have hphase := d4BMPlusPlusRegularAdSConnection_phase n chi hchi hz0 hz1
  have hvalue : R = A * S + B * V := by simpa [R, A, S, B, V] using hphase.1
  have hderiv : Rd = A * Sd + B * Vd := by simpa [Rd, A, Sd, B, Vd] using hphase.2
  have hR := d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero
    n chi hchi hz0 hz1
  have hS := d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n chi hchi hz0 hz1
  have hV := d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hz0 hz1
  change (((z * (1 - z) : ℝ) : ℂ)) * Rdd +
    (c - (a + b + 1) * z) * Rd - a * b * R = 0 at hR
  change (((z * (1 - z) : ℝ) : ℂ)) * Sdd +
    (c - (a + b + 1) * z) * Sd - a * b * S = 0 at hS
  change (((z * (1 - z) : ℝ) : ℂ)) * Vdd +
    (c - (a + b + 1) * z) * Vd - a * b * V = 0 at hV
  have hcoef : (((z * (1 - z) : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (mul_ne_zero hz0.ne' (ne_of_gt (sub_pos.mpr hz1)))
  apply (mul_left_cancel₀ hcoef)
  linear_combination hR - A * hS - B * hV -
    (c - (a + b + 1) * z) * hderiv + a * b * hvalue

/-- Subtract the full normalizable AdS branch, not only its leading square-root singularity. -/
def d4BMPlusPlusCornerRenormalizedRegularSecondDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ) -
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
      d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z

theorem d4BMPlusPlusCornerRenormalizedRegularSecondDerivative_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n chi z =
      d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
        d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z := by
  rw [d4BMPlusPlusCornerRenormalizedRegularSecondDerivative,
    d4BMPlusPlusRegularAdSConnection_secondDerivative n chi hchi hz0 hz1]
  ring

lemma continuousAt_d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ContinuousAt
      (d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi) 0 := by
  let p := d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi
  let q := p.derivSeries
  let r := q.derivSeries
  have hp : ‖(0 : ℂ)‖ₑ < p.radius := by
    rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one n chi hchi]
    norm_num
  have hq : ‖(0 : ℂ)‖ₑ < q.radius :=
    lt_of_lt_of_le hp p.radius_le_radius_derivSeries
  have hr : ‖(0 : ℂ)‖ₑ < r.radius :=
    lt_of_lt_of_le hq q.radius_le_radius_derivSeries
  have hsum := r.hasFDerivAt_sum hr
  have hfirst := hsum.clm_apply (hasFDerivAt_const (1 : ℂ) (0 : ℂ))
  have hsecond := hfirst.clm_apply (hasFDerivAt_const (1 : ℂ) (0 : ℂ))
  change ContinuousAt (fun w : ℂ => (((r.sum w) 1) 1)) 0
  exact hsecond.continuousAt

theorem ordinaryHypergeometricSecondDerivativeSeriesValue_zero
    (a b c : ℂ)
    (hzero : ‖(0 : ℂ)‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius) :
    ordinaryHypergeometricSecondDerivativeSeriesValue a b c 0 =
      2 * ordinaryHypergeometricFormalCoefficient a b c 2 := by
  have hsum :=
    (ordinaryHypergeometric_hasSum_value_first_second a b c 0 hzero).2.2
  have hsingle : HasSum
      (fun j : ℕ => ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricFormalCoefficient a b c (j + 2) * (0 : ℂ) ^ j)
      (2 * ordinaryHypergeometricFormalCoefficient a b c 2) := by
    convert hasSum_single (f := fun j : ℕ =>
      ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricFormalCoefficient a b c (j + 2) * (0 : ℂ) ^ j)
      0 (by
        intro j hj
        simp [zero_pow hj]) using 1
    all_goals norm_num
  exact hsum.unique hsingle

theorem two_mul_ordinaryHypergeometricFormalCoefficient_two
    (a b c : ℂ) :
    2 * ordinaryHypergeometricFormalCoefficient a b c 2 =
      a * (a + 1) * b * (b + 1) / (c * (c + 1)) := by
  simp [ordinaryHypergeometricFormalCoefficient,
    ordinaryHypergeometricCoefficient, ascPochhammer, div_eq_mul_inv,
    mul_inv_rev]
  ring

theorem d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi 0 =
      let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
      let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
      let c := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
      a * (a + 1) * b * (b + 1) / (c * (c + 1)) := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
  have hzero :
      ‖(0 : ℂ)‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖(0 : ℂ)‖ₑ <
      (d4BMPlusPlusAdSForbiddenHypergeometricSeries n chi).radius
    rw [d4BMPlusPlusAdSForbiddenHypergeometricSeries_radius_eq_one n chi hchi]
    norm_num
  change ordinaryHypergeometricSecondDerivativeSeriesValue a b c 0 = _
  rw [ordinaryHypergeometricSecondDerivativeSeriesValue_zero a b c hzero,
    two_mul_ordinaryHypergeometricFormalCoefficient_two]

theorem tendsto_d4BMPlusPlusAdSForbiddenSolutionSecondDerivative_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi)
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi 0)) := by
  have hinner : Tendsto (fun z : ℝ => ((1 - z : ℝ) : ℂ))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    have hcont : ContinuousAt (fun z : ℝ => ((1 - z : ℝ) : ℂ)) 1 := by
      fun_prop
    have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) := inf_le_left
    have ht := hcont.tendsto.mono_left hle
    convert ht using 1
    all_goals norm_num
  have h :=
    (continuousAt_d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative_zero
      n chi hchi).tendsto.comp hinner
  change Tendsto
    (fun z : ℝ =>
      d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi
        ((1 - z : ℝ) : ℂ))
    (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
    (𝓝 (d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative n chi 0))
  exact h

/-- Finite second-jet left after subtracting the full normalizable corner branch. -/
def d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart
    (n : ℕ) (chi : ℂ) : ℂ :=
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
  d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
    (a * (a + 1) * b * (b + 1) / (c * (c + 1)))

theorem d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart n chi ≠ 0 := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMPlusPlusAdSForbiddenHypergeometricC n chi
  have hzero :=
    d4BMPlusPlusAdSForbiddenHypergeometricParameters_ne_negNat n chi hchi 0
  have hone :=
    d4BMPlusPlusAdSForbiddenHypergeometricParameters_ne_negNat n chi hchi 1
  have ha : a ≠ 0 := by
    intro ha
    apply hzero.1
    simp [a, ha]
  have ha1 : a + 1 ≠ 0 := by
    intro ha1
    apply hone.1
    have h : (1 : ℂ) = -a := by
      linear_combination ha1
    simpa [a] using h
  have hb : b ≠ 0 := by
    intro hb
    apply hzero.2.1
    simp [b, hb]
  have hb1 : b + 1 ≠ 0 := by
    intro hb1
    apply hone.2.1
    have h : (1 : ℂ) = -b := by
      linear_combination hb1
    simpa [b] using h
  have hc : c ≠ 0 := by
    simp [c, d4BMPlusPlusAdSForbiddenHypergeometricC_eq]
  have hc1 : c + 1 ≠ 0 := by
    norm_num [c, d4BMPlusPlusAdSForbiddenHypergeometricC_eq]
  change d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
      (a * (a + 1) * b * (b + 1) / (c * (c + 1))) ≠ 0
  exact mul_ne_zero
    (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient_ne_zero n chi hchi)
    (div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha ha1) hb) hb1)
      (mul_ne_zero hc hc1))

theorem tendsto_d4BMPlusPlusCornerRenormalizedRegularSecondDerivative_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    Tendsto
      (d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n chi)
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart n chi)) := by
  have hright : Tendsto
      (fun z : ℝ =>
        d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
          d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi z)
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart n chi)) := by
    simpa [d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart,
      d4BMPlusPlusAdSForbiddenHypergeometricSecondDerivative_zero n chi hchi] using
      (tendsto_const_nhds.mul
        (tendsto_d4BMPlusPlusAdSForbiddenSolutionSecondDerivative_one n chi hchi))
  have hpos : ∀ᶠ z : ℝ in 𝓝[Ico (0 : ℝ) 1] (1 : ℝ), 0 < z := by
    rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)]
    have h : ∀ᶠ z : ℝ in 𝓝 (1 : ℝ), 0 < z :=
      Ioi_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin, hpos] with z hz hz0
  exact (d4BMPlusPlusCornerRenormalizedRegularSecondDerivative_eq
    n chi hchi hz0 hz.2).symm

/-- Premise-free Xi corner-renormalized second derivative has an exact finite endpoint. -/
theorem tendsto_d4BMXiPlusPlusCornerRenormalizedRegularSecondDerivative_one
    (n : ℕ) (q : XiZeroCopy) :
    Tendsto
      (d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q))
      (𝓝[Ico (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart n
        (d4BMXiMixedHorizonAngularMomentum q))) := by
  exact tendsto_d4BMPlusPlusCornerRenormalizedRegularSecondDerivative_one n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- Premise-free Xi corner finite part is nonzero on every mode and zero copy. -/
theorem d4BMXiPlusPlusCornerRenormalizedSecondDerivativeFinitePart_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart n
      (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
  exact d4BMPlusPlusCornerRenormalizedSecondDerivativeFinitePart_ne_zero n
    (d4BMXiMixedHorizonAngularMomentum q)
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

end

end RHTower

