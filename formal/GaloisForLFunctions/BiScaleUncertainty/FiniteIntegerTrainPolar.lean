import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainPackets
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarTopology

/-!
# Exact polar symbol of actual integer trains

Both source moments are computed by finite translation. Their product divided by
the actual coefficient mass gives the normalized polar multiplier.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

namespace IntegerPacketTrain

def polarMultiplier (d : IntegerPacketTrain) (S : ℝ) : ℝ :=
  d.expSymbol S (1 / 2) * d.expSymbol S (-(1 / 2)) / d.mass

theorem integral_source_mul_exp (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (S β : ℝ) :
    (∫ u, d.source f S u * Real.exp (β * u)) = d.expSymbol S β * ∫ u, f u * Real.exp (β * u) := by
  have hi (i : Fin (d.last + 1)) : Integrable (fun u =>
      d.coefficient i * (f (u - (d.site i : ℝ) * S) * Real.exp (β * u))) := by
    apply Integrable.const_mul
    exact ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hfc.comp_homeomorph (Homeomorph.subRight ((d.site i : ℝ) * S))).mul_right
  simp only [source, finiteTranslateSource, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul, integral_shift_mul_exp, expSymbol, Finset.sum_mul, mul_assoc]

theorem integral_source_autocorr_cosh (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (S : ℝ) :
    (∫ x in Ioi 0, autocorr (d.source f S) x * Real.cosh (x / 2)) =
      (d.expSymbol S (1 / 2) * d.expSymbol S (-(1 / 2))) *
        ∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2) := by
  have hp := d.integral_source_mul_exp hf.continuous hfc S (1 / 2)
  have hm := d.integral_source_mul_exp hf.continuous hfc S (-(1 / 2))
  have hp' : (∫ u, d.source f S u * Real.exp (u / 2)) =
      d.expSymbol S (1 / 2) * ∫ u, f u * Real.exp (u / 2) := by
    simpa only [show ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 by intro u; ring] using hp
  have hm' : (∫ u, d.source f S u * Real.exp (-u / 2)) =
      d.expSymbol S (-(1 / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
    simpa only [show ∀ u : ℝ, (-(1 / 2) : ℝ) * u = -u / 2 by intro u; ring] using hm
  have hg := two_mul_integral_autocorr_cosh (d.contDiff_source hf S) (d.hasCompactSupport_source hfc S)
  rw [hp', hm'] at hg
  have hb := two_mul_integral_autocorr_cosh hf hfc
  calc
    _ = (d.expSymbol S (1 / 2) * d.expSymbol S (-(1 / 2))) *
        ((∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2)) / 2 := by
      nlinarith only [hg]
    _ = _ := by rw [← hb]; ring

theorem normalizedPolarMoment_source (d : IntegerPacketTrain) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D S : ℝ} (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0) (hS : 2 * D < S) :
    normalizedPolarMoment (d.source f S) = d.polarMultiplier S * normalizedPolarMoment f := by
  unfold normalizedPolarMoment polarMultiplier
  rw [d.integral_source_autocorr_cosh hf hfc, d.autocorr_source_zero hf.continuous hfc hD hs hS]
  field_simp [hR.ne', d.mass_pos.ne']

end IntegerPacketTrain

theorem tendsto_integerTrain_polar_iff_symbol {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    (hP : normalizedPolarMoment f ≠ 0) {D : ℝ}
    (hD : 0 ≤ D) (hs : ∀ y, D < |y| → autocorr f y = 0)
    (d : ℕ → IntegerPacketTrain) (S : ℕ → ℝ) (hS : ∀ n, 2 * D < S n) :
    Tendsto (fun n => normalizedPolarMoment ((d n).source f (S n))) atTop
      (𝓝 (normalizedPolarMoment f)) ↔ Tendsto (fun n => (d n).polarMultiplier (S n)) atTop (𝓝 1) := by
  constructor
  · intro h
    have hh := h.div_const (normalizedPolarMoment f)
    have he (n : ℕ) : normalizedPolarMoment ((d n).source f (S n)) / normalizedPolarMoment f =
        (d n).polarMultiplier (S n) := by
      rw [(d n).normalizedPolarMoment_source hf hfc hR hD hs (hS n)]
      field_simp [hP]
    simpa only [he, div_self hP] using hh
  · intro h
    have hh := h.mul_const (normalizedPolarMoment f)
    simpa only [(d _).normalizedPolarMoment_source hf hfc hR hD hs (hS _), one_mul] using hh

end
end GaloisForLFunctions.BiScaleUncertainty
