import GaloisForLFunctions.HTGeometry.BoundedPhaseSmirnovToeplitz
import GaloisForLFunctions.RHTower.KapustinGaugeCarrier
import GaloisForLFunctions.RHTower.KapustinGammaToeplitzPhase

/-!
# Actual Smirnov collision forced by a one-sided Kapustin gauge

This file performs the exact analytic-gauge and bounded-phase multiplication from the paper proof.
Under an almost-everywhere nonnegative rotated Kapustin weight, it constructs a nonzero actual
`DiskSmirnovBoundary` Toeplitz-kernel element for the fixed reciprocal-Gamma symbol.
-/

open Complex MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem kapustinUniversalGammaCarrier_ne_zero (t : ℝ) :
    kapustinUniversalGammaCarrier t ≠ 0 := by
  unfold kapustinUniversalGammaCarrier
  apply div_ne_zero
  · exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (Complex.exp_ne_zero _)
  · exact gammaVerticalValue_ne_zero (by norm_num) t

theorem kapustinUniversalGammaCarrier_eq_normFactor_mul_exp_neg_phase (t : ℝ) :
    kapustinUniversalGammaCarrier t =
      ((Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) /
        ‖gammaVerticalValue (1 / 2) t‖ : ℝ) : ℂ) *
        Complex.exp (-I * (kapustinReciprocalGammaPhase t : ℂ)) := by
  rw [kapustinUniversalGammaCarrier,
    gammaVerticalValue_eq_norm_mul_exp_phase (by norm_num : (0 : ℝ) < 1 / 2)]
  have hnorm : ((‖gammaVerticalValue (1 / 2) t‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr
      (gammaVerticalValue_ne_zero (by norm_num : (0 : ℝ) < 1 / 2) t)).ne'
  have hexp : Complex.exp (I * (gammaVerticalPhase (1 / 2) t : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  rw [kapustinReciprocalGammaPhase]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), Complex.norm_exp, Complex.mul_re]
  norm_num
  field_simp
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem kapustinUniversalGammaCarrier_div_conj (t : ℝ) :
    kapustinUniversalGammaCarrier t /
      (starRingEnd ℂ) (kapustinUniversalGammaCarrier t) =
      Complex.exp (-2 * I * (kapustinReciprocalGammaPhase t : ℂ)) := by
  rw [kapustinUniversalGammaCarrier_eq_normFactor_mul_exp_neg_phase]
  let r : ℝ := Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) /
    ‖gammaVerticalValue (1 / 2) t‖
  have hr : (r : ℂ) ≠ 0 := by
    have hnum : 0 < Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) :=
      Real.exp_pos _
    have hden : 0 < ‖gammaVerticalValue (1 / 2) t‖ :=
      norm_pos_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) t)
    dsimp [r]
    exact_mod_cast (div_pos hnum hden).ne'
  change (r : ℂ) * Complex.exp (-I * (kapustinReciprocalGammaPhase t : ℂ)) /
      (starRingEnd ℂ)
        ((r : ℂ) * Complex.exp (-I * (kapustinReciprocalGammaPhase t : ℂ))) = _
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hnegI : (starRingEnd ℂ) (-I) = I := by simp
  rw [hnegI]
  field_simp
  rw [← Complex.exp_add]
  congr 1
  ring

theorem kapustinUniversalGammaCarrier_neg_div_conj (x : ℝ) :
    kapustinUniversalGammaCarrier (-x) /
      (starRingEnd ℂ) (kapustinUniversalGammaCarrier (-x)) =
      Complex.exp (2 * I * (kapustinReciprocalGammaPhase x : ℂ)) := by
  rw [kapustinUniversalGammaCarrier_div_conj, kapustinReciprocalGammaPhase_neg]
  congr 1
  push_cast
  ring

theorem realCayley_eq_neg_exp_two_mul_I_arctan (x : ℝ) :
    realCayley x = -Complex.exp (((2 * Real.arctan x : ℝ) : ℂ) * I) := by
  have hsqrt : 0 < Real.sqrt (1 + x ^ (2 : ℕ)) := Real.sqrt_pos.2 (by positivity)
  have hsqrtSq : Real.sqrt (1 + x ^ (2 : ℕ)) ^ (2 : ℕ) = 1 + x ^ (2 : ℕ) := by
    rw [Real.sq_sqrt (by positivity)]
  have hden : 1 + x ^ (2 : ℕ) ≠ 0 := by positivity
  have hcos : Real.cos (2 * Real.arctan x) = (1 - x ^ (2 : ℕ)) / (1 + x ^ (2 : ℕ)) := by
    rw [Real.cos_two_mul, Real.cos_arctan]
    field_simp
    nlinarith
  have hsin : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ (2 : ℕ)) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp
    rw [hsqrtSq]
  have hcayley : realCayley x =
      (((x ^ (2 : ℕ) - 1) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ) +
        (((-2 * x) / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [realCayley, Complex.div_re]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero,
        Complex.add_re, add_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
        zero_sub, Complex.add_im, zero_add, Complex.normSq_apply,
        Complex.mul_re, mul_zero, zero_mul, sub_zero]
      field_simp [hden]
      ring
    · rw [realCayley, Complex.div_im]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero,
        Complex.add_re, add_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
        zero_sub, Complex.add_im, zero_add, Complex.normSq_apply,
        Complex.mul_im, mul_zero, add_zero, mul_one]
      field_simp [hden]
      ring
  rw [hcayley, Complex.exp_ofReal_mul_I, hcos, hsin]
  have hreal : (x ^ (2 : ℕ) - 1) / (1 + x ^ (2 : ℕ)) =
      -(1 - x ^ (2 : ℕ)) / (1 + x ^ (2 : ℕ)) := by ring
  rw [hreal]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp [hden] <;> ring

theorem conj_realCayley_pow_four_eq_exp_neg_eight_arctan (x : ℝ) :
    (starRingEnd ℂ) (realCayley x ^ (4 : ℕ)) =
      Complex.exp (((-8 * Real.arctan x : ℝ) : ℂ) * I) := by
  rw [realCayley_eq_neg_exp_two_mul_I_arctan, map_pow, map_neg,
    ← Complex.exp_conj]
  have hconjReal (a : ℝ) : (starRingEnd ℂ) ((a : ℂ) * I) =
      -((a : ℂ) * I) := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  have hconj := hconjReal (2 * Real.arctan x)
  rw [hconj]
  simp only [Even.neg_pow (by norm_num : Even 4)]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Kapustin boundary product in the upper-half-plane orientation used by the Toeplitz proof. -/
def kapustinRotatedGaugeQ (Phi : DiskMultiplier) (x : ℝ) : ℂ :=
  kapustinUniversalGammaCarrier (-x) * diskMultiplierLineBoundary Phi x

theorem measurable_kapustinRotatedGaugeQ (Phi : DiskMultiplier) :
    Measurable (kapustinRotatedGaugeQ Phi) :=
  (continuous_kapustinUniversalGammaCarrier.measurable.comp measurable_neg).mul
    (measurable_diskMultiplierLineBoundary Phi)

theorem kapustinRotatedGaugeQ_ne_zero_ae
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0) :
    ∀ᵐ x ∂volume, kapustinRotatedGaugeQ Phi x ≠ 0 := by
  filter_upwards [diskMultiplierLineBoundary_ne_zero_ae Phi hPhi] with x hx
  exact mul_ne_zero (kapustinUniversalGammaCarrier_ne_zero (-x)) hx

/-- Principal right-half-plane phase, transported to the circle and set to zero on the exceptional
set.  The clipping makes the sharp half-period bound pointwise, as required by the Herglotz
construction. -/
def kapustinNonnegativePhaseCircle (Phi : DiskMultiplier) (z : Circle) : ℝ :=
  let q := kapustinRotatedGaugeQ Phi (circleCayleyInverse z)
  if 0 ≤ q.re ∧ q ≠ 0 then q.arg else 0

theorem measurable_kapustinNonnegativePhaseCircle (Phi : DiskMultiplier) :
    Measurable (kapustinNonnegativePhaseCircle Phi) := by
  let q : Circle → ℂ := fun z =>
    kapustinRotatedGaugeQ Phi (circleCayleyInverse z)
  have hq : Measurable q :=
    (measurable_kapustinRotatedGaugeQ Phi).comp measurable_circleCayleyInverse
  have hset : MeasurableSet {z | 0 ≤ (q z).re ∧ q z ≠ 0} := by
    exact ((Complex.measurable_re.comp hq) measurableSet_Ici).inter
      ((hq (measurableSet_singleton 0)).compl)
  unfold kapustinNonnegativePhaseCircle
  exact Measurable.ite hset (Complex.measurable_arg.comp hq) measurable_const

theorem abs_kapustinNonnegativePhaseCircle_le (Phi : DiskMultiplier) (z : Circle) :
    |kapustinNonnegativePhaseCircle Phi z| ≤ Real.pi / 2 := by
  rw [kapustinNonnegativePhaseCircle]
  split_ifs with hz
  · exact abs_arg_le_pi_div_two_of_re_nonneg hz.2 hz.1
  · simp
    positivity

theorem kapustinNonnegativePhaseCircle_pullback_ae
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    ∀ᵐ x ∂volume,
      kapustinNonnegativePhaseCircle Phi (circleCayley x) =
        (kapustinRotatedGaugeQ Phi x).arg := by
  filter_upwards [hnonneg, kapustinRotatedGaugeQ_ne_zero_ae Phi hPhi]
      with x hx hne
  simp [kapustinNonnegativePhaseCircle, hx, hne]

private theorem kapustin_gauge_phase_mul_q_phase
    (A f : ℂ) (hA : A ≠ 0) (hf : f ≠ 0) :
    ((starRingEnd ℂ) f / f) *
      ((A * f) / (starRingEnd ℂ) (A * f)) =
        A / (starRingEnd ℂ) A := by
  simp only [map_mul]
  have hcA : (starRingEnd ℂ) A ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hA
  have hcf : (starRingEnd ℂ) f ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hf
  field_simp [hA, hf, hcA, hcf]

/-- Under one-sided nonnegativity, the product of the literal gauge phase-reflection symbol and
the actual bounded-phase symbol is the fixed reciprocal-Gamma Toeplitz symbol. -/
theorem kapustinGauge_boundedPhase_symbol_eq_ae
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    smirnovToeplitzSymbolMul (diskMultiplierPhaseReflectionSymbol Phi)
      (boundedPhaseToeplitzSymbol (kapustinNonnegativePhaseCircle Phi)) =ᵐ[volume]
        kapustinToeplitzSymbol := by
  have hphase := kapustinNonnegativePhaseCircle_pullback_ae Phi hPhi hnonneg
  filter_upwards [hphase, diskMultiplierLineBoundary_ne_zero_ae Phi hPhi]
      with x hxPhase hxPhi
  have hq : kapustinRotatedGaugeQ Phi x ≠ 0 :=
    mul_ne_zero (kapustinUniversalGammaCarrier_ne_zero (-x)) hxPhi
  rw [smirnovToeplitzSymbolMul, diskMultiplierPhaseReflectionSymbol,
    if_neg hxPhi, boundedPhaseToeplitzSymbol, hxPhase,
    exp_two_mul_I_mul_arg_eq_div_conj hq]
  rw [kapustinRotatedGaugeQ]
  rw [show
    ((starRingEnd ℂ) (diskMultiplierLineBoundary Phi x) /
        diskMultiplierLineBoundary Phi x) *
      ((starRingEnd ℂ) (realCayley x ^ (4 : ℕ)) *
        ((kapustinUniversalGammaCarrier (-x) *
            diskMultiplierLineBoundary Phi x) /
          (starRingEnd ℂ) (kapustinUniversalGammaCarrier (-x) *
            diskMultiplierLineBoundary Phi x))) =
      (starRingEnd ℂ) (realCayley x ^ (4 : ℕ)) *
        (((starRingEnd ℂ) (diskMultiplierLineBoundary Phi x) /
            diskMultiplierLineBoundary Phi x) *
          ((kapustinUniversalGammaCarrier (-x) *
              diskMultiplierLineBoundary Phi x) /
            (starRingEnd ℂ) (kapustinUniversalGammaCarrier (-x) *
              diskMultiplierLineBoundary Phi x))) by ring]
  rw [kapustin_gauge_phase_mul_q_phase
    (kapustinUniversalGammaCarrier (-x)) (diskMultiplierLineBoundary Phi x)
    (kapustinUniversalGammaCarrier_ne_zero (-x)) hxPhi]
  rw [kapustinUniversalGammaCarrier_neg_div_conj,
    conj_realCayley_pow_four_eq_exp_neg_eight_arctan,
    kapustinToeplitzSymbol, kapustinToeplitzPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact nonzero Smirnov Toeplitz-kernel element forced by a nonnegative Kapustin gauge weight. -/
noncomputable def kapustinSmirnovToeplitzElement_of_rotated_nonnegative
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonneg : ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi x).re) :
    SmirnovToeplitzKernelElement kapustinToeplitzSymbol :=
  ((diskMultiplierSmirnovToeplitzElement Phi hPhi).mul
    (boundedPhaseSmirnovToeplitzElement
      (kapustinNonnegativePhaseCircle Phi)
      (measurable_kapustinNonnegativePhaseCircle Phi)
      (abs_kapustinNonnegativePhaseCircle_le Phi))).congr
        (kapustinGauge_boundedPhase_symbol_eq_ae Phi hPhi hnonneg)

theorem kapustinRotatedGaugeQ_neg_ae (Phi : DiskMultiplier) :
    kapustinRotatedGaugeQ Phi.neg =ᵐ[volume]
      fun x => -kapustinRotatedGaugeQ Phi x := by
  filter_upwards [diskMultiplierLineBoundary_neg_ae Phi] with x hx
  rw [kapustinRotatedGaugeQ, kapustinRotatedGaugeQ, hx]
  ring

/-- Exact nonzero Smirnov Toeplitz-kernel element forced by a nonpositive Kapustin gauge weight.
This is the negative branch of the sign contradiction, obtained from the literal analytic gauge
`-Phi`, not from an added sign hypothesis on a different object. -/
noncomputable def kapustinSmirnovToeplitzElement_of_rotated_nonpositive
    (Phi : DiskMultiplier)
    (hPhi : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.fn z ≠ 0)
    (hnonpos : ∀ᵐ x ∂volume, (kapustinRotatedGaugeQ Phi x).re ≤ 0) :
    SmirnovToeplitzKernelElement kapustinToeplitzSymbol := by
  have hPhiNeg : ∃ z ∈ Metric.ball (0 : ℂ) 1, Phi.neg.fn z ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := hPhi
    exact ⟨z, hz, neg_ne_zero.mpr hne⟩
  have hnonnegNeg :
      ∀ᵐ x ∂volume, 0 ≤ (kapustinRotatedGaugeQ Phi.neg x).re := by
    filter_upwards [kapustinRotatedGaugeQ_neg_ae Phi, hnonpos] with x hx hle
    rw [hx]
    simpa using neg_nonneg.mpr hle
  exact kapustinSmirnovToeplitzElement_of_rotated_nonnegative
    Phi.neg hPhiNeg hnonnegNeg

end

end RHTower
