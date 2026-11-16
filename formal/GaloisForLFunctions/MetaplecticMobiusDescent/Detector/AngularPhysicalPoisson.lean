import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularFourierProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.CalibrationCharacters
import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGrossencharacterFactorizesTheProbeCorrection

/-! # Angular reflection of calibrated physical rows

The exact periodic Poisson formula preserves the finite Gauss coefficient and introduces
an explicit modulus phase. A sextic tower character cancels its completed-column factor,
leaving the tower character on the dual frequency and a fixed row phase.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.ProbePhysical
open Eisenstein SchwartzPlanePoisson GaussianShiftedPartition CenteredMomentFourier
open GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
open GaloisForLFunctions.FamilyContinuationTheory
local notation "O" => Eisenstein.O

/-- Angular Poisson reflection uses the same finite Gauss coefficient as the radial row;
its additional phase records the modulus and the dual frequency separately. -/
theorem angular_physical_row_poisson (k : ℕ) (C : CalibrationData) (A s : O)
    (hA : A ≠ 0) (hs : s ≠ 0) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (K : ℝ) (hK : 0 < K) :
    (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) *
      angularRadial k (fun t => W (t / K)) (ringComplex m)) =
      ((K / elementNorm (C.generator * A) : ℝ) : ℂ) * ∑' H : O,
        actualCongruenceCoefficient C A s hA H *
          ((ringComplex ((C.generator * A) * s) /
              (‖ringComplex ((C.generator * A) * s)‖ : ℂ)) ^ k *
            (conj (ringComplex H) / (‖ringComplex H‖ : ℂ)) ^ k *
            paperAngularFourier k W
              (K * elementNorm H / elementNorm ((C.generator * A) * s))) := by
  let c := (C.generator * A) * s
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs
  let := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have ht := actual_angular_poisson_trace k W hW K hK c hc (physicalQuotient C A s hs)
  change (∑' m : O, physicalQuotient C A s hs (Ideal.Quotient.mk _ m) *
    angularRadial k (fun t => W (t / K)) (ringComplex m)) =
    (K / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' H : O,
      (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
        primitiveTrace c hc (Ideal.Quotient.mk _ H * r)) *
        ((ringComplex c / (‖ringComplex c‖ : ℂ)) ^ k *
          (conj (ringComplex H) / (‖ringComplex H‖ : ℂ)) ^ k *
          paperAngularFourier k W (K * ‖ringComplex H‖ ^ 2 / ‖ringComplex c‖ ^ 2)) at ht
  have hf (H : O) : (∑ r : O ⧸ Ideal.span {c}, physicalQuotient C A s hs r *
      primitiveTrace c hc (Ideal.Quotient.mk _ H * r)) =
      (Ideal.absNorm (Ideal.span {s}) : ℂ) * actualCongruenceCoefficient C A s hA H := by
    rw [← actualPhysicalFourier_eq C A s hA hs H]
    exact (tsum_fintype _).symm
  simp_rw [physicalQuotient_mk, ringComplex_norm_sq_eq_absNorm_span, hf] at ht
  rw [ht]
  simp only [mul_assoc, tsum_mul_left, Complex.real_smul, Complex.ofReal_div]
  have hn : (elementNorm s : ℂ) ≠ 0 := by
    simp only [elementNorm, Complex.ofReal_natCast]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  have hnorm : elementNorm c = elementNorm (C.generator * A) * elementNorm s := by
    dsimp only [elementNorm, c]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul]
  simp only [← mul_assoc C.generator A s]
  change ((K : ℂ) / (elementNorm c : ℂ)) * _ = _
  rw [hnorm, Complex.ofReal_mul]
  simp only [elementNorm, Complex.ofReal_natCast] at hn ⊢
  field_simp
  have hnc : (Ideal.absNorm (Ideal.span {c}) : ℝ) =
      (Ideal.absNorm (Ideal.span {C.generator * A}) : ℝ) *
        (Ideal.absNorm (Ideal.span {s}) : ℝ) := hnorm
  simp only [hnc, c]

/-- The tower character cancels the completed-column part of the modulus phase. -/
theorem angular_modulus_phase_cancel (k : ℕ) (a b c : O) (hb : b ≠ 0) :
    elemPsiSix b ^ k *
      (ringComplex ((a * b) * c) / (‖ringComplex ((a * b) * c)‖ : ℂ)) ^ (6 * k) =
      (ringComplex (a * c) / (‖ringComplex (a * c)‖ : ℂ)) ^ (6 * k) := by
  have hn : (‖ringComplex b‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hb))
  have hphase : (conj (ringComplex b) / (‖ringComplex b‖ : ℂ)) *
      (ringComplex b / (‖ringComplex b‖ : ℂ)) = 1 := by
    rw [div_mul_div_comm, Complex.conj_mul', pow_two, div_self (mul_ne_zero hn hn)]
  have hmul (u v : O) :
      ringComplex (u * v) / (‖ringComplex (u * v)‖ : ℂ) =
      (ringComplex u / (‖ringComplex u‖ : ℂ)) *
        (ringComplex v / (‖ringComplex v‖ : ℂ)) := by
    rw [map_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm]
  rw [show (a * b) * c = b * (a * c) by ring, hmul, mul_pow,
    elemPsiSix_apply, complexUnitConj_apply, ← pow_mul, ← mul_assoc,
    ← mul_pow, hphase, one_pow, one_mul]

/-- Angular Poisson summation transfers the tower character from the completed column
index to the dual frequency, up to a phase depending only on the fixed row and calibration. -/
theorem compensated_angular_physical_row_poisson (k : ℕ) (C : CalibrationData) (A s : O)
    (hA : A ≠ 0) (hs : s ≠ 0) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (K : ℝ) (hK : 0 < K) :
    elemPsiSix A ^ k *
      (∑' m : O, calibratedNumerator C A m * sexticGauss s hs (-m) *
        angularRadial (6 * k) (fun t => W (t / K)) (ringComplex m)) =
      ((K / elementNorm (C.generator * A) : ℝ) : ℂ) *
        (ringComplex (C.generator * s) / (‖ringComplex (C.generator * s)‖ : ℂ)) ^ (6 * k) *
        ∑' H : O, actualCongruenceCoefficient C A s hA H * elemPsiSix H ^ k *
          paperAngularFourier (6 * k) W
            (K * elementNorm H / elementNorm ((C.generator * A) * s)) := by
  rw [angular_physical_row_poisson (6 * k) C A s hA hs W hW K hK]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro H
  rw [elemPsiSix_apply H, complexUnitConj_apply, ← pow_mul]
  calc
    _ = ((K / elementNorm (C.generator * A) : ℝ) : ℂ) *
        actualCongruenceCoefficient C A s hA H *
        (elemPsiSix A ^ k *
          (ringComplex ((C.generator * A) * s) /
            (‖ringComplex ((C.generator * A) * s)‖ : ℂ)) ^ (6 * k)) *
        (conj (ringComplex H) / (‖ringComplex H‖ : ℂ)) ^ (6 * k) *
        paperAngularFourier (6 * k) W
          (K * elementNorm H / elementNorm ((C.generator * A) * s)) := by ring
    _ = _ := by rw [angular_modulus_phase_cancel k C.generator A s hA]; ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.ProbePhysical
