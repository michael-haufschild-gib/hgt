import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularSmoothedReflection

/-!
# Finite cusp reflection with angular characters

Finite Fourier inversion acts on the periodic part of the character. The sextic angular
factor remains in the source coefficients and reflects through the higher cusp jets.
The completed squarefree–cube sum therefore has the same finite cusp decomposition and
radial conductor scale as the finite-order source.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

/-- The angular twist of a multiplicative coefficient on Eisenstein integers. -/
def angularSourceTwist (k : ℕ) (Ψ : O →* ℂ) : O →* ℂ :=
  Ψ * elemPsiSix.toMonoidHom ^ k

lemma angularSourceTwist_apply (k : ℕ) (Ψ : O →* ℂ) (h : O) :
    angularSourceTwist k Ψ h = Ψ h * elemPsiSix h ^ k := by
  change Ψ h * (elemPsiSix.toMonoidHom ^ k) h = _
  rw [MonoidHom.pow_apply]
  rfl

lemma fixedThetaTwist_angularSourceTwist (k : ℕ) (Ψ : O →* ℂ) (h : O) :
    fixedThetaTwist (angularSourceTwist k Ψ) h = fixedThetaTwist Ψ h * elemPsiSix h ^ k := by
  by_cases hh : lambda ^ 2 ∣ h - 1
  · simp only [fixedThetaTwist, if_pos hh, angularSourceTwist_apply, mul_assoc]
  · simp only [fixedThetaTwist, if_neg hh, zero_mul]

/-- Exact finite-cusp reflection for the angular arithmetic Gauss sum. -/
theorem thetaSmoothedGaussSum_angular_finite_reflection (k : ℕ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    thetaSmoothedGaussSum (angularSourceTwist k
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) V X =
      rationalSourceThetaScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).angularSmoothingMultiplier k *
            ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).index
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).dualPoint h) *
              angularPaperKernel k V
                ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X *
                  sourceCuspRadialLength h)) := by
  let χ := Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom
  let W : O → ℂ := fun h => elemPsiSix h ^ k * V (sourceCuspRadialLength h / X)
  have hW : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h * W h‖) := by
    have hs := weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
      (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient 0 h) (3 / 2)
      (angularSourceBar_weighted_summable k 0) V a b ha hVs hV X hX
    simpa only [W, mul_assoc, mul_left_comm] using hs
  have hf := sourceBar_smoothed_finite_translation (9 * c) (mul_ne_zero (by norm_num) hc)
    (finiteThetaTwist c Ψ) W hW
  calc
    _ = ∑' h : O, (rationalSourceThetaScalar⁻¹ * star (rationalSourceResidualFourierCoefficient h) *
        fixedThetaTwist (angularSourceTwist k χ) h) *
        (((-2 * Real.pi * Complex.I * star (cuspFrequency h)) /
          (sourceCuspRadialLength h : ℂ)) * V (sourceCuspRadialLength h / X)) :=
      (fixedThetaTwist_source_tsum (angularSourceTwist k χ) _).symm
    _ = rationalSourceThetaScalar⁻¹ *
        ∑' h : O, finiteThetaTwist c Ψ (Ideal.Quotient.mk _ h) * sourceBarRadialCoefficient 0 h * W h := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      rw [sourceBarRadialCoefficient_at_zero, finiteThetaTwist_mk, fixedThetaTwist_angularSourceTwist]
      dsimp only [W]
      ring
    _ = rationalSourceThetaScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ∑' h : O, sourceBarRadialCoefficient (thetaFourierTranslation (9 * c) i) h * W h := by rw [hf]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [← finiteTwistCusp_point (9 * c) (mul_ne_zero (by norm_num) hc) i]
      simpa only [W, mul_assoc, mul_left_comm] using
        (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).angular_smoothed_reflection
          k V a b ha hVs hV X hX

/-- The actual angular completed sum reflects with unchanged finite conductor geometry. -/
theorem completedT_angular_finite_smoothed_reflection (k : ℕ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) W X =
      thetaDerivativeScalar⁻¹ *
        ∑ i, finiteAdditiveFourierCoeff
          (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc)) (finiteThetaTwist c Ψ) i *
          ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).angularSmoothingMultiplier k *
            ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).index
              (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).dualPoint h) *
              angularPaperKernel k (Vstar W)
                ((finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).smoothingScale X *
                  sourceCuspRadialLength h)) := by
  have he := thetaSmoothedGaussSum_angular_finite_reflection k c hc Ψ (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX
  rw [thetaSmoothedGaussSum_eq_completedT] at he
  apply mul_left_cancel₀ thetaRadialDerivativeScalar_ne_zero
  rw [he, thetaDerivativeScalar, mul_inv_rev]
  field_simp [thetaRadialDerivativeScalar_ne_zero]

/-- Angular reflection is independent of the coordinates chosen at each finite cusp. -/
theorem completedT_angular_finite_cusp_reflection (k : ℕ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) W X =
      thetaDerivativeScalar⁻¹ * ∑ i,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) i *
        ((d i).angularSmoothingMultiplier k * ∑' h : O,
          (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient (d i).index (d i).dualPoint h) *
          angularPaperKernel k (Vstar W) ((d i).smoothingScale X * sourceCuspRadialLength h)) := by
  rw [completedT_angular_finite_smoothed_reflection k c hc Ψ W a b ha hs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← (d i).angular_smoothed_reflection k (Vstar W) a b ha (Vstar_support W a b hs)
      (Vstar_contDiff W a b ha hs hW) X hX,
    ← (finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc) i).angular_smoothed_reflection
      k (Vstar W) a b ha (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX,
    hd i, finiteTwistCusp_point]

/-- Reindexing retains the exact unit, ramified, squarefree and cube decomposition. -/
theorem angularSourceCusp_tsum_full_index (k : ℕ) (j : Fin 3) (z : ℂ) (W : O → ℂ) :
    (∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient j z h) * W h) =
      ∑' p : ThetaFullIndex,
        (conj (elemPsiSix (thetaFullFrequency p)) ^ k *
          sourceCuspRadialCoefficient j z (thetaFullFrequency p)) * W (thetaFullFrequency p) := by
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    sourceCuspRadial_tsum_full_index j z (fun h => conj (elemPsiSix h) ^ k * W h)

theorem completedT_angular_finite_cusp_full_reflection (k : ℕ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) W X =
      thetaDerivativeScalar⁻¹ * ∑ i,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) i *
        ((d i).angularSmoothingMultiplier k * ∑' p : ThetaFullIndex,
          (conj (elemPsiSix (thetaFullFrequency p)) ^ k *
            sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)) *
          angularPaperKernel k (Vstar W) ((d i).smoothingScale X *
            (‖ringComplex lambda‖ ^ (2 * p.2.1) * completedMellinLength p.2.2))) := by
  rw [completedT_angular_finite_cusp_reflection k c hc Ψ d hd W a b ha hs hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [angularSourceCusp_tsum_full_index]
  simp only [thetaFullFrequency_radialLength]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
