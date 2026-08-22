import GaloisForLFunctions.RHTower.EulerSquarefreeWickHolonomyRecurrence

open Complex Matrix

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The two colored three-edge source paths agree on the normalized EWQ interaction after
parity compression. -/
theorem eulerWickQuadraticParityCompression_normalizedInteraction_coloredBraid :
    eulerWickQuadraticParityCompression
        (eulerWickQuadraticRowFlip
          (eulerWickQuadraticColumnFlip
            (eulerWickQuadraticRowFlip eulerWickNormalizedInteractionCarrier))) =
      eulerWickQuadraticParityCompression
        (eulerWickQuadraticColumnFlip
          (eulerWickQuadraticRowFlip
            (eulerWickQuadraticColumnFlip eulerWickNormalizedInteractionCarrier))) := by
  rw [eulerWickQuadraticParityCompression_rowFlip,
    eulerWickQuadraticParityCompression_columnFlip,
    eulerWickQuadraticParityCompression_rowFlip,
    eulerWickQuadraticParityCompression_columnFlip,
    eulerWickQuadraticParityCompression_rowFlip,
    eulerWickQuadraticParityCompression_columnFlip]

/-- Minimal colored Reidemeister-III law on the one literal normalized EWQ packet. -/
def EulerWickNormalizedInteractionColoredBraidCompatible (a : ℝ) : Prop :=
  (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
      ((_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec
        ((_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
          (eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier))) =
    (_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec
      ((_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
        ((_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec
          (eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier)))

/-- **Colored-braid rigidity.** The bare and transported physical reflections obey the mixed
three-edge braid relation on the single nonzero EWQ packet exactly at neutral horizontal grade. -/
theorem eulerWickNormalizedInteractionColoredBraidCompatible_iff (a : ℝ) :
    EulerWickNormalizedInteractionColoredBraidCompatible a ↔ a = 0 := by
  constructor
  · intro h
    rw [EulerWickNormalizedInteractionColoredBraidCompatible,
      eulerWickQuadraticParityCompression_normalizedInteraction] at h
    have h1 := congrFun h (1 : Fin 2)
    simp [_root_.RHTower.sourceHorizontalGammaSixBareReflection,
      _root_.RHTower.sourceHorizontalGammaSixTransportedReflection,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    have hexp : Real.exp a = Real.exp (-2 * a) := by
      have hc : Complex.exp (a : ℂ) =
          Complex.exp (-(a : ℂ)) * Complex.exp (-(a : ℂ)) := by
        exact mul_right_cancel₀ (show (8 : ℂ) ≠ 0 by norm_num)
          (by simpa [mul_assoc] using h1)
      rw [← Complex.exp_add] at hc
      have hneg : -(a : ℂ) + -(a : ℂ) = ((-2 * a : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hneg] at hc
      have hre := congrArg Complex.re hc
      simpa only [Complex.exp_ofReal_re] using hre
    have ha : a = -2 * a := Real.exp_injective hexp
    linarith
  · rintro rfl
    simp [EulerWickNormalizedInteractionColoredBraidCompatible,
      _root_.RHTower.sourceHorizontalGammaSixBareReflection,
      _root_.RHTower.sourceHorizontalGammaSixTransportedReflection,
      dotProduct, Fin.sum_univ_two]

/-- At an actual prime clock, the one-packet colored braid law is exactly critical-line placement. -/
theorem eulerWickPrimeNormalizedInteractionColoredBraidCompatible_iff
    (q : _root_.RHTower.XiZeroCopy) (p : Nat.Primes) :
    EulerWickNormalizedInteractionColoredBraidCompatible
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [eulerWickNormalizedInteractionColoredBraidCompatible_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- Global colored-braid compatibility at one fixed prime is RH. -/
theorem everyEulerWickNormalizedInteractionColoredBraidCompatible_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ q : _root_.RHTower.XiZeroCopy,
      EulerWickNormalizedInteractionColoredBraidCompatible
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (eulerWickPrimeNormalizedInteractionColoredBraidCompatible_iff q p).1 (h q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickPrimeNormalizedInteractionColoredBraidCompatible_iff q p).2
    exact _root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end GaloisForLFunctions.RHTower

