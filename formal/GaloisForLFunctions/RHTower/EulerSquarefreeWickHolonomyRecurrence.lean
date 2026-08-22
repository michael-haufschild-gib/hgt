import GaloisForLFunctions.RHTower.EulerSquarefreeWickQuadraticCommonRefinementDescent
import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimeResidueHT

open Complex Matrix

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The literal normalized EWQ anchored interaction, as a vector on the full gauge square. -/
def eulerWickNormalizedInteractionCarrier :
    EulerWickQuadraticCommonRefinement :=
  fun x => eulerSquarefreeWickAnchoredInteractionObservable
    eulerSquarefreeWickNormalizedPacket ⟨x, Set.mem_univ x⟩

/-- Its parity compression retains a nonzero first sector and no second sector. -/
theorem eulerWickQuadraticParityCompression_normalizedInteraction :
    eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier =
      ![(-8 : ℂ), 0] := by
  ext i
  fin_cases i
  · simp [eulerWickQuadraticParityCompression,
      eulerWickNormalizedInteractionCarrier,
      eulerSquarefreeWickAnchoredInteractionObservable_eq,
      eulerSquarefreeWickNormalizedDefect]
    ring
  · simp [eulerWickQuadraticParityCompression,
      eulerWickNormalizedInteractionCarrier,
      eulerSquarefreeWickAnchoredInteractionObservable_eq,
      eulerSquarefreeWickNormalizedDefect]

/-- The source loop obtained by traversing both quadratic gauge edges fixes the normalized
interaction after parity compression. -/
theorem eulerWickQuadraticParityCompression_normalizedInteraction_loop :
    eulerWickQuadraticParityCompression
        (eulerWickQuadraticRowFlip
          (eulerWickQuadraticColumnFlip eulerWickNormalizedInteractionCarrier)) =
      eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier := by
  rw [eulerWickQuadraticParityCompression_rowFlip,
    eulerWickQuadraticParityCompression_columnFlip]
  rw [Matrix.mulVec_mulVec]
  have hsquare := _root_.RHTower.sourceHorizontalGammaSixBareReflection_sq
  rw [hsquare, Matrix.one_mulVec]

/-- Physical relative holonomy around the ordered column--row loop. -/
def eulerWickGammaSixRelativeHolonomy (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  _root_.RHTower.sourceHorizontalGammaSixBareReflection *
    _root_.RHTower.sourceHorizontalGammaSixTransportedReflection a

/-- The relative holonomy is the positive diagonal escape mode. -/
theorem eulerWickGammaSixRelativeHolonomy_eq (a : ℝ) :
    eulerWickGammaSixRelativeHolonomy a =
      Matrix.diagonal ![Complex.exp (-(a : ℂ)), Complex.exp (a : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eulerWickGammaSixRelativeHolonomy,
      _root_.RHTower.sourceHorizontalGammaSixBareReflection,
      _root_.RHTower.sourceHorizontalGammaSixTransportedReflection,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Minimal orientation law: only the one literal normalized interaction packet and its
two-edge loop are required to intertwine with physical relative holonomy. -/
def EulerWickNormalizedInteractionHolonomyCompatible (a : ℝ) : Prop :=
  (eulerWickGammaSixRelativeHolonomy a).mulVec
      (eulerWickQuadraticParityCompression eulerWickNormalizedInteractionCarrier) =
    eulerWickQuadraticParityCompression
      (eulerWickQuadraticRowFlip
        (eulerWickQuadraticColumnFlip eulerWickNormalizedInteractionCarrier))

/-- **One-packet holonomy rigidity.** Compatibility of the physical loop with the single
nonzero EWQ interaction packet holds exactly at neutral horizontal grade. -/
theorem eulerWickNormalizedInteractionHolonomyCompatible_iff (a : ℝ) :
    EulerWickNormalizedInteractionHolonomyCompatible a ↔ a = 0 := by
  constructor
  · intro h
    rw [EulerWickNormalizedInteractionHolonomyCompatible,
      eulerWickQuadraticParityCompression_normalizedInteraction_loop,
      eulerWickQuadraticParityCompression_normalizedInteraction,
      eulerWickGammaSixRelativeHolonomy_eq] at h
    have h0 := congrFun h (0 : Fin 2)
    have hexp : Complex.exp (-(a : ℂ)) = 1 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
        (mul_right_cancel₀ (show (-8 : ℂ) ≠ 0 by norm_num)
          (show Complex.exp (-(a : ℂ)) * (-8 : ℂ) = 1 * (-8 : ℂ) by
            simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0))
    have hreal : Real.exp (-a) = 1 := by
      have hcast : -(a : ℂ) = ((-a : ℝ) : ℂ) := by push_cast; rfl
      have hre := congrArg Complex.re hexp
      rw [hcast, Complex.exp_ofReal_re] at hre
      simpa using hre
    have ha : -a = 0 := (Real.exp_eq_one_iff _).1 hreal
    linarith
  · rintro rfl
    rw [EulerWickNormalizedInteractionHolonomyCompatible,
      eulerWickQuadraticParityCompression_normalizedInteraction_loop,
      eulerWickGammaSixRelativeHolonomy_eq]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- At one actual prime clock, the one-packet loop law is exactly critical-line placement. -/
theorem eulerWickPrimeNormalizedInteractionHolonomyCompatible_iff
    (q : _root_.RHTower.XiZeroCopy) (p : Nat.Primes) :
    EulerWickNormalizedInteractionHolonomyCompatible
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [eulerWickNormalizedInteractionHolonomyCompatible_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- Global compatibility of the literal EWQ packet with one fixed prime holonomy is RH. -/
theorem everyEulerWickNormalizedInteractionHolonomyCompatible_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ q : _root_.RHTower.XiZeroCopy,
      EulerWickNormalizedInteractionHolonomyCompatible
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (eulerWickPrimeNormalizedInteractionHolonomyCompatible_iff q p).1 (h q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickPrimeNormalizedInteractionHolonomyCompatible_iff q p).2
    exact _root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end GaloisForLFunctions.RHTower
