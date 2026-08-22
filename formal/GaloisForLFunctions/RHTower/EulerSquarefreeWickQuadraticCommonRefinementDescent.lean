import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixCurvatureBridge
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming

/-!
# Quadratic common-refinement descent for the EWQ--Gamma-six carrier

The regular two-gauge square has two literal commuting involutions: row flip and column flip.
Its total/checkerboard parity quotient is a coefficient-faithful two-state carrier, and both source
flips descend to the same bare reflection.  This is the canonical dimension-preserving descent of
the mixed EWQ mode before any Xi divisor is selected.

The physical Gamma-six character transports one target reflection by a positive half-density.
The main classification proves that a surjective linear descent intertwining the two commuting
source gauges with the bare and transported target reflections exists exactly at neutral grade.
Equivalently, it exists exactly when the EWQ-valued Gamma-six interaction class vanishes.  At a
prime clock and multiplicity-labelled Xi divisor this is critical-line placement, and demanding the
descent for all divisor copies is equivalent to RH.

Thus completed common-refinement landing and the orientation law are not two separable open steps:
surjective equivariance already contains the entire orientation obstruction.
-/

open Complex Matrix

namespace GaloisForLFunctions.RHTower

noncomputable section

abbrev EulerWickQuadraticCommonRefinement := Fin 2 × Fin 2 → ℂ

/-- Flip the first quadratic gauge coordinate of the regular common-refinement carrier. -/
def eulerWickQuadraticRowFlip :
    EulerWickQuadraticCommonRefinement →ₗ[ℂ]
      EulerWickQuadraticCommonRefinement where
  toFun v x := v (1 - x.1, x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Flip the second quadratic gauge coordinate of the regular common-refinement carrier. -/
def eulerWickQuadraticColumnFlip :
    EulerWickQuadraticCommonRefinement →ₗ[ℂ]
      EulerWickQuadraticCommonRefinement where
  toFun v x := v (x.1, 1 - x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two literal quadratic source gauges commute on their common refinement. -/
theorem eulerWickQuadraticRowFlip_columnFlip_commute (v) :
    eulerWickQuadraticRowFlip (eulerWickQuadraticColumnFlip v) =
      eulerWickQuadraticColumnFlip (eulerWickQuadraticRowFlip v) := rfl

/-- The row gauge has order two. -/
theorem eulerWickQuadraticRowFlip_sq (v) :
    eulerWickQuadraticRowFlip (eulerWickQuadraticRowFlip v) = v := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases i <;> rfl

/-- The column gauge has order two. -/
theorem eulerWickQuadraticColumnFlip_sq (v) :
    eulerWickQuadraticColumnFlip (eulerWickQuadraticColumnFlip v) = v := by
  funext x
  rcases x with ⟨i, j⟩
  fin_cases j <;> rfl

/-- Collapse the four source values to total/checkerboard parity sectors. -/
def eulerWickQuadraticParityCompression :
    EulerWickQuadraticCommonRefinement →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v (0, 0) + v (1, 1), v (0, 1) + v (1, 0)]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Both parity sectors are retained: the canonical compression is onto. -/
theorem eulerWickQuadraticParityCompression_surjective :
    Function.Surjective eulerWickQuadraticParityCompression := by
  intro w
  let v : EulerWickQuadraticCommonRefinement := fun x =>
    if x = ((0 : Fin 2), (0 : Fin 2)) then w 0
    else if x = ((0 : Fin 2), (1 : Fin 2)) then w 1
    else 0
  refine ⟨v, ?_⟩
  ext i
  fin_cases i <;>
    simp [eulerWickQuadraticParityCompression, v]

/-- Row flip descends to the coefficient-free exchange reflection. -/
theorem eulerWickQuadraticParityCompression_rowFlip (v) :
    eulerWickQuadraticParityCompression (eulerWickQuadraticRowFlip v) =
      (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
        (eulerWickQuadraticParityCompression v) := by
  ext i
  fin_cases i <;>
    simp [eulerWickQuadraticParityCompression, eulerWickQuadraticRowFlip,
      _root_.RHTower.sourceHorizontalGammaSixBareReflection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    ring

/-- Column flip descends to the same coefficient-free exchange reflection. -/
theorem eulerWickQuadraticParityCompression_columnFlip (v) :
    eulerWickQuadraticParityCompression (eulerWickQuadraticColumnFlip v) =
      (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
        (eulerWickQuadraticParityCompression v) := by
  ext i
  fin_cases i <;>
    simp [eulerWickQuadraticParityCompression, eulerWickQuadraticColumnFlip,
      _root_.RHTower.sourceHorizontalGammaSixBareReflection, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- A coefficient-faithful common-refinement landing at horizontal grade `a`: one surjective
linear collapse must intertwine the commuting source flips with the bare and half-density
transported target reflections. -/
def EulerWickQuadraticCommonRefinementLanding (a : ℝ) : Prop :=
  ∃ L : EulerWickQuadraticCommonRefinement →ₗ[ℂ] (Fin 2 → ℂ),
    Function.Surjective L ∧
      (∀ v, L (eulerWickQuadraticRowFlip v) =
        (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec (L v)) ∧
      (∀ v, L (eulerWickQuadraticColumnFlip v) =
        (_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec (L v))

/-- **Exact descent obstruction.**  Surjective equivariant common-refinement descent exists exactly
at neutral horizontal grade. -/
theorem eulerWickQuadraticCommonRefinementLanding_iff (a : ℝ) :
    EulerWickQuadraticCommonRefinementLanding a ↔ a = 0 := by
  constructor
  · rintro ⟨L, hL, hrow, hcol⟩
    let w : Fin 2 → ℂ := ![1, 0]
    obtain ⟨v, hv⟩ := hL w
    have hpath :
        (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
            ((_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec (L v)) =
          (_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec
            ((_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec (L v)) := by
      calc
        _ = (_root_.RHTower.sourceHorizontalGammaSixBareReflection).mulVec
              (L (eulerWickQuadraticColumnFlip v)) := by rw [hcol]
        _ = L (eulerWickQuadraticRowFlip
              (eulerWickQuadraticColumnFlip v)) := by rw [hrow]
        _ = L (eulerWickQuadraticColumnFlip
              (eulerWickQuadraticRowFlip v)) := by
              rw [eulerWickQuadraticRowFlip_columnFlip_commute]
        _ = (_root_.RHTower.sourceHorizontalGammaSixTransportedReflection a).mulVec
              (L (eulerWickQuadraticRowFlip v)) := by rw [hcol]
        _ = _ := by rw [hrow]
    rw [hv] at hpath
    have h0 := congrFun hpath (0 : Fin 2)
    have h0re :
        (Complex.exp (-(a : ℂ))).re = (Complex.exp (a : ℂ)).re := by
      simpa [w, _root_.RHTower.sourceHorizontalGammaSixBareReflection,
        _root_.RHTower.sourceHorizontalGammaSixTransportedReflection,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrArg Complex.re h0
    have hexp : Real.exp (-a) = Real.exp a := by
      have hneg : -(a : ℂ) = ((-a : ℝ) : ℂ) := by push_cast; rfl
      rw [hneg, Complex.exp_ofReal_re] at h0re
      simpa only [Complex.exp_ofReal_re] using h0re
    have := Real.exp_injective hexp
    linarith
  · rintro rfl
    refine ⟨eulerWickQuadraticParityCompression,
      eulerWickQuadraticParityCompression_surjective, ?_, ?_⟩
    · exact eulerWickQuadraticParityCompression_rowFlip
    · intro v
      simpa [_root_.RHTower.sourceHorizontalGammaSixTransportedReflection,
        _root_.RHTower.sourceHorizontalGammaSixBareReflection] using
        eulerWickQuadraticParityCompression_columnFlip v

/-- Common-refinement descent exists exactly when the EWQ-valued Gamma-six class vanishes. -/
theorem eulerWickQuadraticCommonRefinementLanding_iff_interactionClass_zero
    (a : ℝ) :
    EulerWickQuadraticCommonRefinementLanding a ↔
      gammaSixOppositeGaugeInteractionClass a = 0 := by
  rw [eulerWickQuadraticCommonRefinementLanding_iff,
    gammaSixOppositeGaugeInteractionClass_eq_zero_iff]

/-- At an actual prime clock, descent exists exactly when the selected Xi copy lies on the line. -/
theorem eulerWickQuadraticPrimeCommonRefinementLanding_iff
    (q : _root_.RHTower.XiZeroCopy) (p : Nat.Primes) :
    EulerWickQuadraticCommonRefinementLanding
        (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [eulerWickQuadraticCommonRefinementLanding_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

/-- One fixed prime supports physical common-refinement descent at every Xi multiplicity copy. -/
def EulerWickQuadraticPhysicalCommonRefinementLanding
    (p : Nat.Primes) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    EulerWickQuadraticCommonRefinementLanding
      (Real.log (p : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)

/-- The all-divisor common-refinement descent law is equivalent to RH. -/
theorem eulerWickQuadraticPhysicalCommonRefinementLanding_iff_riemannHypothesis
    (p : Nat.Primes) :
    EulerWickQuadraticPhysicalCommonRefinementLanding p ↔
      RiemannHypothesis := by
  constructor
  · intro hlanding
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (eulerWickQuadraticPrimeCommonRefinementLanding_iff q p).1 (hlanding q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickQuadraticPrimeCommonRefinementLanding_iff q p).2
    exact _root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end GaloisForLFunctions.RHTower
