import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixTameReaderTransgression
import GaloisForLFunctions.RHTower.GaussReciprocalCharacterAdmission
import GaloisForLFunctions.HTGeometry.ExteriorOddDerivation

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open ExteriorAlgebra

noncomputable section

/-- Pair the two opposite physical-character defects on literal cyclic boundaries. -/
def sourceHorizontalGammaSixOppositeBoundaryCurvature
    (a : ℝ)
    (f g : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) : ℝ :=
  -sourceHorizontalGammaSixCyclicCharacterReadout a
      ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom f) *
    sourceHorizontalGammaSixCyclicCharacterReadout (-a)
      ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom g)

/-- Exact factorization: paired Beck--Chevalley curvature is reciprocal-character split energy,
with coefficient equal to the two primitive readouts. -/
theorem sourceHorizontalGammaSixOppositeBoundaryCurvature_eq_splitEnergy
    (a : ℝ) (f g : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) :
    sourceHorizontalGammaSixOppositeBoundaryCurvature a f g =
      reciprocalCharacterSplitEnergy
        (sourceHorizontalGammaSixCyclicCharacterReadout a f *
          sourceHorizontalGammaSixCyclicCharacterReadout (-a) g) 1 a := by
  have hscalar :
      -(Real.exp a - 1) * (Real.exp (-a) - 1) =
        2 * (Real.cosh a - 1) := by
    have hprod : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [Real.cosh_eq]
    calc
      -(Real.exp a - 1) * (Real.exp (-a) - 1) =
          Real.exp a + Real.exp (-a) - 2 := by nlinarith
      _ = 2 * ((Real.exp a + Real.exp (-a)) / 2 - 1) := by ring_nf
  rw [sourceHorizontalGammaSixOppositeBoundaryCurvature,
    sourceHorizontalGammaSixCyclicCharacterReadout_boundary,
    sourceHorizontalGammaSixCyclicCharacterReadout_boundary,
    reciprocalCharacterSplitEnergy]
  calc
    -((Real.exp a - 1) * sourceHorizontalGammaSixCyclicCharacterReadout a f) *
          ((Real.exp (-a) - 1) *
            sourceHorizontalGammaSixCyclicCharacterReadout (-a) g) =
        (-(Real.exp a - 1) * (Real.exp (-a) - 1)) *
          (sourceHorizontalGammaSixCyclicCharacterReadout a f *
            sourceHorizontalGammaSixCyclicCharacterReadout (-a) g) := by ring_nf
    _ = 2 * (Real.cosh a - 1) *
          (sourceHorizontalGammaSixCyclicCharacterReadout a f *
            sourceHorizontalGammaSixCyclicCharacterReadout (-a) g) := by rw [hscalar]
    _ = 2 *
          (sourceHorizontalGammaSixCyclicCharacterReadout a f *
            sourceHorizontalGammaSixCyclicCharacterReadout (-a) g) *
          (Real.cosh (1 * a) - 1) := by ring_nf

/-- Unit primitive in the literal Gamma-six cyclic source. -/
def sourceHorizontalGammaSixCyclicUnit :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  MonoidAlgebra.single 1 1

@[simp] theorem sourceHorizontalGammaSixCyclicCharacterReadout_unit (a : ℝ) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
      sourceHorizontalGammaSixCyclicUnit = 1 := by
  rw [sourceHorizontalGammaSixCyclicUnit,
    sourceHorizontalGammaSixCyclicCharacterReadout_single]
  norm_num

/-- Canonical paired curvature obtained from the same unit primitive in both orientations. -/
def sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (a : ℝ) : ℝ :=
  sourceHorizontalGammaSixOppositeBoundaryCurvature a
    sourceHorizontalGammaSixCyclicUnit sourceHorizontalGammaSixCyclicUnit

/-- Forward physical-character defect on the canonical literal boundary. -/
def sourceHorizontalGammaSixUnitForwardBoundaryDefect (a : ℝ) : ℝ :=
  sourceHorizontalGammaSixCyclicCharacterReadout a
    ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom
      sourceHorizontalGammaSixCyclicUnit)

/-- Reflected physical-character defect on the same canonical literal boundary. -/
def sourceHorizontalGammaSixUnitReflectedBoundaryDefect (a : ℝ) : ℝ :=
  sourceHorizontalGammaSixCyclicCharacterReadout (-a)
    ((deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom
      sourceHorizontalGammaSixCyclicUnit)

theorem sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq (a : ℝ) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect a = Real.exp a - 1 := by
  rw [sourceHorizontalGammaSixUnitForwardBoundaryDefect,
    sourceHorizontalGammaSixCyclicCharacterReadout_boundary]
  simp

theorem sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq (a : ℝ) :
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect a = Real.exp (-a) - 1 := by
  rw [sourceHorizontalGammaSixUnitReflectedBoundaryDefect,
    sourceHorizontalGammaSixCyclicCharacterReadout_boundary]
  simp

/-- The canonical second-order cyclic defect is exactly `2(cosh a-1)`. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a =
      2 * (Real.cosh a - 1) := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature,
    sourceHorizontalGammaSixOppositeBoundaryCurvature_eq_splitEnergy]
  simp [reciprocalCharacterSplitEnergy]

/-- Nonlinear codiagonal law: the sum of the two opposite defects is their positive paired
curvature. Linear antidiagonal cancellation survives only to first order. -/
theorem sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_curvature (a : ℝ) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect a +
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect a =
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq, Real.cosh_eq]
  ring_nf

/-- The same curvature is minus the product of the two individual boundary defects. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a =
      -sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect a := by
  rfl

theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg (a : ℝ) :
    0 ≤ sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  nlinarith [Real.one_le_cosh a]

/-- The paired boundary curvature has the exact neutral radical. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff (a : ℝ) :
    0 < sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a ↔ a ≠ 0 := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  constructor
  · intro h ha
    subst ha
    simp at h
  · intro ha
    have hcosh := Real.one_lt_cosh.mpr ha
    linarith

theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff (a : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have hpos :=
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).2 ha
    linarith
  · rintro rfl
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-- Exact finite source law still missing from the RH producer: additive cancellation of the two
opposite boundary defects holds exactly at neutral character. -/
theorem sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_zero_iff (a : ℝ) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect a +
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect a = 0 ↔ a = 0 := by
  rw [sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_curvature,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]

/-- Linear cancellation sees no obstruction: the paired nonlinear codiagonal has zero first jet
at the neutral character. -/
theorem hasDerivAt_sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_zero :
    HasDerivAt sourceHorizontalGammaSixUnitOppositeBoundaryCurvature 0 0 := by
  have hfun : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature =
      reciprocalCharacterSplitEnergy 1 1 := by
    funext a
    rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
      reciprocalCharacterSplitEnergy]
    ring_nf
  rw [hfun]
  simpa using hasDerivAt_reciprocalCharacterSplitEnergy 1 1 0

/-- The obstruction reappears sharply at second order with universal coefficient two. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_secondJet :
    deriv (fun a : ℝ => deriv sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) 0 = 2 := by
  have hfun : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature =
      reciprocalCharacterSplitEnergy 1 1 := by
    funext a
    rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
      reciprocalCharacterSplitEnergy]
    ring_nf
  rw [hfun]
  simpa using (reciprocalCharacter_common_quadratic_jet 1 1).1

/-- Prime-clocked paired cyclic curvature. -/
def sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
    (lambda t : ℝ) : ℝ :=
  sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (lambda * t)

/-- The paired cyclic curvature is the universal reciprocal split energy, at every clock. -/
theorem sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_eq_splitEnergy
    (lambda t : ℝ) :
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda t =
      reciprocalCharacterSplitEnergy 1 lambda t := by
  rw [sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    reciprocalCharacterSplitEnergy]
  ring_nf

/-- Its infinitesimal response is the hyperbolic virial derivative. -/
theorem hasDerivAt_sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
    (lambda t : ℝ) :
    HasDerivAt (sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda)
      (2 * lambda * Real.sinh (lambda * t)) t := by
  have hfun : sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy lambda =
      reciprocalCharacterSplitEnergy 1 lambda := by
    funext x
    exact sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_eq_splitEnergy lambda x
  rw [hfun]
  simpa using hasDerivAt_reciprocalCharacterSplitEnergy 1 lambda t

/-- Literal Gauss coefficient multiplying the paired cyclic source curvature. -/
def gaussGammaSixPairedBoundaryEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  gaussReciprocalCharacterWeight m p *
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy
      (Real.log (p : ℝ)) t

theorem gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    gaussGammaSixPairedBoundaryEnergy m p t =
      reciprocalCharacterSplitEnergy (gaussReciprocalCharacterWeight m p)
        (Real.log (p : ℝ)) t := by
  rw [gaussGammaSixPairedBoundaryEnergy,
    sourceHorizontalGammaSixPrimeClockPairedBoundaryEnergy_eq_splitEnergy,
    reciprocalCharacterSplitEnergy, reciprocalCharacterSplitEnergy]
  ring_nf

/-- Frankenstein conservation law: Gauss Hodge mass is the Euler response of the literal paired
opposite-character boundary curvature. -/
theorem gaussHodgeMassCurrent_eq_euler_gaussGammaSixPairedBoundaryEnergy
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      primeDepthBVWoldXiCenteredRate q.1 *
        deriv (gaussGammaSixPairedBoundaryEnergy m p)
          (primeDepthBVWoldXiCenteredRate q.1) := by
  have hfun : gaussGammaSixPairedBoundaryEnergy m p =
      reciprocalCharacterSplitEnergy (gaussReciprocalCharacterWeight m p)
        (Real.log (p : ℝ)) := by
    funext t
    exact gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy m p t
  rw [hfun, ← reciprocalCharacterVirial_eq_t_mul_deriv,
    ← gaussHodgeMassCurrent_eq_reciprocalCharacterVirial]

/-- At a literal prime clock and Xi divisor copy, finite additive cancellation of opposite cyclic
boundary defects is exactly critical-line placement. -/
theorem sourceHorizontalGammaSixPrimePhysicalBoundaryDefects_add_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalGammaSixUnitForwardBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) +
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_zero_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  constructor
  · intro h
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp h).resolve_left hlog)
  · intro hline
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline, mul_zero]

/-- Diagonal contragredience is flat: simultaneous generator translation is invisible to the
product of the two opposite cyclic characters. -/
theorem sourceHorizontalGammaSixOppositeCharacter_diagonalGenerator_flat (a : ℝ) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
        (MonoidAlgebra.single
          (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1) *
      sourceHorizontalGammaSixCyclicCharacterReadout (-a)
        (MonoidAlgebra.single
          (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1) = 1 := by
  rw [sourceHorizontalGammaSixCyclicCharacterReadout_single,
    sourceHorizontalGammaSixCyclicCharacterReadout_single]
  have hval : Multiplicative.toAdd
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) = (1 : ℤ) := rfl
  rw [hval]
  push_cast
  simp only [mul_one]
  rw [← Real.exp_add]
  norm_num

/-- Diagonal flatness does not annihilate the two individual boundary defects: their paired
curvature is strictly positive at every nonneutral character. -/
theorem sourceHorizontalGammaSix_diagonalFlat_but_pairedCurvature_pos_iff (a : ℝ) :
    (sourceHorizontalGammaSixCyclicCharacterReadout a
          (MonoidAlgebra.single
            (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1) *
        sourceHorizontalGammaSixCyclicCharacterReadout (-a)
          (MonoidAlgebra.single
            (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1) = 1 ∧
      0 < sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a) ↔ a ≠ 0 := by
  constructor
  · intro h
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).1 h.2
  · intro ha
    exact ⟨sourceHorizontalGammaSixOppositeCharacter_diagonalGenerator_flat a,
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).2 ha⟩

/-- Any scalar algebra character of an exterior source kills every odd generator. -/
theorem exteriorAlgebraRealCharacter_generator_eq_zero
    {U : Type*} [AddCommGroup U] [Module ℝ U]
    (F : ExteriorAlgebra ℝ U →ₐ[ℝ] ℝ) (u : U) :
    F (ExteriorAlgebra.ι ℝ u) = 0 := by
  have hs := congrArg F (ExteriorAlgebra.ι_sq_zero u)
  rw [map_mul, map_zero] at hs
  nlinarith

/-- A nonneutral physical defect cannot extend to a multiplicative scalar character on even the
two-generator exterior source. Thus square-zero/Bianchi packaging alone cannot kill the positive
paired curvature; a genuinely nonmultiplicative trace/Stokes law is required. -/
theorem not_exists_exteriorCharacter_carrying_oppositePhysicalDefects
    {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ F : ExteriorAlgebra ℝ (ℝ × ℝ) →ₐ[ℝ] ℝ,
        F (ExteriorAlgebra.ι ℝ ((1, 0) : ℝ × ℝ)) = Real.exp a - 1 ∧
        F (ExteriorAlgebra.ι ℝ ((0, 1) : ℝ × ℝ)) = Real.exp (-a) - 1 := by
  rintro ⟨F, hforward, _hreflected⟩
  have hzero := exteriorAlgebraRealCharacter_generator_eq_zero F ((1, 0) : ℝ × ℝ)
  rw [hforward] at hzero
  have hexp : Real.exp a = 1 := sub_eq_zero.mp hzero
  have : a = 0 := Real.exp_injective (by simpa using hexp)
  exact ha this

end

end RHTower
