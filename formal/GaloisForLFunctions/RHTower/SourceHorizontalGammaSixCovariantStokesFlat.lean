import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixTameReaderTransgression

/-!
# Covariant Stokes flatness of the literal Gamma-six cyclic character

The fixed Deninger cyclic differential is `t - 1`, while the literal horizontal character sends
`t` to `exp(a)`.  The corresponding rank-one local system therefore has covariant differential
`t - exp(a)`.  This file constructs that differential on the existing cyclic source and proves
that the existing physical character kills it identically, before any Xi or prime specialization.

The result is not fitted prime cancellation: holonomy is the value of the same character on the
source generator, and is independent of prime labels.  A uniqueness theorem proves that no other
scalar local-system differential works.  The final untwisting theorem is sharp: the covariant
differential equals the fixed `t - 1` differential exactly at neutral horizontal grade.  Thus the
new producer is genuine Stokes flatness, not boundary exactness, while the remaining RH-bearing
operation is now precisely trivialization of its source holonomy.
-/

open Complex

namespace RHTower

noncomputable section

/-- Cyclic source differential with scalar holonomy `u`: algebraically `t - u`. -/
def sourceHorizontalGammaSixHolonomyBoundary (u : ℝ) :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup →ₗ[ℝ]
      MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap -
    (u - 1) • LinearMap.id

@[simp] theorem sourceHorizontalGammaSixHolonomyBoundary_apply
    (u : ℝ) (f : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) :
    sourceHorizontalGammaSixHolonomyBoundary u f =
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom f -
        (u - 1) • f := by
  simp [sourceHorizontalGammaSixHolonomyBoundary]

/-- Universal local-coefficient Stokes formula.  The complete anomaly is the mismatch between
physical holonomy `exp(a)` and source holonomy `u`. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary
    (a u : ℝ) (f : MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
        (sourceHorizontalGammaSixHolonomyBoundary u f) =
      (Real.exp a - u) * sourceHorizontalGammaSixCyclicCharacterReadout a f := by
  rw [sourceHorizontalGammaSixHolonomyBoundary_apply, map_sub, map_smul,
    sourceHorizontalGammaSixCyclicCharacterReadout_boundary]
  simp only [smul_eq_mul]
  ring

/-- **Literal covariant Stokes producer.**  Every horizontal character annihilates the cyclic
differential carrying its own source holonomy.  This is character flatness, not a statement that
one selected boundary happens to be exact. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_covariantStokesFlat
    (a : ℝ) :
    (sourceHorizontalGammaSixCyclicCharacterReadout a).comp
        (sourceHorizontalGammaSixHolonomyBoundary (Real.exp a)) = 0 := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.comp_apply, LinearMap.zero_apply,
    sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary]
  ring

/-- Holonomy is forced coefficient-faithfully: no different scalar cyclic differential makes the
literal character Stokes-flat. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary_eq_zero_iff
    (a u : ℝ) :
    (sourceHorizontalGammaSixCyclicCharacterReadout a).comp
        (sourceHorizontalGammaSixHolonomyBoundary u) = 0 ↔
      u = Real.exp a := by
  constructor
  · intro hzero
    have h := LinearMap.congr_fun hzero
      (MonoidAlgebra.single (1 : SourceHorizontalGammaSixCyclicGroup) (1 : ℝ))
    rw [LinearMap.comp_apply, LinearMap.zero_apply,
      sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary,
      sourceHorizontalGammaSixCyclicCharacterReadout_single] at h
    norm_num at h
    exact (sub_eq_zero.mp h).symm
  · rintro rfl
    exact sourceHorizontalGammaSixCyclicCharacterReadout_covariantStokesFlat a

/-- The local-system differential is the fixed Deninger differential exactly at trivial
holonomy. -/
theorem sourceHorizontalGammaSixHolonomyBoundary_eq_deningerZBoundary_iff
    (u : ℝ) :
    sourceHorizontalGammaSixHolonomyBoundary u =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap ↔
      u = 1 := by
  constructor
  · intro hboundary
    have hflat :
        (sourceHorizontalGammaSixCyclicCharacterReadout 0).comp
            (sourceHorizontalGammaSixHolonomyBoundary u) = 0 := by
      rw [hboundary]
      exact
        (sourceHorizontalGammaSixCyclicCharacterReadout_comp_boundary_eq_zero_iff 0).2 rfl
    have hu :=
      (sourceHorizontalGammaSixCyclicCharacterReadout_holonomyBoundary_eq_zero_iff 0 u).1
        hflat
    simpa using hu
  · rintro rfl
    simp [sourceHorizontalGammaSixHolonomyBoundary]

/-- Genuine Gamma-six physical holonomy, selected before any ordinary-prime specialization. -/
def sourceHorizontalGammaSixPhysicalHolonomy (q : XiZeroCopy) : ℝ :=
  Real.exp (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))

/-- Xi-selected covariant source differential.  It retains the literal cyclic group algebra and
changes only its rank-one coefficient system. -/
def sourceHorizontalGammaSixPhysicalCovariantBoundary (q : XiZeroCopy) :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup →ₗ[ℝ]
      MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  sourceHorizontalGammaSixHolonomyBoundary
    (sourceHorizontalGammaSixPhysicalHolonomy q)

/-- **Unconditional source-selected producer.**  The literal cyclic physical character is
Stokes-flat on its genuine Gamma local system for every retained Xi divisor copy. -/
theorem sourceZeroGammaSixCyclicPhysicalCharacter_covariantStokesFlat
    (q : XiZeroCopy) :
    (sourceHorizontalGammaSixCyclicCharacterReadout
        (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).comp
      (sourceHorizontalGammaSixPhysicalCovariantBoundary q) = 0 := by
  rw [sourceHorizontalGammaSixPhysicalCovariantBoundary,
    sourceHorizontalGammaSixPhysicalHolonomy]
  exact sourceHorizontalGammaSixCyclicCharacterReadout_covariantStokesFlat _

/-- The covariant source untwists to the fixed Deninger source exactly on the critical line. -/
theorem sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff
    (q : XiZeroCopy) :
    sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixPhysicalCovariantBoundary,
    sourceHorizontalGammaSixHolonomyBoundary_eq_deningerZBoundary_iff,
    sourceHorizontalGammaSixPhysicalHolonomy]
  constructor
  · intro h
    have hparameter :
        sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ) = 0 :=
      (Real.exp_eq_one_iff _).1 h
    rw [sourceHorizontalGammaSixPhysicalCharacterParameter] at hparameter
    have hlog : Real.log (6 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp hparameter).resolve_right hlog)
  · intro hline
    rw [sourceHorizontalGammaSixPhysicalCharacterParameter, hline]
    norm_num

/-- Pointwise fixed-source descent and covariant-source untwisting are the same operation. -/
theorem sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff_sourceUntwisting
    (q : XiZeroCopy) :
    SourceZeroGammaSixCyclicPhysicalCharacterDescends q ↔
      sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap := by
  rw [sourceZeroGammaSixCyclicPhysicalCharacterDescends_iff,
    sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff]

/-- Covariant flatness descends to the fixed source once source holonomy is trivialized. -/
theorem sourceZeroGammaSixCyclicPhysicalCharacterDescends_of_sourceUntwisting
    (q : XiZeroCopy)
    (huntwist : sourceHorizontalGammaSixPhysicalCovariantBoundary q =
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap) :
    SourceZeroGammaSixCyclicPhysicalCharacterDescends q := by
  rw [SourceZeroGammaSixCyclicPhysicalCharacterDescends, ← huntwist]
  exact sourceZeroGammaSixCyclicPhysicalCharacter_covariantStokesFlat q

/-- Global source-holonomy trivialization is exactly RH.  This prevents the covariant producer
from being mistaken for the still-missing fixed-source theorem. -/
theorem everySourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap) ↔
      RiemannHypothesis := by
  constructor
  · intro huntwist
    apply sourceZeroGammaSixCyclicPhysicalCharactersDescend_iff_riemannHypothesis.mp
    intro q
    exact sourceZeroGammaSixCyclicPhysicalCharacterDescends_of_sourceUntwisting q
      (huntwist q)
  · intro hRH q
    apply (sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
