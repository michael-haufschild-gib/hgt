import GaloisForLFunctions.RHTower.XiPreDivisorReflectionDefectStabilization
import GaloisForLFunctions.RHTower.XiTransverseDualNumberArc
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPositiveStarUntwisting

/-!
# Pre-divisor transverse dual-number formal neighbourhood

The Route-R transverse infinitesimal is defined on the whole spectral plane before selecting an
Xi divisor.  Its coefficient is the already source-defined pre-divisor centered rate.  Reflection
reverses the infinitesimal frame while preserving its unframed image algebra.

This constructs the Xi-independent first-order object required by the reflection-normal derived
program.  It does not assert that completed Euler--Gamma formation makes the frame descend.  Its
specialization to the Xi divisor is exactly `xiTransverseDualNumberArc`.
-/

open Complex

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization

/-- Whole-plane transverse completion class formed before divisor selection. -/
def preDivisorTransverseCompletionDefect (s : ℂ) :
    RouteRSummableHadamardCorona :=
  routeRPrimeGammaCriticalWallSummableHadamardClass
    (preDivisorCenteredRate s)

/-- Whole-plane first-order transverse formal neighbourhood. -/
def preDivisorTransverseDualNumberArc (s : ℂ) :
    DualNumber ℂ →ₐ[ℂ] RouteRSummableHadamardCorona :=
  SquareZeroDualNumber.dualNumberMap
    (preDivisorTransverseCompletionDefect s)
    (routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero _)

@[simp]
theorem preDivisorTransverseDualNumberArc_apply
    (s : ℂ) (x : DualNumber ℂ) :
    preDivisorTransverseDualNumberArc s x =
      algebraMap ℂ RouteRSummableHadamardCorona x.fst +
        x.snd • preDivisorTransverseCompletionDefect s := by
  exact SquareZeroDualNumber.dualNumberMap_apply _ _ _

/-- Source reflection reverses the whole-plane transverse class. -/
theorem preDivisorTransverseCompletionDefect_lineConj (s : ℂ) :
    preDivisorTransverseCompletionDefect (preDivisorLineConj s) =
      -preDivisorTransverseCompletionDefect s := by
  rw [preDivisorTransverseCompletionDefect, preDivisorCenteredRate_lineConj,
    routeRPrimeGammaCriticalWallSummableHadamardClass_neg,
    preDivisorTransverseCompletionDefect]

/-- The pre-divisor transverse class is nonzero precisely off the reflection wall. -/
theorem preDivisorTransverseCompletionDefect_ne_zero_iff (s : ℂ) :
    preDivisorTransverseCompletionDefect s ≠ 0 ↔ s.re ≠ 1 / 2 := by
  rw [preDivisorTransverseCompletionDefect,
    routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff,
    preDivisorCenteredRate]
  constructor <;> intro h
  · intro hs
    apply h
    linarith
  · intro hz
    apply h
    linarith

/-- The whole-plane dual-number formal neighbourhood is faithful exactly off the wall. -/
theorem preDivisorTransverseDualNumberArc_injective_iff (s : ℂ) :
    Function.Injective (preDivisorTransverseDualNumberArc s) ↔
      s.re ≠ 1 / 2 := by
  rw [preDivisorTransverseDualNumberArc,
    SquareZeroDualNumber.dualNumberMap_injective_iff,
    preDivisorTransverseCompletionDefect_ne_zero_iff]

/-- Image algebra of the whole-plane source-normal arc. -/
abbrev PreDivisorTransverseArcAlgebra (s : ℂ) :=
  (preDivisorTransverseDualNumberArc s).range

/-- Off the reflection wall, the whole-plane image is an embedded dual-number algebra. -/
def preDivisorTransverseArcAlgEquiv
    (s : ℂ) (hoff : s.re ≠ 1 / 2) :
    DualNumber ℂ ≃ₐ[ℂ] PreDivisorTransverseArcAlgebra s :=
  AlgEquiv.ofInjective (preDivisorTransverseDualNumberArc s)
    ((preDivisorTransverseDualNumberArc_injective_iff s).2 hoff)

/-- Off-wall source-normal image has a nontrivial cotangent direction. -/
theorem preDivisorTransverseArcAlgebra_not_formallyUnramified_of_offWall
    (s : ℂ) (hoff : s.re ≠ 1 / 2) :
    ¬ Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra s) :=
  SquareZeroDualNumber.not_formallyUnramified_of_equiv
    (preDivisorTransverseArcAlgEquiv s hoff)

/-- On the reflection wall, the source-normal image collapses to the scalar algebra. -/
theorem preDivisorTransverseArcAlgebra_formallyUnramified_of_onWall
    (s : ℂ) (hwall : s.re = 1 / 2) :
    Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra s) := by
  have hzero : preDivisorTransverseCompletionDefect s = 0 := by
    by_contra hne
    exact ((preDivisorTransverseCompletionDefect_ne_zero_iff s).1 hne) hwall
  apply Algebra.FormallyUnramified.of_surjective
    (Algebra.ofId ℂ (PreDivisorTransverseArcAlgebra s))
  intro y
  rcases y.2 with ⟨x, hx⟩
  refine ⟨x.fst, ?_⟩
  apply Subtype.ext
  change algebraMap ℂ RouteRSummableHadamardCorona x.fst = y.1
  calc
    algebraMap ℂ RouteRSummableHadamardCorona x.fst =
        preDivisorTransverseDualNumberArc s x := by
      rw [preDivisorTransverseDualNumberArc_apply, hzero, smul_zero, add_zero]
    _ = y.1 := hx

/-- Exact whole-plane directional formal-unramified locus. -/
theorem preDivisorTransverseArcAlgebra_formallyUnramified_iff (s : ℂ) :
    Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra s) ↔
      s.re = 1 / 2 := by
  constructor
  · intro hunramified
    by_contra hoff
    exact
      (preDivisorTransverseArcAlgebra_not_formallyUnramified_of_offWall s hoff)
        hunramified
  · exact preDivisorTransverseArcAlgebra_formallyUnramified_of_onWall s

/-- Reflection is the sign involution on the whole-plane framed arc. -/
theorem preDivisorTransverseDualNumberArc_lineConj_comp_sign (s : ℂ) :
    preDivisorTransverseDualNumberArc (preDivisorLineConj s) =
      (preDivisorTransverseDualNumberArc s).comp
        GaloisForLFunctions.HTGeometry.dualNumberSignHom := by
  apply AlgHom.ext
  intro x
  rw [preDivisorTransverseDualNumberArc_apply, AlgHom.comp_apply,
    preDivisorTransverseDualNumberArc_apply,
    preDivisorTransverseCompletionDefect_lineConj]
  simp [GaloisForLFunctions.HTGeometry.dualNumberSignHom]

/-- Forgetting the source-normal frame erases reflection displacement on the whole plane. -/
theorem preDivisorTransverseDualNumberArc_range_lineConj (s : ℂ) :
    (preDivisorTransverseDualNumberArc (preDivisorLineConj s)).range =
      (preDivisorTransverseDualNumberArc s).range := by
  rw [preDivisorTransverseDualNumberArc_lineConj_comp_sign]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨GaloisForLFunctions.HTGeometry.dualNumberSignHom x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨GaloisForLFunctions.HTGeometry.dualNumberSignHom x, ?_⟩
    simp [AlgHom.comp_apply,
      GaloisForLFunctions.HTGeometry.dualNumberSignHom_involutive]

/-- Covariant frame transport is automatic: after transporting the reflected normal coordinate
by its natural sign action, the two source arcs agree at every spectral point. -/
theorem preDivisorTransverseDualNumberArc_covariantDescends (s : ℂ) :
    (preDivisorTransverseDualNumberArc (preDivisorLineConj s)).comp
        GaloisForLFunctions.HTGeometry.dualNumberSignHom =
      preDivisorTransverseDualNumberArc s := by
  rw [preDivisorTransverseDualNumberArc_lineConj_comp_sign]
  apply AlgHom.ext
  intro x
  simp [AlgHom.comp_apply,
    GaloisForLFunctions.HTGeometry.dualNumberSignHom_involutive]

/-- Whole-plane framed reflection descent occurs exactly on the reflection wall. -/
theorem preDivisorTransverseDualNumberArc_lineConj_eq_iff (s : ℂ) :
    preDivisorTransverseDualNumberArc (preDivisorLineConj s) =
        preDivisorTransverseDualNumberArc s ↔
      s.re = 1 / 2 := by
  constructor
  · intro hframe
    have heps := DFunLike.congr_fun hframe
      (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)
    rw [preDivisorTransverseDualNumberArc_apply,
      preDivisorTransverseDualNumberArc_apply,
      preDivisorTransverseCompletionDefect_lineConj] at heps
    simp only [TrivSqZeroExt.fst_inr, map_zero,
      TrivSqZeroExt.snd_inr, one_smul, zero_add] at heps
    have hzero : preDivisorTransverseCompletionDefect s = 0 := by
      have hadd : preDivisorTransverseCompletionDefect s +
          preDivisorTransverseCompletionDefect s = 0 := by
        calc
          preDivisorTransverseCompletionDefect s +
              preDivisorTransverseCompletionDefect s =
            preDivisorTransverseCompletionDefect s +
              (-preDivisorTransverseCompletionDefect s) := by rw [heps]
          _ = 0 := add_neg_cancel _
      have hsmul : (2 : ℂ) • preDivisorTransverseCompletionDefect s = 0 := by
        simpa [two_smul] using hadd
      exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
    by_contra hoff
    exact (preDivisorTransverseCompletionDefect_ne_zero_iff s).2 hoff hzero
  · intro hline
    apply AlgHom.ext
    intro x
    rw [preDivisorTransverseDualNumberArc_apply,
      preDivisorTransverseDualNumberArc_apply,
      preDivisorTransverseCompletionDefect_lineConj]
    have hzero : preDivisorTransverseCompletionDefect s = 0 := by
      by_contra hne
      exact ((preDivisorTransverseCompletionDefect_ne_zero_iff s).1 hne) hline
    rw [hzero, neg_zero]

/-- Whole-plane source-fixed star law on the canonical cyclic Hermitian square.  This is a shadow
of fixed-frame descent, not an additional source theorem. -/
def PreDivisorTransverseSourceStarPositive (s : ℂ) : Prop :=
  0 ≤ sourceHorizontalGammaSixCyclicCharacterReadout
      (sourceHorizontalGammaSixPhysicalCharacterParameter s)
      sourceHorizontalGammaSixCyclicHermitianSquare

/-- The source-fixed star locus is exactly the reflection wall. -/
theorem preDivisorTransverseSourceStarPositive_iff (s : ℂ) :
    PreDivisorTransverseSourceStarPositive s ↔ s.re = 1 / 2 := by
  rw [PreDivisorTransverseSourceStarPositive,
    sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare_nonneg_iff,
    sourceHorizontalGammaSixPhysicalCharacterParameter]
  have hlog : Real.log (6 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · intro hzero
    have hrate : 2 * s.re - 1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hlog
    linarith
  · intro hwall
    apply mul_eq_zero_of_left
    linarith

/-- Fixed-frame descent and the minimal fixed-star law are the same pre-divisor obstruction. -/
theorem preDivisorTransverseDualNumberArc_sourceFixed_iff_starPositive (s : ℂ) :
    preDivisorTransverseDualNumberArc (preDivisorLineConj s) =
        preDivisorTransverseDualNumberArc s ↔
      PreDivisorTransverseSourceStarPositive s := by
  rw [preDivisorTransverseDualNumberArc_lineConj_eq_iff,
    preDivisorTransverseSourceStarPositive_iff]

/-- The whole-plane construction specializes coefficient-for-coefficient to the Xi transverse
class; no post-divisor frame is inserted. -/
theorem preDivisorTransverseCompletionDefect_at_xiSupport
    (rho : XiDivisorSupport) :
    preDivisorTransverseCompletionDefect (rho : ℂ) =
      xiTransverseCompletionDefect rho := by
  rfl

/-- The pre-divisor first-order formal neighbourhood restricts exactly to the Xi-divisor arc. -/
theorem preDivisorTransverseDualNumberArc_at_xiSupport
    (rho : XiDivisorSupport) :
    preDivisorTransverseDualNumberArc (rho : ℂ) =
      xiTransverseDualNumberArc rho := by
  apply AlgHom.ext
  intro x
  rw [preDivisorTransverseDualNumberArc_apply,
    xiTransverseDualNumberArc_apply,
    preDivisorTransverseCompletionDefect_at_xiSupport]

end

end RHTower
