import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2Inflation
import GaloisForLFunctions.HTGeometry.ABHN.FiniteTorsionInvariantTransition

/-!
# Local-invariant defect of actual cohomological inflation

Suppose finite continuous unit-`H²` layers are identified with finite torsion subgroups of
`RatModInt`.  There are then two maps between layers: actual cohomological inflation and canonical
transport through the invariant coordinates.  Their difference in target coordinates is the
inflation-invariant defect.

The defect vanishes exactly when actual inflation is the canonical torsion transition, equivalently
when the standard complex phases are stable.  Defects satisfy a cocycle law through scalar towers.
Thus failure of local-invariant compatibility is not merely a proposition: it is an additive,
coherently propagating obstruction.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Difference between the target invariant after actual inflation and finite-torsion inclusion of
the source invariant. -/
def finiteGaloisContinuousH2InflationInvariantDefect
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M]
    {m n : ℕ}
    (eL : continuousGaloisH2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisH2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) :
    continuousGaloisH2 K L →+ ratModIntNTorsion n :=
  eM.toAddMonoidHom.comp (finiteGaloisContinuousH2Inflation K L M) -
    (ratModIntNTorsionInclusion hmn).comp eL.toAddMonoidHom

/-- Pointwise form of the inflation-invariant defect. -/
theorem finiteGaloisContinuousH2InflationInvariantDefect_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M]
    {m n : ℕ}
    (eL : continuousGaloisH2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisH2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2InflationInvariantDefect K L M eL eM hmn z =
      eM (finiteGaloisContinuousH2Inflation K L M z) -
        ratModIntNTorsionInclusion hmn (eL z) := rfl

/-- Defect vanishing is exactly equality of genuine cohomological inflation and canonical
invariant-coordinate transition. -/
theorem finiteGaloisContinuousH2InflationInvariantDefect_eq_zero_iff
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M]
    {m n : ℕ}
    (eL : continuousGaloisH2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisH2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) :
    finiteGaloisContinuousH2InflationInvariantDefect K L M eL eM hmn = 0 ↔
      finiteGaloisContinuousH2Inflation K L M =
        continuousGaloisH2TorsionTransition K L M eL eM hmn := by
  constructor
  · intro h
    apply finiteTorsionInvariantTransition_unique eL eM hmn
    intro z
    have hz := congrArg
      (fun f : continuousGaloisH2 K L →+ ratModIntNTorsion n ↦ f z) h
    change eM (finiteGaloisContinuousH2Inflation K L M z) -
      ratModIntNTorsionInclusion hmn (eL z) = 0 at hz
    exact sub_eq_zero.mp hz
  · intro h
    ext z
    rw [finiteGaloisContinuousH2InflationInvariantDefect_apply, h,
      continuousGaloisH2TorsionTransition_invariant]
    exact sub_self _

/-- Actual inflation is the canonical invariant transition exactly when its standard complex phase
is stable under refinement.  This is the nonlinear character form suited to reciprocity products. -/
theorem finiteGaloisContinuousH2Inflation_eq_torsionTransition_iff_character
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Normal K L] [FiniteDimensional K L] [FiniteDimensional K M]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (eL : continuousGaloisH2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisH2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) :
    finiteGaloisContinuousH2Inflation K L M =
        continuousGaloisH2TorsionTransition K L M eL eM hmn ↔
      ∀ z, continuousGaloisH2TorsionStdAddChar K M n hn eM
          (finiteGaloisContinuousH2Inflation K L M z) =
        continuousGaloisH2TorsionStdAddChar K L m hm eL z := by
  constructor
  · intro h z
    rw [h]
    exact continuousGaloisH2TorsionTransition_character K L M hm hn eL eM hmn z
  · intro h
    apply finiteTorsionInvariantTransition_unique eL eM hmn
    intro z
    apply ratModIntNTorsionStdAddChar_injective n hn
    rw [ratModIntNTorsionStdAddChar_inclusion hm hn hmn]
    exact h z

/-- Cocycle law for inflation-invariant defects through a three-level scalar tower.  The direct
defect equals the upper defect evaluated after lower inflation plus inclusion of the lower defect. -/
theorem finiteGaloisContinuousH2InflationInvariantDefect_cocycle
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [Normal K L] [Normal K M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    {l m n : ℕ}
    (eL : continuousGaloisH2 K L ≃+ ratModIntNTorsion l)
    (eM : continuousGaloisH2 K M ≃+ ratModIntNTorsion m)
    (eN : continuousGaloisH2 K N ≃+ ratModIntNTorsion n)
    (hlm : l ∣ m) (hmn : m ∣ n) (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2InflationInvariantDefect K L N eL eN
        (dvd_trans hlm hmn) z =
      finiteGaloisContinuousH2InflationInvariantDefect K M N eM eN hmn
          (finiteGaloisContinuousH2Inflation K L M z) +
        ratModIntNTorsionInclusion hmn
          (finiteGaloisContinuousH2InflationInvariantDefect K L M eL eM hlm z) := by
  rw [finiteGaloisContinuousH2InflationInvariantDefect_apply,
    finiteGaloisContinuousH2InflationInvariantDefect_apply,
    finiteGaloisContinuousH2InflationInvariantDefect_apply]
  have hcomp := congrArg
    (fun f : continuousGaloisH2 K L →+ continuousGaloisH2 K N ↦ f z)
    (finiteGaloisContinuousH2Inflation_comp K L M N)
  change finiteGaloisContinuousH2Inflation K M N
      (finiteGaloisContinuousH2Inflation K L M z) =
    finiteGaloisContinuousH2Inflation K L N z at hcomp
  rw [← hcomp]
  apply Subtype.ext
  change ((eN (finiteGaloisContinuousH2Inflation K M N
      (finiteGaloisContinuousH2Inflation K L M z)) : ratModIntNTorsion n) : RatModInt) -
        ((eL z : ratModIntNTorsion l) : RatModInt) =
    (((eN (finiteGaloisContinuousH2Inflation K M N
      (finiteGaloisContinuousH2Inflation K L M z)) : ratModIntNTorsion n) : RatModInt) -
        ((eM (finiteGaloisContinuousH2Inflation K L M z) :
          ratModIntNTorsion m) : RatModInt)) +
      (((eM (finiteGaloisContinuousH2Inflation K L M z) :
          ratModIntNTorsion m) : RatModInt) -
        ((eL z : ratModIntNTorsion l) : RatModInt))
  abel

end

end GaloisForLFunctions.HTGeometry.ABHN
