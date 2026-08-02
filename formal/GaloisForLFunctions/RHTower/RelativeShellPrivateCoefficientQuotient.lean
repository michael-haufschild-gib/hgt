import GaloisForLFunctions.RHTower.RelativeShellPrivateHypertranscendenceCoefficientWall

/-!
# Canonical infinite-rank private-shell coefficient quotients

The exact deletion field for a private label is a complex submodule of the
full shell observable field.  Quotienting by it produces a canonical
complex-linear coefficient channel:

* its kernel is exactly absence of that label;
* the positive power orbit of the private multiplier has linearly
  independent image;
* the quotient is not finite-dimensional.

Taking the product of all label quotients gives a complex-linear provenance
map whose joint kernel is exactly the common zeta differential field.

This is the positive survivor of the finite coefficient-rank wall.  It
constructs an unconditional algebraic target, but supplies no topology,
Meyer comparison, Hodge form, or positivity.
-/

open Set
open scoped Classical
open scoped Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The deletion field for label `m`, regarded as a complex submodule of the
full shell observable field. -/
def relativeShellLabelDeletionSubmodule
    (m : RelativeShellLabel) :
    Submodule ℂ RelativeShellFullObservable where
  carrier := {x |
    (x : upperEndMeroField) ∈
      relativeShellSubsetDifferentialField
        (relativeShellLabelComplement m)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact
      (relativeShellSubsetDifferentialField
        (relativeShellLabelComplement m)).add_mem hx hy
  smul_mem' := by
    intro c x hx
    change
      ((c • x : RelativeShellFullObservable) :
        upperEndMeroField) ∈
      relativeShellSubsetDifferentialField
        (relativeShellLabelComplement m)
    change
      algebraMap upperEndRationalCoordinateField
          upperEndMeroField
          (algebraMap ℂ
            upperEndRationalCoordinateField c) *
        (x : upperEndMeroField) ∈
      relativeShellSubsetDifferentialField
        (relativeShellLabelComplement m)
    exact
      (relativeShellSubsetDifferentialField
        (relativeShellLabelComplement m)).mul_mem
          ((relativeShellSubsetDifferentialField
            (relativeShellLabelComplement m)).algebraMap_mem
              (algebraMap ℂ
                upperEndRationalCoordinateField c))
          hx

@[simp]
theorem mem_relativeShellLabelDeletionSubmodule_iff
    (m : RelativeShellLabel)
    (x : RelativeShellFullObservable) :
    x ∈ relativeShellLabelDeletionSubmodule m ↔
      relativeShellLabelCoordinateSize m x = 0 := by
  exact
    (relativeShellLabelCoordinateSize_kernel m x).symm

/-- Canonical complex coefficient space detecting one private label. -/
abbrev RelativeShellLabelCoefficientQuotient
    (m : RelativeShellLabel) :=
  RelativeShellFullObservable ⧸
    relativeShellLabelDeletionSubmodule m

/-- Quotient coefficient map for one private label. -/
def relativeShellLabelCoefficientMap
    (m : RelativeShellLabel) :
    RelativeShellFullObservable →ₗ[ℂ]
      RelativeShellLabelCoefficientQuotient m :=
  (relativeShellLabelDeletionSubmodule m).mkQ

/-- The quotient coefficient vanishes exactly when label `m` is absent. -/
@[simp]
theorem relativeShellLabelCoefficientMap_eq_zero_iff
    (m : RelativeShellLabel)
    (x : RelativeShellFullObservable) :
    relativeShellLabelCoefficientMap m x = 0 ↔
      relativeShellLabelCoordinateSize m x = 0 := by
  rw [relativeShellLabelCoefficientMap,
    Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact mem_relativeShellLabelDeletionSubmodule_iff m x

/-- Positive powers of the private multiplier remain linearly independent in
the exact deletion quotient. -/
theorem relativeShellLabelCoefficient_powerImages_linearIndependent
    (m : RelativeShellLabel) :
    LinearIndependent ℂ
      (fun n : ℕ =>
        relativeShellLabelCoefficientMap m
          ((relativeShellMultiplierObservable m) ^
            (n + 1))) := by
  exact
    relativeShellLabel_exactKernel_powerImages_linearIndependent
      m (relativeShellLabelCoefficientMap m)
      (relativeShellLabelCoefficientMap_eq_zero_iff m)

/-- The exact one-label coefficient quotient necessarily has infinite
complex dimension. -/
theorem relativeShellLabelCoefficientQuotient_not_finiteDimensional
    (m : RelativeShellLabel) :
    ¬ FiniteDimensional ℂ
      (RelativeShellLabelCoefficientQuotient m) := by
  intro hfinite
  letI : FiniteDimensional ℂ
      (RelativeShellLabelCoefficientQuotient m) :=
    hfinite
  exact
    no_finiteDimensional_complexLinearMap_exact_relativeShellLabelKernel
      m (RelativeShellLabelCoefficientQuotient m)
      ⟨relativeShellLabelCoefficientMap m,
        relativeShellLabelCoefficientMap_eq_zero_iff m⟩

/-- Product of all exact private-label coefficient channels. -/
def relativeShellAllLabelCoefficientMap :
    RelativeShellFullObservable →ₗ[ℂ]
      ((m : RelativeShellLabel) →
        RelativeShellLabelCoefficientQuotient m) :=
  LinearMap.pi relativeShellLabelCoefficientMap

@[simp]
theorem relativeShellAllLabelCoefficientMap_apply
    (x : RelativeShellFullObservable)
    (m : RelativeShellLabel) :
    relativeShellAllLabelCoefficientMap x m =
      relativeShellLabelCoefficientMap m x := rfl

/-- Joint kernel of the linear coefficient product is exactly the common
zeta differential field. -/
theorem relativeShellAllLabelCoefficientMap_eq_zero_iff
    (x : RelativeShellFullObservable) :
    relativeShellAllLabelCoefficientMap x = 0 ↔
      (x : upperEndMeroField) ∈
        relativeShellSubsetDifferentialField
          (∅ : Set RelativeShellLabel) := by
  rw [← relativeShellLabelCoordinateSize_joint_kernel]
  constructor
  · intro hzero m
    apply
      (relativeShellLabelCoefficientMap_eq_zero_iff
        m x).1
    have hm := congrFun hzero m
    simpa using hm
  · intro hall
    funext m
    apply
      (relativeShellLabelCoefficientMap_eq_zero_iff
        m x).2
    exact hall m

end

end RHTower
