import GaloisForLFunctions.RHTower.FieldOnePadicCyclicHaarQuadrature
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Unit-ball-normalized additive Haar measure on `ℚ_p`

The source Fourier convention uses additive Haar measure giving `ℤ_p` mass
one.  This file constructs that measure on the literal field `ℚ_p` and proves
that its pullback along `ℤ_p ↪ ℚ_p` is exactly the probability Haar measure
used by finite cyclic quadrature.  Thus the finite and ambient local theories
have one proved normalization, rather than independently chosen scalars.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace

variable (p : ℕ) [Fact p.Prime]

/-- The compact open unit ball of `ℚ_p`, used as Haar normalization set. -/
def fieldOnePadicUnitBallPositiveCompacts : PositiveCompacts ℚ_[p] where
  carrier := Set.range ((↑) : ℤ_[p] → ℚ_[p])
  isCompact' := by
    have hs : Set.range ((↑) : ℤ_[p] → ℚ_[p]) =
        Metric.closedBall (0 : ℚ_[p]) 1 := by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm_sub]
    rw [hs]
    exact isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' := by
    have hopen : IsOpen (Set.range ((↑) : ℤ_[p] → ℚ_[p])) :=
      PadicInt.isOpenEmbedding_coe.isOpen_range
    rw [hopen.interior_eq]
    exact ⟨0, ⟨⟨(0 : ℚ_[p]), by simp⟩, rfl⟩⟩

/-- Additive Haar measure on `ℚ_p` normalized by `μ(ℤ_p) = 1`. -/
def fieldOnePadicUnitBallNormalizedHaar : Measure ℚ_[p] :=
  Measure.addHaarMeasure (fieldOnePadicUnitBallPositiveCompacts p)

instance fieldOnePadicUnitBallNormalizedHaar_isAddHaar :
    (fieldOnePadicUnitBallNormalizedHaar p).IsAddHaarMeasure := by
  unfold fieldOnePadicUnitBallNormalizedHaar
  infer_instance

@[simp]
theorem fieldOnePadicUnitBallNormalizedHaar_unitBall :
    fieldOnePadicUnitBallNormalizedHaar p
        (Set.range ((↑) : ℤ_[p] → ℚ_[p])) = 1 := by
  exact Measure.addHaarMeasure_self

/-- Additive inclusion of the integral unit ball into `ℚ_p`. -/
def fieldOnePadicIntCoeAddMonoidHom : ℤ_[p] →+ ℚ_[p] where
  toFun := ((↑) : ℤ_[p] → ℚ_[p])
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Pullback of unit-ball-normalized Haar measure to `ℤ_p`. -/
def fieldOnePadicUnitBallNormalizedHaarIntComap : Measure ℤ_[p] :=
  (fieldOnePadicUnitBallNormalizedHaar p).comap
    (fieldOnePadicIntCoeAddMonoidHom p)

instance fieldOnePadicUnitBallNormalizedHaarIntComap_isAddHaar :
    (fieldOnePadicUnitBallNormalizedHaarIntComap p).IsAddHaarMeasure := by
  unfold fieldOnePadicUnitBallNormalizedHaarIntComap
  exact Measure.IsAddHaarMeasure.comap
    (mH := fieldOnePadicMeasurableAdd p)
    (fieldOnePadicUnitBallNormalizedHaar p)
    (by
      change Topology.IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p])
      exact PadicInt.isOpenEmbedding_coe)

@[simp]
theorem fieldOnePadicUnitBallNormalizedHaarIntComap_univ :
    fieldOnePadicUnitBallNormalizedHaarIntComap p Set.univ = 1 := by
  calc
    fieldOnePadicUnitBallNormalizedHaarIntComap p Set.univ =
        fieldOnePadicUnitBallNormalizedHaar p
          (fieldOnePadicIntCoeAddMonoidHom p '' Set.univ) := by
      exact (show MeasurableEmbedding (fieldOnePadicIntCoeAddMonoidHom p) by
        change MeasurableEmbedding ((↑) : ℤ_[p] → ℚ_[p])
        exact PadicInt.isOpenEmbedding_coe.measurableEmbedding).comap_apply
          (fieldOnePadicUnitBallNormalizedHaar p) Set.univ
    _ = fieldOnePadicUnitBallNormalizedHaar p
          (Set.range ((↑) : ℤ_[p] → ℚ_[p])) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, Set.mem_univ _, rfl⟩
    _ = 1 := fieldOnePadicUnitBallNormalizedHaar_unitBall p

/-- The ambient Haar measure restricted to `ℤ_p` is exactly the normalized
probability Haar measure used in cyclic Fourier quadrature. -/
theorem fieldOnePadicUnitBallNormalizedHaarIntComap_eq_normalized :
    fieldOnePadicUnitBallNormalizedHaarIntComap p =
      fieldOnePadicIntNormalizedHaar p := by
  letI : IsProbabilityMeasure
      (fieldOnePadicUnitBallNormalizedHaarIntComap p) :=
    ⟨fieldOnePadicUnitBallNormalizedHaarIntComap_univ p⟩
  letI : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
    ⟨fieldOnePadicIntNormalizedHaar_univ p⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (fieldOnePadicUnitBallNormalizedHaarIntComap p)
    (fieldOnePadicIntNormalizedHaar p)

end

end GaloisForLFunctions.RHTower
