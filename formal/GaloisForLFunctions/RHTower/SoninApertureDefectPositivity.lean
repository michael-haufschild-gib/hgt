import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect

/-!
# The aperture restriction defect is positive, and vanishes only with the lost layer

At one dilation scale the defect between the larger-aperture Gram corner and the compression of
the smaller-aperture corner is the Gram square of the transition through the lost Sonin layer.
Being a Gram square it is a positive operator, and in the C*-algebra of bounded operators a Gram
square vanishes exactly when its factor does.

So canonical aperture restriction is exact precisely when the lost-layer transition vanishes: the
defect is never negative, and it is never a cancellation of two nonzero effects.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The lost-layer transition is the compression of the dilation between the smaller-aperture
projection and the complement of the larger one. -/
theorem evenSoninApertureLostTransition_eq_compress {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenSoninApertureLostTransition a b r hr =
      evenCentralSoninProjection a * (1 - evenCentralSoninProjection b) *
        evenDilationSum r hr * evenCentralSoninProjection b := by
  have hnest := (evenCentralSoninProjection_mul_of_le hab).2
  have hQ : evenCentralSoninProjection a * (1 - evenCentralSoninProjection b) =
      evenSoninApertureLayer a b := by
    rw [evenSoninApertureLayer, mul_sub, mul_one, hnest]
  rw [evenSoninApertureLostTransition, ← hQ]

/-- **The diagonal aperture restriction defect is a positive operator.** -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_isPositive
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    (evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b).IsPositive := by
  rw [evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab hr]
  simpa only [ContinuousLinearMap.mul_def] using
    ContinuousLinearMap.isPositive_adjoint_comp_self
      (evenSoninApertureLostTransition a b r hr)

/-- The defect has nonnegative diagonal against every vector. -/
theorem reApplyInnerSelf_restrictionDefect_nonneg
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) (x : evenSubspace) :
    0 ≤ (evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b).reApplyInnerSelf x :=
  (evenCentralSoninQuadraticCorner_restrictionDefect_isPositive hab hr).2 x

/-- **The defect vanishes exactly with the lost-layer transition.** -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_eq_zero_iff
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenCentralSoninQuadraticCorner b r r hr hr -
          evenCentralSoninProjection b *
            evenCentralSoninQuadraticCorner a r r hr hr *
              evenCentralSoninProjection b = 0 ↔
      evenSoninApertureLostTransition a b r hr = 0 := by
  rw [evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab hr,
    ← ContinuousLinearMap.star_eq_adjoint]
  exact CStarRing.star_mul_self_eq_zero_iff (evenSoninApertureLostTransition a b r hr)

/-- **Exactness of canonical aperture restriction.**  The larger-aperture Gram corner is the
compression of the smaller-aperture corner precisely when the lost-layer transition vanishes. -/
theorem evenCentralSoninQuadraticCorner_compress_eq_iff
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenCentralSoninQuadraticCorner b r r hr hr =
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b ↔
      evenSoninApertureLostTransition a b r hr = 0 := by
  rw [← sub_eq_zero]
  exact evenCentralSoninQuadraticCorner_restrictionDefect_eq_zero_iff hab hr

/-- In the strict crossing chamber the restriction is never exact: the defect is a nonzero
positive operator, because a noncompact operator is nonzero. -/
theorem evenCentralSoninQuadraticCorner_restrictionDefect_ne_zero
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r) (hcross : b < r * a) :
    evenCentralSoninQuadraticCorner b r r hr hr -
        evenCentralSoninProjection b *
          evenCentralSoninQuadraticCorner a r r hr hr *
            evenCentralSoninProjection b ≠ 0 := by
  intro hzero
  refine evenCentralSoninQuadraticCorner_restrictionDefect_not_isCompactOperator
    ha hab hr hcross ?_
  rw [hzero]
  exact isCompactOperator_zero

/-- In the strict crossing chamber the lost-layer transition itself is nonzero. -/
theorem evenSoninApertureLostTransition_ne_zero
    {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 1 < r) (hcross : b < r * a) :
    evenSoninApertureLostTransition a b r hr ≠ 0 := by
  intro hzero
  exact evenCentralSoninQuadraticCorner_restrictionDefect_ne_zero ha hab hr hcross
    ((evenCentralSoninQuadraticCorner_restrictionDefect_eq_zero_iff hab.le hr).mpr hzero)

end RHTower
