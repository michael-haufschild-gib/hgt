import GaloisForLFunctions.HTGeometry.FiniteUnitaryDeterminantProduct
import GaloisForLFunctions.HTGeometry.CircleProductCovering

/-!
# An explicit universal covering of finite unitary groups

The determinant product coordinates send `SU(ι) × ℝ` onto `U(ι)` by
exponentiating the real coordinate. The map is a surjective covering with
simply connected total space. Its fibers are exactly the integer translates
of the real coordinate by `2π`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit covering projection from `SU(ι) × ℝ` to `U(ι)`. -/
def finiteUnitaryUniversalCoverMap (i0 : ι)
    (p : Matrix.specialUnitaryGroup ι ℂ × ℝ) : Matrix.unitaryGroup ι ℂ :=
  (finiteUnitaryDeterminantProductHomeomorph i0).symm (p.1, Circle.exp p.2)

/-- The explicit projection is a covering map. -/
theorem finiteUnitaryUniversalCover_isCoveringMap (i0 : ι) :
    IsCoveringMap (finiteUnitaryUniversalCoverMap i0) :=
  (circleProduct_isCoveringMap (Matrix.specialUnitaryGroup ι ℂ)).homeomorph_comp
    (finiteUnitaryDeterminantProductHomeomorph i0).symm

/-- Every unitary matrix has a lift to the explicit universal covering. -/
theorem finiteUnitaryUniversalCover_surjective (i0 : ι) :
    Function.Surjective (finiteUnitaryUniversalCoverMap i0) := by
  intro U
  let p := finiteUnitaryDeterminantProductHomeomorph i0 U
  obtain ⟨t, ht⟩ := Circle.exp_surjective p.2
  refine ⟨(p.1, t), ?_⟩
  unfold finiteUnitaryUniversalCoverMap
  rw [ht]
  exact (finiteUnitaryDeterminantProductHomeomorph i0).symm_apply_apply U

/-- The total space of the explicit unitary covering is simply connected. -/
theorem finiteUnitaryUniversalCover_simplyConnected :
    SimplyConnectedSpace (Matrix.specialUnitaryGroup ι ℂ × ℝ) := inferInstance

/-- The fibers are exactly the integer `2π` translations of the real phase. -/
theorem finiteUnitaryUniversalCover_fiber_iff (i0 : ι)
    (p q : Matrix.specialUnitaryGroup ι ℂ × ℝ) :
    finiteUnitaryUniversalCoverMap i0 p = finiteUnitaryUniversalCoverMap i0 q ↔
      p.1 = q.1 ∧ ∃ k : ℤ, p.2 = q.2 + k * (2 * Real.pi) := by
  unfold finiteUnitaryUniversalCoverMap
  rw [(finiteUnitaryDeterminantProductHomeomorph i0).symm.injective.eq_iff,
    Prod.mk.injEq, Circle.exp_eq_exp]

end

end GaloisForLFunctions.HTGeometry
