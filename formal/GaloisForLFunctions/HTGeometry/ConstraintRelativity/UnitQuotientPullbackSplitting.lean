import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence

/-!
# A lifted quotient line splits its pullback

If a quotient class has an actual ambient lift, the pullback of the quotient map along its scalar
line has a canonical bounded section.  This is the exact functional-analytic core of the unit-line
splitting used by the logarithmic Marcinkiewicz tail audit.  No completion or closed-subspace
claim is made here: applications must separately supply the genuine normed/Banach quotient they
need.
-/

namespace HTGeometry.ConstraintRelativity

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The equality defining the pullback of the scalar line through the quotient class of `e`. -/
def quotientUnitPullbackConstraint (N : Submodule 𝕜 E) (e : E) :
    E × 𝕜 →L[𝕜] E ⧸ N :=
  (quotientCLM N).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd 𝕜 E 𝕜)
      (Submodule.Quotient.mk e : E ⧸ N)

/-- The pullback of `E → E ⧸ N` along `c ↦ c • [e]`. -/
def quotientUnitPullback (N : Submodule 𝕜 E) (e : E) : Submodule 𝕜 (E × 𝕜) :=
  LinearMap.ker (quotientUnitPullbackConstraint N e : E × 𝕜 →ₗ[𝕜] E ⧸ N)

/-- Projection of the quotient-unit pullback onto its scalar-line coordinate. -/
def quotientUnitPullbackProjection (N : Submodule 𝕜 E) (e : E) :
    quotientUnitPullback N e →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.snd 𝕜 E 𝕜).comp (quotientUnitPullback N e).subtypeL

/-- The distinguished lift `e` gives a bounded section of the quotient-unit pullback. -/
def quotientUnitPullbackSection (N : Submodule 𝕜 E) (e : E) :
    𝕜 →L[𝕜] quotientUnitPullback N e :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) (e, (1 : 𝕜))).codRestrict
    (quotientUnitPullback N e) (by
      intro c
      rw [quotientUnitPullback, LinearMap.mem_ker]
      simp [quotientUnitPullbackConstraint, quotientCLM])

/-- The canonical lifted line is a continuous right inverse to pullback projection. -/
@[simp] theorem quotientUnitPullbackProjection_section (N : Submodule 𝕜 E) (e : E) :
    (quotientUnitPullbackProjection N e).comp (quotientUnitPullbackSection N e) =
      ContinuousLinearMap.id 𝕜 𝕜 := by
  apply ContinuousLinearMap.ext
  intro c
  simp [quotientUnitPullbackProjection, quotientUnitPullbackSection]

/-- The canonical section is literally `c ↦ (c • e, c)`. -/
@[simp] theorem quotientUnitPullbackSection_apply (N : Submodule 𝕜 E) (e : E) (c : 𝕜) :
    ((quotientUnitPullbackSection N e c : quotientUnitPullback N e) : E × 𝕜) = (c • e, c) := by
  simp [quotientUnitPullbackSection]

end

end HTGeometry.ConstraintRelativity
