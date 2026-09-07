import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactPicture

/-!
# Principal-series action in the compact picture

The algebraically coinduced right-translation representation is conjugated through the Iwasawa
compact-picture equivalence.  The resulting action has the explicit formula
`(πσ(g)φ)(k) = χσ(b(kg)) φ(k(kg))`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

private theorem compactPicture_conj_comp {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (A B : Module.End ℂ V) :
    e.conj (A.comp B) = (e.conj A).comp (e.conj B) := by
  ext w
  rcases e.surjective w with ⟨v, rfl⟩
  simp [LinearEquiv.conj_apply]

private theorem compactPicture_conj_id {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    e.conj LinearMap.id = LinearMap.id := by
  ext w
  rcases e.surjective w with ⟨v, rfl⟩
  simp [LinearEquiv.conj_apply]

/-- Algebraic principal-series representation transported to the compact picture. -/
def compactRealPrincipalSeries (σ : ℝ) :
    Representation ℂ SL2R (realCompactPictureSpace σ) where
  toFun g := (algebraicRealPrincipalSeriesCompactPicture σ).conj
    (algebraicRealPrincipalSeries σ g)
  map_one' := by
    rw [map_one]
    simp only [Module.End.one_eq_id]
    exact compactPicture_conj_id (algebraicRealPrincipalSeriesCompactPicture σ)
  map_mul' g h := by
    rw [map_mul]
    simp only [Module.End.mul_eq_comp]
    exact compactPicture_conj_comp (algebraicRealPrincipalSeriesCompactPicture σ) _ _

/-- Restriction to `K` intertwines coinduced right translation with compact-picture action. -/
theorem realPrincipalSeriesRestrictToK_intertwines (σ : ℝ) (g : SL2R)
    (f : Representation.coindV realUpperBorel.subtype
      (realUpperBorelExponentRepresentation σ)) :
    realPrincipalSeriesRestrictToK σ ((algebraicRealPrincipalSeries σ) g f) =
      compactRealPrincipalSeries σ g (realPrincipalSeriesRestrictToK σ f) := by
  change (algebraicRealPrincipalSeriesCompactPicture σ)
      ((algebraicRealPrincipalSeries σ) g f) =
    (algebraicRealPrincipalSeriesCompactPicture σ)
      ((algebraicRealPrincipalSeries σ) g
        ((algebraicRealPrincipalSeriesCompactPicture σ).symm
          ((algebraicRealPrincipalSeriesCompactPicture σ) f)))
  rw [LinearEquiv.symm_apply_apply]

/-- Explicit Iwasawa formula for the principal-series action on compact-picture functions. -/
@[simp]
theorem compactRealPrincipalSeries_apply (σ : ℝ) (g : SL2R)
    (φ : realCompactPictureSpace σ) (k : upperHalfPlaneStabilizer) :
    ((compactRealPrincipalSeries σ) g φ).1 k =
      realUpperBorelRpowCharacter σ
          (realIwasawaB ((k : SL2R) * g)) *
        φ.1 (realIwasawaK ((k : SL2R) * g)) := by
  rfl

/-- Identity acts trivially in the explicit compact-picture formula. -/
@[simp]
theorem compactRealPrincipalSeries_one_apply (σ : ℝ)
    (φ : realCompactPictureSpace σ) (k : upperHalfPlaneStabilizer) :
    ((compactRealPrincipalSeries σ) 1 φ).1 k = φ.1 k := by
  simp

end
end GaloisForLFunctions.RHTower
