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

/-- Evaluate the compact-picture action using any explicit `B K` factorization of `k g`. -/
theorem compactRealPrincipalSeries_factor_apply (σ : ℝ) (g : SL2R)
    (k : upperHalfPlaneStabilizer) (φ : realCompactPictureSpace σ)
    (b : realUpperBorel) (q : upperHalfPlaneStabilizer)
    (hfactor : (b : SL2R) * (q : SL2R) = (k : SL2R) * g) :
    ((compactRealPrincipalSeries σ g) φ).1 k =
      realUpperBorelRpowCharacter σ b * φ.1 q := by
  have hintertwine := realPrincipalSeriesRestrictToK_intertwines σ g
    (realCompactPictureExtend σ φ)
  have heval := congrArg
    (fun ψ : realCompactPictureSpace σ => ψ.1 k) hintertwine
  rw [realPrincipalSeriesRestrictToK_extend] at heval
  rw [← heval]
  change (realCompactPictureExtend σ φ).1 ((k : SL2R) * g) = _
  rw [← hfactor]
  have hq : (realCompactPictureExtend σ φ).1 (q : SL2R) = φ.1 q := by
    have hrestrict := congrArg
      (fun ψ : realCompactPictureSpace σ => ψ.1 q)
      (realPrincipalSeriesRestrictToK_extend σ φ)
    exact hrestrict
  have hproperty := (realCompactPictureExtend σ φ).property b (q : SL2R)
  rw [hq] at hproperty
  simpa [realUpperBorelExponentRepresentation] using hproperty

/-- Identity acts trivially in the explicit compact-picture formula. -/
@[simp]
theorem compactRealPrincipalSeries_one_apply (σ : ℝ)
    (φ : realCompactPictureSpace σ) (k : upperHalfPlaneStabilizer) :
    ((compactRealPrincipalSeries σ) 1 φ).1 k = φ.1 k := by
  simp

end
end GaloisForLFunctions.RHTower
