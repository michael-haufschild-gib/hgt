import GaloisForLFunctions.RHTower.DeningerGaloisPlaceAction
import GaloisForLFunctions.RHTower.DeningerTestHeightBridge

/-!
# The Galois action on the place space, and the invariance of the Kummer scale

A field automorphism permutes the infinite places by composition and the finite places by the
pullback of primes, so it permutes the place space of the card.  Under this permutation the
logarithmic Kummer function of `τ α` is the Kummer function of `α` transported along the
permutation, because the multiplicity of an infinite place is unchanged and every place value of
`τ α` is a place value of `α`.

Reindexing a sum along the permutation is therefore harmless: the mass, the height and the `ℓ¹`
norm of a Kummer function do not change under a field automorphism.  This is the arithmetic form
of the card's assertion that the Galois maps act on the whole scale and preserve the mass-zero
condition.

* `deningerPlaceEquiv` : **a field automorphism permutes the place space.**
* `deningerKummerFun_comap` : **the Kummer function is Galois equivariant.**
* `deningerPlaceSum_comap` : sums over the place space are invariant.
* `deningerL1Seminorm_galois`, `deningerLogHeight_galois` : **the Kummer norm and the height are
  Galois invariant.**
-/

namespace RHTower

open NumberField

section PlaceEquiv

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The multiplicity of an infinite place is unchanged by a field automorphism. -/
theorem deningerMult_comap (τ : K ≃+* K) (w : InfinitePlace K) :
    (w.comap (τ : K →+* K)).mult = w.mult := by
  classical
  by_cases h : w.IsReal
  · have h' : (w.comap (τ : K →+* K)).IsReal :=
      (InfinitePlace.isReal_comap_iff (f := τ)).mpr h
    simp [InfinitePlace.mult, h, h']
  · have h' : ¬ (w.comap (τ : K →+* K)).IsReal := fun hc =>
      h ((InfinitePlace.isReal_comap_iff (f := τ)).mp hc)
    simp [InfinitePlace.mult, h, h']

/-- **The place map induced by a field automorphism.** -/
noncomputable def deningerPlaceComap (τ : K ≃+* K) : DeningerPlace K → DeningerPlace K :=
  Sum.map (fun w : InfinitePlace K => w.comap (τ : K →+* K)) (deningerFinitePlaceComap τ)

@[simp] theorem deningerPlaceComap_inl (τ : K ≃+* K) (w : InfinitePlace K) :
    deningerPlaceComap τ (Sum.inl w : DeningerPlace K)
      = Sum.inl (w.comap (τ : K →+* K)) := rfl

@[simp] theorem deningerPlaceComap_inr (τ : K ≃+* K) (w : FinitePlace K) :
    deningerPlaceComap τ (Sum.inr w : DeningerPlace K)
      = Sum.inr (deningerFinitePlaceComap τ w) := rfl

theorem deningerFinitePlaceComap_comp (τ : K ≃+* K) (w : FinitePlace K) :
    deningerFinitePlaceComap τ.symm (deningerFinitePlaceComap τ w) = w := by
  refine Subtype.ext (AbsoluteValue.ext fun x => ?_)
  have h1 : deningerFinitePlaceComap τ.symm (deningerFinitePlaceComap τ w) x
      = deningerFinitePlaceComap τ w (τ.symm x) :=
    deningerFinitePlaceComap_apply τ.symm _ x
  have h2 : deningerFinitePlaceComap τ w (τ.symm x) = w (τ (τ.symm x)) :=
    deningerFinitePlaceComap_apply τ w (τ.symm x)
  show deningerFinitePlaceComap τ.symm (deningerFinitePlaceComap τ w) x = w x
  rw [h1, h2, τ.apply_symm_apply]

omit [NumberField K] in
theorem deningerInfinitePlaceComap_comp (τ : K ≃+* K) (w : InfinitePlace K) :
    (w.comap (τ : K →+* K)).comap (τ.symm : K →+* K) = w := by
  refine Subtype.ext (AbsoluteValue.ext fun x => ?_)
  show w (τ (τ.symm x)) = w x
  rw [τ.apply_symm_apply]

theorem deningerPlaceComap_comp (τ : K ≃+* K) (v : DeningerPlace K) :
    deningerPlaceComap τ.symm (deningerPlaceComap τ v) = v := by
  cases v with
  | inl w => exact congrArg Sum.inl (deningerInfinitePlaceComap_comp τ w)
  | inr w => exact congrArg Sum.inr (deningerFinitePlaceComap_comp τ w)

/-- **A field automorphism permutes the place space.** -/
noncomputable def deningerPlaceEquiv (τ : K ≃+* K) : DeningerPlace K ≃ DeningerPlace K where
  toFun := deningerPlaceComap τ
  invFun := deningerPlaceComap τ.symm
  left_inv v := deningerPlaceComap_comp τ v
  right_inv v := by
    have h := deningerPlaceComap_comp τ.symm v
    rwa [RingEquiv.symm_symm] at h

@[simp] theorem deningerPlaceEquiv_apply (τ : K ≃+* K) (v : DeningerPlace K) :
    deningerPlaceEquiv τ v = deningerPlaceComap τ v := rfl

end PlaceEquiv

section Equivariance

variable {K : Type*} [Field K] [NumberField K]

/-- **The logarithmic Kummer function is Galois equivariant**: the function of `τ α` is the
function of `α` composed with the induced permutation of the place space. -/
theorem deningerKummerFun_comap (τ : K ≃+* K) (α : K) (v : DeningerPlace K) :
    deningerKummerFun K (τ α) v = deningerKummerFun K α (deningerPlaceComap τ v) := by
  cases v with
  | inl w =>
    rw [deningerPlaceComap_inl, deningerKummerFun_inl, deningerKummerFun_inl,
      deningerMult_comap]
    rfl
  | inr w =>
    rw [deningerPlaceComap_inr, deningerKummerFun_inr, deningerKummerFun_inr,
      deningerFinitePlaceComap_apply]

/-- Sums over the place space are unchanged by the Galois permutation. -/
theorem deningerPlaceSum_comap (τ : K ≃+* K) (g h : DeningerTestSpace (DeningerPlace K))
    (hgh : ∀ v, (g : DeningerPlace K → ℝ) v
      = (h : DeningerPlace K → ℝ) (deningerPlaceComap τ v)) :
    deningerPlaceSum K g = deningerPlaceSum K h := by
  rw [deningerPlaceSum_eq_finsum, deningerPlaceSum_eq_finsum]
  have hfun : (fun v => (g : DeningerPlace K → ℝ) v)
      = fun v => (h : DeningerPlace K → ℝ) (deningerPlaceEquiv τ v) := funext hgh
  rw [hfun]
  exact finsum_comp_equiv (deningerPlaceEquiv τ)

/-- **The Weil height is Galois invariant.** -/
theorem deningerHeightSum_galois (τ : K ≃+* K) {α : K} (hα : α ≠ 0)
    (hτα : τ α ≠ 0) :
    deningerPlaceSum K (deningerHeightTest K hτα) = deningerPlaceSum K (deningerHeightTest K hα) :=
  deningerPlaceSum_comap τ _ _ fun v => by
    show max (deningerKummerFun K (τ α) v) 0
      = max (deningerKummerFun K α (deningerPlaceComap τ v)) 0
    rw [deningerKummerFun_comap]

/-- On a Kummer function the `ℓ¹` seminorm is the place sum of the absolute value. -/
theorem deningerL1Seminorm_eq_placeSum {α : K} (hα : α ≠ 0) :
    deningerL1Seminorm K (deningerKummerTest K hα)
      = deningerPlaceSum K (deningerAbsTest K hα) := by
  rw [deningerPlaceSum_eq_finsum]
  rfl

/-- **The `ℓ¹` norm of a Kummer function is Galois invariant.** -/
theorem deningerL1Seminorm_galois (τ : K ≃+* K) {α : K} (hα : α ≠ 0) (hτα : τ α ≠ 0) :
    deningerL1Seminorm K (deningerKummerTest K hτα)
      = deningerL1Seminorm K (deningerKummerTest K hα) := by
  rw [deningerL1Seminorm_eq_placeSum, deningerL1Seminorm_eq_placeSum]
  refine deningerPlaceSum_comap τ _ _ fun v => ?_
  show |deningerKummerFun K (τ α) v| = |deningerKummerFun K α (deningerPlaceComap τ v)|
  rw [deningerKummerFun_comap]

/-- **The logarithmic height of mathlib is Galois invariant**, through the identification of the
place sum of the positive part with the height. -/
theorem deningerLogHeight_galois (τ : K ≃+* K) {α : K} (hα : α ≠ 0) :
    Height.logHeight₁ (τ α) = Height.logHeight₁ α := by
  have hτα : τ α ≠ 0 := fun h => hα (by simpa using congrArg τ.symm h)
  rw [← deningerHeightSum_eq_logHeight hτα, ← deningerHeightSum_eq_logHeight hα]
  exact deningerHeightSum_galois τ hα hτα

/-- **The Kummer subspace is Galois stable**: the Galois image of a generator is a generator. -/
theorem deningerKummerTest_galois (τ : K ≃+* K) {α : K} (hτα : τ α ≠ 0) :
    deningerKummerTest K hτα ∈ DeningerKummerSpan K :=
  Submodule.subset_span ⟨τ α, hτα, rfl⟩

end Equivariance

end RHTower
