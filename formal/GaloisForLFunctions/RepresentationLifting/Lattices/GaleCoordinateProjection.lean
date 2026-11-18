import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Prod

/-!
# Complementary coordinate recovery in relation modules

Choi–Jang's complementary-minor criterion is a statement about projecting
a kernel. For blocks `P,Q`, the coordinates on the second block of a
relation are exactly the vectors whose image under `Q` lies in the image
of `P`. The ambiguity in recovering the first block is precisely `ker P`.
-/

namespace GaloisForLFunctions.RepresentationLifting
noncomputable section

variable {R V W Z : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

/-- Read the second block of a relation `P v + Q w = 0`. -/
def galeProjection (P : V →ₗ[R] Z) (Q : W →ₗ[R] Z) :
    (P.coprod Q).ker →ₗ[R] W := (LinearMap.snd R V W).comp (P.coprod Q).ker.subtype

/-- A second block lifts precisely when its image is in the span of the first block. -/
theorem galeProjection_range (P : V →ₗ[R] Z) (Q : W →ₗ[R] Z) :
    LinearMap.range (galeProjection P Q) = (LinearMap.range P).comap Q := by
  ext w
  constructor
  · rintro ⟨x,rfl⟩
    have hx : P x.val.1 + Q x.val.2 = 0 := x.property
    refine ⟨-x.val.1, ?_⟩
    change P (-x.val.1) = Q x.val.2
    rw [map_neg]
    exact (neg_eq_iff_add_eq_zero.mpr hx)
  · rintro ⟨v,hv⟩
    refine ⟨⟨(-v,w), ?_⟩,rfl⟩
    change P (-v) + Q w = 0
    rw [map_neg,hv,neg_add_cancel]

/-- Forgetting the first block of a relation forgets exactly the kernel of `P`. -/
def galeProjectionKernel (P : V →ₗ[R] Z) (Q : W →ₗ[R] Z) :
    (galeProjection P Q).ker ≃ₗ[R] P.ker where
  toFun x := ⟨x.val.val.1, by
    have hx : P x.val.val.1 + Q x.val.val.2 = 0 := x.val.property
    have hw : x.val.val.2 = 0 := x.property
    simpa [hw] using hx⟩
  invFun v := ⟨⟨(v.val,0), by
    change P v.val + Q 0 = 0
    simp [show P v.val = 0 from v.property]⟩,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (show 0 = x.val.val.2 from x.property.symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Injective complementary recovery tests independence of the first block alone. -/
theorem galeProjection_injective (P : V →ₗ[R] Z) (Q : W →ₗ[R] Z) :
    Function.Injective (galeProjection P Q) ↔ Function.Injective P := by
  constructor
  · intro h u v huv
    let x : (P.coprod Q).ker := ⟨(u-v,0), by
      change P (u-v) + Q 0 = 0
      simp [huv]⟩
    have he : x = 0 := h (show galeProjection P Q x = galeProjection P Q 0 from rfl)
    exact sub_eq_zero.mp (congrArg (fun z : (P.coprod Q).ker => z.val.1) he)
  · intro h x y hxy
    change x.val.2 = y.val.2 at hxy
    have hx : P x.val.1 + Q x.val.2 = 0 := x.property
    have hy : P y.val.1 + Q y.val.2 = 0 := y.property
    rw [hxy] at hx
    exact Subtype.ext (Prod.ext (h (add_right_cancel (hx.trans hy.symm))) hxy)

/-- Both existence and uniqueness of reconstruction by a complementary coordinate set. -/
theorem galeProjection_bijective (P : V →ₗ[R] Z) (Q : W →ₗ[R] Z) :
    Function.Bijective (galeProjection P Q) ↔
      Function.Injective P ∧ LinearMap.range Q ≤ LinearMap.range P := by
  rw [Function.Bijective, galeProjection_injective, ← LinearMap.range_eq_top, galeProjection_range]
  apply and_congr_right
  intro _
  constructor
  · rintro he x ⟨w,rfl⟩
    exact (show w ∈ (LinearMap.range P).comap Q from he ▸ Submodule.mem_top)
  · intro h
    apply top_unique
    exact fun w _ => h ⟨w,rfl⟩

variable {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A square selected column block is nonsingular exactly when the
complementary coordinates parametrise the entire relation space. -/
theorem galeComplementaryMinor (A : Matrix ι ι K) (B : Matrix ι κ K) :
    Function.Bijective (galeProjection A.mulVecLin B.mulVecLin) ↔ A.det ≠ 0 := by
  rw [galeProjection_bijective]
  have hu : Function.Injective A.mulVecLin ↔ A.det ≠ 0 :=
    Matrix.mulVec_injective_iff_isUnit.trans ((Matrix.isUnit_iff_isUnit_det A).trans isUnit_iff_ne_zero)
  constructor
  · exact fun h => hu.mp h.1
  · intro hd
    have hs : Function.Surjective A.mulVecLin :=
      Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hd.isUnit)
    exact ⟨hu.mpr hd, by rw [LinearMap.range_eq_top.mpr hs]; exact le_top⟩

#print axioms galeProjection_range
#print axioms galeProjectionKernel
#print axioms galeComplementaryMinor

end
end GaloisForLFunctions.RepresentationLifting
