import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistMultiplication
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveSectionRatios

/-! A nonvanishing section identifies every twist with the degree-zero bundle on its chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X} {V W : X.Opens}

theorem isUnit_coord_of_le_nonzeroLocus (s : H.Sec) (i : H.ι)
    (hi : W ≤ H.U i) (h : W ≤ nonzeroLocus s) : IsUnit (resG X hi (s.f i)) := by
  have hb : W ≤ X.basicOpen (s.f i) := by
    rw [← GlobalTheory.nonzeroLocus_inf_bundleChart]
    exact le_inf h hi
  have hu : IsUnit (resG X (X.basicOpen_le (s.f i)) (s.f i)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f i)
  have hunit := hu.map (resG X hb)
  rw [resG_resG] at hunit
  exact hunit

def coordUnit (s : H.Sec) (i : H.ι) (hi : W ≤ H.U i) (h : W ≤ nonzeroLocus s) :
    Γ(X, W)ˣ :=
  (isUnit_coord_of_le_nonzeroLocus s i hi h).unit

@[simp]
theorem coordUnit_val (s : H.Sec) (i : H.ι) (hi : W ≤ H.U i) (h : W ≤ nonzeroLocus s) :
    (coordUnit s i hi h).val = resG X hi (s.f i) := rfl

theorem coordUnit_rel (s : H.Sec) (i j : H.ι) (hi : W ≤ H.U i) (hj : W ≤ H.U j)
    (h : W ≤ nonzeroLocus s) :
    coordUnit s i hi h = res (le_inf hi hj) (H.g i j) * coordUnit s j hj h :=
  Units.ext (globalSec_rel s i j hi hj)

theorem resG_coordUnit_zpow (s : H.Sec) (i : H.ι) (hi : V ≤ H.U i)
    (h : V ≤ nonzeroLocus s) (e : W ≤ V) (t : ℤ) :
    resG X e ((coordUnit s i hi h) ^ t).val =
      ((coordUnit s i (e.trans hi) (e.trans h)) ^ t).val := by
  have he : res e (coordUnit s i hi h) = coordUnit s i (e.trans hi) (e.trans h) :=
    Units.ext (resG_resG hi e (s.f i))
  change (res e ((coordUnit s i hi h) ^ t)).val = _
  rw [map_zpow, he]

private theorem cancel_transition {A : Type*} [CommRing A] (g c u : Aˣ) (t : ℤ) :
    (g * u) ^ (-t) * (c * g ^ t) = c * u ^ (-t) := by
  rw [mul_zpow]
  calc
    g ^ (-t) * u ^ (-t) * (c * g ^ t) = (g ^ (-t) * g ^ t) * (u ^ (-t) * c) := by
      rw [mul_comm c (g ^ t), mul_mul_mul_comm]
    _ = c * u ^ (-t) := by rw [← zpow_add, neg_add_cancel, zpow_zero, one_mul, mul_comm]

/-- Divide a twisted section by the indicated power of a nowhere-vanishing section. -/
def divTwistSection (M : LB X) (s : H.Sec) (h : V ≤ nonzeroLocus s) (t : ℤ) :
    Γ(toMod (twist M H t), V) →ₗ[Γ(X, V)] Γ(toMod (twist M H 0), V) where
  toFun x := mkTwistSection 0
    (fun p => ((coordUnit s p.2 (inf_le_right.trans inf_le_right) (inf_le_left.trans h)) ^ (-t)).val *
      twistCoord x p)
    (fun p q W hp hq => by
      rw [map_mul, map_mul, resG_coordUnit_zpow, resG_coordUnit_zpow,
        twistCoord_rel x p q hp hq, coordUnit_rel s p.2 q.2 _ ((hq.trans inf_le_right).trans inf_le_right),
        zpow_zero, mul_one]
      let c := res (le_inf ((hp.trans inf_le_right).trans inf_le_left)
        ((hq.trans inf_le_right).trans inf_le_left)) (M.g p.1 q.1)
      let g := res (le_inf ((hp.trans inf_le_right).trans inf_le_right)
        ((hq.trans inf_le_right).trans inf_le_right)) (H.g p.2 q.2)
      let u := coordUnit s q.2 ((hq.trans inf_le_right).trans inf_le_right) (hq.trans (inf_le_left.trans h))
      have e := congrArg (fun b : Γ(X, W)ˣ => b.val * resG X hq (twistCoord x q))
        (cancel_transition g c u t)
      simpa only [c, g, u, Units.val_mul, mul_assoc] using e)
  map_add' x y := sec_ext fun p => by
    change _ * (twistCoord x p + twistCoord y p) =
      _ * twistCoord x p + _ * twistCoord y p
    exact mul_add _ _ _
  map_smul' a x := sec_ext fun p => by
    simp only [RingHom.id_apply, twistCoord_mkTwistSection, coord_smul]
    exact mul_left_comm _ _ _

@[simp]
theorem twistCoord_divTwistSection (s : H.Sec) (h : V ≤ nonzeroLocus s) (t : ℤ)
    (x : Γ(toMod (twist M H t), V)) (p : M.ι × H.ι) :
    twistCoord (divTwistSection M s h t x) p =
      ((coordUnit s p.2 (inf_le_right.trans inf_le_right) (inf_le_left.trans h)) ^ (-t)).val *
        twistCoord x p := rfl

theorem divTwistSection_zero (s : H.Sec) (h : V ≤ nonzeroLocus s)
    (x : Γ(toMod (twist M H 0), V)) :
    divTwistSection M s h 0 x = x := by
  apply sec_ext
  intro p
  change twistCoord (divTwistSection M s h 0 x) p = twistCoord x p
  rw [twistCoord_divTwistSection, neg_zero, zpow_zero, Units.val_one, one_mul]

theorem divTwistSection_injective (s : H.Sec) (h : V ≤ nonzeroLocus s) (t : ℤ) :
    Function.Injective (divTwistSection M s h t) := by
  intro a b e
  refine sec_ext fun p => ?_
  let W := V ⊓ (M.U p.1 ⊓ H.U p.2)
  let u := coordUnit s p.2 (inf_le_right.trans inf_le_right : W ≤ H.U p.2) (inf_le_left.trans h)
  have he := congrArg (fun x : Γ(toMod (twist M H 0), V) => twistCoord x p) e
  change (u ^ (-t)).val * twistCoord a p = (u ^ (-t)).val * twistCoord b p at he
  exact (u ^ (-t)).isUnit.mul_left_cancel he

private theorem divPower_mul_coord {A : Type*} [CommRing A] (u : Aˣ) (t : ℤ) (z : A) :
    (u ^ (-(t + 1))).val * (u.val * z) = (u ^ (-t)).val * z := by
  rw [← mul_assoc, ← Units.val_mul, ← zpow_add_one, show -(t + 1) + 1 = -t by omega]

theorem divTwistSection_mulTwistSection (s : H.Sec) (h : V ≤ nonzeroLocus s) (t : ℤ)
    (x : Γ(toMod (twist M H t), V)) :
    divTwistSection M s h (t + 1) (mulTwistSection M t s V x) = divTwistSection M s h t x := by
  apply sec_ext
  intro p
  let W := V ⊓ (M.U p.1 ⊓ H.U p.2)
  let u := coordUnit s p.2 (inf_le_right.trans inf_le_right : W ≤ H.U p.2) (inf_le_left.trans h)
  change (u ^ (-(t + 1))).val * (u.val * twistCoord x p) = (u ^ (-t)).val * twistCoord x p
  exact divPower_mul_coord u t (twistCoord x p)

end GlobalTheory.LineBundleSections
