import GaloisForLFunctions.HTGeometry.MilnorKTwoFieldMonomial


/-!
# Projection from compatible amalgamated semidirect products

A pair of compatible target maps descends from `G ⋊ W` through Milnor's graph quotient.
An abstract alignment condition and exact first-factor kernel then identify the quotient projection's
kernel with the range of a specified central subgroup. This isolates reusable group theory from
the field-monomial calculation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace AmalgamatedSemidirect

variable {G W M A : Type*} [Group G] [Group W] [Group M] [Group A]
variable (K : Subgroup G) (i : K →* W) (rho : W →* MulAut G)
variable (h : Compatible K i rho)
variable (gmap : G →* M) (wmap : W →* M)

structure ProjectionCompatible : Prop where
  action_map : ∀ (w : W) (g : G),
    gmap (rho w g) = wmap w * gmap g * (wmap w)⁻¹
  common_map : ∀ k : K, gmap k.1 = wmap (i k)

variable (hp : ProjectionCompatible K i rho gmap wmap)

def semidirectProjection : G ⋊[rho] W →* M where
  toFun x := gmap x.left * wmap x.right
  map_one' := by simp
  map_mul' x y := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    rw [hp.action_map]
    group

theorem graphSubgroup_le_semidirectProjection_ker :
    graphSubgroup K i rho h ≤
      (semidirectProjection (K := K) (i := i) (rho := rho)
        (gmap := gmap) (wmap := wmap) hp).ker := by
  rintro x ⟨k, rfl⟩
  change gmap ((k : G)⁻¹) * wmap (i k) = 1
  rw [map_inv, ← ProjectionCompatible.common_map hp]
  simp

def projection : Construction K i rho h →* M :=
  QuotientGroup.lift (graphSubgroup K i rho h)
    (semidirectProjection (K := K) (i := i) (rho := rho)
      (gmap := gmap) (wmap := wmap) hp)
    (graphSubgroup_le_semidirectProjection_ker K i rho h gmap wmap hp)

theorem projection_inl (g : G) :
    projection K i rho h (gmap := gmap) (wmap := wmap) hp
      (inl K i rho h g) = gmap g := by
  change semidirectProjection (K := K) (i := i) (rho := rho)
    (gmap := gmap) (wmap := wmap) hp (SemidirectProduct.inl g) = gmap g
  simp [semidirectProjection]

theorem projection_inr (w : W) :
    projection K i rho h (gmap := gmap) (wmap := wmap) hp
      (inr K i rho h w) = wmap w := by
  change semidirectProjection (K := K) (i := i) (rho := rho)
    (gmap := gmap) (wmap := wmap) hp (SemidirectProduct.inr w) = wmap w
  simp [semidirectProjection]

theorem projection_surjective
    (hfactor : ∀ m : M, ∃ (g : G) (w : W), m = gmap g * wmap w) :
    Function.Surjective
      (projection K i rho h (gmap := gmap) (wmap := wmap) hp) := by
  intro m
  obtain ⟨g, w, rfl⟩ := hfactor m
  refine ⟨inl K i rho h g * inr K i rho h w, ?_⟩
  rw [map_mul, projection_inl, projection_inr]

theorem projection_ker_eq_central_range
    (central : A →* G)
    (hcentralMap : ∀ a, gmap (central a) = 1)
    (halign : ∀ (g : G) (w : W), gmap g * wmap w = 1 →
      ∃ k : K, i k = w)
    (hkernel : ∀ g : G, gmap g = 1 → ∃ a : A, central a = g) :
    (projection K i rho h (gmap := gmap) (wmap := wmap) hp).ker =
      MonoidHom.range ((inl K i rho h).comp central) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (graphSubgroup K i rho h) q
    have hxproj : gmap x.left * wmap x.right = 1 := by
      exact hq
    obtain ⟨k, hk⟩ := halign x.left x.right hxproj
    have htarget : gmap (x.left * (k : G)) = 1 := by
      rw [map_mul, ProjectionCompatible.common_map hp, hk]
      exact hxproj
    obtain ⟨a, ha⟩ := hkernel (x.left * (k : G)) htarget
    refine ⟨a, ?_⟩
    have hx : x = SemidirectProduct.inl x.left *
        SemidirectProduct.inr x.right :=
      (SemidirectProduct.inl_left_mul_inr_right x).symm
    symm
    change (QuotientGroup.mk' (graphSubgroup K i rho h)) x =
      inl K i rho h (central a)
    rw [hx, map_mul]
    change inl K i rho h x.left * inr K i rho h x.right = _
    rw [← hk, ← common_identified]
    rw [← map_mul, ← ha]
  · rintro ⟨a, rfl⟩
    change projection K i rho h (gmap := gmap) (wmap := wmap) hp
        (inl K i rho h (central a)) = 1
    rw [projection_inl, hcentralMap]

end AmalgamatedSemidirect
end GaloisForLFunctions.HTGeometry

end
