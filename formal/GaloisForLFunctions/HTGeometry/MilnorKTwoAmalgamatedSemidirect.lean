import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group


/-!
# Compatible amalgamation inside a semidirect product

Milnor's identification space is realized as a quotient of a semidirect product by the graph
of its common subgroup. Compatibility makes that graph normal; injectivity of the common map
then proves that quotienting does not collapse the first factor.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace AmalgamatedSemidirect

variable {G W : Type*} [Group G] [Group W]
variable (K : Subgroup G) (i : K →* W) (rho : W →* MulAut G)

/-- Hypotheses making a common subgroup compatible with a semidirect action. -/
structure Compatible where
  injective : Function.Injective i
  stable : ∀ (w : W) (k : K), rho w (k : G) ∈ K
  equivariant : ∀ (w : W) (k : K),
    i ⟨rho w (k : G), stable w k⟩ = w * i k * w⁻¹
  common_action : ∀ (k : K) (g : G),
    rho (i k) g = (k : G) * g * (k : G)⁻¹

variable (h : Compatible K i rho)

/-- Relation element identifying a common-subgroup element in both factors. -/
def graphHom : K →* G ⋊[rho] W where
  toFun k := ⟨(k : G)⁻¹, i k⟩
  map_one' := by
    ext <;> simp
  map_mul' k l := by
    ext
    · simp only [SemidirectProduct.mul_left, Subgroup.coe_mul,
        mul_inv_rev]
      rw [h.common_action]
      simp [mul_assoc]
    · exact map_mul i k l

/-- Graph subgroup implementing Milnor's identification `(h h₀,w) ~ (h,h₀ w)`. -/
def graphSubgroup : Subgroup (G ⋊[rho] W) :=
  MonoidHom.range (graphHom K i rho (h := h))

theorem graphHom_conj_inl (g : G) (k : K) :
    SemidirectProduct.inl g * graphHom K i rho (h := h) k *
        (SemidirectProduct.inl g)⁻¹ =
      graphHom K i rho (h := h) k := by
  change SemidirectProduct.inl g *
      (⟨(k : G)⁻¹, i k⟩ : G ⋊[rho] W) *
        (SemidirectProduct.inl g)⁻¹ = ⟨(k : G)⁻¹, i k⟩
  ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.inv_left, inv_one,
      map_one, MulAut.one_apply, one_mul]
    rw [h.common_action]
    simp [mul_assoc]
  · simp

theorem graphHom_conj_inr (w : W) (k : K) :
    SemidirectProduct.inr w * graphHom K i rho (h := h) k *
        (SemidirectProduct.inr w)⁻¹ =
      graphHom K i rho (h := h)
        ⟨rho w (k : G), h.stable w k⟩ := by
  change SemidirectProduct.inr w *
      (⟨(k : G)⁻¹, i k⟩ : G ⋊[rho] W) *
        (SemidirectProduct.inr w)⁻¹ =
      ⟨(rho w (k : G))⁻¹,
        i ⟨rho w (k : G), h.stable w k⟩⟩
  ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      SemidirectProduct.inv_left, map_inv, inv_one, map_one, one_mul, mul_one]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr,
      SemidirectProduct.inv_right]
    rw [h.equivariant]

instance graphSubgroup_normal : (graphSubgroup K i rho h).Normal where
  conj_mem n hn x := by
    obtain ⟨k, rfl⟩ := hn
    let g : G := x.left
    let w : W := x.right
    let k' : K := ⟨rho w (k : G), h.stable w k⟩
    refine ⟨k', ?_⟩
    symm
    have hx : x = SemidirectProduct.inl g * SemidirectProduct.inr w := by
      exact (SemidirectProduct.inl_left_mul_inr_right x).symm
    rw [hx]
    calc
      (SemidirectProduct.inl g * SemidirectProduct.inr w) *
            graphHom K i rho (h := h) k *
          (SemidirectProduct.inl g * SemidirectProduct.inr w)⁻¹ =
          SemidirectProduct.inl g *
            (SemidirectProduct.inr w * graphHom K i rho (h := h) k *
              (SemidirectProduct.inr w)⁻¹) *
            (SemidirectProduct.inl g)⁻¹ := by group
      _ = SemidirectProduct.inl g *
            graphHom K i rho (h := h) k' *
              (SemidirectProduct.inl g)⁻¹ := by
          rw [graphHom_conj_inr]
      _ = graphHom K i rho (h := h) k' := graphHom_conj_inl K i rho h g k'

/-- Milnor's identification quotient of the compatible semidirect product. -/
abbrev Construction :=
  (G ⋊[rho] W) ⧸ graphSubgroup K i rho h

/-- Canonical copy of the first factor in the identification quotient. -/
def inl : G →* Construction K i rho h :=
  (QuotientGroup.mk' (graphSubgroup K i rho h)).comp
    SemidirectProduct.inl

/-- Canonical copy of the second factor in the identification quotient. -/
def inr : W →* Construction K i rho h :=
  (QuotientGroup.mk' (graphSubgroup K i rho h)).comp
    SemidirectProduct.inr

/-- Conjugation by the second factor realizes the prescribed action on the first factor. -/
theorem inr_conj_inl (w : W) (g : G) :
    inr K i rho h w * inl K i rho h g * (inr K i rho h w)⁻¹ =
      inl K i rho h (rho w g) := by
  change (QuotientGroup.mk' (graphSubgroup K i rho h))
        (SemidirectProduct.inr w) *
      (QuotientGroup.mk' (graphSubgroup K i rho h))
        (SemidirectProduct.inl g) *
      ((QuotientGroup.mk' (graphSubgroup K i rho h))
        (SemidirectProduct.inr w))⁻¹ =
    (QuotientGroup.mk' (graphSubgroup K i rho h))
      (SemidirectProduct.inl (rho w g))
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (QuotientGroup.mk' (graphSubgroup K i rho h))
  ext <;> simp

/-- Every amalgamated-semidirect element has a first-factor/second-factor representative. -/
theorem exists_inl_mul_inr (q : Construction K i rho h) :
    ∃ (g : G) (w : W), q = inl K i rho h g * inr K i rho h w := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (graphSubgroup K i rho h) q
  exact ⟨x.left, x.right, by
    change (QuotientGroup.mk' (graphSubgroup K i rho h)) x =
      (QuotientGroup.mk' (graphSubgroup K i rho h))
          (SemidirectProduct.inl x.left) *
        (QuotientGroup.mk' (graphSubgroup K i rho h))
          (SemidirectProduct.inr x.right)
    rw [← map_mul]
    exact congrArg (QuotientGroup.mk' (graphSubgroup K i rho h))
      (SemidirectProduct.inl_left_mul_inr_right x).symm⟩

/-- Both copies of every common-subgroup element are identified. -/
theorem common_identified (k : K) :
    inl K i rho h (k : G) = inr K i rho h (i k) := by
  have hgraph :
      (QuotientGroup.mk' (graphSubgroup K i rho h))
          (graphHom K i rho (h := h) k) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr ⟨k, rfl⟩
  have hform : graphHom K i rho (h := h) k =
      SemidirectProduct.inl (k : G)⁻¹ * SemidirectProduct.inr (i k) := by
    ext <;> simp [graphHom]
  rw [hform, map_mul] at hgraph
  have hrelation :
      (inl K i rho h (k : G))⁻¹ * inr K i rho h (i k) = 1 := by
    simpa [inl, inr] using hgraph
  calc
    inl K i rho h (k : G) =
        inl K i rho h (k : G) *
          ((inl K i rho h (k : G))⁻¹ * inr K i rho h (i k)) := by
            rw [hrelation, mul_one]
    _ = inr K i rho h (i k) := by group

/-- Identification does not collapse the first factor. -/
theorem inl_injective : Function.Injective (inl K i rho h) := by
  intro g₁ g₂ heq
  have hmem : SemidirectProduct.inl g₁ / SemidirectProduct.inl g₂ ∈
      graphSubgroup K i rho h := by
    exact QuotientGroup.eq_iff_div_mem.mp heq
  rw [← map_div] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hik : i k = 1 := by
    have hright : i k =
        (SemidirectProduct.inl g₁ / SemidirectProduct.inl g₂ :
          G ⋊[rho] W).right := by
      simpa [graphHom] using congrArg SemidirectProduct.right hk
    have hrightOne :
        (SemidirectProduct.inl g₁ / SemidirectProduct.inl g₂ :
          G ⋊[rho] W).right = 1 := by
      rw [div_eq_mul_inv]
      simp
    exact hright.trans hrightOne
  have hkOne : k = 1 := h.injective (by simpa using hik)
  have hdiv : g₁ / g₂ = 1 := by
    exact SemidirectProduct.inl_injective (φ := rho) (calc
      SemidirectProduct.inl (g₁ / g₂) = graphHom K i rho (h := h) k := hk.symm
      _ = graphHom K i rho (h := h) 1 := congrArg (graphHom K i rho (h := h)) hkOne
      _ = 1 := map_one _)
  exact div_eq_one.mp hdiv

theorem semidirect_inl_mem_center (z : G)
    (hz : z ∈ Subgroup.center G) (hfixed : ∀ w : W, rho w z = z) :
    SemidirectProduct.inl z ∈ Subgroup.center (G ⋊[rho] W) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rw [hfixed]
    exact (Subgroup.mem_center_iff.mp hz x.left)
  · simp

/-- A central, action-fixed element stays central after identification. -/
theorem inl_mem_center (z : G)
    (hz : z ∈ Subgroup.center G) (hfixed : ∀ w : W, rho w z = z) :
    inl K i rho h z ∈ Subgroup.center (Construction K i rho h) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (graphSubgroup K i rho h) q
  change (QuotientGroup.mk' (graphSubgroup K i rho h)) x *
      (QuotientGroup.mk' (graphSubgroup K i rho h))
        (SemidirectProduct.inl z) =
    (QuotientGroup.mk' (graphSubgroup K i rho h))
        (SemidirectProduct.inl z) *
      (QuotientGroup.mk' (graphSubgroup K i rho h)) x
  rw [← map_mul, ← map_mul]
  exact congrArg (QuotientGroup.mk' (graphSubgroup K i rho h))
    (Subgroup.mem_center_iff.mp
      (semidirect_inl_mem_center (rho := rho) z hz hfixed) x)

end AmalgamatedSemidirect
end GaloisForLFunctions.HTGeometry

end
