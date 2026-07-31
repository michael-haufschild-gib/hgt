import Mathlib

/-!
# The local ring of analytic germs, and pullback along an analytic map

Germs at a point that are represented by a function analytic there form a subring of all germs.
A map analytic at `q` and sending `q` to `p` pulls these germs back by composition, and a pair of
mutually inverse analytic germs — an analytic change of coordinates — induces a ring isomorphism of
the two local rings.

* `analyticGermSubring p`, `AnalyticGerm p` — the local ring.
* `analyticGermPullback` — the ring homomorphism induced by an analytic map.
* `analyticGermEquiv` — the ring isomorphism induced by an analytic change of coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- The germs at `p` that are represented by a function analytic at `p`. -/
def analyticGermSubring (p : E) : Subring (Germ (𝓝 p) ℂ) where
  carrier := {g | ∃ f : E → ℂ, AnalyticAt ℂ f p ∧ (f : Germ (𝓝 p) ℂ) = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro a ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- The local ring of analytic germs at `p`. -/
abbrev AnalyticGerm (p : E) : Type _ := ↥(analyticGermSubring p)

theorem mem_analyticGermSubring {p : E} {f : E → ℂ} (hf : AnalyticAt ℂ f p) :
    (f : Germ (𝓝 p) ℂ) ∈ analyticGermSubring p := ⟨f, hf, rfl⟩

/-- The analytic germ of a function analytic at `p`. -/
def analyticGermOf {p : E} {f : E → ℂ} (hf : AnalyticAt ℂ f p) : AnalyticGerm p :=
  ⟨(f : Germ (𝓝 p) ℂ), mem_analyticGermSubring hf⟩

@[simp]
theorem analyticGermOf_val {p : E} {f : E → ℂ} (hf : AnalyticAt ℂ f p) :
    (analyticGermOf hf : Germ (𝓝 p) ℂ) = (f : Germ (𝓝 p) ℂ) := rfl

/-- Two analytic germs agree exactly when their representatives agree near the point. -/
theorem analyticGermOf_eq_iff {p : E} {f g : E → ℂ} (hf : AnalyticAt ℂ f p)
    (hg : AnalyticAt ℂ g p) : analyticGermOf hf = analyticGermOf hg ↔ f =ᶠ[𝓝 p] g := by
  rw [Subtype.ext_iff, analyticGermOf_val, analyticGermOf_val, Germ.coe_eq]

/-! ### Pullback of germs -/

/-- A map analytic at `q` and sending `q` to `p` tends to `p` along `𝓝 q`. -/
theorem tendsto_of_analyticAt {Ψ : E' → E} {q : E'} {p : E} (hΨ : AnalyticAt ℂ Ψ q)
    (hq : Ψ q = p) : Tendsto Ψ (𝓝 q) (𝓝 p) := by
  have h : Tendsto Ψ (𝓝 q) (𝓝 (Ψ q)) := hΨ.continuousAt
  rwa [hq] at h

omit [NormedSpace ℂ E] [NormedSpace ℂ E'] in
/-- Pullback of germs along a map that tends to the base point. -/
def germPullbackHom {Ψ : E' → E} {q : E'} {p : E} (htend : Tendsto Ψ (𝓝 q) (𝓝 p)) :
    Germ (𝓝 p) ℂ →+* Germ (𝓝 q) ℂ where
  toFun g := g.compTendsto Ψ htend
  map_one' := by
    show ((1 : E → ℂ) : Germ (𝓝 p) ℂ).compTendsto Ψ htend = 1
    rw [Germ.coe_compTendsto]
    rfl
  map_mul' g₁ g₂ := by
    refine Germ.inductionOn₂ g₁ g₂ fun f₁ f₂ => ?_
    rw [← Germ.coe_mul, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
      ← Germ.coe_mul]
    rfl
  map_zero' := by
    show ((0 : E → ℂ) : Germ (𝓝 p) ℂ).compTendsto Ψ htend = 0
    rw [Germ.coe_compTendsto]
    rfl
  map_add' g₁ g₂ := by
    refine Germ.inductionOn₂ g₁ g₂ fun f₁ f₂ => ?_
    rw [← Germ.coe_add, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
      ← Germ.coe_add]
    rfl

omit [NormedSpace ℂ E] [NormedSpace ℂ E'] in
@[simp]
theorem germPullbackHom_coe {Ψ : E' → E} {q : E'} {p : E} (htend : Tendsto Ψ (𝓝 q) (𝓝 p))
    (f : E → ℂ) : germPullbackHom htend (f : Germ (𝓝 p) ℂ) = ((f ∘ Ψ : E' → ℂ) : Germ (𝓝 q) ℂ) :=
  Germ.coe_compTendsto f htend

/-- Pullback of analytic germs along a map analytic at the point. -/
def analyticGermPullback {Ψ : E' → E} {q : E'} {p : E} (hΨ : AnalyticAt ℂ Ψ q) (hq : Ψ q = p) :
    AnalyticGerm p →+* AnalyticGerm q :=
  RingHom.codRestrict
    ((germPullbackHom (tendsto_of_analyticAt hΨ hq)).comp (analyticGermSubring p).subtype) _ (by
      rintro ⟨-, f, hf, rfl⟩
      refine ⟨f ∘ Ψ, ?_, ?_⟩
      · exact (hq ▸ hf : AnalyticAt ℂ f (Ψ q)).comp hΨ
      · exact (germPullbackHom_coe (tendsto_of_analyticAt hΨ hq) f).symm)

@[simp]
theorem analyticGermPullback_val {Ψ : E' → E} {q : E'} {p : E} (hΨ : AnalyticAt ℂ Ψ q)
    (hq : Ψ q = p) (x : AnalyticGerm p) :
    (analyticGermPullback hΨ hq x : Germ (𝓝 q) ℂ)
      = germPullbackHom (tendsto_of_analyticAt hΨ hq) (x : Germ (𝓝 p) ℂ) := rfl

theorem analyticGermPullback_analyticGermOf {Ψ : E' → E} {q : E'} {p : E} (hΨ : AnalyticAt ℂ Ψ q)
    (hq : Ψ q = p) {f : E → ℂ} (hf : AnalyticAt ℂ f p) :
    (analyticGermPullback hΨ hq (analyticGermOf hf) : Germ (𝓝 q) ℂ)
      = ((f ∘ Ψ : E' → ℂ) : Germ (𝓝 q) ℂ) :=
  germPullbackHom_coe (tendsto_of_analyticAt hΨ hq) f

/-! ### Analytic change of coordinates -/

/-- **An analytic change of coordinates induces a ring isomorphism of the local rings of analytic
germs.**  The two pullbacks are mutually inverse because each round trip composes a germ with a map
that is the identity near the point. -/
def analyticGermEquiv {Φ : E → E'} {Ψ : E' → E} {p : E} {q : E'}
    (hΦ : AnalyticAt ℂ Φ p) (hΨ : AnalyticAt ℂ Ψ q) (hp : Φ p = q) (hq : Ψ q = p)
    (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 p] id) (hΦΨ : (Φ ∘ Ψ) =ᶠ[𝓝 q] id) :
    AnalyticGerm q ≃+* AnalyticGerm p where
  toFun := analyticGermPullback hΦ hp
  invFun := analyticGermPullback hΨ hq
  left_inv := by
    rintro ⟨-, f, hf, rfl⟩
    refine Subtype.ext ?_
    rw [analyticGermPullback_val, analyticGermPullback_val]
    show germPullbackHom (tendsto_of_analyticAt hΨ hq)
        (germPullbackHom (tendsto_of_analyticAt hΦ hp) (f : Germ (𝓝 q) ℂ)) = (f : Germ (𝓝 q) ℂ)
    rw [germPullbackHom_coe, germPullbackHom_coe, Germ.coe_eq]
    exact hΦΨ.fun_comp f
  right_inv := by
    rintro ⟨-, f, hf, rfl⟩
    refine Subtype.ext ?_
    rw [analyticGermPullback_val, analyticGermPullback_val]
    show germPullbackHom (tendsto_of_analyticAt hΦ hp)
        (germPullbackHom (tendsto_of_analyticAt hΨ hq) (f : Germ (𝓝 p) ℂ)) = (f : Germ (𝓝 p) ℂ)
    rw [germPullbackHom_coe, germPullbackHom_coe, Germ.coe_eq]
    exact hΨΦ.fun_comp f
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem analyticGermEquiv_apply {Φ : E → E'} {Ψ : E' → E} {p : E} {q : E'}
    (hΦ : AnalyticAt ℂ Φ p) (hΨ : AnalyticAt ℂ Ψ q) (hp : Φ p = q) (hq : Ψ q = p)
    (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 p] id) (hΦΨ : (Φ ∘ Ψ) =ᶠ[𝓝 q] id) (x : AnalyticGerm q) :
    analyticGermEquiv hΦ hΨ hp hq hΨΦ hΦΨ x = analyticGermPullback hΦ hp x := rfl

end GaloisForLFunctions.HTGeometry
