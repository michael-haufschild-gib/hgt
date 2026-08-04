import GaloisForLFunctions.HTGeometry.DirectionalMeromorphicField

/-!
# Evaluation and first-factor pullback for the directional meromorphic field

Two structural bridges are needed to run a capacity argument inside the meromorphic field of a
product domain.

* **Evaluation at a point of the domain** is a ring homomorphism on analytic germs.  It is what turns
  the interpolation identity `M(0) = I` into `det M ≠ 0` without computing a determinant of
  functions.
* **Pullback along the first projection** embeds the meromorphic field of the first factor into the
  meromorphic field of the product, and its image consists of differential constants for the
  second-factor direction.  It is what supplies the constant coefficient field that a finite-shadow
  observation matrix lives in.

Both are elementary once the germ ring is in place, and both are stated for an arbitrary pair of
complex normed spaces.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Evaluation at a point -/

/-- Evaluation of a germ along a set at a point of that set. -/
def germEvalHom {U : Set E} {x : E} (hx : x ∈ U) : Germ (𝓟 U) ℂ →+* ℂ where
  toFun g := Quotient.liftOn' g (fun f => f x) fun _ _ hfg => eventually_principal.mp hfg x hx
  map_one' := rfl
  map_mul' := by rintro ⟨f⟩ ⟨g⟩; rfl
  map_zero' := rfl
  map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp] theorem germEvalHom_coe {U : Set E} {x : E} (hx : x ∈ U) (f : E → ℂ) :
    germEvalHom hx (f : Germ (𝓟 U) ℂ) = f x := rfl

/-- **Evaluation is a ring homomorphism on the analytic germs.** -/
def analyticGermEval {U : Set E} {x : E} (hx : x ∈ U) : analyticGermSubringOn U →+* ℂ :=
  (germEvalHom hx).comp (analyticGermSubringOn U).subtype

@[simp] theorem analyticGermEval_apply {U : Set E} {x : E} (hx : x ∈ U)
    (a : analyticGermSubringOn U) :
    analyticGermEval hx a = germEvalHom hx (a : Germ (𝓟 U) ℂ) := rfl

theorem analyticGermEval_of_coe {U : Set E} {x : E} (hx : x ∈ U)
    {a : analyticGermSubringOn U} {f : E → ℂ}
    (hfa : (Germ.coeRingHom (𝓟 U) f) = (a : Germ (𝓟 U) ℂ)) :
    analyticGermEval hx a = f x := by
  rw [analyticGermEval_apply, ← hfa]
  rfl

/-! ### Pullback along the first projection -/

/-- Pullback of a germ along the first projection of a product set. -/
def germPullbackFstHom (U : Set E) (V : Set F) : Germ (𝓟 U) ℂ →+* Germ (𝓟 (U ×ˢ V)) ℂ where
  toFun g := Quotient.liftOn' g (fun f => ((fun p : E × F => f p.1 : E × F → ℂ) :
      Germ (𝓟 (U ×ˢ V)) ℂ)) (by
    intro f g hfg
    refine Quotient.sound ?_
    refine eventually_principal.mpr fun p hp => ?_
    exact eventually_principal.mp hfg p.1 (Set.mem_prod.mp hp).1)
  map_one' := rfl
  map_mul' := by rintro ⟨f⟩ ⟨g⟩; rfl
  map_zero' := rfl
  map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] in
@[simp] theorem germPullbackFstHom_coe (U : Set E) (V : Set F) (f : E → ℂ) :
    germPullbackFstHom U V (f : Germ (𝓟 U) ℂ)
      = ((fun p : E × F => f p.1 : E × F → ℂ) : Germ (𝓟 (U ×ˢ V)) ℂ) := rfl

/-- **The first-factor pullback of an analytic germ is analytic on the product.** -/
theorem germPullbackFstHom_mem (U : Set E) (V : Set F) (a : analyticGermSubringOn U) :
    germPullbackFstHom U V (a : Germ (𝓟 U) ℂ) ∈ analyticGermSubringOn (U ×ˢ V) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨fun p : E × F => f p.1,
    analyticOnNhd_comp_fst hf fun p hp => (Set.mem_prod.mp hp).1, ?_⟩
  rw [← hfa]
  rfl

/-- Pullback along the first projection, as a ring map of analytic germ domains. -/
def analyticGermPullbackFst (U : Set E) (V : Set F) :
    analyticGermSubringOn U →+* analyticGermSubringOn (U ×ˢ V) where
  toFun a := ⟨germPullbackFstHom U V (a : Germ (𝓟 U) ℂ), germPullbackFstHom_mem U V a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[simp] theorem analyticGermPullbackFst_coe (U : Set E) (V : Set F) (a : analyticGermSubringOn U) :
    ((analyticGermPullbackFst U V a : analyticGermSubringOn (U ×ˢ V)) : Germ (𝓟 (U ×ˢ V)) ℂ)
      = germPullbackFstHom U V (a : Germ (𝓟 U) ℂ) := rfl

/-- **The pullback is injective**: a function of the first factor vanishing on the product vanishes
on the first factor, provided the second factor is inhabited. -/
theorem analyticGermPullbackFst_injective (U : Set E) {V : Set F} (hV : V.Nonempty) :
    Function.Injective (analyticGermPullbackFst U V) := by
  intro a b hab
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  obtain ⟨y, hy⟩ := hV
  have h := congrArg (fun c : analyticGermSubringOn (U ×ˢ V) => (c : Germ (𝓟 (U ×ˢ V)) ℂ)) hab
  rw [analyticGermPullbackFst_coe, analyticGermPullbackFst_coe, ← hfa, ← hgb] at h
  have h2 : ((fun p : E × F => f p.1 : E × F → ℂ) : Germ (𝓟 (U ×ˢ V)) ℂ)
      = ((fun p : E × F => g p.1 : E × F → ℂ) : Germ (𝓟 (U ×ˢ V)) ℂ) := h
  rw [Germ.coe_eq] at h2
  apply Subtype.ext
  rw [← hfa, ← hgb]
  show ((f : Germ (𝓟 U) ℂ)) = (g : Germ (𝓟 U) ℂ)
  rw [Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  exact eventually_principal.mp h2 (z, y) (Set.mem_prod.mpr ⟨hz, hy⟩)

/-- **The pullback lands in the differential constants.**  A function of the first factor has no
derivative in a second-factor direction. -/
theorem dirSubringDeriv_analyticGermPullbackFst {U : Set E} {V : Set F}
    (hUVo : IsOpen (U ×ˢ V)) (v : F) (a : analyticGermSubringOn U) :
    dirSubringDeriv hUVo ((0 : E), v) (analyticGermPullbackFst U V a) = 0 := by
  obtain ⟨f, hf, hfa⟩ := a.2
  refine dirSubringDeriv_comp_fst_eq_zero hUVo v hf (fun p hp => (Set.mem_prod.mp hp).1) ?_
  rw [analyticGermPullbackFst_coe, ← hfa]
  rfl

/-! ### The induced embedding of meromorphic fields -/

/-- **The meromorphic field of the first factor embeds in the meromorphic field of the product.** -/
def meroPullbackFst {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hWo : IsOpen (U ×ˢ V)) (hWc : IsPreconnected (U ×ˢ V)) (hWne : (U ×ˢ V).Nonempty)
    (hV : V.Nonempty) :
    dirMeroField U →+* dirMeroField (U ×ˢ V) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI := isDomain_analyticGermSubringOn (U ×ˢ V) hWo hWc hWne
  refine IsFractionRing.lift (A := analyticGermSubringOn U) (K := dirMeroField U)
    (g := (algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))).comp
      (analyticGermPullbackFst U V)) ?_
  exact (IsFractionRing.injective _ _).comp (analyticGermPullbackFst_injective U hV)

theorem meroPullbackFst_algebraMap {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hWo : IsOpen (U ×ˢ V)) (hWc : IsPreconnected (U ×ˢ V)) (hWne : (U ×ˢ V).Nonempty)
    (hV : V.Nonempty) (a : analyticGermSubringOn U) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    letI := isDomain_analyticGermSubringOn (U ×ˢ V) hWo hWc hWne
    meroPullbackFst hUo hUc hUne hWo hWc hWne hV
        (algebraMap (analyticGermSubringOn U) (dirMeroField U) a)
      = algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
          (analyticGermPullbackFst U V a) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI := isDomain_analyticGermSubringOn (U ×ˢ V) hWo hWc hWne
  exact IsFractionRing.lift_algebraMap _ a

end

end GaloisForLFunctions.HTGeometry
