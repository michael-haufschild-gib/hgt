import GaloisForLFunctions.HTGeometry.ProductMeromorphicPullback

/-!
# Slicing a product domain at a point of the first factor

A capacity palette lives in the second factor, and its independence is easiest to certify over the
constants.  Transporting that certificate to independence over the whole first-factor field is a
specialization argument: a relation whose coefficients are functions of the first variable may be
restricted to a slice `{z₁} × V`, where those coefficients become genuine constants.

This file supplies the slice.  Restriction to `{z₁} × V` is a ring homomorphism of analytic germ
domains, it intertwines the second-factor directional derivations, and it carries a first-factor
pullback to the constant germ of its value at `z₁` — which is exactly what makes the coefficients of
a specialized relation constant.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### The slice of an analytic function -/

theorem analyticOnNhd_slice {U : Set E} {V : Set F} {f : E × F → ℂ}
    (hf : AnalyticOnNhd ℂ f (U ×ˢ V)) {z₁ : E} (hz₁ : z₁ ∈ U) :
    AnalyticOnNhd ℂ (fun w : F => f (z₁, w)) V := by
  have hmap : AnalyticOnNhd ℂ (fun w : F => (z₁, w)) V := by
    have h := ((ContinuousLinearMap.inr ℂ E F).analyticOnNhd V).add
      (analyticOnNhd_const (v := (z₁, (0 : F))))
    have heq : (⇑(ContinuousLinearMap.inr ℂ E F) + fun _ : F => (z₁, (0 : F)))
        = fun w : F => (z₁, w) := by
      funext w
      simp
    rwa [heq] at h
  exact hf.comp hmap fun w hw => Set.mem_prod.mpr ⟨hz₁, hw⟩

/-- The directional derivative along `(0, v)` restricted to a slice is the directional derivative of
the slice along `v`. -/
theorem dirFderiv_slice {f : E × F → ℂ} {z₁ : E} {w : F} (v : F)
    (hd : DifferentiableAt ℂ f (z₁, w)) :
    dirFderiv v (fun t : F => f (z₁, t)) w = dirFderiv ((0 : E), v) f (z₁, w) := by
  have hmk : HasFDerivAt (fun t : F => (z₁, t)) (ContinuousLinearMap.inr ℂ E F) w := by
    have h := (ContinuousLinearMap.inr ℂ E F).hasFDerivAt (x := w) |>.const_add (z₁, (0 : F))
    have heq : (fun t : F => (z₁, (0 : F)) + (ContinuousLinearMap.inr ℂ E F) t)
        = fun t : F => (z₁, t) := by
      funext t
      simp
    rwa [heq] at h
  have hcomp : HasFDerivAt (fun t : F => f (z₁, t))
      ((fderiv ℂ f (z₁, w)).comp (ContinuousLinearMap.inr ℂ E F)) w :=
    hd.hasFDerivAt.comp w hmk
  rw [dirFderiv_apply, hcomp.fderiv, dirFderiv_apply]
  simp

/-! ### The slice homomorphism on germs -/

/-- Restriction of a germ on a product to a slice at a point of the first factor. -/
def germSliceHom (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U) :
    Germ (𝓟 (U ×ˢ V)) ℂ →+* Germ (𝓟 V) ℂ where
  toFun g := Quotient.liftOn' g (fun f => ((fun w : F => f (z₁, w) : F → ℂ) : Germ (𝓟 V) ℂ)) (by
    intro f g hfg
    refine Quotient.sound ?_
    refine eventually_principal.mpr fun w hw => ?_
    exact eventually_principal.mp hfg (z₁, w) (Set.mem_prod.mpr ⟨hz₁, hw⟩))
  map_one' := rfl
  map_mul' := by rintro ⟨f⟩ ⟨g⟩; rfl
  map_zero' := rfl
  map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] in
@[simp] theorem germSliceHom_coe (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U) (f : E × F → ℂ) :
    germSliceHom U V hz₁ (f : Germ (𝓟 (U ×ˢ V)) ℂ)
      = ((fun w : F => f (z₁, w) : F → ℂ) : Germ (𝓟 V) ℂ) := rfl

/-- The slice of an analytic germ is an analytic germ. -/
theorem germSliceHom_mem (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U)
    (a : analyticGermSubringOn (U ×ˢ V)) :
    germSliceHom U V hz₁ (a : Germ (𝓟 (U ×ˢ V)) ℂ) ∈ analyticGermSubringOn V := by
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨fun w : F => f (z₁, w), analyticOnNhd_slice hf hz₁, ?_⟩
  rw [← hfa]
  rfl

/-- **Restriction to a slice is a ring map of analytic germ domains.** -/
def analyticGermSlice (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U) :
    analyticGermSubringOn (U ×ˢ V) →+* analyticGermSubringOn V where
  toFun a := ⟨germSliceHom U V hz₁ (a : Germ (𝓟 (U ×ˢ V)) ℂ), germSliceHom_mem U V hz₁ a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[simp] theorem analyticGermSlice_coe (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U)
    (a : analyticGermSubringOn (U ×ˢ V)) :
    ((analyticGermSlice U V hz₁ a : analyticGermSubringOn V) : Germ (𝓟 V) ℂ)
      = germSliceHom U V hz₁ (a : Germ (𝓟 (U ×ˢ V)) ℂ) := rfl

/-! ### Compatibility with the derivations -/

/-- **The slice map intertwines the two directional derivations.** -/
theorem analyticGermSlice_dirSubringDeriv {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hVo : IsOpen V) {z₁ : E} (hz₁ : z₁ ∈ U) (v : F)
    (a : analyticGermSubringOn (U ×ˢ V)) :
    analyticGermSlice U V hz₁ (dirSubringDeriv (hUo.prod hVo) ((0 : E), v) a)
      = dirSubringDeriv hVo v (analyticGermSlice U V hz₁ a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  rw [analyticGermSlice_coe, dirSubringDeriv_coe, dirSubringDeriv_coe, analyticGermSlice_coe,
    ← hfa]
  show ((fun w : F => dirFderiv ((0 : E), v) f (z₁, w) : F → ℂ) : Germ (𝓟 V) ℂ)
    = ((dirFderiv v (fun w : F => f (z₁, w)) : F → ℂ) : Germ (𝓟 V) ℂ)
  rw [Germ.coe_eq]
  refine eventually_principal.mpr fun w hw => ?_
  exact (dirFderiv_slice v (hf (z₁, w) (Set.mem_prod.mpr ⟨hz₁, hw⟩)).differentiableAt).symm

/-! ### First-factor pullbacks become constants -/

/-- **A first-factor pullback slices to a constant.**  Its germ on the slice is the constant germ of
its value at the slice point — which is what makes a specialized relation have constant
coefficients. -/
theorem analyticGermSlice_pullbackFst (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U)
    (a : analyticGermSubringOn U) :
    ((analyticGermSlice U V hz₁ (analyticGermPullbackFst U V a) : analyticGermSubringOn V)
        : Germ (𝓟 V) ℂ)
      = ((fun _ : F => analyticGermEval hz₁ a : F → ℂ) : Germ (𝓟 V) ℂ) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  rw [analyticGermSlice_coe, analyticGermPullbackFst_coe, ← hfa,
    analyticGermEval_of_coe hz₁ hfa]
  rfl

/-! ### The second-factor pullback -/

/-- A function of the second factor is analytic on a product domain when it is analytic on the
projection. -/
theorem analyticOnNhd_comp_snd {h : F → ℂ} {W : Set (E × F)} {V : Set F}
    (hh : AnalyticOnNhd ℂ h V) (hWV : ∀ p ∈ W, p.2 ∈ V) :
    AnalyticOnNhd ℂ (fun p : E × F => h p.2) W :=
  hh.comp ((ContinuousLinearMap.snd ℂ E F).analyticOnNhd W) hWV

/-- Pullback of a germ along the second projection of a product set. -/
def germPullbackSndHom (U : Set E) (V : Set F) : Germ (𝓟 V) ℂ →+* Germ (𝓟 (U ×ˢ V)) ℂ where
  toFun g := Quotient.liftOn' g (fun f => ((fun p : E × F => f p.2 : E × F → ℂ) :
      Germ (𝓟 (U ×ˢ V)) ℂ)) (by
    intro f g hfg
    refine Quotient.sound ?_
    refine eventually_principal.mpr fun p hp => ?_
    exact eventually_principal.mp hfg p.2 (Set.mem_prod.mp hp).2)
  map_one' := rfl
  map_mul' := by rintro ⟨f⟩ ⟨g⟩; rfl
  map_zero' := rfl
  map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] in
@[simp] theorem germPullbackSndHom_coe (U : Set E) (V : Set F) (f : F → ℂ) :
    germPullbackSndHom U V (f : Germ (𝓟 V) ℂ)
      = ((fun p : E × F => f p.2 : E × F → ℂ) : Germ (𝓟 (U ×ˢ V)) ℂ) := rfl

theorem germPullbackSndHom_mem (U : Set E) (V : Set F) (a : analyticGermSubringOn V) :
    germPullbackSndHom U V (a : Germ (𝓟 V) ℂ) ∈ analyticGermSubringOn (U ×ˢ V) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  refine ⟨fun p : E × F => f p.2,
    analyticOnNhd_comp_snd hf fun p hp => (Set.mem_prod.mp hp).2, ?_⟩
  rw [← hfa]
  rfl

/-- Pullback along the second projection, as a ring map of analytic germ domains. -/
def analyticGermPullbackSnd (U : Set E) (V : Set F) :
    analyticGermSubringOn V →+* analyticGermSubringOn (U ×ˢ V) where
  toFun a := ⟨germPullbackSndHom U V (a : Germ (𝓟 V) ℂ), germPullbackSndHom_mem U V a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[simp] theorem analyticGermPullbackSnd_coe (U : Set E) (V : Set F) (a : analyticGermSubringOn V) :
    ((analyticGermPullbackSnd U V a : analyticGermSubringOn (U ×ˢ V)) : Germ (𝓟 (U ×ˢ V)) ℂ)
      = germPullbackSndHom U V (a : Germ (𝓟 V) ℂ) := rfl

/-- **Slicing undoes the second-factor pullback.**  Every slice of a function of the second factor is
that function. -/
theorem analyticGermSlice_pullbackSnd (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U)
    (a : analyticGermSubringOn V) :
    analyticGermSlice U V hz₁ (analyticGermPullbackSnd U V a) = a := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  rw [analyticGermSlice_coe, analyticGermPullbackSnd_coe, ← hfa]
  rfl

end

end GaloisForLFunctions.HTGeometry
