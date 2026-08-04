import GaloisForLFunctions.HTGeometry.AlgebraicIndependentSpecialization
import GaloisForLFunctions.HTGeometry.ProductSliceSpecialization

/-!
# A second-factor palette is independent over the whole first-factor field

The capacity argument needs a palette of functions of the second factor which is differentially
independent over the *meromorphic field of the first factor*, not merely over the constants.  The
specialization criterion reduces the first to the second: a relation with first-factor coefficients
restricts to a slice, where the coefficients become constants and the palette is unchanged.

This file instantiates that criterion at the concrete slice data and obtains the palette theorem: a
family of second-factor germs whose jets are algebraically independent over the constants pulls back
to a differentially independent family over the first-factor meromorphic field.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Constants -/

/-- The constant germs, as a ring map from the scalars. -/
def constGermHom (V : Set F) : ℂ →+* analyticGermSubringOn V where
  toFun c := ⟨((fun _ : F => c : F → ℂ) : Germ (𝓟 V) ℂ),
    ⟨fun _ => c, analyticOnNhd_const, rfl⟩⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' a b := by apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' a b := by apply Subtype.ext; rfl

@[simp] theorem constGermHom_coe (V : Set F) (c : ℂ) :
    ((constGermHom V c : analyticGermSubringOn V) : Germ (𝓟 V) ℂ)
      = ((fun _ : F => c : F → ℂ) : Germ (𝓟 V) ℂ) := rfl

/-! ### Separation: a germ is detected by its values -/

/-- A germ vanishing at every point of the set is zero. -/
theorem analyticGerm_eq_zero_of_eval {U : Set E} (r : analyticGermSubringOn U)
    (h : ∀ (z : E) (hz : z ∈ U), analyticGermEval hz r = 0) : r = 0 := by
  obtain ⟨f, hf, hfa⟩ := r.2
  apply Subtype.ext
  rw [← hfa, ZeroMemClass.coe_zero, ← Germ.coe_zero]
  show ((f : Germ (𝓟 U) ℂ)) = ((0 : E → ℂ) : Germ (𝓟 U) ℂ)
  rw [Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  have := h z hz
  rwa [analyticGermEval_of_coe hz hfa] at this

/-! ### Compatibilities in the shape the criterion consumes -/

/-- The slice of a first-factor pullback is the constant germ of its value. -/
theorem analyticGermSlice_pullbackFst_eq_const (U : Set E) (V : Set F) {z₁ : E} (hz₁ : z₁ ∈ U)
    (r : analyticGermSubringOn U) :
    analyticGermSlice U V hz₁ (analyticGermPullbackFst U V r)
      = constGermHom V (analyticGermEval hz₁ r) := by
  apply Subtype.ext
  rw [analyticGermSlice_pullbackFst U V hz₁ r, constGermHom_coe]

/-- Slicing commutes with every iterate of the directional derivation. -/
theorem analyticGermSlice_iterate {U : Set E} {V : Set F} (hUo : IsOpen U) (hVo : IsOpen V)
    {z₁ : E} (hz₁ : z₁ ∈ U) (v : F) (m : ℕ) (a : analyticGermSubringOn (U ×ˢ V)) :
    analyticGermSlice U V hz₁ ((dirSubringDeriv (hUo.prod hVo) ((0 : E), v))^[m] a)
      = (dirSubringDeriv hVo v)^[m] (analyticGermSlice U V hz₁ a) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        analyticGermSlice_dirSubringDeriv hUo hVo hz₁ v a]

/-- The differential jets of the image of a germ are the images of its iterated derivatives. -/
theorem differentialJet_algebraMap_dirMeroField {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {W : Set G} (hWo : IsOpen W) (hWc : IsPreconnected W) (hWne : W.Nonempty)
    (v : G) (m : ℕ) (a : analyticGermSubringOn W) :
    letI := isDomain_analyticGermSubringOn W hWo hWc hWne
    letI := dirMeroFieldDifferential hWo hWc hWne v
    differentialJet m (algebraMap (analyticGermSubringOn W) (dirMeroField W) a)
      = algebraMap (analyticGermSubringOn W) (dirMeroField W) ((dirSubringDeriv hWo v)^[m] a) := by
  letI := isDomain_analyticGermSubringOn W hWo hWc hWne
  letI := dirMeroFieldDifferential hWo hWc hWne v
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
      rw [differentialJet_succ, ih, dirMeroFieldDifferential_algebraMap hWo hWc hWne v,
        Function.iterate_succ_apply']

/-! ### The palette theorem -/

/-- **A second-factor palette independent over the constants is differentially independent over the
first-factor meromorphic field.**  Every slice sees the same palette and turns the coefficients into
constants, so the specialization criterion applies. -/
theorem differentialIndependent_pullbackSnd_of_slice {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (v : F) {n : ℕ} (ψ : Fin n → analyticGermSubringOn V)
    (hψ : letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
      AlgebraicIndependent ℂ
        fun q : Fin n × ℕ => (dirSubringDeriv hVo v)^[q.2] (ψ q.1)) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne)
    letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
    letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
      (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
    DifferentialIndependent (dirMeroField U)
      fun k : Fin n => algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
        (analyticGermPullbackSnd U V (ψ k)) := by
  letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne)
  letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
  letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
    (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
  -- the jets of the palette, at germ level
  set x : Fin n × ℕ → analyticGermSubringOn (U ×ˢ V) :=
    fun q => (dirSubringDeriv (hUo.prod hVo) ((0 : E), v))^[q.2]
      (analyticGermPullbackSnd U V (ψ q.1)) with hxdef
  have hjet : (fun q : Fin n × ℕ => differentialJet q.2
      (algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
        (analyticGermPullbackSnd U V (ψ q.1))))
      = fun q => algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V)) (x q) := by
    funext q
    exact differentialJet_algebraMap_dirMeroField (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne) ((0 : E), v) q.2 _
  show AlgebraicIndependent (dirMeroField U) _
  rw [hjet]
  refine algebraicIndependent_of_pointwise_specialization
    (R := analyticGermSubringOn U) (K := dirMeroField U)
    (RP := analyticGermSubringOn (U ×ˢ V)) (KP := dirMeroField (U ×ˢ V))
    (T := ℂ) (S := fun _ : {z : E // z ∈ U} => analyticGermSubringOn V)
    (analyticGermPullbackFst U V) ?_ ?_ x
    (fun p => analyticGermSlice U V p.2) (fun p => analyticGermEval p.2) ?_ ?_ ?_
  · intro r
    exact meroPullbackFst_algebraMap hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne) hVne r
  · exact IsFractionRing.injective (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
  · intro p r
    exact analyticGermSlice_pullbackFst_eq_const U V p.2 r
  · intro p
    have hslice : (fun q : Fin n × ℕ => analyticGermSlice U V p.2 (x q))
        = fun q : Fin n × ℕ => (dirSubringDeriv hVo v)^[q.2] (ψ q.1) := by
      funext q
      rw [hxdef]
      simp only []
      rw [analyticGermSlice_iterate hUo hVo p.2 v q.2,
        analyticGermSlice_pullbackSnd U V p.2 (ψ q.1)]
    rw [hslice]
    exact hψ
  · intro r hr
    exact analyticGerm_eq_zero_of_eval r fun z hz => hr ⟨z, hz⟩

end

end GaloisForLFunctions.HTGeometry
