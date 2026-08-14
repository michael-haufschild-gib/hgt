import GaloisForLFunctions.HTGeometry.EntireDirectionalDerivation

/-!
# Translations of the entire fraction field

Translation of the variable of a complex space is an automorphism of the entire functions, hence of
their fraction field, and it commutes with every directional derivation.  These are the deck
transformations of a complex torus `ℂ^n / Λ`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Translation of an entire function. -/
noncomputable def entireTranslate (t : V) (a : entireSubring V) : entireSubring V :=
  ⟨fun z => (a : V → ℂ) (z + t), by
    have hshift : AnalyticOnNhd ℂ (fun z : V => z + t) Set.univ :=
      analyticOnNhd_id.add analyticOnNhd_const
    exact (analyticOnNhd_of_mem_entireSubring a.2).comp hshift (Set.mapsTo_univ _ _)⟩

@[simp] theorem entireTranslate_coe (t : V) (a : entireSubring V) :
    ((entireTranslate t a : entireSubring V) : V → ℂ) = fun z => (a : V → ℂ) (z + t) := rfl

theorem entireTranslate_add (t s : V) (a : entireSubring V) :
    entireTranslate t (entireTranslate s a) = entireTranslate (s + t) a := by
  apply Subtype.ext
  funext z
  show (a : V → ℂ) (z + t + s) = (a : V → ℂ) (z + (s + t))
  rw [add_assoc, add_comm t s]

theorem entireTranslate_zero (a : entireSubring V) : entireTranslate 0 a = a := by
  apply Subtype.ext
  funext z
  show (a : V → ℂ) (z + 0) = _
  rw [add_zero]

/-- Translation of the variable, as an automorphism of the entire functions. -/
noncomputable def entireTranslateEquiv (t : V) : entireSubring V ≃+* entireSubring V where
  toFun := entireTranslate t
  invFun := entireTranslate (-t)
  left_inv := by
    intro a
    rw [entireTranslate_add, add_neg_cancel, entireTranslate_zero]
  right_inv := by
    intro a
    rw [entireTranslate_add, neg_add_cancel, entireTranslate_zero]
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem entireTranslateEquiv_apply (t : V) (a : entireSubring V) :
    entireTranslateEquiv t a = entireTranslate t a := rfl

/-- Translation of the variable, as an automorphism of the entire fraction field. -/
noncomputable def fieldTranslateEquiv (t : V) : EntireField V ≃+* EntireField V :=
  IsFractionRing.ringEquivOfRingEquiv (entireTranslateEquiv t)

theorem fieldTranslateEquiv_algebraMap (t : V) (a : entireSubring V) :
    fieldTranslateEquiv t (algebraMap (entireSubring V) (EntireField V) a)
      = algebraMap (entireSubring V) (EntireField V) (entireTranslate t a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (entireTranslateEquiv t) a

theorem fieldTranslateEquiv_ofEntire (t : V) {f : V → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    fieldTranslateEquiv t (ofEntire f hf)
      = ofEntire (fun z => f (z + t)) (entireTranslate t ⟨f, hf⟩).2 :=
  fieldTranslateEquiv_algebraMap t ⟨f, hf⟩

@[simp] theorem fieldTranslateEquiv_constEntire (t : V) (c : ℂ) :
    fieldTranslateEquiv t (constEntire V c) = constEntire V c := by
  rw [constEntire, RingHom.comp_apply, fieldTranslateEquiv_algebraMap]
  rfl

/-- **Translation commutes with every directional derivation.** -/
theorem entireTranslate_dirDeriv (t v : V) (a : entireSubring V) :
    entireTranslate t (entireDirDeriv v a) = entireDirDeriv v (entireTranslate t a) := by
  apply Subtype.ext
  funext z
  show fderiv ℂ (a : V → ℂ) (z + t) v = fderiv ℂ (fun w : V => (a : V → ℂ) (w + t)) z v
  have hdiff : Differentiable ℂ (a : V → ℂ) := differentiable_of_analyticOnNhd a.2
  have hshift : HasFDerivAt (fun w : V => w + t) (ContinuousLinearMap.id ℂ V) z :=
    (hasFDerivAt_id z).add_const t
  have hcomp : HasFDerivAt (fun w : V => (a : V → ℂ) (w + t))
      ((fderiv ℂ (a : V → ℂ) (z + t)).comp (ContinuousLinearMap.id ℂ V)) z :=
    (hdiff (z + t)).hasFDerivAt.comp z hshift
  rw [hcomp.fderiv]
  rfl

end GaloisForLFunctions.HTGeometry
