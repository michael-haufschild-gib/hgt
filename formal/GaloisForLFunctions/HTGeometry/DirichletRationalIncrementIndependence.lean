import GaloisForLFunctions.HTGeometry.BaseShiftIncrementIndependence
import GaloisForLFunctions.HTGeometry.DirichletDefectInertness

/-!
# Rational increment families over the full Dirichlet coefficient field

The Dirichlet leading-term theorem descends rational coboundaries to the rational coordinate
field. Together with base-field shift elimination, this transfers any finite rational increment
obstruction to algebraic independence over every finite-abscissa Dirichlet series at once.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance dirichletRationalIncrementDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance dirichletRationalIncrementComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

private theorem dirCoord_aeval_nonZeroDivisors :
    nonZeroDivisors (Polynomial ℂ) ≤
      Submonoid.comap (Polynomial.aeval dirCoordMero).toRingHom
        (nonZeroDivisors upperEndMeroField) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact aeval_dirCoordMero_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp hp)

/-- Rational functions evaluated in the Dirichlet coordinate `s=-I*z`. -/
def dirRatRealization : RatFunc ℂ →+* upperEndMeroField :=
  RatFunc.liftRingHom (Polynomial.aeval dirCoordMero).toRingHom
    dirCoord_aeval_nonZeroDivisors

theorem dirRatRealization_algebraMap (p : Polynomial ℂ) :
    dirRatRealization (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      Polynomial.aeval dirCoordMero p :=
  RatFunc.liftRingHom_algebraMap _ _ _

theorem dirRatRealization_C (c : ℂ) :
    dirRatRealization (RatFunc.C c) = algebraMap ℂ upperEndMeroField c := by
  rw [← RatFunc.algebraMap_C, dirRatRealization_algebraMap, Polynomial.aeval_C]

theorem dirRatRealization_X : dirRatRealization RatFunc.X = dirCoordMero := by
  rw [← RatFunc.algebraMap_X, dirRatRealization_algebraMap, Polynomial.aeval_X]

theorem dirRatRealization_const (c : ℂ) :
    dirRatRealization (algebraMap ℂ (RatFunc ℂ) c) = algebraMap ℂ upperEndMeroField c :=
  dirRatRealization_C c

theorem dirRatRealization_mem (r : RatFunc ℂ) : dirRatRealization r ∈ dirRatBase := by
  induction r using RatFunc.induction_on with
  | f p q _ =>
      rw [map_div₀, dirRatRealization_algebraMap, dirRatRealization_algebraMap]
      exact div_mem (aeval_mem_dirRatBase p) (aeval_mem_dirRatBase q)

theorem exists_dirRatRealization {x : upperEndMeroField} (hx : x ∈ dirRatBase) :
    ∃ r : RatFunc ℂ, dirRatRealization r = x := by
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ x).mp hx
  refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) q, ?_⟩
  rw [map_div₀, dirRatRealization_algebraMap, dirRatRealization_algebraMap]
  exact hpq.symm

theorem dirRatRealization_ratShift (r : RatFunc ℂ) :
    dirRatRealization (ratShift r) =
      upperEndTranslationMeroEquiv Complex.I (dirRatRealization r) := by
  induction r using RatFunc.induction_on with
  | f p q _ =>
      simp only [map_div₀, ratShift_algebraMap, dirRatRealization_algebraMap,
        sigma_aeval_dirCoordMero]

/-- Translation by one in the Dirichlet variable, restricted to the whole coefficient field. -/
def dirZetaBaseShift : dirZetaBase →+* dirZetaBase where
  toFun a := ⟨upperEndTranslationMeroEquiv Complex.I a, (dirZetaBase_stable a).mpr a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext ((upperEndTranslationMeroEquiv Complex.I).map_add
    (a : upperEndMeroField) (b : upperEndMeroField))
  map_mul' a b := Subtype.ext ((upperEndTranslationMeroEquiv Complex.I).map_mul
    (a : upperEndMeroField) (b : upperEndMeroField))

theorem dirZetaBaseShift_const (c : ℂ) :
    dirZetaBaseShift (algebraMap ℂ dirZetaBase c) = algebraMap ℂ dirZetaBase c :=
  Subtype.ext (upperEndTranslate_algebraMap_complex_gen Complex.I c)

theorem dirZetaBaseShift_fixed (w : dirZetaBase) (hw : dirZetaBaseShift w = w) :
    ∃ c : ℂ, w = algebraMap ℂ dirZetaBase c := by
  obtain ⟨c, hc⟩ := dirZetaBase_fixed_const w w.2 (congrArg Subtype.val hw)
  exact ⟨c, Subtype.ext hc⟩

/-- Rational increment independence survives adjoining every convergent Dirichlet series. -/
theorem algebraicIndependent_dirZetaBase_of_rationalIncrements
    {m : ℕ} (x : Fin m → upperEndMeroField) (r : ℕ → RatFunc ℂ)
    (hshift : ∀ j, upperEndTranslationMeroEquiv Complex.I (x j) =
      x j + dirRatRealization (r (j : ℕ)))
    (hcharge : ∀ (w : RatFunc ℂ) (delta : Fin m → ℂ),
      ratShift w - w = ∑ j : Fin m, algebraMap ℂ (RatFunc ℂ) (delta j) * r (j : ℕ) →
        ∀ j, delta j = 0) :
    AlgebraicIndependent (dirZetaBase : Type _) x := by
  let rB : ℕ → dirZetaBase := fun n =>
    ⟨dirRatRealization (r n), dirRatBase_le_dirZetaBase (dirRatRealization_mem _)⟩
  refine algebraicIndependent_of_baseShiftIncrements dirZetaBaseShift
    (upperEndTranslationMeroEquiv Complex.I)
    (fun a b hab => Subtype.ext
      ((upperEndTranslationMeroEquiv Complex.I).injective (congrArg Subtype.val hab)))
    dirZetaBaseShift_const dirZetaBaseShift_fixed (fun _ => rfl) x rB hshift ?_
  intro w delta hw
  let v : RatFunc ℂ := ∑ j : Fin m, algebraMap ℂ (RatFunc ℂ) (delta j) * r (j : ℕ)
  have hval : upperEndTranslationMeroEquiv Complex.I (w : upperEndMeroField) - w =
      dirRatRealization v := by
    have h := congrArg (fun a : dirZetaBase => (a : upperEndMeroField)) hw
    simpa [v, rB, dirZetaBaseShift, map_sum, map_mul,
      dirRatRealization_const, dirRatRealization_C] using h
  obtain ⟨R, hR, hdef⟩ := rational_defect_inert w.2 (dirRatRealization_mem v) hval
  obtain ⟨q, rfl⟩ := exists_dirRatRealization hR
  apply hcharge q delta
  apply dirRatRealization.injective
  simpa only [map_sub, dirRatRealization_ratShift] using hdef

end

end GaloisForLFunctions.HTGeometry
