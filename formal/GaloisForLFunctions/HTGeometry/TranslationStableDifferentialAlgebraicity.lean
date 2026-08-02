import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.HolderShiftElimination
import GaloisForLFunctions.HTGeometry.TwoShiftKoszulCochain

/-!
# Differential algebraicity is stable under translation

A translation of the plane commutes with the derivation and carries the coordinate field into
itself, covering the shift automorphism of that field.  A differential-algebraic relation therefore
transports: applying the translation to a relation for the jets of an element gives a relation, with
shifted coefficients, for the jets of its translate.

This is what makes the differentially algebraic coefficients of the bi-anomaly a *subcomplex* rather
than a graded subgroup: the group differential moves cochain entries by translations.
-/

open Filter Topology Set Function Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- Composition with a translation, as a map from polynomials into the rational function field. -/
def shiftCompHomBy (q : ℂ) : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.aeval (Polynomial.X + Polynomial.C q) : Polynomial ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom

theorem shiftCompHomBy_apply (q : ℂ) (p : Polynomial ℂ) :
    shiftCompHomBy q p
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.X + Polynomial.C q)) := by
  rw [shiftCompHomBy, RingHom.comp_apply]
  rfl

theorem shiftCompHomBy_mem_nonZeroDivisors (q : ℂ) :
    nonZeroDivisors (Polynomial ℂ)
      ≤ Submonoid.comap (shiftCompHomBy q) (nonZeroDivisors (RatFunc ℂ)) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [shiftCompHomBy_apply]
  intro h0
  have hcomp : p.comp (Polynomial.X + Polynomial.C q) = 0 :=
    RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero])
  have hne : p.comp (Polynomial.X + Polynomial.C q) ≠ 0 := by
    intro hzero
    exact hp (Polynomial.comp_X_add_C_eq_zero_iff.mp hzero)
  exact hne hcomp

/-- The translation endomorphism `r(X) ↦ r(X + q)` of the rational function field. -/
def ratShiftBy (q : ℂ) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom (shiftCompHomBy q) (shiftCompHomBy_mem_nonZeroDivisors q)

theorem ratShiftBy_algebraMap (q : ℂ) (p : Polynomial ℂ) :
    ratShiftBy q (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.X + Polynomial.C q)) := by
  have h := RatFunc.liftRingHom_apply_div (shiftCompHomBy q)
    (shiftCompHomBy_mem_nonZeroDivisors q) p 1
  simp only [map_one, div_one] at h
  rw [ratShiftBy, h, shiftCompHomBy_apply]

/-- **Translation of the meromorphic field restricts to the coordinate shift.** -/
theorem addTranslationMeroEquiv_ratfuncToMero_by (q : ℂ) (r : RatFunc ℂ) :
    addTranslationMeroEquiv q
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r)
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (ratShiftBy q r) := by
  let rho := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
  have hhom : (addTranslationMeroEquiv q).toRingHom.comp rho = rho.comp (ratShiftBy q) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply,
      ratfuncToMero_algebraMap_polynomial, ratShiftBy_algebraMap,
      ratfuncToMero_algebraMap_polynomial]
    simp only [polyToMero, RingHom.comp_apply]
    change addTranslationMeroEquiv q
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ p)) = _
    rw [addTranslationMeroEquiv_algebraMap, addTranslationAnalyticEquiv_polyToAnalytic]
  exact RingHom.congr_fun hhom r

/-- Jets commute with translation. -/
theorem differentialJet_addTranslationMeroEquiv (q : ℂ) (n : ℕ)
    (x : meroField (Set.univ : Set ℂ)) :
    differentialJet n (addTranslationMeroEquiv q x)
      = addTranslationMeroEquiv q (differentialJet n x) := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ k ih =>
      rw [differentialJet_succ, differentialJet_succ, ih, addTranslationMeroEquiv_deriv]

/-- **Differential algebraicity transports along a derivation-compatible automorphism covering an
automorphism of the base.** -/
theorem differentialAlgebraicOver_of_transport
    {sigma : meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ)}
    {rho : RatFunc ℂ ≃+* RatFunc ℂ}
    (hjet : ∀ (n : ℕ) (y : meroField (Set.univ : Set ℂ)),
      differentialJet n (sigma y) = sigma (differentialJet n y))
    (hbase : ∀ r : RatFunc ℂ,
      sigma (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)
        = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (rho r))
    {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (sigma x) := by
  classical
  intro hindep
  refine hx ?_
  refine (algebraicIndependent_iff_injective_aeval).mpr fun P Q hPQ => ?_
  have hval : ∀ R : MvPolynomial (Unit × ℕ) (RatFunc ℂ),
      sigma ((MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 x) R)
        = (MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 (sigma x))
          (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) R) := by
    intro R
    have hleft := MvPolynomial.eval₂_comp_left (sigma : meroField (Set.univ : Set ℂ) →+*
        meroField (Set.univ : Set ℂ))
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
      (fun p : Unit × ℕ => differentialJet p.2 x) R
    have hcomp : (sigma : meroField (Set.univ : Set ℂ) →+* meroField (Set.univ : Set ℂ)).comp
        (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
        = (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).comp
          (rho : RatFunc ℂ →+* RatFunc ℂ) := by
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact hbase r
    have hfun : (fun p : Unit × ℕ => sigma (differentialJet p.2 x))
        = fun p : Unit × ℕ => differentialJet p.2 (sigma x) := by
      funext p
      rw [hjet]
    have hstep : sigma ((MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 x) R)
        = MvPolynomial.eval₂ ((sigma : meroField (Set.univ : Set ℂ) →+*
            meroField (Set.univ : Set ℂ)).comp
              (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))))
            (fun p : Unit × ℕ => sigma (differentialJet p.2 x)) R := by
      simpa [MvPolynomial.aeval_def, Function.comp_def] using hleft
    rw [hstep, hcomp, ← MvPolynomial.eval₂_map, hfun]
    rfl
  have hmap : MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) P
      = MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) Q := by
    have h1 := hval P
    have h2 := hval Q
    rw [hPQ] at h1
    rw [h1] at h2
    have hindep' : AlgebraicIndependent (RatFunc ℂ)
        (fun p : Unit × ℕ => differentialJet p.2 (sigma x)) := hindep
    have hinj2 := (algebraicIndependent_iff_injective_aeval).mp hindep'
    exact hinj2 h2
  have hinj : Function.Injective
      (MvPolynomial.map (rho : RatFunc ℂ →+* RatFunc ℂ) :
        MvPolynomial (Unit × ℕ) (RatFunc ℂ) → MvPolynomial (Unit × ℕ) (RatFunc ℂ)) :=
    MvPolynomial.map_injective _ rho.injective
  exact hinj hmap

theorem ratShiftBy_comp_neg (q : ℂ) (r : RatFunc ℂ) :
    ratShiftBy (-q) (ratShiftBy q r) = r := by
  have hhom : (ratShiftBy (-q)).comp (ratShiftBy q) = RingHom.id (RatFunc ℂ) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, ratShiftBy_algebraMap, ratShiftBy_algebraMap, RingHom.id_apply]
    congr 1
    rw [Polynomial.comp_assoc]
    have hx : (Polynomial.X + Polynomial.C q).comp
        (Polynomial.X + Polynomial.C (-q)) = Polynomial.X := by
      simp
    rw [hx, Polynomial.comp_X]
  exact RingHom.congr_fun hhom r

/-- The translation automorphism of the rational function field. -/
def ratShiftEquivBy (q : ℂ) : RatFunc ℂ ≃+* RatFunc ℂ where
  toFun := ratShiftBy q
  invFun := ratShiftBy (-q)
  left_inv := fun r => ratShiftBy_comp_neg q r
  right_inv := fun r => by
    have h := ratShiftBy_comp_neg (-q) r
    rwa [neg_neg] at h
  map_mul' := map_mul _
  map_add' := map_add _

/-- **Differential algebraicity is stable under translation.** -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv (q : ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (addTranslationMeroEquiv q x) := by
  refine differentialAlgebraicOver_of_transport (rho := ratShiftEquivBy q)
    (fun n y => differentialJet_addTranslationMeroEquiv q n y) (fun r => ?_) hx
  exact addTranslationMeroEquiv_ratfuncToMero_by q r

/-- **The differentially algebraic sector is translation stable**, hence a genuine subcomplex
for the group differential. -/
theorem daSector_addTranslationMeroEquiv (q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ daSector) : addTranslationMeroEquiv q x ∈ daSector :=
  differentialAlgebraicOver_addTranslationMeroEquiv q hx

/-- **The sector is stable under the shift quotient**, the entrywise group differential. -/
theorem daSector_shiftQuotient (q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ daSector) : shiftQuotient q x ∈ daSector := by
  rw [shiftQuotient]
  exact differentialAlgebraicOver_mul (daSector_addTranslationMeroEquiv q hx)
    (differentialAlgebraicOver_inv hx)

end

end GaloisForLFunctions.HTGeometry
