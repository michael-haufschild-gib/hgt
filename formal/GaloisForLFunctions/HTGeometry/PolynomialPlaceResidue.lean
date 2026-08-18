import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation
import GaloisForLFunctions.HTGeometry.MilnorKResidueUnits
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The finite places of a rational function field, and their residue fields

`Polynomial F` is a principal ideal domain, hence a Dedekind domain, and `RatFunc F` is its
fraction field, so the whole residue machinery of Milnor `K`-theory applies to `F(t)`.  Its finite
places are the irreducible polynomials, and the residue field at `π` is `F[X]/(π)`; at the place
`X` it is `F` itself.

This is the first brick of Milnor's exact sequence

`0 → K_n^M(F) → K_n^M(F(t)) → ⊕_π K_{n-1}^M(F[X]/π) → 0`,

whose splitting is the source of the Bass–Tate–Kato norm.  The identification of the residue field
is the step that lets the target of the residue be named; it comes for free from
`residueFieldAtPlaceEquiv`.

* `polyPlace` : the place attached to an irreducible polynomial.
* `polyPlaceResidueEquiv` : **the residue field at `π` is `F[X]/(π)`.**
* `polyPlaceXResidueEquiv` : **the residue field at `X` is `F`.**
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain Polynomial

variable {F : Type*} [Field F]

/-- **The finite place of `F(t)` attached to an irreducible polynomial.** -/
noncomputable def polyPlace {π : Polynomial F} (hπ : Irreducible π) : HeightOneSpectrum (Polynomial F) where
  asIdeal := Ideal.span {π}
  isPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero

@[simp]
theorem polyPlace_asIdeal {π : Polynomial F} (hπ : Irreducible π) :
    (polyPlace hπ).asIdeal = Ideal.span {π} := rfl

/-- **The residue field of `F(t)` at an irreducible `π` is `F[X]/(π)`.** -/
noncomputable def polyPlaceResidueEquiv {π : Polynomial F} (hπ : Irreducible π) :
    IsLocalRing.ResidueField
        (((polyPlace hπ).valuation (RatFunc F)).valuationSubring)
      ≃+* (Polynomial F ⧸ Ideal.span {π}) :=
  residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)

/-- The class of `p ∈ F[X]` in the residue field at `π` is its class modulo `π`. -/
theorem polyPlaceResidueEquiv_residue {π : Polynomial F} (hπ : Irreducible π)
    (p : Polynomial F) :
    polyPlaceResidueEquiv hπ
        (IsLocalRing.residue _ (placeIntegerElt (RatFunc F) (polyPlace hπ) p))
      = Ideal.Quotient.mk (Ideal.span {π}) p :=
  residueFieldAtPlaceEquiv_residue (RatFunc F) (polyPlace hπ) p

/-- The ideal `(X)` is `(X - C 0)`. -/
theorem span_X_eq_span_X_sub_C_zero :
    Ideal.span {(X : Polynomial F)} = Ideal.span {X - C (0 : F)} := by
  rw [map_zero, sub_zero]

/-- **The residue field of `F(t)` at the place `X` is `F` itself.** -/
noncomputable def polyPlaceXResidueEquiv :
    IsLocalRing.ResidueField
        (((polyPlace (Polynomial.irreducible_X (R := F))).valuation (RatFunc F)).valuationSubring)
      ≃+* F :=
  (polyPlaceResidueEquiv (Polynomial.irreducible_X (R := F))).trans
    ((Ideal.quotEquivOfEq (span_X_eq_span_X_sub_C_zero (F := F))).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : F)).toRingEquiv)

/-- **The residue at the place `X` of a polynomial is its constant term.** -/
theorem polyPlaceXResidueEquiv_residue (p : Polynomial F) :
    polyPlaceXResidueEquiv
        (IsLocalRing.residue _
          (placeIntegerElt (RatFunc F) (polyPlace (Polynomial.irreducible_X (R := F))) p))
      = p.eval 0 := by
  rw [polyPlaceXResidueEquiv]
  show (Polynomial.quotientSpanXSubCAlgEquiv (0 : F))
      ((Ideal.quotEquivOfEq (span_X_eq_span_X_sub_C_zero (F := F)))
        (polyPlaceResidueEquiv (Polynomial.irreducible_X (R := F))
          (IsLocalRing.residue _ (placeIntegerElt (RatFunc F) _ p)))) = p.eval 0
  rw [polyPlaceResidueEquiv_residue]
  rfl

/-! ## Integral units of valuation zero -/

section IntegralUnit

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- A nonzero element of `R`, as a unit of `K`. -/
noncomputable def placeIntegerUnit {r : R} (hr0 : r ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K r)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr0)

omit [IsDedekindDomain R] in
@[simp]
theorem placeIntegerUnit_val {r : R} (hr0 : r ≠ 0) :
    ((placeIntegerUnit K hr0 : Kˣ) : K) = algebraMap R K r := rfl

/-- **An element of `R` outside `v` is a unit of valuation zero at `v`.**  This is the hypothesis
that `milnorSpecialization_of_units` consumes: on a symbol all of whose entries are such units the
specialization is the symbol of the residues. -/
theorem residueDataAtPlace_val'_eq_zero {r : R} (hr0 : r ≠ 0) (hr : r ∉ v.asIdeal) :
    (residueDataAtPlace K v).val' (placeIntegerUnit K hr0) = 0 := by
  have hker : (placeIntegerUnit K hr0) ∈ (tameValHom (v.valuation K)).ker := by
    rw [tameValHom_mem_ker_iff, placeIntegerUnit_val]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mpr hr
  have h1 : tameValHom (v.valuation K) (placeIntegerUnit K hr0) = 1 :=
    MonoidHom.mem_ker.1 hker
  show Multiplicative.toAdd (tameValHom (v.valuation K) (placeIntegerUnit K hr0)) = 0
  rw [h1]
  rfl

theorem placeIntegerUnit_mem_ker {r : R} (hr0 : r ≠ 0) (hr : r ∉ v.asIdeal) :
    placeIntegerUnit K hr0 ∈ ((residueDataAtPlace K v).val).ker :=
  (residueDataAtPlace K v).val'_eq_zero_iff.1 (residueDataAtPlace_val'_eq_zero K v hr0 hr)

/-- **The residue of an integral unit is its class modulo `v`.**  The bridge between the
`ResidueData` residue that Milnor's specialization uses and the ring-theoretic identification
`residueFieldAtPlaceEquiv`. -/
theorem residueFieldAtPlaceEquiv_residueUnit {r : R} (hr0 : r ≠ 0) (hr : r ∉ v.asIdeal) :
    residueFieldAtPlaceEquiv K v
        ((((residueDataAtPlace K v).residueUnit (placeIntegerUnit K hr0)) :
          (ResidueField ((v.valuation K).valuationSubring))ˣ) :
          ResidueField ((v.valuation K).valuationSubring))
      = Ideal.Quotient.mk v.asIdeal r := by
  rw [ResidueData.residueUnit_of_mem_ker _ (placeIntegerUnit_mem_ker K v hr0 hr)]
  have hval : (((residueDataAtPlace K v).res
        ⟨placeIntegerUnit K hr0, placeIntegerUnit_mem_ker K v hr0 hr⟩ :
        (ResidueField ((v.valuation K).valuationSubring))ˣ) :
        ResidueField ((v.valuation K).valuationSubring))
      = IsLocalRing.residue _ (placeIntegerElt K v r) := rfl
  rw [hval]
  exact residueFieldAtPlaceEquiv_residue K v r

end IntegralUnit

/-! ## Constants at the place `X` -/

section ConstantsAtX

variable {F : Type*} [Field F]

theorem C_notMem_span_X {a : F} (ha : a ≠ 0) :
    (Polynomial.C a) ∉ Ideal.span {(Polynomial.X : Polynomial F)} := by
  intro h
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_C_zero] at h
  exact ha h

theorem C_ne_zero_of_unit (c : Fˣ) : (Polynomial.C (c : F)) ≠ 0 := fun h =>
  c.ne_zero (Polynomial.C_eq_zero.1 h)

/-- The residue of an integral unit at a place of `F(t)`, in the `polyPlace` idiom. -/
theorem polyPlaceResidueEquiv_residueUnit {π : Polynomial F} (hπ : Irreducible π)
    {p : Polynomial F} (hp0 : p ≠ 0) (hp : p ∉ Ideal.span {π}) :
    polyPlaceResidueEquiv hπ
        ((((residueDataAtPlace (RatFunc F) (polyPlace hπ)).residueUnit
            (placeIntegerUnit (RatFunc F) hp0)) :
          (IsLocalRing.ResidueField
            (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))ˣ) :
          IsLocalRing.ResidueField
            (((polyPlace hπ).valuation (RatFunc F)).valuationSubring))
      = Ideal.Quotient.mk (Ideal.span {π}) p :=
  residueFieldAtPlaceEquiv_residueUnit (RatFunc F) (polyPlace hπ) hp0 hp

/-- **The residue at the place `X` of a constant is that constant.**  This is the last ingredient of
the specialization retraction: a constant is a unit of valuation zero at `X` whose residue, under
the identification of the residue field with `F`, is itself. -/
theorem polyPlaceXResidueEquiv_residueUnit_C (c : Fˣ) :
    polyPlaceXResidueEquiv
        ((((residueDataAtPlace (RatFunc F)
              (polyPlace (Polynomial.irreducible_X (R := F)))).residueUnit
            (placeIntegerUnit (RatFunc F) (C_ne_zero_of_unit c))) :
          (IsLocalRing.ResidueField
            (((polyPlace (Polynomial.irreducible_X (R := F))).valuation
              (RatFunc F)).valuationSubring))ˣ) :
          IsLocalRing.ResidueField
            (((polyPlace (Polynomial.irreducible_X (R := F))).valuation
              (RatFunc F)).valuationSubring))
      = (c : F) := by
  rw [polyPlaceXResidueEquiv]
  show (Polynomial.quotientSpanXSubCAlgEquiv (0 : F))
      ((Ideal.quotEquivOfEq (span_X_eq_span_X_sub_C_zero (F := F)))
        (polyPlaceResidueEquiv (Polynomial.irreducible_X (R := F)) _)) = (c : F)
  rw [polyPlaceResidueEquiv_residueUnit (Polynomial.irreducible_X (R := F))
    (C_ne_zero_of_unit c) (C_notMem_span_X c.ne_zero)]
  show (Polynomial.C (c : F)).eval 0 = (c : F)
  rw [Polynomial.eval_C]

/-- The constants of `F(t)`, as a ring homomorphism `F →+* F(t)`. -/
noncomputable def ratFuncConstHom : F →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp (Polynomial.C)

@[simp]
theorem ratFuncConstHom_apply (a : F) :
    ratFuncConstHom a = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C a) := rfl

/-- The image of a unit of `F` in `F(t)` is the integral unit of the constant polynomial. -/
theorem placeIntegerUnit_C_eq (c : Fˣ) :
    placeIntegerUnit (RatFunc F) (C_ne_zero_of_unit c)
      = milnorUnitMap (ratFuncConstHom (F := F)) c :=
  Units.ext rfl

/-- **The residue at `X` of the image of a unit of `F` is that unit.**  Combined with
`milnorSpecialization_of_units` this is the statement that specialization at `X` retracts the
structure map `K_n^M(F) → K_n^M(F(t))` on every entry of a symbol of constants. -/
theorem residueUnit_ratFuncConstHom (c : Fˣ) :
    milnorUnitMap (polyPlaceXResidueEquiv (F := F)).toRingHom
        ((residueDataAtPlace (RatFunc F)
            (polyPlace (Polynomial.irreducible_X (R := F)))).residueUnit
          (milnorUnitMap (ratFuncConstHom (F := F)) c))
      = c := by
  refine Units.ext ?_
  rw [← placeIntegerUnit_C_eq c]
  exact polyPlaceXResidueEquiv_residueUnit_C c

/-- **The specialization at `X` retracts the structure map.**  Hence `K_n^M(F) → K_n^M(F(t))` is
split injective — the first exactness statement of Milnor's sequence

`0 → K_n^M(F) → K_n^M(F(t)) → ⊕_π K_{n−1}^M(F[X]/π) → 0`. -/
theorem milnorSpecialization_polyPlaceX_retract (n : ℕ) (x : MilnorKDeg F n) :
    milnorKDegMap (polyPlaceXResidueEquiv (F := F)).toRingHom n
      (milnorSpecialization (residueDataAtPlace (RatFunc F)
          (polyPlace (Polynomial.irreducible_X (R := F)))) n
        (milnorKDegMap (ratFuncConstHom (F := F)) n x))
      = x := by
  classical
  set D := residueDataAtPlace (RatFunc F)
    (polyPlace (Polynomial.irreducible_X (R := F))) with hD
  set E : IsLocalRing.ResidueField
      (((polyPlace (Polynomial.irreducible_X (R := F))).valuation
        (RatFunc F)).valuationSubring) →+* F :=
    (polyPlaceXResidueEquiv (F := F)).toRingHom with hE
  set φ : MilnorKDeg F n →+ MilnorKDeg F n :=
    (milnorKDegMap E n).comp
      ((milnorSpecialization D n).comp (milnorKDegMap (ratFuncConstHom (F := F)) n)) with hφ
  have hsub : ∀ s : MilnorSymbolDeg F n, φ (milnorClassDeg F n s) = milnorClassDeg F n s := by
    intro s
    have hvals : ∀ a ∈ (milnorSymbolDegMap (ratFuncConstHom (F := F)) n s).val,
        D.val' a = 0 := by
      intro a ha
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 ha
      rw [hD, ← placeIntegerUnit_C_eq c]
      exact residueDataAtPlace_val'_eq_zero (RatFunc F) _ (C_ne_zero_of_unit c)
        (C_notMem_span_X c.ne_zero)
    show milnorKDegMap E n (milnorSpecialization D n
        (milnorKDegMap (ratFuncConstHom (F := F)) n (milnorClassDeg F n s)))
      = milnorClassDeg F n s
    rw [milnorKDegMap_class, milnorSpecialization_of_units D n _ hvals, milnorKDegMap_class]
    refine congrArg (milnorClassDeg F n) (Subtype.ext ?_)
    show ((s.val.map (milnorUnitMap (ratFuncConstHom (F := F)))).map D.residueUnit).map
        (milnorUnitMap E) = s.val
    have hfun : ((milnorUnitMap E) ∘ D.residueUnit)
        ∘ (milnorUnitMap (ratFuncConstHom (F := F))) = id := by
      funext c
      exact residueUnit_ratFuncConstHom c
    rw [List.map_map, List.map_map, hfun, List.map_id]
  exact milnorKDeg_mem_of_gen (AddMonoidHom.eqLocus φ (AddMonoidHom.id _)) hsub x

end ConstantsAtX

end GaloisForLFunctions.HTGeometry
