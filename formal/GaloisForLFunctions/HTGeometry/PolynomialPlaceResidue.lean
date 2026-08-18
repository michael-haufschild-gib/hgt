import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation
import GaloisForLFunctions.HTGeometry.MilnorKResidueUnits
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality
import GaloisForLFunctions.HTGeometry.MilnorKResidueUniformizer
import GaloisForLFunctions.HTGeometry.MilnorKSlotGeneration
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

/-- **Every residue class at a finite place is the residue of an integral unit.** -/
theorem residueDataAtPlace_residueUnit_surjective
    (y : (ResidueField ((v.valuation K).valuationSubring))ˣ) :
    ∃ a : Kˣ, (residueDataAtPlace K v).val' a = 0
      ∧ (residueDataAtPlace K v).residueUnit a = y := by
  obtain ⟨r, hr⟩ := residue_placeIntegerElt_surjective K v
    ((y : ResidueField ((v.valuation K).valuationSubring)))
  have hy0 : ((y : ResidueField ((v.valuation K).valuationSubring))) ≠ 0 := y.ne_zero
  have hrmem : r ∉ v.asIdeal := by
    intro hmem
    refine hy0 ?_
    rw [← hr]
    refine (residueFieldAtPlaceEquiv K v).injective ?_
    rw [residueFieldAtPlaceEquiv_residue, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
  have hr0 : r ≠ 0 := by
    intro h
    exact hrmem (h ▸ v.asIdeal.zero_mem)
  refine ⟨placeIntegerUnit K hr0, residueDataAtPlace_val'_eq_zero K v hr0 hrmem, ?_⟩
  refine Units.ext ?_
  rw [ResidueData.residueUnit_of_mem_ker _ (placeIntegerUnit_mem_ker K v hr0 hrmem)]
  show IsLocalRing.residue _ (placeIntegerElt K v r)
    = ((y : (ResidueField ((v.valuation K).valuationSubring))ˣ) :
        ResidueField ((v.valuation K).valuationSubring))
  exact hr

/-- **Milnor's residue at a finite place of a Dedekind domain is surjective.**  This is the
right-exactness of the Gersten complex at its last term, with every side condition discharged. -/
theorem milnorResidueAtPlace_surjective (n : ℕ) :
    Function.Surjective (milnorResidue (residueDataAtPlace K v) (n + 1)) :=
  milnorResidue_surjective _ (residueDataAtPlace_residueUnit_surjective K v) n

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

/-- **`K_n^M(F) → K_n^M(F(t))` is injective**, split by the specialization at `X`.  This is the
left-exactness half of Milnor's sequence for a rational function field. -/
theorem milnorKDegMap_ratFuncConstHom_injective (n : ℕ) :
    Function.Injective (milnorKDegMap (ratFuncConstHom (F := F)) n) :=
  Function.LeftInverse.injective
    (g := fun y => milnorKDegMap (polyPlaceXResidueEquiv (F := F)).toRingHom n
      (milnorSpecialization (residueDataAtPlace (RatFunc F)
        (polyPlace (Polynomial.irreducible_X (R := F)))) n y))
    (milnorSpecialization_polyPlaceX_retract (F := F) n)

/-! ## The degree bound and the residue -/

/-- A nonzero polynomial, as a unit of `F(t)`. -/
noncomputable def polyUnit {p : Polynomial F} (hp : p ≠ 0) : (RatFunc F)ˣ :=
  placeIntegerUnit (RatFunc F) hp

/-- A nonzero polynomial of degree smaller than `π` is not divisible by `π`. -/
theorem notMem_span_of_natDegree_lt {π p : Polynomial F} (hp : p ≠ 0)
    (hdeg : p.natDegree < π.natDegree) : p ∉ Ideal.span {π} := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  have hle : π.natDegree ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hmem hp
  exact absurd hle (not_le.2 hdeg)

/-- **A polynomial of degree smaller than `π` is a unit of valuation zero at `π`.**  Hence the
residue at `π` kills every symbol whose entries all have degree below `deg π` — the statement that
the degree filtration of Milnor's sequence is compatible with the residues. -/
theorem polyUnit_val'_eq_zero_of_natDegree_lt {π p : Polynomial F} (hπ : Irreducible π)
    (hp : p ≠ 0) (hdeg : p.natDegree < π.natDegree) :
    (residueDataAtPlace (RatFunc F) (polyPlace hπ)).val' (polyUnit hp) = 0 :=
  residueDataAtPlace_val'_eq_zero (RatFunc F) (polyPlace hπ) hp
    (notMem_span_of_natDegree_lt hp hdeg)

/-- **The residue at `π` kills a symbol all of whose entries have degree below `deg π`.** -/
theorem milnorResidue_eq_zero_of_natDegree_lt {π : Polynomial F} (hπ : Irreducible π) (n : ℕ)
    (s : MilnorSymbolDeg (RatFunc F) n)
    (hs : ∀ a ∈ s.val, ∃ (p : Polynomial F) (hp : p ≠ 0),
      p.natDegree < π.natDegree ∧ a = polyUnit hp) :
    milnorResidue (residueDataAtPlace (RatFunc F) (polyPlace hπ)) n
        (milnorClassDeg (RatFunc F) n s) = 0 := by
  refine milnorResidue_eq_zero_of_units _ n s ?_
  intro a ha
  obtain ⟨p, hp, hdeg, rfl⟩ := hs a ha
  exact polyUnit_val'_eq_zero_of_natDegree_lt hπ hp hdeg

/-! ## The degree filtration -/

/-- **The nonzero polynomials generate the units of `F(t)`.** -/
theorem closure_polyUnit_eq_top :
    Subgroup.closure {u : (RatFunc F)ˣ | ∃ (p : Polynomial F) (hp : p ≠ 0), u = polyUnit hp}
      = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := Polynomial F) ((u : RatFunc F))
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    subst h
    rw [map_zero, zero_div] at hx
    exact u.ne_zero hx.symm
  have hu : u = polyUnit ha0 * (polyUnit hb0)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    show (u : RatFunc F)
      = algebraMap (Polynomial F) (RatFunc F) a * (algebraMap (Polynomial F) (RatFunc F) b)⁻¹
    rw [← div_eq_mul_inv, hx]
  rw [hu]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a, ha0, rfl⟩) ?_
  exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨b, hb0, rfl⟩)

/-- The `d`-th stage of Milnor's degree filtration of `K_n^M(F(t))`. -/
noncomputable def degreeFiltration (d n : ℕ) : AddSubgroup (MilnorKDeg (RatFunc F) n) :=
  AddSubgroup.closure {x | ∃ s : MilnorSymbolDeg (RatFunc F) n,
    (∀ a ∈ s.val, ∃ (p : Polynomial F) (hp : p ≠ 0), p.natDegree ≤ d ∧ a = polyUnit hp)
      ∧ x = milnorClassDeg (RatFunc F) n s}

theorem degreeFiltration_mono {d d' n : ℕ} (h : d ≤ d') :
    degreeFiltration (F := F) d n ≤ degreeFiltration (F := F) d' n := by
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, fun a ha => by
    obtain ⟨p, hp, hdeg, hap⟩ := hs a ha
    exact ⟨p, hp, le_trans hdeg h, hap⟩, rfl⟩

/-- **The residue at `π` annihilates the degree filtration below `deg π`.**  This is the
compatibility that makes Milnor's filtration argument run: `∂_π(L_d) = 0` whenever `deg π > d`. -/
theorem milnorResidue_degreeFiltration_eq_zero {π : Polynomial F} (hπ : Irreducible π) {d n : ℕ}
    (hd : d < π.natDegree) :
    ∀ x ∈ degreeFiltration (F := F) d n,
      milnorResidue (residueDataAtPlace (RatFunc F) (polyPlace hπ)) n x = 0 := by
  intro x hx
  have hle : degreeFiltration (F := F) d n
      ≤ (milnorResidue (residueDataAtPlace (RatFunc F) (polyPlace hπ)) n).ker := by
    refine AddSubgroup.closure_le _ |>.2 ?_
    rintro y ⟨s, hs, rfl⟩
    refine milnorResidue_eq_zero_of_natDegree_lt hπ n s ?_
    intro a ha
    obtain ⟨p, hp, hdeg, hap⟩ := hs a ha
    exact ⟨p, hp, lt_of_le_of_lt hdeg hd, hap⟩
  exact hle hx

/-- A finite list of polynomial units has a common degree bound. -/
theorem exists_common_degree_bound :
    ∀ l : List (RatFunc F)ˣ,
      (∀ a ∈ l, ∃ (p : Polynomial F) (hp : p ≠ 0), a = polyUnit hp) →
      ∃ d : ℕ, ∀ a ∈ l, ∃ (p : Polynomial F) (hp : p ≠ 0),
        p.natDegree ≤ d ∧ a = polyUnit hp := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, by simp⟩
  | cons a t ih =>
      intro hl
      obtain ⟨p, hp, hap⟩ := hl a (by simp)
      obtain ⟨d, hd⟩ := ih (fun b hb => hl b (by simp [hb]))
      refine ⟨max d p.natDegree, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact ⟨p, hp, le_max_right _ _, hap⟩
      · obtain ⟨q, hq, hqd, hbq⟩ := hd b hb'
        exact ⟨q, hq, le_trans hqd (le_max_left _ _), hbq⟩

/-- The union of the degree filtration, as a subgroup. -/
noncomputable def degreeFiltrationUnion (n : ℕ) : AddSubgroup (MilnorKDeg (RatFunc F) n) where
  carrier := {x | ∃ d, x ∈ degreeFiltration (F := F) d n}
  zero_mem' := ⟨0, AddSubgroup.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨d₁, hx⟩ ⟨d₂, hy⟩
    exact ⟨max d₁ d₂, AddSubgroup.add_mem _
      (degreeFiltration_mono (le_max_left d₁ d₂) hx)
      (degreeFiltration_mono (le_max_right d₁ d₂) hy)⟩
  neg_mem' := by
    rintro x ⟨d, hx⟩
    exact ⟨d, AddSubgroup.neg_mem _ hx⟩

/-- **Milnor's degree filtration is exhaustive.**  Every class of `K_n^M(F(t))` is a combination of
symbols of polynomials, so it lies in some `L_d`. -/
theorem exists_mem_degreeFiltration (n : ℕ) (x : MilnorKDeg (RatFunc F) n) :
    ∃ d, x ∈ degreeFiltration (F := F) d n := by
  have hx : x ∈ degreeFiltrationUnion (F := F) n := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) x
    refine milnorClassDeg_mem_of_generating _ (closure_polyUnit_eq_top (F := F)) ?_ s.val s.property
    intro l p hl
    obtain ⟨d, hd⟩ := exists_common_degree_bound (F := F) l hl
    exact ⟨d, AddSubgroup.subset_closure ⟨⟨l, p⟩, hd, rfl⟩⟩
  exact hx

/-- A polynomial unit of degree zero is the image of a unit of `F`. -/
theorem polyUnit_of_natDegree_le_zero {p : Polynomial F} (hp : p ≠ 0) (hd : p.natDegree ≤ 0) :
    ∃ c : Fˣ, polyUnit hp = milnorUnitMap (ratFuncConstHom (F := F)) c := by
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 (Nat.le_zero.1 hd)
  have ha0 : a ≠ 0 := by
    intro h
    apply hp
    rw [← ha, h, map_zero]
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  show algebraMap (Polynomial F) (RatFunc F) p
    = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C a)
  rw [ha]

/-- A list of degree-zero polynomial units lifts to a list of units of `F`. -/
theorem exists_list_constUnits :
    ∀ l : List (RatFunc F)ˣ,
      (∀ a ∈ l, ∃ (p : Polynomial F) (hp : p ≠ 0), p.natDegree ≤ 0 ∧ a = polyUnit hp) →
      ∃ m : List Fˣ, m.map (milnorUnitMap (ratFuncConstHom (F := F))) = l := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons a t ih =>
      intro hl
      obtain ⟨p, hp, hd, hap⟩ := hl a (by simp)
      obtain ⟨c, hc⟩ := polyUnit_of_natDegree_le_zero hp hd
      obtain ⟨m, hm⟩ := ih (fun b hb => hl b (by simp [hb]))
      exact ⟨c :: m, by rw [List.map_cons, hm, ← hc, ← hap]⟩

/-- **The bottom of the degree filtration is the image of `K_n^M(F)`.** -/
theorem degreeFiltration_zero_le_range (n : ℕ) :
    degreeFiltration (F := F) 0 n
      ≤ AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n) := by
  refine AddSubgroup.closure_le _ |>.2 ?_
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨m, hm⟩ := exists_list_constUnits (F := F) s.val hs
  have hlen : m.length = n := by
    rw [← s.property, ← hm, List.length_map]
  refine ⟨milnorClassDeg F n ⟨m, hlen⟩, ?_⟩
  rw [milnorKDegMap_class]
  exact congrArg (milnorClassDeg (RatFunc F) n) (Subtype.ext hm)

/-! ## `π` as the uniformizer at its own place -/

theorem polyUnit_tameVal {π : Polynomial F} (hπ : Irreducible π) :
    Multiplicative.toAdd
      (tameValHom ((polyPlace hπ).valuation (RatFunc F)) (polyUnit hπ.ne_zero)) = 1 := by
  have hval : ((polyPlace hπ).valuation (RatFunc F))
      ((polyUnit hπ.ne_zero : (RatFunc F)ˣ) : RatFunc F) = WithZero.exp (-1 : ℤ) := by
    show ((polyPlace hπ).valuation (RatFunc F))
      (algebraMap (Polynomial F) (RatFunc F) π) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero rfl
  have hcoe : ((tameUnzero ((polyPlace hπ).valuation (RatFunc F)) (polyUnit hπ.ne_zero) :
      Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact hval
  have hun : tameUnzero ((polyPlace hπ).valuation (RatFunc F)) (polyUnit hπ.ne_zero)
      = Multiplicative.ofAdd (-1 : ℤ) := WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- **The residue data at `π` with `π` itself as the uniformizer.**  Milnor's residue depends on a
choice of uniformizer; taking `π` itself is what makes the degree filtration argument work, because
then the symbol `{u₁, …, u_{n}, π}` realising a class of `F[X]/(π)` has all its entries of degree at
most `deg π`. -/
noncomputable def polyResidueData {π : Polynomial F} (hπ : Irreducible π) :
    ResidueData (RatFunc F) (IsLocalRing.ResidueField
      (((polyPlace hπ).valuation (RatFunc F)).valuationSubring)) :=
  residueDataOfValuation ((polyPlace hπ).valuation (RatFunc F)) (polyUnit hπ.ne_zero)
    (polyUnit_tameVal hπ)

@[simp]
theorem polyResidueData_unif {π : Polynomial F} (hπ : Irreducible π) :
    (polyResidueData hπ).unif = polyUnit hπ.ne_zero := rfl

@[simp]
theorem polyResidueData_toTameData {π : Polynomial F} (hπ : Irreducible π) :
    (polyResidueData hπ).toTameData
      = tameDataOfValuation ((polyPlace hπ).valuation (RatFunc F)) := rfl

end ConstantsAtX

end GaloisForLFunctions.HTGeometry
