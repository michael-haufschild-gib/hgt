import GaloisForLFunctions.HTGeometry.MilnorKTameResidueFinite

/-!
# The residue field at a finite place is the residue ring of the prime

The valuation subring at a height-one prime `v` of a Dedekind domain `R` is the localization of `R`
at `v`, so its residue field is the residue field of the prime.  A nonzero prime of a Dedekind
domain is maximal, so `R ⧸ v.asIdeal` is already a field, and a fraction field of a field is that
field.  Hence

`ResidueField ((v.valuation K).valuationSubring) ≅ R ⧸ v.asIdeal`,

compatibly with the two maps out of `R`.  The corpus already had this chain inlined inside the proof
that the residue fields at the finite places of a number ring are finite; this module makes it a
named isomorphism with its compatibility, which is what any computation with the residue or the
specialization of Milnor `K`-theory at a finite place needs.

* `quotientEquivIdealResidueField` : **for a maximal ideal, `R ⧸ I ≅ κ(I)`.**
* `residueFieldAtPlaceEquiv` : **`κ(v) ≅ R ⧸ v.asIdeal` at a finite place.**
* `residueFieldAtPlaceEquiv_residue_algebraMap` : **it carries the residue of an element of `R` to
  its class mod `v`.**
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsLocalRing

section MaximalIdeal

variable {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime]

/-- **For a maximal ideal, the quotient ring is already the residue field.**  The structure map is
injective because the quotient injects into its fraction field, and surjective because every nonzero
element of a field is a unit. -/
noncomputable def quotientEquivIdealResidueField [I.IsMaximal] :
    (R ⧸ I) ≃+* Ideal.ResidueField I :=
  RingEquiv.ofBijective (algebraMap (R ⧸ I) (Ideal.ResidueField I))
    ⟨Ideal.injective_algebraMap_quotient_residueField I,
      algebraMap_surjective_of_isFractionRing_of_isUnit fun a ha => by
        obtain ⟨b, hb⟩ :=
          ((Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 inferInstance).mul_inv_cancel ha
        exact ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩⟩

@[simp]
theorem quotientEquivIdealResidueField_apply [I.IsMaximal] (x : R ⧸ I) :
    quotientEquivIdealResidueField I x = algebraMap (R ⧸ I) (Ideal.ResidueField I) x := rfl

@[simp]
theorem quotientEquivIdealResidueField_mk [I.IsMaximal] (r : R) :
    quotientEquivIdealResidueField I (Ideal.Quotient.mk I r)
      = algebraMap R (Ideal.ResidueField I) r := by
  rw [quotientEquivIdealResidueField_apply]
  exact Ideal.algebraMap_quotient_residueField_mk I r

end MaximalIdeal

section AtPlace

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- The localization of `R` at `v` is the valuation subring at `v`, as an `R`-algebra. -/
noncomputable def placeLocalizationAlgEquiv :
    Localization.AtPrime v.asIdeal ≃ₐ[R] (HeightOneSpectrum.valuationSubringAtPrime K v) :=
  IsLocalization.algEquiv v.asIdeal.primeCompl _ _

/-- The two presentations of the valuation subring at `v` agree. -/
noncomputable def placeValuationSubringCongr :
    (HeightOneSpectrum.valuationSubringAtPrime K v) ≃+*
      ((v.valuation K).valuationSubring) :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring
      (HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v))

@[simp]
theorem placeValuationSubringCongr_coe
    (x : HeightOneSpectrum.valuationSubringAtPrime K v) :
    ((placeValuationSubringCongr K v x : ((v.valuation K).valuationSubring)) : K)
      = (x : K) := rfl

instance placeAsIdeal_isMaximal : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot

/-- The two-step comparison `κ(v.asIdeal) ≅ ResidueField (valuation subring at v)`. -/
noncomputable def placeResidueChain :
    Ideal.ResidueField v.asIdeal ≃+* ResidueField ((v.valuation K).valuationSubring) :=
  (ResidueField.mapEquiv (placeLocalizationAlgEquiv K v).toRingEquiv).trans
    (ResidueField.mapEquiv (placeValuationSubringCongr K v))

/-- **The residue field at a finite place is the residue ring of the prime.** -/
noncomputable def residueFieldAtPlaceEquiv :
    ResidueField ((v.valuation K).valuationSubring) ≃+* (R ⧸ v.asIdeal) :=
  ((placeResidueChain K v).symm).trans (quotientEquivIdealResidueField v.asIdeal).symm

/-- An element of `R` is a valuation integer at every finite place. -/
theorem algebraMap_mem_valuationSubringAtPlace (r : R) :
    algebraMap R K r ∈ (v.valuation K).valuationSubring :=
  (Valuation.mem_valuationSubring_iff _ _).2 (v.valuation_le_one r)

/-- An element of `R`, as an element of the valuation subring at a finite place. -/
def placeIntegerElt (r : R) : ((v.valuation K).valuationSubring) :=
  ⟨algebraMap R K r, algebraMap_mem_valuationSubringAtPlace K v r⟩

@[simp]
theorem placeIntegerElt_coe (r : R) : ((placeIntegerElt K v r : _) : K) = algebraMap R K r := rfl

/-- **The isomorphism is compatible with the two maps out of `R`**: the residue of an element of
`R` at a finite place is its class modulo that place. -/
theorem residueFieldAtPlaceEquiv_residue (r : R) :
    residueFieldAtPlaceEquiv K v (residue _ (placeIntegerElt K v r))
      = Ideal.Quotient.mk v.asIdeal r := by
  refine (quotientEquivIdealResidueField v.asIdeal).injective ?_
  have hstep : (placeResidueChain K v)
      (algebraMap R (Ideal.ResidueField v.asIdeal) r)
      = residue _ (placeIntegerElt K v r) := by
    rw [placeResidueChain]
    have hloc : algebraMap R (Ideal.ResidueField v.asIdeal) r
        = residue (Localization.AtPrime v.asIdeal)
          (algebraMap R (Localization.AtPrime v.asIdeal) r) := by
      rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal)
        (Ideal.ResidueField v.asIdeal), ResidueField.algebraMap_eq]
    rw [hloc]
    show residue _ ((placeValuationSubringCongr K v)
        ((placeLocalizationAlgEquiv K v)
          (algebraMap R (Localization.AtPrime v.asIdeal) r))) = _
    congr 1
    refine Subtype.ext ?_
    rw [placeValuationSubringCongr_coe, placeIntegerElt_coe]
    show ((placeLocalizationAlgEquiv K v)
      (algebraMap R (Localization.AtPrime v.asIdeal) r) : K) = algebraMap R K r
    rw [AlgEquiv.commutes]
    rfl
  rw [quotientEquivIdealResidueField_mk]
  show (quotientEquivIdealResidueField v.asIdeal)
    ((quotientEquivIdealResidueField v.asIdeal).symm
      ((placeResidueChain K v).symm (residue _ (placeIntegerElt K v r))))
    = algebraMap R (Ideal.ResidueField v.asIdeal) r
  rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_eq, hstep]

/-- **Every residue class at a finite place is represented by an element of `R`.** -/
theorem residue_placeIntegerElt_surjective :
    Function.Surjective
      (fun r : R => residue ((v.valuation K).valuationSubring) (placeIntegerElt K v r)) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (residueFieldAtPlaceEquiv K v y)
  refine ⟨r, ?_⟩
  refine (residueFieldAtPlaceEquiv K v).injective ?_
  rw [residueFieldAtPlaceEquiv_residue, hr]

end AtPlace

/-! ## Finite residue fields force a cyclotomic divisibility -/

section CyclotomicDivisibility

variable {R : Type*} [CommRing R]

/-- **A prime with finite residue field divides `aⁿ − 1` for some `n > 0`, whenever it does not
divide `a`.**  The residue of `a` is a nonzero element of a finite field, hence a root of unity.

This is the arithmetic half of the cyclotomic engine for Milnor symbols: it guarantees that every
prime not dividing `a` occurs in the factorisation of some `1 − aⁿ`, and `{a, 1 − aⁿ}` is always
`n`-torsion. -/
theorem exists_pow_sub_one_mem_of_finite_quotient (I : Ideal R) [I.IsMaximal]
    [Finite (R ⧸ I)] {a : R} (ha : a ∉ I) :
    ∃ n : ℕ, 0 < n ∧ a ^ n - 1 ∈ I := by
  classical
  have hne : (Ideal.Quotient.mk I a) ≠ 0 := fun h => ha ((Ideal.Quotient.eq_zero_iff_mem).1 h)
  haveI : Finite ((R ⧸ I)ˣ) :=
    Finite.of_injective (fun u : (R ⧸ I)ˣ => (u : R ⧸ I)) (fun _ _ h => Units.ext h)
  obtain ⟨b, hb⟩ :=
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 inferInstance).mul_inv_cancel hne
  set u : (R ⧸ I)ˣ :=
    ⟨Ideal.Quotient.mk I a, b, hb, by rw [mul_comm]; exact hb⟩ with hu
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  refine (Ideal.Quotient.eq_zero_iff_mem).1 ?_
  have hval : ((u : (R ⧸ I)ˣ) : R ⧸ I) = Ideal.Quotient.mk I a := rfl
  have hpow : (Ideal.Quotient.mk I a) ^ orderOf u = 1 := by
    rw [← hval, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  rw [map_sub, map_pow, map_one, hpow, sub_self]

end CyclotomicDivisibility

end GaloisForLFunctions.HTGeometry
