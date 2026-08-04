import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# A unit has no variables, and the cleared characteristic has an irreducible factor

A unit multivariable polynomial over a field is a nonzero constant, so it has no variables.  The
cleared two-block polynomial is therefore not a unit — a unit would survive the clearing identity and
force the characteristic itself to have empty variable set, which minimality forbids — and in a unique
factorization domain it consequently has an irreducible factor.

That factor is the object the corpus's right-variable support theorems are stated for, and the one a
divisibility bridge may legitimately be applied to, since irreducibility does not survive the
coefficient map into the jet fraction field.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K σ : Type*} [Field K]

/-- **A unit multivariable polynomial over a field has no variables.** -/
theorem mvPolynomial_vars_eq_empty_of_isUnit {P : MvPolynomial σ K} (hP : IsUnit P) :
    P.vars = ∅ := by
  classical
  rw [MvPolynomial.isUnit_iff] at hP
  have hzero : ∀ i, i ≠ 0 → P.coeff i = 0 := fun i hi => by
    simpa using (isNilpotent_iff_eq_zero).1 (hP.2 i hi)
  have hPC : P = MvPolynomial.C (P.coeff 0) := by
    refine MvPolynomial.ext _ _ fun m => ?_
    by_cases hm : m = 0
    · simp [hm]
    · rw [hzero m hm, MvPolynomial.coeff_C, if_neg (Ne.symm hm)]
  rw [hPC, MvPolynomial.vars_C]

/-- **A polynomial with a variable is not a unit.** -/
theorem mvPolynomial_not_isUnit_of_vars_nonempty {P : MvPolynomial σ K}
    (hvars : P.vars.Nonempty) : ¬ IsUnit P := by
  intro hP
  rw [mvPolynomial_vars_eq_empty_of_isUnit hP] at hvars
  simp at hvars

/-- **A nonzero nonunit has an irreducible factor.**  Specialization of unique factorization to the
polynomial rings the Lüroth argument works in. -/
theorem exists_irreducible_factor_of_vars_nonempty
    {P : MvPolynomial σ K} (hP0 : P ≠ 0) (hvars : P.vars.Nonempty) :
    ∃ A : MvPolynomial σ K, Irreducible A ∧ A ∣ P :=
  WfDvdMonoid.exists_irreducible_factor
    (mvPolynomial_not_isUnit_of_vars_nonempty hvars) hP0

/-! ### The cleared two-block characteristic -/

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **The cleared two-block polynomial is not a unit.**  A unit would survive the clearing identity
and force the characteristic to have no variables. -/
theorem twoBlockPolynomial_not_isUnit (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hPvars : P.vars.Nonempty)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    ¬ IsUnit C.polynomial := by
  classical
  intro hunit
  have hequiv : IsUnit (differentialPolynomialTwoBlockEquiv F C.polynomial) :=
    hunit.map (differentialPolynomialTwoBlockEquiv F)
  have hmap : IsUnit (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F C.polynomial)) :=
    hequiv.map (MvPolynomial.map _)
  rw [C.clearing] at hmap
  have hP : IsUnit (MvPolynomial.map
      (differentialIntermediateToJetFraction G hG hy).toRingHom P) :=
    isUnit_of_mul_isUnit_right hmap
  have hvars := mvPolynomial_vars_eq_empty_of_isUnit hP
  rw [MvPolynomial.vars_map_of_injective P
    (differentialIntermediateToJetFraction G hG hy).injective] at hvars
  rw [hvars] at hPvars
  simp at hPvars

/-- **The cleared two-block characteristic has an irreducible factor.** -/
theorem exists_irreducible_factor_twoBlockPolynomial (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hPvars : P.vars.Nonempty)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    ∃ A : DifferentialPolynomial (Unit ⊕ Unit) F, Irreducible A ∧ A ∣ C.polynomial :=
  WfDvdMonoid.exists_irreducible_factor
    (twoBlockPolynomial_not_isUnit G hG hy hPvars C) C.ne_zero

/-- **An irreducible factor with the characteristic's exact right-variable support.**  Combining the
existence of a factor with the corpus's support theorem: the cleared two-block characteristic has an
irreducible factor whose two-block reading has exactly the characteristic's variables. -/
theorem exists_irreducible_factor_right_vars_eq (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hPirreducible : Irreducible P)
    (hPvars : P.vars.Nonempty)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    ∃ A : DifferentialPolynomial (Unit ⊕ Unit) F, Irreducible A ∧ A ∣ C.polynomial ∧
      (differentialPolynomialTwoBlockEquiv F A).vars = P.vars := by
  obtain ⟨A, hAirr, hAdiv⟩ :=
    exists_irreducible_factor_twoBlockPolynomial G hG hy hPvars C
  exact ⟨A, hAirr, hAdiv,
    PrimitiveTwoBlockDifferentialCharacteristic.irreducible_factor_right_vars_eq
      G hG hy P hPirreducible C hAirr hAdiv⟩

/-- **A factor of the cleared characteristic divides the mapped characteristic.**  Reading the
clearing identity through the two-block equivalence turns a factor over the base field into a divisor
of the characteristic in the jet fraction field, the unit scalar dropping out. -/
theorem mapped_twoBlockFactor_dvd (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G}
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {A : DifferentialPolynomial (Unit ⊕ Unit) F} (hAdiv : A ∣ C.polynomial) :
    MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)
      ∣ MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P := by
  classical
  have hdvd1 : differentialPolynomialTwoBlockEquiv F A
      ∣ differentialPolynomialTwoBlockEquiv F C.polynomial :=
    map_dvd (differentialPolynomialTwoBlockEquiv F) hAdiv
  have hdvd2 : MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A)
      ∣ MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F C.polynomial) :=
    map_dvd (MvPolynomial.map _) hdvd1
  rw [C.clearing] at hdvd2
  have hunit : IsUnit (MvPolynomial.C (C.scalar :
      FractionRing (DifferentialPolynomial Unit F)) :
      DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F))) :=
    (C.scalar.isUnit).map MvPolynomial.C
  exact (hunit.dvd_mul_left).1 hdvd2

/-- **The mapped characteristic has a nonconstant irreducible factor.**  Irreducibility need not
survive the coefficient map, so the factor is taken in the jet fraction field's own polynomial ring,
where unique factorization supplies it. -/
theorem exists_irreducible_factor_mapped_characteristic (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hP0 : P ≠ 0) (hPvars : P.vars.Nonempty) :
    ∃ A : DifferentialPolynomial Unit (FractionRing (DifferentialPolynomial Unit F)),
      Irreducible A ∧
        A ∣ MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P ∧
        A.vars.Nonempty := by
  classical
  have hinj : Function.Injective
      (differentialIntermediateToJetFraction G hG hy).toRingHom :=
    (differentialIntermediateToJetFraction G hG hy).injective
  have hmap0 : MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P ≠ 0 :=
    fun h0 => hP0 (MvPolynomial.map_injective _ hinj (by simpa using h0))
  have hmapvars : (MvPolynomial.map
      (differentialIntermediateToJetFraction G hG hy).toRingHom P).vars.Nonempty := by
    rw [MvPolynomial.vars_map_of_injective P hinj]
    exact hPvars
  obtain ⟨A, hAirr, hAdvd⟩ := exists_irreducible_factor_of_vars_nonempty hmap0 hmapvars
  exact ⟨A, hAirr, hAdvd,
    mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit hAirr.ne_zero hAirr.not_isUnit⟩

end

end GaloisForLFunctions
