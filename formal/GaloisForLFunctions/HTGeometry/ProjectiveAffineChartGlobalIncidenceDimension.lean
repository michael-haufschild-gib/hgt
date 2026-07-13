import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullEvaluation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable local instance (priority := 10000) globalDimensionMvPolynomialCommRing
    {R σ : Type} [CommRing R] : CommRing (MvPolynomial σ R) := inferInstance

noncomputable local instance (priority := 10000) globalDimensionMvPolynomialRing
    {R σ : Type} [CommRing R] : Ring (MvPolynomial σ R) :=
  @CommRing.toRing _ globalDimensionMvPolynomialCommRing

noncomputable local instance (priority := 10000) globalDimensionMvPolynomialSemiring
    {R σ : Type} [CommRing R] : Semiring (MvPolynomial σ R) :=
  @Ring.toSemiring _ globalDimensionMvPolynomialRing

noncomputable local instance (priority := 10000) globalDimensionIdealQuotientCommRing
    {R : Type} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) :=
  { toRing := Ideal.Quotient.ring I
    mul_comm := (Ideal.Quotient.commRing I).mul_comm }

noncomputable local instance (priority := 10000) globalDimensionIdealQuotientRing
    {R : Type} [CommRing R] (I : Ideal R) : Ring (R ⧸ I) :=
  Ideal.Quotient.ring I

noncomputable local instance (priority := 10000) globalDimensionIdealQuotientSemiring
    {R : Type} [CommRing R] (I : Ideal R) : Semiring (R ⧸ I) :=
  (Ideal.Quotient.ring I).toSemiring

noncomputable local instance (priority := 10000) globalDimensionIdealQuotientCommSemiring
    {R : Type} [CommRing R] (I : Ideal R) : CommSemiring (R ⧸ I) :=
  @CommRing.toCommSemiring _ (globalDimensionIdealQuotientCommRing I)

/-- Uniform prime-height bounds with a fixed finite codimension assemble to a global Krull bound. -/
theorem ringKrullDim_add_nat_le_of_prime_height_add_nat_le
    {B : Type} [CommRing B] [Nonempty (PrimeSpectrum B)]
    (e N : ℕ)
    (h : ∀ (q : Ideal B), q.IsPrime →
      (q.height : WithBot ℕ∞) + e ≤ (N : WithBot ℕ∞)) :
    ringKrullDim B + e ≤ (N : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_height_of_nonempty,
    ← WithBot.coe_natCast e, ← WithBot.coe_natCast N,
    ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro q
  rw [← q.height_eq_orderHeight]
  exact_mod_cast h q.asIdeal q.isPrime

/-- A prime has no greater height than any localization in which it survives. -/
theorem Ideal.height_le_ringKrullDim_isLocalization_of_disjoint
    {B S : Type} [CommRing B] [CommRing S] [Algebra B S]
    (M : Submonoid B) [IsLocalization M S]
    (q : Ideal B) [q.IsPrime] (hdisj : Disjoint (M : Set B) (q : Set B)) :
    (q.height : WithBot ℕ∞) ≤ ringKrullDim S := by
  have hheight : (q.map (algebraMap B S)).height = q.height :=
    IsLocalization.height_map_of_disjoint (S := S) M q hdisj
  haveI : (q.map (algebraMap B S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S q inferInstance hdisj
  rw [← hheight]
  exact Ideal.height_le_ringKrullDim_of_isPrime

set_option maxHeartbeats 1600000 in
/-- The manuscript's exact incidence-codimension bound on the genuine global affine-chart
coordinate ring. -/
theorem projectiveChartGlobalIncidenceRing_evaluationCodimension
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) ≤
      (Fintype.card row * n : ℕ) := by
  let e := Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1
  let N := Fintype.card row * n
  change ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
    (e : WithBot ℕ∞) ≤ (N : WithBot ℕ∞)
  cases isEmpty_or_nonempty
      (PrimeSpectrum (projectiveChartGlobalIncidenceRing q n z j exponent)) with
  | inl hempty =>
      letI : IsEmpty
          (PrimeSpectrum (projectiveChartGlobalIncidenceRing q n z j exponent)) := hempty
      have hdim : ringKrullDim
          (projectiveChartGlobalIncidenceRing q n z j exponent) = ⊥ := by
        unfold ringKrullDim
        exact Order.krullDim_eq_bot
      rw [hdim]
      simp
  | inr hnonempty =>
      letI : Nonempty
          (PrimeSpectrum (projectiveChartGlobalIncidenceRing q n z j exponent)) := hnonempty
      rw [ringKrullDim, Order.krullDim_eq_iSup_height_of_nonempty,
        ← WithBot.coe_natCast e, ← WithBot.coe_natCast N,
        ← WithBot.coe_add, ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
      intro Qs
      let Q := Qs.asIdeal
      letI : Q.IsPrime := Qs.isPrime
      let p : Ideal (projectiveChartCoefficientRing j) := Q.comap
        (algebraMap (projectiveChartCoefficientRing j)
          (projectiveChartGlobalIncidenceRing q n z j exponent))
      letI : p.IsPrime := inferInstance
      let S0 := MvPolynomial (row × Fin n) (Localization.AtPrime p)
      let S := projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p
      let M0 := p.primeCompl.map
        (MvPolynomial.C : projectiveChartCoefficientRing j →+*
          MvPolynomial (row × Fin n) (projectiveChartCoefficientRing j))
      let M := M0.map
        (Ideal.Quotient.mk (projectiveChartGlobalIncidenceIdeal q n z j exponent))
      letI : Algebra (projectiveChartGlobalIncidenceRing q n z j exponent) S :=
        (localizationQuotientMap (S := S0)
          (projectiveChartGlobalIncidenceIdeal q n z j exponent)).toAlgebra
      letI : IsLocalization M S := by
        exact isLocalization_projectiveChartBaseChangedGlobalIncidenceRing
          q n z j exponent p
      have hdisj : Disjoint
          (M : Set (projectiveChartGlobalIncidenceRing q n z j exponent))
          (Q : Set (projectiveChartGlobalIncidenceRing q n z j exponent)) := by
        rw [Set.disjoint_left]
        intro x hxM hxQ
        rcases hxM with ⟨y, hy, rfl⟩
        rcases hy with ⟨a, ha, rfl⟩
        exact ha hxQ
      let E := IsLocalization.orderIsoOfPrime
        (R := projectiveChartGlobalIncidenceRing q n z j exponent) M S
      let Qd : {P : Ideal (projectiveChartGlobalIncidenceRing q n z j exponent) //
          P.IsPrime ∧ Disjoint
            (M : Set (projectiveChartGlobalIncidenceRing q n z j exponent))
            (P : Set (projectiveChartGlobalIncidenceRing q n z j exponent))} :=
        ⟨Q, inferInstance, hdisj⟩
      let Psub := E.symm Qd
      let P : Ideal S := Psub.1
      letI : P.IsPrime := Psub.2
      have hunder : P.under (projectiveChartGlobalIncidenceRing q n z j exponent) = Q := by
        exact congrArg (fun X => X.1) (E.apply_symm_apply Qd)
      have hheight : (Q.height : WithBot ℕ∞) ≤ ringKrullDim S := by
        rw [← hunder, IsLocalization.height_under M P]
        exact Ideal.height_le_ringKrullDim_of_isPrime
      rw [← Qs.height_eq_orderHeight]
      exact_mod_cast (show (Q.height : WithBot ℕ∞) + e ≤ (N : WithBot ℕ∞) from calc
        (Q.height : WithBot ℕ∞) + e ≤ ringKrullDim S + e := by
          simpa [add_comm] using add_le_add_right hheight e
        _ ≤ (N : WithBot ℕ∞) := by
          exact projectiveChartBaseChangedGlobalIncidenceRing_evaluationCodimension
            q n z hz j exponent hexponent p hrows)

end
end GaloisForLFunctions.HTGeometry
