import GaloisForLFunctions.HTGeometry.GeneralComponentIdeal
import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing
import GaloisForLFunctions.HTGeometry.DifferentialRelationBaseChange
import GaloisForLFunctions.HTGeometry.JetFractionDerivationTransport

/-!
# Ritt reduction over a coefficient ring, driven by a general component

A characteristic of a prime differential ideal absorbs the whole ideal after multiplication by
powers of its initial and its separant.  Over a field this is the classical Ritt reduction.  Here
the coefficient ring is only a differential domain of characteristic zero, and the characteristic
property is imported from the general component of the polynomial over an ambient differential
field.

The point of running the reduction over the ring rather than over the fraction field is the shape of
the multiplier.  A certificate obtained over the fraction field and cleared of denominators carries
an unknown coefficient-ring factor; here the two multipliers are the initial and the separant of the
polynomial itself, so every variable occurring in them already occurs in the polynomial.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

/-- A multiple of `A` that is reduced with respect to `A` vanishes:  a nonzero multiple has at least
the rank of `A`, while reducedness puts it strictly below. -/
theorem reduced_eq_zero_of_dvd {K : Type*} [Field K]
    {A R : DifferentialPolynomial Unit K} (hA : A ≠ 0) (hdvd : A ∣ R)
    (horder : scalarDifferentialPolynomialOrder R ≤ scalarDifferentialPolynomialOrder A)
    (hdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) R <
      MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) A) :
    R = 0 := by
  by_contra hR
  refine not_rank_lt_of_dvd hA hR hdvd ?_
  rcases lt_or_eq_of_le horder with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeader,
      scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeader, heq]
    exact hdeg

variable {K L : Type*} [CommRing K] [IsDomain K] [CharZero K] [Differential K]
variable [Field L] [Differential L] [CharZero L]

omit [Differential K] in
/-- The separant of a nonconstant differential polynomial over a differential domain of
characteristic zero is nonzero. -/
theorem scalarDifferentialPolynomialSeparant_ne_zero_of_domain
    {A : DifferentialPolynomial Unit K} (hA : A.vars.Nonempty) :
    scalarDifferentialPolynomialSeparant A ≠ 0 :=
  pderiv_ne_zero_of_mem_vars_domain (scalarDifferentialPolynomialLeader_mem_vars hA)

omit [CharZero L] in
/-- **Ritt reduction over a coefficient ring, driven by a characteristic oracle over an ambient
differential field.**

The prime is supplied by the caller together with the only two properties the reduction uses: it
contains the differential ideal of the image of `A`, and every one of its elements whose order does
not exceed that of the image of `A` is divisible by it.  Every polynomial whose image lies in the
prime is then absorbed into the differential ideal of `A` after multiplication by a power of the
initial and a power of the separant of `A`.

Both multipliers are polynomials in the jets of `A`, so the certificate stays in the polynomial ring
over the coefficient ring: no denominator, and no variable outside those of `A`. -/
theorem exists_oracle_initial_separant_powers_mem_diffPolyIterateIdeal
    (φ : K →+* L) (hinj : Function.Injective φ) (hcomm : ∀ c : K, φ c′ = (φ c)′)
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty)
    {P : Ideal (DifferentialPolynomial Unit L)}
    (hPle : differentialPolynomialIterateIdeal (MvPolynomial.map φ A) ≤ P)
    (hPdvd : ∀ Z : DifferentialPolynomial Unit L, Z ∈ P →
      scalarDifferentialPolynomialOrder Z ≤
        scalarDifferentialPolynomialOrder (MvPolynomial.map φ A) →
      MvPolynomial.map φ A ∣ Z)
    {Q : DifferentialPolynomial Unit K} (hQ : MvPolynomial.map φ Q ∈ P) :
    ∃ a b : ℕ,
      scalarDifferentialPolynomialInitial A ^ a *
          (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈ diffPolyIterateIdeal A := by
  classical
  set A' : DifferentialPolynomial Unit L := MvPolynomial.map φ A with hA'
  have hmapinj : Function.Injective
      (MvPolynomial.map (σ := Unit × ℕ) φ) := MvPolynomial.map_injective φ hinj
  have hA'0 : A' ≠ 0 := by
    intro h0
    have hA0 : A = 0 := by
      refine hmapinj ?_
      simpa [hA'] using h0
    obtain ⟨j, hj⟩ := hAvars
    simp [hA0] at hj
  set m : ℕ := scalarDifferentialPolynomialOrder A with hm
  have hAjets : ∀ j : ℕ, m < j → ((), j) ∉ A.vars := by
    intro j hj hmem
    have hle : j ≤ scalarDifferentialPolynomialOrder A :=
      Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2) hmem
    omega
  have hS : MvPolynomial.pderiv (((), m) : Unit × ℕ) A ≠ 0 :=
    scalarDifferentialPolynomialSeparant_ne_zero_of_domain hAvars
  have hAleader : MvPolynomial.degreeOf (((), m) : Unit × ℕ) A ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (scalarDifferentialPolynomialLeaderDegree_pos hAvars)
  have hOrderA' : scalarDifferentialPolynomialOrder A' = m := by
    rw [hA', scalarDifferentialPolynomialOrder_map hinj]
  -- the differential ideal of `A` maps into the prime
  have hle : diffPolyIterateIdeal A ≤ Ideal.comap (MvPolynomial.map (σ := Unit × ℕ) φ) P := by
    rw [diffPolyIterateIdeal, Ideal.span_le]
    rintro _ ⟨n, rfl⟩
    have hmapn : MvPolynomial.map φ (diffPolyIterate n A) = diffPolyIterate n A' :=
      map_diffPolyIterate_of_commutes φ hcomm n A
    have hmem : diffPolyIterate n A' ∈ P := by
      refine hPle ?_
      rw [diffPolyIterate_eq_iterateOver]
      exact differentialPolynomialIterateOver_mem_iterateIdeal A' n
    simpa [Ideal.mem_comap, hmapn] using hmem
  -- a reduced element of the prime vanishes
  have hreduced : ∀ R : DifferentialPolynomial Unit K,
      R ∈ Ideal.comap (MvPolynomial.map (σ := Unit × ℕ) φ) P →
      (∀ j : ℕ, m < j → ((), j) ∉ R.vars) →
      MvPolynomial.degreeOf (((), m) : Unit × ℕ) R <
        MvPolynomial.degreeOf (((), m) : Unit × ℕ) A → R = 0 := by
    intro R hRP hRjets hRdeg
    have hRmem : MvPolynomial.map φ R ∈ P := hRP
    have hRorder : scalarDifferentialPolynomialOrder R ≤ m := by
      refine Finset.sup_le ?_
      intro p hp
      by_contra hcon
      obtain ⟨u, j⟩ := p
      obtain rfl : u = () := Subsingleton.elim _ _
      exact hRjets j (by omega) hp
    have hmapOrder : scalarDifferentialPolynomialOrder (MvPolynomial.map φ R) ≤
        scalarDifferentialPolynomialOrder A' := by
      rw [scalarDifferentialPolynomialOrder_map hinj, hOrderA']
      exact hRorder
    have hdvd : A' ∣ MvPolynomial.map φ R := hPdvd _ hRmem hmapOrder
    have hdegmap : MvPolynomial.degreeOf (((), m) : Unit × ℕ) (MvPolynomial.map φ R) <
        MvPolynomial.degreeOf (((), m) : Unit × ℕ) A' := by
      rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
        MvPolynomial.support_map_of_injective _ hinj, hA',
        MvPolynomial.support_map_of_injective _ hinj]
      rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup] at hRdeg
      exact hRdeg
    have hmap0 : MvPolynomial.map φ R = 0 := by
      refine reduced_eq_zero_of_dvd hA'0 hdvd ?_ ?_
      · rw [hOrderA', scalarDifferentialPolynomialOrder_map hinj]
        exact hRorder
      · rw [hOrderA']
        exact hdegmap
    have hzero : MvPolynomial.map φ R = MvPolynomial.map φ (0 : DifferentialPolynomial Unit K) := by
      simpa using hmap0
    exact hmapinj hzero
  exact exists_initial_separant_powers_mem_diffPolyIterateIdeal (i := ()) hAjets hS hAleader hle
    hreduced (scalarDifferentialPolynomialOrder Q) (Q := Q)
    (by
      intro j hj hmemj
      have hle : j ≤ scalarDifferentialPolynomialOrder Q :=
        Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2) hmemj
      omega)
    hQ

/-- **Ritt reduction over a coefficient ring for an irreducible polynomial.**  The general component
of the image supplies the characteristic oracle. -/
theorem exists_component_initial_separant_powers_mem_diffPolyIterateIdeal
    (φ : K →+* L) (hinj : Function.Injective φ) (hcomm : ∀ c : K, φ c′ = (φ c)′)
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty)
    (hAirr : Irreducible (MvPolynomial.map φ A)) :
    ∃ P : Ideal (DifferentialPolynomial Unit L),
      P.IsPrime ∧
        differentialPolynomialIterateIdeal (MvPolynomial.map φ A) ≤ P ∧
          ∀ Q : DifferentialPolynomial Unit K, MvPolynomial.map φ Q ∈ P →
            ∃ a b : ℕ,
              scalarDifferentialPolynomialInitial A ^ a *
                  (scalarDifferentialPolynomialSeparant A ^ b * Q) ∈ diffPolyIterateIdeal A := by
  classical
  have hA'vars : (MvPolynomial.map φ A).vars.Nonempty := by
    obtain ⟨j, hj⟩ := hAvars
    exact ⟨j, by rw [MvPolynomial.vars_map_of_injective _ hinj]; exact hj⟩
  obtain ⟨P, hPprime, hPle, hPdvd, _hinit, _hsep, _hirr⟩ :=
    exists_component_prime_of_irreducible hA'vars hAirr
  exact ⟨P, hPprime, hPle, fun Q hQ =>
    exists_oracle_initial_separant_powers_mem_diffPolyIterateIdeal φ hinj hcomm hAvars hPle
      hPdvd hQ⟩

end

end GaloisForLFunctions
