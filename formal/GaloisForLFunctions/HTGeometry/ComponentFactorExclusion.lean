import GaloisForLFunctions.HTGeometry.RittRingGeneralComponent

/-!
# The initial and the separant avoid the component of a factor

A characteristic polynomial may become reducible after the coefficient field is enlarged, so the
component that carries the characteristic property belongs to an irreducible factor rather than to
the polynomial itself.  The two exceptional polynomials of the reduction -- the initial and the
separant -- still avoid that component, provided the factor keeps the leader of the polynomial and
the polynomial is squarefree.

For the initial this is a degree count: it has leader degree zero while the factor has positive
leader degree.  For the separant it is the Leibniz rule: a factor dividing the separant of a product
whose leader it shares must divide either its own separant, which is excluded by degree, or the
complementary factor, which would make the polynomial a square.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {L : Type*} [Field L] [Differential L] [CharZero L]

/-- The initial does not involve the variable it is taken at. -/
theorem mvPolynomialInitialAt_degreeOf_eq_zero {K σ : Type*} [CommSemiring K] (i : σ)
    (P : MvPolynomial σ K) : MvPolynomial.degreeOf i (mvPolynomialInitialAt i P) = 0 := by
  classical
  by_contra hne
  obtain ⟨b, _, hbv⟩ := MvPolynomial.mem_vars_rename Subtype.val
    (mvPolynomialAsPolynomialAt i P).leadingCoeff
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.2 hne)
  exact b.2 hbv

/-- The initial of a nonzero polynomial is nonzero. -/
theorem mvPolynomialInitialAt_ne_zero {K σ : Type*} [CommSemiring K] (i : σ)
    {P : MvPolynomial σ K} (hP : P ≠ 0) : mvPolynomialInitialAt i P ≠ 0 := by
  classical
  intro hzero
  refine mvPolynomialAsPolynomialAt_ne_zero (i := i) hP ?_
  refine Polynomial.leadingCoeff_eq_zero.mp ?_
  refine MvPolynomial.rename_injective Subtype.val Subtype.val_injective ?_
  simpa [mvPolynomialInitialAt] using hzero

omit [Differential L] [CharZero L] in
/-- A polynomial dividing a nonzero polynomial of at most its own order and of strictly smaller
leader degree is impossible. -/
theorem not_dvd_of_lower_leaderDegree {A R : DifferentialPolynomial Unit L} (hA : A ≠ 0)
    (hR : R ≠ 0) (horder : scalarDifferentialPolynomialOrder R ≤
      scalarDifferentialPolynomialOrder A)
    (hdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) R <
      MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) A) :
    ¬ A ∣ R := fun hdvd => hR (reduced_eq_zero_of_dvd hA hdvd horder hdeg)

omit [Differential L] [CharZero L] in
/-- The order of a polynomial bounds the order of every polynomial whose variables it contains. -/
theorem scalarDifferentialPolynomialOrder_le_of_vars_subset
    {P Q : DifferentialPolynomial Unit L} (h : P.vars ⊆ Q.vars) :
    scalarDifferentialPolynomialOrder P ≤ scalarDifferentialPolynomialOrder Q :=
  Finset.sup_le fun _ hp => Finset.le_sup (f := fun j : Unit × ℕ ↦ j.2) (h hp)

omit [Differential L] [CharZero L] in
/-- **The initial of a polynomial is outside the component of any factor with the same leader.**
The initial has leader degree zero, so a factor of positive leader degree cannot divide it, and the
component's characteristic property would force exactly that. -/
theorem initial_notMem_of_oracle {C A : DifferentialPolynomial Unit L}
    (hC : C ≠ 0) (hAvars : A.vars.Nonempty)
    (horder : scalarDifferentialPolynomialOrder A = scalarDifferentialPolynomialOrder C)
    {P : Ideal (DifferentialPolynomial Unit L)}
    (hPdvd : ∀ Z : DifferentialPolynomial Unit L, Z ∈ P →
      scalarDifferentialPolynomialOrder Z ≤ scalarDifferentialPolynomialOrder A → A ∣ Z) :
    scalarDifferentialPolynomialInitial C ∉ P := by
  classical
  intro hmem
  have hA0 : A ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := hAvars
    simp [h0] at hj
  have hIvars : (scalarDifferentialPolynomialInitial C).vars ⊆ C.vars :=
    mvPolynomialInitialAt_vars_subset _ C
  have hIorder : scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialInitial C) ≤
      scalarDifferentialPolynomialOrder A := by
    rw [horder]
    exact scalarDifferentialPolynomialOrder_le_of_vars_subset hIvars
  have hI0 : scalarDifferentialPolynomialInitial C ≠ 0 :=
    mvPolynomialInitialAt_ne_zero _ hC
  have hIdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A)
      (scalarDifferentialPolynomialInitial C) = 0 := by
    rw [horder]
    exact mvPolynomialInitialAt_degreeOf_eq_zero _ C
  have hApos : 0 < MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) A :=
    scalarDifferentialPolynomialLeaderDegree_pos hAvars
  exact not_dvd_of_lower_leaderDegree hA0 hI0 hIorder (by omega) (hPdvd _ hmem hIorder)

omit [Differential L] [CharZero L] in
/-- The separant of a product is computed by the Leibniz rule at the shared leader. -/
theorem separant_mul_of_order_eq {A B : DifferentialPolynomial Unit L}
    (horder : scalarDifferentialPolynomialOrder A =
      scalarDifferentialPolynomialOrder (A * B)) :
    scalarDifferentialPolynomialSeparant (A * B) =
      MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) A * B +
        A * MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) B := by
  rw [scalarDifferentialPolynomialSeparant, scalarDifferentialPolynomialLeader, ← horder,
    Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

omit [Differential L] in
/-- **The separant of a squarefree polynomial is outside the component of an irreducible factor with
the same leader.**  Divisibility of the separant would, by the Leibniz rule, make the factor divide
either its own separant -- impossible by leader degree in characteristic zero -- or the
complementary factor, which would make the polynomial a square. -/
theorem separant_notMem_of_oracle {A B : DifferentialPolynomial Unit L}
    (hAirr : Irreducible A) (hAvars : A.vars.Nonempty)
    (hsquarefree : Squarefree (A * B))
    (horder : scalarDifferentialPolynomialOrder A =
      scalarDifferentialPolynomialOrder (A * B))
    {P : Ideal (DifferentialPolynomial Unit L)}
    (hPdvd : ∀ Z : DifferentialPolynomial Unit L, Z ∈ P →
      scalarDifferentialPolynomialOrder Z ≤ scalarDifferentialPolynomialOrder A → A ∣ Z) :
    scalarDifferentialPolynomialSeparant (A * B) ∉ P := by
  classical
  intro hmem
  have hA0 : A ≠ 0 := hAirr.ne_zero
  have hSvars : (scalarDifferentialPolynomialSeparant (A * B)).vars ⊆ (A * B).vars :=
    mvPolynomial_vars_pderiv_subset _ _
  have hSorder : scalarDifferentialPolynomialOrder
      (scalarDifferentialPolynomialSeparant (A * B)) ≤
      scalarDifferentialPolynomialOrder A := by
    rw [horder]
    exact scalarDifferentialPolynomialOrder_le_of_vars_subset hSvars
  have hdvd : A ∣ scalarDifferentialPolynomialSeparant (A * B) := hPdvd _ hmem hSorder
  rw [separant_mul_of_order_eq horder] at hdvd
  have hdvd' : A ∣ MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) A * B := by
    have hsecond : A ∣ A * MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) B :=
      Dvd.intro _ rfl
    simpa using (dvd_sub hdvd hsecond)
  have hprime : Prime A := hAirr.prime
  rcases (hprime.dvd_mul.mp hdvd') with hsep | hB
  · have hAdegpos : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) A ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (scalarDifferentialPolynomialLeaderDegree_pos hAvars)
    have hSA0 : MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) A ≠ 0 :=
      scalarDifferentialPolynomialSeparant_ne_zero hAvars
    have hSAorder : scalarDifferentialPolynomialOrder
        (MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) A) ≤
        scalarDifferentialPolynomialOrder A :=
      scalarDifferentialPolynomialOrder_le_of_vars_subset (mvPolynomial_vars_pderiv_subset _ _)
    have hSAdeg : MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A)
        (MvPolynomial.pderiv ((), scalarDifferentialPolynomialOrder A) A) <
        MvPolynomial.degreeOf ((), scalarDifferentialPolynomialOrder A) A :=
      mvPolynomial_degreeOf_pderiv_lt hAdegpos
    exact not_dvd_of_lower_leaderDegree hA0 hSA0 hSAorder hSAdeg hsep
  · obtain ⟨T, hT⟩ := hB
    have hsq : A * A ∣ A * B := by
      rw [hT]
      exact ⟨T, by ring⟩
    exact hAirr.not_isUnit (hsquarefree A hsq)

omit [Differential L] in
/-- **The saturation multiplier can be cancelled against the component of a factor.**  A product of
powers of the initial and the separant with a further factor lies in the component only through that
further factor, because neither exceptional polynomial lies in it. -/
theorem mem_of_initial_separant_powers_mem {A B W : DifferentialPolynomial Unit L} {a b : ℕ}
    (hAirr : Irreducible A) (hAvars : A.vars.Nonempty)
    (hsquarefree : Squarefree (A * B))
    (horder : scalarDifferentialPolynomialOrder A =
      scalarDifferentialPolynomialOrder (A * B))
    {P : Ideal (DifferentialPolynomial Unit L)} (hPprime : P.IsPrime)
    (hPdvd : ∀ Z : DifferentialPolynomial Unit L, Z ∈ P →
      scalarDifferentialPolynomialOrder Z ≤ scalarDifferentialPolynomialOrder A → A ∣ Z)
    (hmem : scalarDifferentialPolynomialInitial (A * B) ^ a *
        (scalarDifferentialPolynomialSeparant (A * B) ^ b * W) ∈ P) :
    W ∈ P := by
  have hC0 : A * B ≠ 0 := by
    intro h0
    rw [h0] at hsquarefree
    exact not_squarefree_zero hsquarefree
  rcases hPprime.mem_or_mem hmem with hI | hrest
  · exact absurd (hPprime.mem_of_pow_mem a hI)
      (initial_notMem_of_oracle hC0 hAvars horder hPdvd)
  · rcases hPprime.mem_or_mem hrest with hS | hW
    · exact absurd (hPprime.mem_of_pow_mem b hS)
        (separant_notMem_of_oracle hAirr hAvars hsquarefree horder hPdvd)
    · exact hW

end

end GaloisForLFunctions
