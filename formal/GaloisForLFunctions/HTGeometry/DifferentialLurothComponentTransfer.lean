import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient
import GaloisForLFunctions.HTGeometry.DifferentialLurothScalarExtensionSquarefree

/-!
# Component transfer for the differential Luroth coefficient theorem

This file moves the characteristic saturation from the intermediate coefficient field to the
formal fraction field of one free jet palette.  The fraction field is equipped with the derivation
transported through the canonical free-jet parametrization, so the coefficient embedding really
commutes with total differentiation; it is not treated as a constant-coefficient map.

The resulting package has three parts.

* total derivatives and their generated ideal commute with a derivation-preserving coefficient
  embedding;
* the coefficient cross-relation belongs to the characteristic saturation and its image is exactly
  the two-copy cross-difference, up to the single denominator-clearing unit;
* equation (78) implies that the cleared characteristic is squarefree after passage to the formal
  fraction field, even though its irreducibility need not survive scalar extension.

These are the componentwise inputs to Ritt's reciprocity argument.  No finite-generation
hypothesis on the intermediate differential field is introduced.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-! ## The differential structure on the formal free-jet fraction field -/

/-- Transport the ambient derivation to the rational formal-jet field through the canonical
parametrization.  This presentation is intentionally tied to `y`: it makes the inverse
parametrization, and hence every restricted intermediate-field coefficient, commute with the
derivation definitionally up to the displayed equivalence. -/
@[reducible]
noncomputable def differentialIndependentJetFractionDifferential
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (y : E) (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    Differential (FractionRing (DifferentialPolynomial Unit F)) := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  exact
    { deriv :=
        { toLinearMap :=
            { toFun := fun z ↦ e.symm ((e z)′)
              map_add' := by
                intro z w
                simp
              map_smul' := by
                intro n z
                simp }
          map_one_eq_zero' := by simp
          leibniz' := by
            intro z w
            change e.symm ((e (z * w))′) =
              z • e.symm ((e w)′) + w • e.symm ((e z)′)
            simp only [map_mul, Derivation.leibniz, map_add, map_smul]
            simp [smul_eq_mul, mul_comm] } }

/-- The transported formal-jet derivation is intertwined by the free-jet parametrization. -/
@[simp]
theorem differentialIndependentJetFraction_deriv
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (y : E) (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (z : FractionRing (DifferentialPolynomial Unit F)) :
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy z′ =
      (differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy z)′ := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  change e (e.symm ((e z)′)) = (e z)′
  exact e.apply_symm_apply _

/-- The inverse free-jet coordinate map on a derivation-closed intermediate field commutes with
the restricted derivation. -/
theorem differentialIntermediateToJetFraction_deriv
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) (g : G) :
    letI : Differential G := derivationClosedDifferential G hGclosed
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    (differentialIntermediateToJetFraction G hG hy g)′ =
      differentialIntermediateToJetFraction G hG hy g′ := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  apply e.injective
  rw [differentialIndependentJetFraction_deriv]
  apply Subtype.ext
  simp [e, φ, A, differentialIntermediateToJetFraction,
    derivationClosedDifferential_apply]

/-! ## Total derivatives commute with coefficient embeddings -/

/-- Mapping coefficients through a derivation-preserving ring homomorphism commutes with the total
differential-polynomial derivation. -/
theorem map_differentialPolynomialOverDerivation_of_commutes
    {K L ι : Type*} [CommRing K] [CommRing L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    (P : DifferentialPolynomial ι K) :
    MvPolynomial.map f (differentialPolynomialOverDerivation ι K P) =
      differentialPolynomialOverDerivation ι L (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialOverDerivation_C, MvPolynomial.map_C]
      exact congrArg MvPolynomial.C (hf c)
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨i, n⟩
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hP,
        differentialPolynomialOverDerivation_X, MvPolynomial.map_X]

/-- Every iterated total derivative commutes with a derivation-preserving coefficient map. -/
theorem map_differentialPolynomialIterateOver_of_commutes
    {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    (n : ℕ) (P : DifferentialPolynomial Unit K) :
    MvPolynomial.map f (differentialPolynomialIterateOver n P) =
      differentialPolynomialIterateOver n (MvPolynomial.map f P) := by
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [differentialPolynomialIterateOver_succ,
        differentialPolynomialIterateOver_succ,
        map_differentialPolynomialOverDerivation_of_commutes, hn]

/-- The differential principal ideal generated by one polynomial maps into the differential
principal ideal generated by its coefficient image. -/
theorem map_mem_differentialPolynomialIterateIdeal_of_commutes
    {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L]
    (f : K →+* L) (hf : ∀ c : K, f c′ = (f c)′)
    {P Q : DifferentialPolynomial Unit K}
    (hQ : Q ∈ differentialPolynomialIterateIdeal P) :
    MvPolynomial.map f Q ∈
      differentialPolynomialIterateIdeal (MvPolynomial.map f P) := by
  let R := DifferentialPolynomial Unit K
  change Q ∈ Submodule.span R
    (Set.range fun n : ℕ ↦ differentialPolynomialIterateOver n P) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rw [map_differentialPolynomialIterateOver_of_commutes f hf]
    exact differentialPolynomialIterateOver_mem_iterateIdeal _ _
  · simpa using (Ideal.zero_mem
      (differentialPolynomialIterateIdeal (MvPolynomial.map f P)))
  · intro A B _ _ hA hB
    simpa using (Ideal.add_mem _ hA hB)
  · intro a A _ hA
    simpa [smul_eq_mul] using
      (differentialPolynomialIterateIdeal (MvPolynomial.map f P)).mul_mem_left
        (MvPolynomial.map f a) hA

/-- The ideal spanned by all total derivatives of one polynomial is itself stable under total
differentiation. -/
theorem differentialPolynomialOverDerivation_mem_iterateIdeal
    {K : Type*} [Field K] [Differential K]
    {P Q : DifferentialPolynomial Unit K}
    (hQ : Q ∈ differentialPolynomialIterateIdeal P) :
    differentialPolynomialOverDerivation Unit K Q ∈
      differentialPolynomialIterateIdeal P := by
  let R := DifferentialPolynomial Unit K
  change Q ∈ Submodule.span R
    (Set.range fun n : ℕ ↦ differentialPolynomialIterateOver n P) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    simpa only [differentialPolynomialIterateOver_succ] using
      differentialPolynomialIterateOver_mem_iterateIdeal P (n + 1)
  · simpa using (Ideal.zero_mem (differentialPolynomialIterateIdeal P))
  · intro A B _ _ hA hB
    simpa using (differentialPolynomialIterateIdeal P).add_mem hA hB
  · intro a A hA hDA
    rw [show a • A = a * A by simp, Derivation.leibniz]
    simpa [smul_eq_mul] using
      (differentialPolynomialIterateIdeal P).add_mem
        ((differentialPolynomialIterateIdeal P).mul_mem_left a hDA)
        ((differentialPolynomialIterateIdeal P).mul_mem_right
          (differentialPolynomialOverDerivation Unit K a) hA)

/-- Multiplying a differential polynomial by a coefficient-field unit does not change the
differential principal ideal generated by all of its total derivatives. -/
theorem differentialPolynomialIterateIdeal_C_mul_unit
    {K : Type*} [Field K] [Differential K]
    (c : Kˣ) (P : DifferentialPolynomial Unit K) :
    differentialPolynomialIterateIdeal (MvPolynomial.C (c : K) * P) =
      differentialPolynomialIterateIdeal P := by
  apply le_antisymm
  · apply differentialPolynomialIterateIdeal_le_of_derivation_stable
    · have hP : P ∈ differentialPolynomialIterateIdeal P := by
        simpa using differentialPolynomialIterateOver_mem_iterateIdeal P 0
      exact (differentialPolynomialIterateIdeal P).mul_mem_left
        (MvPolynomial.C (c : K)) hP
    · intro Q hQ
      exact differentialPolynomialOverDerivation_mem_iterateIdeal hQ
  · apply differentialPolynomialIterateIdeal_le_of_derivation_stable
    · have hCP : MvPolynomial.C (c : K) * P ∈
          differentialPolynomialIterateIdeal (MvPolynomial.C (c : K) * P) := by
        simpa using differentialPolynomialIterateOver_mem_iterateIdeal
          (MvPolynomial.C (c : K) * P) 0
      have hscaled :=
        (differentialPolynomialIterateIdeal (MvPolynomial.C (c : K) * P)).mul_mem_left
          (MvPolynomial.C ((c⁻¹ : Kˣ) : K)) hCP
      simpa [← MvPolynomial.C_mul, mul_assoc] using hscaled
    · intro Q hQ
      exact differentialPolynomialOverDerivation_mem_iterateIdeal hQ

/-- Differential principal ideals reverse ordinary divisibility of their generators: if `A`
divides `C`, every total derivative consequence of `C` is already a consequence of `A`. -/
theorem differentialPolynomialIterateIdeal_le_of_dvd
    {K : Type*} [Field K] [Differential K]
    {A C : DifferentialPolynomial Unit K} (hdiv : A ∣ C) :
    differentialPolynomialIterateIdeal C ≤ differentialPolynomialIterateIdeal A := by
  apply differentialPolynomialIterateIdeal_le_of_derivation_stable
  · obtain ⟨H, rfl⟩ := hdiv
    have hA : A ∈ differentialPolynomialIterateIdeal A := by
      simpa using differentialPolynomialIterateOver_mem_iterateIdeal A 0
    exact (differentialPolynomialIterateIdeal A).mul_mem_right H hA
  · intro Q hQ
    exact differentialPolynomialOverDerivation_mem_iterateIdeal hQ

/-- Swapping the two scalar jet blocks carries a jet variable to the corresponding variable in
the opposite block. -/
@[simp]
theorem differentialPolynomialTwoBlockSwap_X
    {F : Type*} [CommRing F] (i : Unit ⊕ Unit) (n : ℕ) :
    differentialPolynomialTwoBlockSwap F (MvPolynomial.X (i, n)) =
      MvPolynomial.X (Equiv.sumComm Unit Unit i, n) := by
  simp [differentialPolynomialTwoBlockSwap]

/-- The two-block swap commutes with the total differential-polynomial derivation. -/
theorem differentialPolynomialTwoBlockSwap_derivation
    {F : Type*} [Field F] [Differential F]
    (P : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockSwap F
        (differentialPolynomialOverDerivation (Unit ⊕ Unit) F P) =
      differentialPolynomialOverDerivation (Unit ⊕ Unit) F
        (differentialPolynomialTwoBlockSwap F P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialOverDerivation_C]
      simp [differentialPolynomialTwoBlockSwap]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨i, n⟩
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hP,
        differentialPolynomialOverDerivation_X,
        differentialPolynomialTwoBlockSwap_X]

/-- The `n`-fold total derivative for an arbitrary family of differential indeterminates.  The
existing scalar construction is intentionally specialized to `Unit`; Ritt's component relation
needs the same elementary recursion on two blocks. -/
def differentialPolynomialFamilyIterateOver
    {K ι : Type*} [Field K] [Differential K] :
    ℕ → DifferentialPolynomial ι K → DifferentialPolynomial ι K
  | 0, P => P
  | n + 1, P => differentialPolynomialOverDerivation ι K
      (differentialPolynomialFamilyIterateOver n P)

@[simp]
theorem differentialPolynomialFamilyIterateOver_zero
    {K ι : Type*} [Field K] [Differential K]
    (P : DifferentialPolynomial ι K) :
    differentialPolynomialFamilyIterateOver 0 P = P := rfl

@[simp]
theorem differentialPolynomialFamilyIterateOver_succ
    {K ι : Type*} [Field K] [Differential K]
    (n : ℕ) (P : DifferentialPolynomial ι K) :
    differentialPolynomialFamilyIterateOver (n + 1) P =
      differentialPolynomialOverDerivation ι K
        (differentialPolynomialFamilyIterateOver n P) := rfl

/-- The differential principal ideal for an arbitrary family of indeterminates. -/
def differentialPolynomialFamilyIterateIdeal
    {K ι : Type*} [Field K] [Differential K]
    (P : DifferentialPolynomial ι K) : Ideal (DifferentialPolynomial ι K) :=
  Ideal.span (Set.range fun n : ℕ ↦ differentialPolynomialFamilyIterateOver n P)

theorem differentialPolynomialFamilyIterateOver_mem_iterateIdeal
    {K ι : Type*} [Field K] [Differential K]
    (P : DifferentialPolynomial ι K) (n : ℕ) :
    differentialPolynomialFamilyIterateOver n P ∈
      differentialPolynomialFamilyIterateIdeal P :=
  Ideal.subset_span ⟨n, rfl⟩

/-- The arbitrary-family differential principal ideal is stable under total differentiation. -/
theorem differentialPolynomialFamilyOverDerivation_mem_iterateIdeal
    {K ι : Type*} [Field K] [Differential K]
    {P Q : DifferentialPolynomial ι K}
    (hQ : Q ∈ differentialPolynomialFamilyIterateIdeal P) :
    differentialPolynomialOverDerivation ι K Q ∈
      differentialPolynomialFamilyIterateIdeal P := by
  let R := DifferentialPolynomial ι K
  change Q ∈ Submodule.span R
    (Set.range fun n : ℕ ↦ differentialPolynomialFamilyIterateOver n P) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    simpa only [differentialPolynomialFamilyIterateOver_succ] using
      differentialPolynomialFamilyIterateOver_mem_iterateIdeal P (n + 1)
  · simpa using (Ideal.zero_mem (differentialPolynomialFamilyIterateIdeal P))
  · intro A B _ _ hA hB
    simpa using (differentialPolynomialFamilyIterateIdeal P).add_mem hA hB
  · intro a A hA hDA
    rw [show a • A = a * A by simp, Derivation.leibniz]
    simpa [smul_eq_mul] using
      (differentialPolynomialFamilyIterateIdeal P).add_mem
        ((differentialPolynomialFamilyIterateIdeal P).mul_mem_left a hDA)
        ((differentialPolynomialFamilyIterateIdeal P).mul_mem_right
          (differentialPolynomialOverDerivation ι K a) hA)

/-- The arbitrary-family differential principal ideal reverses ordinary divisibility of its
generator. -/
theorem differentialPolynomialFamilyIterateIdeal_le_of_dvd
    {K ι : Type*} [Field K] [Differential K]
    {A C : DifferentialPolynomial ι K} (hdiv : A ∣ C) :
    differentialPolynomialFamilyIterateIdeal C ≤
      differentialPolynomialFamilyIterateIdeal A := by
  let I := differentialPolynomialFamilyIterateIdeal A
  have hAI : A ∈ I := by
    exact differentialPolynomialFamilyIterateOver_mem_iterateIdeal A 0
  have hCI : C ∈ I := by
    obtain ⟨H, rfl⟩ := hdiv
    exact I.mul_mem_right H hAI
  rw [differentialPolynomialFamilyIterateIdeal, Ideal.span_le]
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact hCI
  | succ n hn =>
      rw [differentialPolynomialFamilyIterateOver_succ]
      exact differentialPolynomialFamilyOverDerivation_mem_iterateIdeal hn

/-- Every iterated total derivative commutes with the two-block swap. -/
theorem differentialPolynomialTwoBlockSwap_iterate
    {F : Type*} [Field F] [Differential F]
    (n : ℕ) (P : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockSwap F (differentialPolynomialFamilyIterateOver n P) =
      differentialPolynomialFamilyIterateOver n (differentialPolynomialTwoBlockSwap F P) := by
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [differentialPolynomialFamilyIterateOver_succ,
        differentialPolynomialFamilyIterateOver_succ,
        differentialPolynomialTwoBlockSwap_derivation, hn]

/-- The two-block swap transports membership in a differential principal ideal. -/
theorem differentialPolynomialTwoBlockSwap_mem_iterateIdeal
    {F : Type*} [Field F] [Differential F]
    {P Q : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hQ : Q ∈ differentialPolynomialFamilyIterateIdeal P) :
    differentialPolynomialTwoBlockSwap F Q ∈
      differentialPolynomialFamilyIterateIdeal (differentialPolynomialTwoBlockSwap F P) := by
  let R := DifferentialPolynomial (Unit ⊕ Unit) F
  change Q ∈ Submodule.span R
    (Set.range fun n : ℕ ↦ differentialPolynomialFamilyIterateOver n P) at hQ
  refine Submodule.span_induction (hx := hQ) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rw [differentialPolynomialTwoBlockSwap_iterate]
    exact differentialPolynomialFamilyIterateOver_mem_iterateIdeal _ _
  · simpa using (Ideal.zero_mem
      (differentialPolynomialFamilyIterateIdeal
        (differentialPolynomialTwoBlockSwap F P)))
  · intro A B _ _ hA hB
    simpa using (Ideal.add_mem _ hA hB)
  · intro a A _ hA
    simpa [smul_eq_mul] using
      (differentialPolynomialFamilyIterateIdeal
        (differentialPolynomialTwoBlockSwap F P)).mul_mem_left
          (differentialPolynomialTwoBlockSwap F a) hA

/-! ## Bounded multiplier cancellation on the general component -/

/-- A bounded-order multiplier which is nonzero on the ordinary hypersurface can be cancelled
from a finite differential-ideal membership certificate.  This is the form of general-component
contraction needed in Ritt's factor peeling: after all factors of larger order have been removed,
both the residual quotient and the multiplier seen by the current factor have order at most that
of the factor.

The proof uses the finite generic point already constructed in
`DifferentialLurothCoefficient`.  Passing first to the fraction field of the ordinary prime
quotient `(A)` makes the multiplier nonzero; the recursive higher-jet construction leaves every
bounded-order polynomial unchanged, so it may be cancelled in that field. -/
theorem irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal
    {K : Type*} [Field K] [Differential K] [CharZero K]
    {A M Q : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (hAirreducible : Irreducible A)
    (hMorder : scalarDifferentialPolynomialOrder M ≤
      scalarDifferentialPolynomialOrder A)
    (hMnot : ¬A ∣ M)
    (hQorder : scalarDifferentialPolynomialOrder Q ≤
      scalarDifferentialPolynomialOrder A)
    (hmem : M * Q ∈ differentialPolynomialIterateIdeal A) :
    A ∣ Q := by
  classical
  obtain ⟨N, hmemN⟩ :=
    mem_differentialPolynomialIterateIdeal_exists_upTo A _ hmem
  let R := DifferentialPolynomial Unit K
  let I : Ideal R := Ideal.span ({A} : Set R)
  have hIprime : I.IsPrime := by
    dsimp [I]
    exact (Ideal.span_singleton_prime hAirreducible.ne_zero).mpr hAirreducible.prime
  let B := R ⧸ I
  letI : IsDomain B := (Ideal.Quotient.isDomain_iff_prime I).mpr hIprime
  let L := FractionRing B
  let q : R →+* B := Ideal.Quotient.mk I
  let ι : B →+* L := algebraMap B L
  let Φ : R →+* L := ι.comp q
  let f : K →+* L := Φ.comp MvPolynomial.C
  let x₀ : Unit × ℕ → L := fun j ↦ Φ (MvPolynomial.X j)
  have hcanonical : MvPolynomial.eval₂Hom f x₀ = Φ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [f]
    · intro j
      simp [x₀]
  have hcanonical_apply (T : R) : MvPolynomial.eval₂ f x₀ T = Φ T :=
    RingHom.congr_fun hcanonical T
  have hqA : q A = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton_self A
  have hbaseA : MvPolynomial.eval₂ f x₀ A = 0 := by
    rw [hcanonical_apply]
    change ι (q A) = 0
    rw [hqA, map_zero]
  have hqSeparant : q (scalarDifferentialPolynomialSeparant A) ≠ 0 := by
    intro hzero
    have hmemI : scalarDifferentialPolynomialSeparant A ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hdiv : A ∣ scalarDifferentialPolynomialSeparant A := by
      rw [← Ideal.mem_span_singleton]
      simpa [I] using hmemI
    exact (irreducible_not_dvd_scalarDifferentialPolynomialSeparant
      hAvars hAirreducible) hdiv
  have hbaseSeparant : MvPolynomial.eval₂ f x₀
      (scalarDifferentialPolynomialSeparant A) ≠ 0 := by
    rw [hcanonical_apply]
    change ι (q (scalarDifferentialPolynomialSeparant A)) ≠ 0
    intro hzero
    apply hqSeparant
    apply IsFractionRing.injective B L
    simpa using hzero
  have hqM : q M ≠ 0 := by
    intro hzero
    apply hMnot
    rw [← Ideal.mem_span_singleton]
    simpa [I] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hbaseM : MvPolynomial.eval₂ f x₀ M ≠ 0 := by
    rw [hcanonical_apply]
    change ι (q M) ≠ 0
    intro hzero
    apply hqM
    apply IsFractionRing.injective B L
    simpa using hzero
  have hproductEval :=
    differentialPolynomialGeneralComponentJets_eval_mem_iterateIdealUpTo
      f hAvars x₀ hbaseA hbaseSeparant hmemN
  change (MvPolynomial.eval₂Hom f
      (differentialPolynomialGeneralComponentJets f A x₀ N)) (M * Q) = 0 at
    hproductEval
  rw [map_mul] at hproductEval
  have hMStable := differentialPolynomialGeneralComponentJets_eval_of_order_le
    f A x₀ N hMorder
  have hMne : MvPolynomial.eval₂ f
      (differentialPolynomialGeneralComponentJets f A x₀ N) M ≠ 0 := by
    rw [hMStable]
    exact hbaseM
  have hQEval : MvPolynomial.eval₂ f
      (differentialPolynomialGeneralComponentJets f A x₀ N) Q = 0 :=
    (mul_eq_zero.mp hproductEval).resolve_left hMne
  have hQStable := differentialPolynomialGeneralComponentJets_eval_of_order_le
    f A x₀ N hQorder
  have hQbase : MvPolynomial.eval₂ f x₀ Q = 0 := by
    rw [← hQStable]
    exact hQEval
  have hΦQ : Φ Q = 0 := by
    rw [← hcanonical_apply]
    exact hQbase
  have hqQ : q Q = 0 := by
    apply IsFractionRing.injective B L
    change ι (q Q) = ι 0
    simpa [Φ] using hΦQ
  rw [← Ideal.mem_span_singleton]
  simpa [I] using (Ideal.Quotient.eq_zero_iff_mem.mp hqQ)

/-! ## Cleared Bezout cancellation away from one jet -/

/-- Two relatively prime multivariable polynomials admit a cleared Bezout identity whose nonzero
right-hand side omits any prescribed variable.  All other variables are placed in the coefficient
UFD, the two polynomials are viewed as univariate in `x`, and
`exists_distinguishedVariable_bezout_clear` clears the Bezout denominators.

In the Ritt descent, `x` is the top jet shared by every factor through equation (78).  The resulting
multiplier has strictly lower order in that block; after swapping blocks it is therefore eligible
for `irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal`. -/
theorem exists_mvPolynomial_bezout_clear_away_from_variable
    {F σ : Type*} [Field F] (x : σ)
    {A B : MvPolynomial σ F} (hAB : IsRelPrime A B) :
    ∃ U V N : MvPolynomial σ F,
      N ≠ 0 ∧ x ∉ N.vars ∧ U * A + V * B = N := by
  classical
  let R := MvPolynomial {j : σ // j ≠ x} F
  let K := FractionRing R
  let e : MvPolynomial σ F ≃ₐ[F] Polynomial R :=
    mvPolynomialPolynomialEquivAt x
  let H : Fin 2 → Polynomial R :=
    fun i ↦ Fin.cases (e A) (fun _ ↦ e B) i
  have hcommon (q : Polynomial R) (hq : ∀ i, q ∣ H i) : IsUnit q := by
    have hqA : e.symm q ∣ A := by
      simpa [H] using map_dvd e.symm (hq 0)
    have hqB : e.symm q ∣ B := by
      simpa [H] using map_dvd e.symm (hq 1)
    exact IsUnit.map e (hAB hqA hqB)
  obtain ⟨M, n, hn, hbezout⟩ :=
    exists_distinguishedVariable_bezout_clear (R := R) (K := K) H hcommon
  rw [Fin.sum_univ_two] at hbezout
  simp only [H, Fin.cases_zero, Fin.cases_succ] at hbezout
  let U : MvPolynomial σ F := e.symm (M 0)
  let V : MvPolynomial σ F := e.symm (M 1)
  let N : MvPolynomial σ F := e.symm (Polynomial.C n)
  have heN : e N = Polynomial.C n := e.apply_symm_apply _
  have hN0 : N ≠ 0 := by
    intro hzero
    have : Polynomial.C n = 0 := by
      simpa [heN] using congrArg e hzero
    exact (Polynomial.C_ne_zero.mpr hn) this
  have hNx : x ∉ N.vars := by
    have hdegree : MvPolynomial.degreeOf x N = 0 := by
      calc
        MvPolynomial.degreeOf x N = (mvPolynomialAsPolynomialAt x N).natDegree :=
          mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt x N
        _ = (e N).natDegree := by
          exact congrArg Polynomial.natDegree
            (mvPolynomialPolynomialEquivAt_apply x N).symm
        _ = (Polynomial.C n).natDegree := by rw [heN]
        _ = 0 := by simp
    simpa [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, hdegree]
  refine ⟨U, V, N, hN0, hNx, ?_⟩
  apply e.injective
  simp only [map_add, map_mul]
  change M 0 * e A + M 1 * e B = Polynomial.C n
  exact hbezout

/-! ## The coefficient cross-relation and characteristic saturation -/

/-- The relation over the intermediate coefficient field obtained from two cleared coefficients.
Its image in the free-jet fraction field is the two-copy projective cross-difference, apart from
the one common clearing unit. -/
def differentialCharacteristicCoefficientCrossRelation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (G : IntermediateField F E) (p q : G)
    (P Q : DifferentialPolynomial Unit F) :
    DifferentialPolynomial Unit G :=
  MvPolynomial.C q * MvPolynomial.map (algebraMap F G) P -
    MvPolynomial.C p * MvPolynomial.map (algebraMap F G) Q

/-- The cross-relation of two characteristic coefficients vanishes at the original free element. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.coefficientCrossRelation_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
        (differentialPolynomialTwoBlockCoefficient m C.polynomial)
        (differentialPolynomialTwoBlockCoefficient n C.polynomial) ∈
      differentialIntermediateRelationIdeal G y := by
  change differentialPolynomialEvalOver (K := G) (fun _ : Unit ↦ y)
      (differentialCharacteristicCoefficientCrossRelation G (P.coeff m) (P.coeff n)
        (differentialPolynomialTwoBlockCoefficient m C.polynomial)
        (differentialPolynomialTwoBlockCoefficient n C.polynomial)) = 0
  simp only [differentialCharacteristicCoefficientCrossRelation, map_sub, map_mul,
    differentialPolynomialEvalOver_C,
    differentialPolynomialEvalOver_map_intermediate]
  rw [C.coefficient_specialization G hG hy P m,
    C.coefficient_specialization G hG hy P n]
  ring

/-- After mapping to the formal fraction field, the coefficient cross-relation is exactly the
two-block cross-difference multiplied by the denominator-clearing unit. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.map_coefficientCrossRelation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
    MvPolynomial.map (algebraMap R K)
        (differentialPolynomialTwoBlockEquiv F
          (differentialPolynomialCrossDifference
            (differentialPolynomialTwoBlockCoefficient m C.polynomial)
            (differentialPolynomialTwoBlockCoefficient n C.polynomial))) =
      MvPolynomial.C (C.scalar : K) *
        MvPolynomial.map φ.toRingHom
          (differentialCharacteristicCoefficientCrossRelation G
            (P.coeff m) (P.coeff n)
            (differentialPolynomialTwoBlockCoefficient m C.polynomial)
            (differentialPolynomialTwoBlockCoefficient n C.polynomial)) := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  let P₀ := differentialPolynomialTwoBlockCoefficient m C.polynomial
  let Q₀ := differentialPolynomialTwoBlockCoefficient n C.polynomial
  have hm := congrArg (MvPolynomial.coeff m) C.clearing
  have hn := congrArg (MvPolynomial.coeff n) C.clearing
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hm hn
  have hbaseR :
      (algebraMap R K).comp (MvPolynomial.C : F →+* R) = algebraMap F K := by
    ext c
    simp [R, K]
  have hbaseG : φ.toRingHom.comp (algebraMap F G) = algebraMap F K := by
    ext c
    exact φ.commutes c
  rw [differentialPolynomialTwoBlockEquiv_crossDifference]
  simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
  rw [hbaseR]
  change MvPolynomial.C (algebraMap R K Q₀) * MvPolynomial.map (algebraMap F K) P₀ -
      MvPolynomial.C (algebraMap R K P₀) * MvPolynomial.map (algebraMap F K) Q₀ = _
  rw [hm, hn]
  simp only [differentialCharacteristicCoefficientCrossRelation, map_sub, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_map]
  rw [hbaseG]
  ring

/-- The characteristic saturation transports to the formal free-jet fraction field.  The
coefficient map here carries the restricted differential structure, so this is a map of total
differential ideals rather than only of their underlying ordinary ideals. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.exists_mappedCrossRelation_saturation
    {F E : Type*} [Field F] [Field E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    [CharZero E]
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m n : (Unit × ℕ) →₀ ℕ) :
    let K := FractionRing (DifferentialPolynomial Unit F)
    let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
    letI : Differential G := derivationClosedDifferential G hGclosed
    letI : Differential K := differentialIndependentJetFractionDifferential y hy
    ∃ a b : ℕ,
      MvPolynomial.map φ.toRingHom (scalarDifferentialPolynomialInitial P) ^ a *
          MvPolynomial.map φ.toRingHom (scalarDifferentialPolynomialSeparant P) ^ b *
          MvPolynomial.map φ.toRingHom
            (differentialCharacteristicCoefficientCrossRelation G
              (P.coeff m) (P.coeff n)
              (differentialPolynomialTwoBlockCoefficient m C.polynomial)
              (differentialPolynomialTwoBlockCoefficient n C.polynomial)) ∈
        differentialPolynomialIterateIdeal (MvPolynomial.map φ.toRingHom P) := by
  let K := FractionRing (DifferentialPolynomial Unit F)
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  letI : Differential G := derivationClosedDifferential G hGclosed
  letI : Differential K := differentialIndependentJetFractionDifferential y hy
  let Q := differentialCharacteristicCoefficientCrossRelation G
    (P.coeff m) (P.coeff n)
    (differentialPolynomialTwoBlockCoefficient m C.polynomial)
    (differentialPolynomialTwoBlockCoefficient n C.polynomial)
  have hQ : Q ∈ differentialIntermediateRelationIdeal G y :=
    C.coefficientCrossRelation_mem G hG hy P m n
  obtain ⟨a, b, hab⟩ :=
    exists_initial_separant_powers_mem_differentialIntermediatePolynomialIterateIdeal
      G hGclosed y hP hQ
  refine ⟨a, b, ?_⟩
  have hφ : ∀ g : G, φ g′ = (φ g)′ := by
    intro g
    exact (differentialIntermediateToJetFraction_deriv G hGclosed hG hy g).symm
  have hmapped :=
    map_mem_differentialPolynomialIterateIdeal_of_commutes φ.toRingHom hφ hab
  simpa [Q] using hmapped

/-! ## Equation (78), squarefree recombination, and the cleared characteristic -/

/-- A squarefree element of a unique-factorization monoid divides any element divisible by each
of its irreducible factors.  This is the recombination step used after componentwise contraction. -/
theorem Squarefree.dvd_of_forall_irreducible_factor_dvd
    {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    {P Q : R} (hP : Squarefree P)
    (hfactor : ∀ A : R, Irreducible A → A ∣ P → A ∣ Q) :
    P ∣ Q := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (not_squarefree_zero hP).elim
  | unit u hu => exact hu.dvd
  | mul A p hA0 hp ih =>
      have hsplit := squarefree_mul_iff.mp hP
      have hAQ : A ∣ Q := by
        apply ih hsplit.2.2
        intro q hq hqA
        apply hfactor q hq
        simpa [mul_comm] using dvd_mul_of_dvd_right hqA p
      have hpQ : p ∣ Q := hfactor p hp (dvd_mul_right p A)
      exact hsplit.1.mul_dvd hpQ hAQ

/-- The cleared two-block characteristic is squarefree over the formal left-jet fraction field.
This is the direct downstream use of equation (78): scalar extension may split the irreducible
characteristic polynomial, but the support theorem prevents any factor from repeating. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.mappedPolynomial_squarefree
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E] [CharZero E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) (hPirreducible : Irreducible P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    Squarefree
      (MvPolynomial.map (algebraMap R K)
        (differentialPolynomialTwoBlockEquiv F C.polynomial)) := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  letI : Algebra G K := φ.toRingHom.toAlgebra
  have hmap : Squarefree (MvPolynomial.map φ.toRingHom P) := by
    simpa [φ] using
      (irreducible_map_squarefree_of_charZero (K := K) hPirreducible)
  rw [C.clearing]
  have hunit : IsUnit
      (MvPolynomial.C (C.scalar : K) : MvPolynomial (Unit × ℕ) K) :=
    IsUnit.map MvPolynomial.C C.scalar.isUnit
  exact (associated_unit_mul_left _ _ hunit).squarefree_iff.mpr hmap

/-- **Equation (78) for factors of the cleared two-block characteristic.**  Every irreducible
factor over the original two-block polynomial ring still contains every right-block jet variable
of the irreducible characteristic relation.

The point requiring primitivity is that a full-ring factor might otherwise become a coefficient
constant after the left jets are inverted.  Primitivity excludes this.  We may therefore choose an
irreducible factor after localization, where `irreducible_map_factor_vars_subset` applies directly
to the original characteristic polynomial. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.irreducible_factor_right_vars
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) (hPirreducible : Irreducible P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {A : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAirreducible : Irreducible A) (hAdiv : A ∣ C.polynomial) :
    P.vars ⊆ (differentialPolynomialTwoBlockEquiv F A).vars := by
  classical
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  let A₀ := differentialPolynomialTwoBlockEquiv F A
  let C₀ := differentialPolynomialTwoBlockEquiv F C.polynomial
  have hA₀irreducible : Irreducible A₀ :=
    hAirreducible.map (differentialPolynomialTwoBlockEquiv F)
  have hA₀div : A₀ ∣ C₀ :=
    map_dvd (differentialPolynomialTwoBlockEquiv F) hAdiv
  have hA₀vars : A₀.vars.Nonempty := by
    by_contra hnone
    have hempty : A₀.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hconstant : A₀ = MvPolynomial.C (A₀.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hempty
    have hconstantDiv : MvPolynomial.C (A₀.coeff 0) ∣ C₀ := by
      simpa [hconstant] using hA₀div
    have hcoefficientUnit : IsUnit (A₀.coeff 0) :=
      C.primitive (A₀.coeff 0) hconstantDiv
    have hA₀unit : IsUnit A₀ := by
      rw [hconstant]
      exact IsUnit.map MvPolynomial.C hcoefficientUnit
    exact hA₀irreducible.not_isUnit hA₀unit
  let A₁ : MvPolynomial (Unit × ℕ) K :=
    MvPolynomial.map (algebraMap R K) A₀
  have hA₁vars : A₁.vars = A₀.vars := by
    exact MvPolynomial.vars_map_of_injective (IsFractionRing.injective R K)
  have hA₁ne : A₁ ≠ 0 := by
    exact MvPolynomial.map_injective (algebraMap R K)
      (IsFractionRing.injective R K) hA₀irreducible.ne_zero
  have hA₁notUnit : ¬IsUnit A₁ := by
    intro hunit
    obtain ⟨r, _hr, hA₁constant⟩ :=
      MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
    have hvarsEmpty : A₁.vars = ∅ := by
      rw [hA₁constant]
      simp
    exact hA₀vars.ne_empty (hA₁vars ▸ hvarsEmpty)
  obtain ⟨B, hBirreducible, hBdivA₁⟩ :=
    WfDvdMonoid.exists_irreducible_factor hA₁notUnit hA₁ne
  have hBdivC : B ∣ MvPolynomial.map (algebraMap R K) C₀ := by
    exact hBdivA₁.trans (map_dvd (MvPolynomial.mapRingHom (algebraMap R K)) hA₀div)
  have hBdivMapP : B ∣ MvPolynomial.map φ.toRingHom P := by
    rw [C.clearing] at hBdivC
    rcases hBirreducible.prime.dvd_mul.mp hBdivC with hBscalar | hBP
    · have hscalarUnit : IsUnit
          (MvPolynomial.C (C.scalar : K) : MvPolynomial (Unit × ℕ) K) :=
        IsUnit.map MvPolynomial.C C.scalar.isUnit
      exact (hBirreducible.not_isUnit
        (isUnit_of_dvd_unit hBscalar hscalarUnit)).elim
    · exact hBP
  letI : Algebra G K := φ.toRingHom.toAlgebra
  have hBdivAlgebraMap : B ∣ MvPolynomial.map (algebraMap G K) P := by
    simpa [φ] using hBdivMapP
  have hright : P.vars ⊆ B.vars :=
    irreducible_map_factor_vars_subset hPirreducible hBirreducible hBdivAlgebraMap
  have hBvars : B.vars ⊆ A₁.vars :=
    mvPolynomial_vars_subset_of_dvd hBdivA₁ hA₁ne
  intro j hj
  have hjA₁ : j ∈ A₁.vars := hBvars (hright hj)
  rwa [hA₁vars] at hjA₁

/-- Exact right-variable support form of equation (78) for a full-ring irreducible factor of the
cleared characteristic. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.irreducible_factor_right_vars_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) (hPirreducible : Irreducible P)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {A : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAirreducible : Irreducible A) (hAdiv : A ∣ C.polynomial) :
    (differentialPolynomialTwoBlockEquiv F A).vars = P.vars := by
  classical
  apply Finset.Subset.antisymm
  · let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
    let A₀ := differentialPolynomialTwoBlockEquiv F A
    let C₀ := differentialPolynomialTwoBlockEquiv F C.polynomial
    have hA₀div : A₀ ∣ C₀ :=
      map_dvd (differentialPolynomialTwoBlockEquiv F) hAdiv
    have hC₀ne : C₀ ≠ 0 :=
      (differentialPolynomialTwoBlockEquiv F).injective.ne C.ne_zero
    have hfactorVars : A₀.vars ⊆ C₀.vars :=
      mvPolynomial_vars_subset_of_dvd hA₀div hC₀ne
    have hcharacteristicVars : C₀.vars = P.vars := by
      have hvars := congrArg MvPolynomial.vars C.clearing
      rw [MvPolynomial.vars_map_of_injective (IsFractionRing.injective R K),
        MvPolynomial.vars_C_mul (C.scalar : K) C.scalar.ne_zero,
        MvPolynomial.vars_map_of_injective φ.injective] at hvars
      exact hvars
    rw [hcharacteristicVars] at hfactorVars
    simpa [A₀] using hfactorVars
  · exact C.irreducible_factor_right_vars G hG hy P hPirreducible
      hAirreducible hAdiv

/-! ## Primitive products needed by the terminal reciprocity step -/

/-- Extending a nonzero polynomial over a field as coefficient constants gives a primitive
multivariable polynomial over the new polynomial coefficient ring. -/
theorem MvPolynomialPrimitive.map_C_of_ne_zero
    {F σ τ : Type*} [Field F]
    {P : MvPolynomial σ F} (hP0 : P ≠ 0) :
    MvPolynomialPrimitive
      (MvPolynomial.map
        (MvPolynomial.C : F →+* MvPolynomial τ F) P) := by
  intro r hr
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hr
  obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hP0
  have hrd : r ∣ MvPolynomial.C (P.coeff m) := by
    simpa using hr m
  exact isUnit_of_dvd_unit hrd
    (IsUnit.map (MvPolynomial.C : F →+* MvPolynomial τ F) hm.isUnit)

/-- The product of two nonzero primitive multivariable polynomials over a UFD is primitive. -/
theorem MvPolynomialPrimitive.mul
    {R σ : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    {P Q : MvPolynomial σ R}
    (hP : MvPolynomialPrimitive P)
    (hQ : MvPolynomialPrimitive Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    MvPolynomialPrimitive (P * Q) := by
  intro r hr
  by_contra hru
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    rcases hr with ⟨T, hT⟩
    exact (mul_ne_zero hP0 hQ0) (by simpa using hT)
  obtain ⟨p, hp, hpr⟩ :=
    WfDvdMonoid.exists_irreducible_factor hru hr0
  have hpCprime : Prime (MvPolynomial.C p : MvPolynomial σ R) :=
    (MvPolynomial.prime_C_iff σ).2 hp.prime
  have hpdiv : MvPolynomial.C p ∣ P * Q :=
    (map_dvd (MvPolynomial.C : R →+* MvPolynomial σ R) hpr).trans hr
  rcases hpCprime.dvd_mul.mp hpdiv with hpP | hpQ
  · exact hp.not_isUnit (hP p hpP)
  · exact hp.not_isUnit (hQ p hpQ)

/-- A two-copy cross-difference vanishes exactly when its two entries are proportional over the
base field. -/
theorem differentialPolynomialCrossDifference_eq_zero_iff
    {F : Type*} [Field F]
    {P Q : DifferentialPolynomial Unit F} (hQ0 : Q ≠ 0) :
    differentialPolynomialCrossDifference P Q = 0 ↔
      ∃ c : F, P = MvPolynomial.C c * Q := by
  constructor
  · intro hzero
    obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hQ0
    have hcoeff := congrArg
      (differentialPolynomialTwoBlockCoefficient m) hzero
    rw [differentialPolynomialTwoBlockCoefficient_crossDifference] at hcoeff
    simp only [map_zero, differentialPolynomialTwoBlockCoefficient] at hcoeff
    have heq : MvPolynomial.C (Q.coeff m) * P =
        MvPolynomial.C (P.coeff m) * Q := by
      calc
        MvPolynomial.C (Q.coeff m) * P = P * MvPolynomial.C (Q.coeff m) :=
          mul_comm _ _
        _ = Q * MvPolynomial.C (P.coeff m) := (sub_eq_zero.mp hcoeff).symm
        _ = MvPolynomial.C (P.coeff m) * Q := mul_comm _ _
    refine ⟨P.coeff m / Q.coeff m, ?_⟩
    apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hm)
    calc
      MvPolynomial.C (Q.coeff m) * P =
          MvPolynomial.C (P.coeff m) * Q := heq
      _ = MvPolynomial.C (Q.coeff m) *
          (MvPolynomial.C (P.coeff m / Q.coeff m) * Q) := by
        rw [← mul_assoc, ← MvPolynomial.C_mul,
          mul_div_cancel₀ (P.coeff m) hm]
  · rintro ⟨c, rfl⟩
    simp [differentialPolynomialCrossDifference]
    ring

end

end GaloisForLFunctions
