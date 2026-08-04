import GaloisForLFunctions.HTGeometry.TwoBlockEquivDerivation

/-!
# The jet fraction field extends the jet derivation

The rational formal-jet field carries the derivation transported from the free element.  On the
polynomial subring that derivation is the jet derivation, so the inclusion of the scalar
differential-polynomial ring into its fraction field is a map of differential rings.

This is the last compatibility needed to move a differential-ideal certificate between the
polynomial and the fraction-field pictures.
-/

namespace GaloisForLFunctions

open MvPolynomial

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- **The inclusion into the jet fraction field is differential.** -/
theorem algebraMap_jetFraction_deriv {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (p : DifferentialPolynomial Unit F) :
    letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)) p′ =
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)) p)′ := by
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  set e := differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy with he
  refine e.injective (Subtype.ext ?_)
  have hleft : ((e (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)) p′) :
        differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) =
      differentialPolynomialEval (C := F) (fun _ : Unit ↦ y) p′ :=
    differentialIndependentAdjoinParametrization_algebraMap_val hy p′
  have hright : ((e ((algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)) p)′) :
        differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) =
      (differentialPolynomialEval (C := F) (fun _ : Unit ↦ y) p)′ := by
    rw [differentialIndependentJetFraction_deriv y hy]
    rw [derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F (Set.range fun _ : Unit ↦ y))]
    exact congrArg Differential.deriv
      (differentialIndependentAdjoinParametrization_algebraMap_val hy p)
  rw [hleft, hright]
  have hderiv : differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y)
      (differentialPolynomialOverDerivation Unit F p) =
      (differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) p)′ :=
    differentialPolynomialEvalOver_derivation (fun _ : Unit ↦ y) p
  exact hderiv


/-- Iterated total derivatives commute with a derivation-preserving coefficient map. -/
theorem map_diffPolyIterate_of_commutes {R L ι : Type*} [CommRing R] [CommRing L]
    [Differential R] [Differential L] (f : R →+* L) (hf : ∀ c : R, f c′ = (f c)′) (n : ℕ)
    (P : DifferentialPolynomial ι R) :
    MvPolynomial.map f (diffPolyIterate n P) = diffPolyIterate n (MvPolynomial.map f P) := by
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [diffPolyIterate_succ, diffPolyIterate_succ,
        map_differentialPolynomialOverDerivation_of_commutes f hf, hn]

/-- Over a field the scalar iterate agrees with the corpus's. -/
theorem diffPolyIterate_eq_iterateOver {K : Type*} [Field K] [Differential K] (n : ℕ)
    (P : DifferentialPolynomial Unit K) :
    diffPolyIterate n P = differentialPolynomialIterateOver n P := by
  induction n with
  | zero => rfl
  | succ n hn => rw [diffPolyIterate_succ, differentialPolynomialIterateOver_succ, hn]

/-- **Descent of a differential-ideal certificate.**  A membership holding after passing to the jet
fraction field holds over the polynomial ring after clearing one denominator. -/
theorem exists_clear_mem_familyIterateIdeal_of_map_mem {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {C Q : DifferentialPolynomial (Unit ⊕ Unit) F}
    (h :
      letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
        differentialIndependentJetFractionDifferential y hy
      MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F Q) ∈
        differentialPolynomialIterateIdeal
          (MvPolynomial.map
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))
            (differentialPolynomialTwoBlockEquiv F C))) :
    ∃ d : DifferentialPolynomial Unit F, d ≠ 0 ∧
      differentialPolynomialLeft (κ := Unit) d * Q ∈
        differentialPolynomialFamilyIterateIdeal C := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  set R := DifferentialPolynomial Unit F with hR
  set K := FractionRing R with hK
  set φ : R →+* K := algebraMap R K with hφ
  have hcomm : ∀ c : R, φ c′ = (φ c)′ := fun c => algebraMap_jetFraction_deriv hy c
  have hφinj : Function.Injective φ := IsFractionRing.injective R K
  have hmapinj : Function.Injective (MvPolynomial.map (σ := Unit × ℕ) φ) :=
    MvPolynomial.map_injective _ hφinj
  -- the fraction-field ideal is the extension of the polynomial-level one
  set J : Ideal (MvPolynomial (Unit × ℕ) R) :=
    Ideal.span (Set.range fun n : ℕ =>
      diffPolyIterate n (differentialPolynomialTwoBlockEquiv F C)) with hJ
  have hgen : differentialPolynomialIterateIdeal
      (MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F C)) =
      J.map (MvPolynomial.map (σ := Unit × ℕ) φ) := by
    rw [differentialPolynomialIterateIdeal, hJ, Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨diffPolyIterate n (differentialPolynomialTwoBlockEquiv F C), ⟨n, rfl⟩, ?_⟩
      rw [map_diffPolyIterate_of_commutes φ hcomm, diffPolyIterate_eq_iterateOver]
    · rintro ⟨w, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      rw [map_diffPolyIterate_of_commutes φ hcomm, diffPolyIterate_eq_iterateOver]
  rw [hgen] at h
  letI : Algebra (MvPolynomial (Unit × ℕ) R) (MvPolynomial (Unit × ℕ) K) :=
    MvPolynomial.algebraMvPolynomial
  haveI : IsLocalization
      (Submonoid.map (MvPolynomial.C (σ := Unit × ℕ)) (nonZeroDivisors R))
      (MvPolynomial (Unit × ℕ) K) := MvPolynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨⟨⟨x, hxJ⟩, ⟨m, hm⟩⟩, heq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.map (MvPolynomial.C (σ := Unit × ℕ)) (nonZeroDivisors R))
      (MvPolynomial (Unit × ℕ) K)).1 h
  obtain ⟨d, hd, hdm⟩ := hm
  -- clear the denominator and descend
  have hdne : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have halg : ∀ z : MvPolynomial (Unit × ℕ) R,
      (algebraMap (MvPolynomial (Unit × ℕ) R) (MvPolynomial (Unit × ℕ) K)) z =
        MvPolynomial.map φ z := fun _ => rfl
  subst hdm
  simp only [halg, MvPolynomial.map_C] at heq
  have hdescend : differentialPolynomialTwoBlockEquiv F Q * MvPolynomial.C d = x := by
    refine hmapinj ?_
    rw [map_mul, MvPolynomial.map_C]
    exact heq
  refine ⟨d, hdne, ?_⟩
  have hequiv : differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialLeft (κ := Unit) d * Q) =
      MvPolynomial.C d * differentialPolynomialTwoBlockEquiv F Q := by
    rw [map_mul, differentialPolynomialTwoBlockEquiv_left]
  have hxmem : differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialLeft (κ := Unit) d * Q) ∈ J := by
    rw [hequiv, mul_comm, hdescend]
    exact hxJ
  -- pull the membership back through the splitting
  have hkey : ∀ w ∈ J, (differentialPolynomialTwoBlockEquiv F).symm w ∈
      differentialPolynomialFamilyIterateIdeal C := by
    intro w hw
    rw [hJ] at hw
    refine Submodule.span_induction (hx := hw) ?_ ?_ ?_ ?_
    · rintro _ ⟨n, rfl⟩
      show (differentialPolynomialTwoBlockEquiv F).symm
          (diffPolyIterate n ((differentialPolynomialTwoBlockEquiv F) C)) ∈
        differentialPolynomialFamilyIterateIdeal C
      rw [← differentialPolynomialTwoBlockEquiv_diffPolyIterate, AlgEquiv.symm_apply_apply,
        diffPolyIterate_eq_familyIterateOver]
      exact differentialPolynomialFamilyIterateOver_mem_iterateIdeal C n
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ ha
  have := hkey _ hxmem
  rwa [AlgEquiv.symm_apply_apply] at this

/-- **Ascent of a differential-ideal certificate.**  Membership in the two-block differential ideal
persists after splitting and passing to the jet fraction field. -/
theorem map_equiv_mem_iterateIdeal_of_mem_familyIterateIdeal {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {A Q : DifferentialPolynomial (Unit ⊕ Unit) F}
    (h : Q ∈ differentialPolynomialFamilyIterateIdeal A) :
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F Q) ∈
      differentialPolynomialIterateIdeal
        (MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F A)) := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  set R := DifferentialPolynomial Unit F with hR
  set K := FractionRing R with hK
  set φ : R →+* K := algebraMap R K with hφ
  have hcomm : ∀ c : R, φ c′ = (φ c)′ := fun c => algebraMap_jetFraction_deriv hy c
  change Q ∈ Submodule.span (DifferentialPolynomial (Unit ⊕ Unit) F)
    (Set.range fun n : ℕ ↦ differentialPolynomialFamilyIterateOver n A) at h
  refine Submodule.span_induction (hx := h) ?_ ?_ ?_ ?_
  · rintro _ ⟨n, rfl⟩
    show MvPolynomial.map φ (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialFamilyIterateOver n A)) ∈ _
    rw [← diffPolyIterate_eq_familyIterateOver,
      differentialPolynomialTwoBlockEquiv_diffPolyIterate,
      map_diffPolyIterate_of_commutes φ hcomm, diffPolyIterate_eq_iterateOver]
    exact differentialPolynomialIterateOver_mem_iterateIdeal _ n
  · simp
  · intro u v _ _ hu hv
    rw [map_add, map_add]
    exact Ideal.add_mem _ hu hv
  · intro r u _ hu
    rw [smul_eq_mul, map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ hu

/-- The same certificate in the swapped view, where the left block becomes the polynomial
variables. -/
theorem map_equiv_swap_mem_iterateIdeal_of_mem_familyIterateIdeal {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {A Q : DifferentialPolynomial (Unit ⊕ Unit) F}
    (h : Q ∈ differentialPolynomialFamilyIterateIdeal A) :
    letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
      differentialIndependentJetFractionDifferential y hy
    MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F Q)) ∈
      differentialPolynomialIterateIdeal
        (MvPolynomial.map
          (algebraMap (DifferentialPolynomial Unit F)
            (FractionRing (DifferentialPolynomial Unit F)))
          (differentialPolynomialTwoBlockEquiv F
            (differentialPolynomialTwoBlockSwap F A))) :=
  map_equiv_mem_iterateIdeal_of_mem_familyIterateIdeal hy
    (differentialPolynomialTwoBlockSwap_mem_iterateIdeal h)

end

end GaloisForLFunctions
