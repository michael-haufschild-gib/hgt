import GaloisForLFunctions.HTGeometry.TwoBlockCrossSaturation
import GaloisForLFunctions.HTGeometry.TwoBlockSwapSymmetry
import GaloisForLFunctions.HTGeometry.TwoBlockInitialSeparant
import GaloisForLFunctions.HTGeometry.MvPolynomialGaussAscent

/-!
# The two block orders of a cleared characteristic

A cleared two-block characteristic cannot involve a left-block jet above its right-block order.

The argument is a contradiction that turns the obstruction into the hypothesis it needs.  Assume a
left-block jet above the right-block order occurs.  Some irreducible factor of the characteristic
contains that jet, so its left-block order is at least as large; the block swap of the characteristic
is saturated into the differential ideal of that factor by a power of its separant, whose variables
are variables of the factor; and the divisibility bridge, read in the swapped view, needs exactly the
inequality that the assumption provides.  It therefore returns that the factor divides the swap,
hence that the swapped factor divides the characteristic -- and the swapped factor carries a
right-block jet above the right-block order of the characteristic, which no divisor can do.
-/

namespace GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [CharZero F] [CharZero E]

/-- **The left-block order of a cleared characteristic does not exceed its right-block order.** -/
theorem twoBlock_leftOrder_le_rightOrder
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F Cc.polynomial)) ≤
      scalarDifferentialPolynomialOrder
        (differentialPolynomialTwoBlockEquiv F Cc.polynomial) := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : StrongNormalizationMonoid (DifferentialPolynomial Unit F) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (DifferentialPolynomial Unit F) :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  set m : ℕ := scalarDifferentialPolynomialOrder
    (differentialPolynomialTwoBlockEquiv F Cc.polynomial) with hm
  by_contra hcon
  push Not at hcon
  -- a left-block jet above the right-block order
  obtain ⟨n, hn, hnmem⟩ : ∃ n : ℕ, m < n ∧
      ((Sum.inl () : Unit ⊕ Unit), n) ∈ Cc.polynomial.vars := by
    by_contra hno
    push Not at hno
    exact absurd ((scalarDifferentialPolynomialOrder_swap_le_iff Cc.polynomial m).2 hno)
      (by omega)
  -- an irreducible factor carrying it
  obtain ⟨A, hAirrTB, hAdvd, hAleft⟩ :=
    exists_irreducible_factor_mem_vars Cc.ne_zero hnmem
  have hA0 : A ≠ 0 := hAirrTB.ne_zero
  have hAvars : (differentialPolynomialTwoBlockEquiv F A).vars = P.vars :=
    Cc.irreducible_factor_right_vars_eq G hG hy P hPirr hAirrTB hAdvd
  have hAprimUn : MvPolynomialPrimitive (differentialPolynomialTwoBlockEquiv F A) := by
    intro r hr
    exact Cc.primitive r (hr.trans (map_dvd (differentialPolynomialTwoBlockEquiv F) hAdvd))
  have hAirrEquiv : Irreducible (differentialPolynomialTwoBlockEquiv F A) :=
    hAirrTB.map (differentialPolynomialTwoBlockEquiv F)
  have hAirrK : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A)) :=
    hAprimUn.irreducible_map hAirrEquiv
  -- the separant certificate for the block swap
  obtain ⟨e, hmem⟩ := exists_twoBlock_swap_separant_saturation G hGclosed hG hy P hP hPirr Cc
    hAdvd hAvars hAirrK
  -- the multiplier is a power of the two-block separant
  set mA : ℕ := scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F A)
    with hmA
  have hsep : (differentialPolynomialTwoBlockEquiv F).symm
      (scalarDifferentialPolynomialSeparant (differentialPolynomialTwoBlockEquiv F A) ^ e) =
      MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e := by
    have hone : scalarDifferentialPolynomialSeparant
        (differentialPolynomialTwoBlockEquiv F A) =
        differentialPolynomialTwoBlockEquiv F
          (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A) := by
      rw [differentialPolynomialTwoBlockEquiv_pderiv_inr,
        scalarDifferentialPolynomialSeparant, scalarDifferentialPolynomialLeader, hmA]
    rw [hone, ← map_pow, AlgEquiv.symm_apply_apply]
  rw [hsep] at hmem
  -- the bridge hypotheses, in the swapped view
  have hswapA0 : differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F A) ≠ 0 := by
    intro h0
    refine hA0 ?_
    have h1 : differentialPolynomialTwoBlockSwap F A = 0 :=
      (differentialPolynomialTwoBlockEquiv F).injective (by simpa using h0)
    have h2 := congrArg (differentialPolynomialTwoBlockSwap F) h1
    rwa [differentialPolynomialTwoBlockSwap_swap, map_zero] at h2
  have hAprimSwap : MvPolynomialPrimitive (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F A)) :=
    primitive_swap_of_irreducible hAirrTB hAleft
  have hAirrSwapEquiv : Irreducible (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F A)) := by
    refine Irreducible.map (differentialPolynomialTwoBlockEquiv F) ?_
    refine Irreducible.map (MvPolynomial.renameEquiv F
      ((Equiv.sumComm Unit Unit).prodCongr (Equiv.refl ℕ))) ?_
    exact hAirrTB
  have hAirrSwapK : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F A))) :=
    hAprimSwap.irreducible_map hAirrSwapEquiv
  -- the left-block order of the factor is at least `n`
  have hnA : (((), n) : Unit × ℕ) ∈ (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F A)).vars :=
    (mem_vars_twoBlockEquiv_iff _ n).2 ((mem_vars_twoBlockSwap_iff A n).2 hAleft)
  have hnAorder : n ≤ scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F
      (differentialPolynomialTwoBlockSwap F A)) :=
    Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2) hnA
  have hinj : Function.Injective (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))) :=
    IsFractionRing.injective _ _
  have hAvarsBridge : (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F A))).vars.Nonempty := by
    refine ⟨((), n), ?_⟩
    rw [MvPolynomial.vars_map_of_injective _ hinj]
    exact hnA
  -- the multiplier keeps the left-block order of the factor
  have hMorder : scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F
          (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e)))) ≤
      scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F
          (differentialPolynomialTwoBlockSwap F A))) := by
    rw [scalarDifferentialPolynomialOrder_map hinj, scalarDifferentialPolynomialOrder_map hinj]
    refine (scalarDifferentialPolynomialOrder_swap_le_iff _ _).2 ?_
    intro k hk hmemk
    have hsub : (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e).vars ⊆ A.vars :=
      (MvPolynomial.vars_pow _ _).trans (mvPolynomial_vars_pderiv_subset _ _)
    have hmemA : ((Sum.inl () : Unit ⊕ Unit), k) ∈ A.vars := hsub hmemk
    have hkle : k ≤ scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F A)) :=
      Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2)
        ((mem_vars_twoBlockEquiv_iff _ k).2 ((mem_vars_twoBlockSwap_iff A k).2 hmemA))
    omega
  -- the factor does not divide its own separant power
  have hleaderMem : (((), mA) : Unit × ℕ) ∈
      (differentialPolynomialTwoBlockEquiv F A).vars := by
    refine scalarDifferentialPolynomialLeader_mem_vars ?_
    rw [hAvars]
    exact hP.2.2.1
  have hleaderdeg : MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), mA) A ≠ 0 := by
    rw [← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact (mem_vars_twoBlockEquiv_iff A mA).1 hleaderMem
  have hMnot : ¬ (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F A)) ∣
    MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F
        (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e)))) := by
    intro hdvd
    have hring : differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F A) ∣
        differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F
          (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e)) :=
      hAprimSwap.dvd_of_fraction_map_dvd hswapA0 hdvd
    have hswapdvd : differentialPolynomialTwoBlockSwap F A ∣
        differentialPolynomialTwoBlockSwap F
          (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e) := by
      have hmapped := map_dvd (differentialPolynomialTwoBlockEquiv F).symm hring
      simpa using hmapped
    have hAdvdM : A ∣ MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), mA) A ^ e := by
      have hmapped := map_dvd (differentialPolynomialTwoBlockSwap F) hswapdvd
      rwa [differentialPolynomialTwoBlockSwap_swap,
        differentialPolynomialTwoBlockSwap_swap] at hmapped
    exact not_dvd_pderiv_pow hAirrTB.prime hleaderdeg e hAdvdM
  -- the swap of the characteristic has small left-block order
  have hQorder : scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F (differentialPolynomialTwoBlockSwap F
          (differentialPolynomialTwoBlockSwap F Cc.polynomial)))) ≤
      scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F
          (differentialPolynomialTwoBlockSwap F A))) := by
    rw [differentialPolynomialTwoBlockSwap_swap,
      scalarDifferentialPolynomialOrder_map hinj, scalarDifferentialPolynomialOrder_map hinj,
      ← hm]
    omega
  -- the bridge
  have hAdvdSwap : A ∣ differentialPolynomialTwoBlockSwap F Cc.polynomial :=
    dvd_of_saturation_bridge hy hmem hAprimSwap hswapA0 hAvarsBridge hAirrSwapK hMorder hMnot
      hQorder
  have hswapAdvd : differentialPolynomialTwoBlockSwap F A ∣ Cc.polynomial := by
    have hmapped := map_dvd (differentialPolynomialTwoBlockSwap F) hAdvdSwap
    rwa [differentialPolynomialTwoBlockSwap_swap] at hmapped
  have hvarsub : (differentialPolynomialTwoBlockSwap F A).vars ⊆ Cc.polynomial.vars :=
    mvPolynomial_vars_subset_of_dvd hswapAdvd Cc.ne_zero
  have hmemP : ((Sum.inr () : Unit ⊕ Unit), n) ∈ Cc.polynomial.vars :=
    hvarsub ((mem_vars_twoBlockSwap_iff A n).2 hAleft)
  have hnm : n ≤ m := by
    rw [hm]
    exact Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2)
      ((mem_vars_twoBlockEquiv_iff Cc.polynomial n).2 hmemP)
  omega

omit [Differential F] [DifferentialAlgebra F E] [CharZero F] [CharZero E] in
/-- The right-block variables of the cleared characteristic are the variables of the characteristic
relation. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.twoBlockEquiv_vars_eq
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    (differentialPolynomialTwoBlockEquiv F Cc.polynomial).vars = P.vars := by
  classical
  have hvars := congrArg MvPolynomial.vars Cc.clearing
  rw [MvPolynomial.vars_map_of_injective _
      (IsFractionRing.injective (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F))),
    MvPolynomial.vars_C_mul _ Cc.scalar.ne_zero,
    MvPolynomial.vars_map_of_injective _
      (differentialIntermediateToJetFraction G hG hy).injective] at hvars
  exact hvars

/-- **Every irreducible factor of the cleared characteristic divides its block swap.**  The
cross-differences put the swap in the factor's general component, the left-block order does not
exceed the right-block order, so the component's characteristic property gives divisibility over the
jet fraction field, and primitivity contracts it to the two-block ring. -/
theorem irreducible_factor_dvd_twoBlockSwap
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    {A : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hAirrTB : Irreducible A) (hAdvd : A ∣ Cc.polynomial) :
    A ∣ differentialPolynomialTwoBlockSwap F Cc.polynomial := by
  classical
  letI : Differential (DifferentialPolynomial Unit F) := differentialPolynomialDifferential F
  letI : Differential (FractionRing (DifferentialPolynomial Unit F)) :=
    differentialIndependentJetFractionDifferential y hy
  letI : StrongNormalizationMonoid (DifferentialPolynomial Unit F) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (DifferentialPolynomial Unit F) :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have hinj : Function.Injective (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))) :=
    IsFractionRing.injective _ _
  have hA0 : A ≠ 0 := hAirrTB.ne_zero
  have hAvars : (differentialPolynomialTwoBlockEquiv F A).vars = P.vars :=
    Cc.irreducible_factor_right_vars_eq G hG hy P hPirr hAirrTB hAdvd
  have hAprimUn : MvPolynomialPrimitive (differentialPolynomialTwoBlockEquiv F A) := by
    intro r hr
    exact Cc.primitive r (hr.trans (map_dvd (differentialPolynomialTwoBlockEquiv F) hAdvd))
  have hAirrK : Irreducible (MvPolynomial.map
      (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F A)) :=
    hAprimUn.irreducible_map (hAirrTB.map (differentialPolynomialTwoBlockEquiv F))
  obtain ⟨Pc, hPcprime, hPcle, hPcdvd, hcross⟩ :=
    exists_component_crossDifference_mem G hGclosed hG hy P hP hPirr Cc hAdvd hAvars hAirrK
  have hCne : differentialPolynomialTwoBlockEquiv F Cc.polynomial ≠ 0 :=
    (differentialPolynomialTwoBlockEquiv F).injective.ne Cc.ne_zero
  obtain ⟨μ, hμsupp⟩ : (differentialPolynomialTwoBlockEquiv F Cc.polynomial).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hCne (MvPolynomial.support_eq_empty.mp hempty)
  have hμ : algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))
      (differentialPolynomialTwoBlockCoefficient μ Cc.polynomial) ≠ 0 := by
    refine fun h0 => (MvPolynomial.mem_support_iff.mp hμsupp) ?_
    have hzero : differentialPolynomialTwoBlockCoefficient μ Cc.polynomial = 0 :=
      hinj (by simpa using h0)
    exact hzero
  have hswapmem := twoBlockSwap_mem_of_crossDifference_mem
    (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
    Cc.polynomial Cc.diagonal hcross hμ
  -- the order comparison, from the proved order half
  have horder : scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F
          (differentialPolynomialTwoBlockSwap F Cc.polynomial))) ≤
      scalarDifferentialPolynomialOrder (MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F A)) := by
    rw [scalarDifferentialPolynomialOrder_map hinj, scalarDifferentialPolynomialOrder_map hinj,
      scalarDifferentialPolynomialOrder, scalarDifferentialPolynomialOrder, hAvars,
      ← Cc.twoBlockEquiv_vars_eq G hG hy P]
    exact twoBlock_leftOrder_le_rightOrder G hGclosed hG hy P hP hPirr Cc
  have hdvdK := hPcdvd _ hswapmem horder
  have hdvdRing : differentialPolynomialTwoBlockEquiv F A ∣
      differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialTwoBlockSwap F Cc.polynomial) :=
    hAprimUn.dvd_of_fraction_map_dvd ((differentialPolynomialTwoBlockEquiv F).injective.ne hA0)
      hdvdK
  have hmapped := map_dvd (differentialPolynomialTwoBlockEquiv F).symm hdvdRing
  simpa using hmapped

omit [Differential F] [DifferentialAlgebra F E] [CharZero F] in
/-- The cleared characteristic is squarefree in the two-block ring: a repeated factor would repeat
after inverting the left jets unless it were a left-block constant, which primitivity excludes. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.squarefree
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    Squarefree Cc.polynomial := by
  classical
  have hinj : Function.Injective (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F))) :=
    IsFractionRing.injective _ _
  have hsqK := Cc.mappedPolynomial_squarefree G hG hy P hPirr
  intro X hX
  obtain ⟨T, hT⟩ := hX
  have hmapdvd : (MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F X)) *
      (MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F X)) ∣
      MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F Cc.polynomial) := by
    refine ⟨MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
      (FractionRing (DifferentialPolynomial Unit F)))
      (differentialPolynomialTwoBlockEquiv F T), ?_⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ hT)
  have hunitK := hsqK _ hmapdvd
  -- a unit after inverting the left jets is a left-block constant
  have hvarsempty : (differentialPolynomialTwoBlockEquiv F X).vars = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    have hmem : j ∈ (MvPolynomial.map (algebraMap (DifferentialPolynomial Unit F)
        (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F X)).vars := by
      rw [MvPolynomial.vars_map_of_injective _ hinj]
      exact hj
    have hsubset := mvPolynomial_vars_subset_of_dvd hunitK.dvd
      (one_ne_zero (α := DifferentialPolynomial Unit
        (FractionRing (DifferentialPolynomial Unit F))))
    have h1 : j ∈ (1 : DifferentialPolynomial Unit
        (FractionRing (DifferentialPolynomial Unit F))).vars := hsubset hmem
    simp at h1
  set c := (differentialPolynomialTwoBlockEquiv F X).coeff 0 with hc
  have hXC : differentialPolynomialTwoBlockEquiv F X = MvPolynomial.C c :=
    MvPolynomial.vars_eq_empty_iff_eq_C.mp hvarsempty
  have hCdvd : MvPolynomial.C c ∣ differentialPolynomialTwoBlockEquiv F Cc.polynomial := by
    refine ⟨MvPolynomial.C c * differentialPolynomialTwoBlockEquiv F T, ?_⟩
    rw [hT, map_mul, map_mul, hXC]
    ring
  have hrunit := Cc.primitive _ hCdvd
  have hXunit : IsUnit (differentialPolynomialTwoBlockEquiv F X) := by
    rw [hXC]
    exact (MvPolynomial.C (σ := Unit × ℕ)).isUnit_map hrunit
  have hback := (differentialPolynomialTwoBlockEquiv F).symm.toRingHom.isUnit_map hXunit
  simpa using hback

/-- **The cleared characteristic divides its own block swap.**  Every irreducible factor does, and
the characteristic is squarefree. -/
theorem twoBlock_dvd_swap
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    Cc.polynomial ∣ differentialPolynomialTwoBlockSwap F Cc.polynomial :=
  Squarefree.dvd_of_forall_irreducible_factor_dvd
    (Cc.squarefree G hG hy P hPirr)
    fun _A hAirr hAdvd =>
      irreducible_factor_dvd_twoBlockSwap G hGclosed hG hy P hP hPirr Cc hAirr hAdvd

/-- **Block symmetry of the cleared characteristic.**  It is an associate of its own block swap. -/
theorem twoBlock_associated_swap
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) :
    Associated Cc.polynomial (differentialPolynomialTwoBlockSwap F Cc.polynomial) := by
  obtain ⟨T, hT⟩ := twoBlock_dvd_swap G hGclosed hG hy P hP hPirr Cc
  have hback := congrArg (differentialPolynomialTwoBlockSwap F) hT
  rw [differentialPolynomialTwoBlockSwap_swap, map_mul] at hback
  have hTT : T * differentialPolynomialTwoBlockSwap F T = 1 := by
    have hcancel : Cc.polynomial * (T * differentialPolynomialTwoBlockSwap F T) =
        Cc.polynomial * 1 := by
      rw [mul_one, ← mul_assoc, ← hT]
      exact hback.symm
    exact mul_left_cancel₀ Cc.ne_zero hcancel
  exact ⟨⟨T, differentialPolynomialTwoBlockSwap F T, hTT, by rw [mul_comm]; exact hTT⟩, hT.symm⟩

/-- **(★).**  The two blocks of a cleared characteristic carry the same jet degrees: the degree in a
left-block jet equals the degree in the corresponding right-block jet.  In particular the left-block
order and leader degree agree with the right-block ones. -/
theorem twoBlock_degreeOf_inl_eq_degreeOf_inr
    (G : IntermediateField F E) (hGclosed : DerivationClosed G) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (hP : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal G y : Set _) P)
    (hPirr : Irreducible P)
    (Cc : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) (k : ℕ) :
    MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) Cc.polynomial =
      MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k) Cc.polynomial := by
  classical
  obtain ⟨u, hu⟩ := twoBlock_associated_swap G hGclosed hG hy P hP hPirr Cc
  have hinj : Function.Injective
      (fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((Equiv.sumComm Unit Unit).injective h.1) h.2
  have hswapdeg : MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k)
      (differentialPolynomialTwoBlockSwap F Cc.polynomial) =
      MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) Cc.polynomial := by
    unfold differentialPolynomialTwoBlockSwap
    rw [show ((Sum.inr () : Unit ⊕ Unit), k) =
        (fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2))
          ((Sum.inl () : Unit ⊕ Unit), k) by simp]
    exact MvPolynomial.degreeOf_rename_of_injective hinj _
  have hudeg : MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k)
      ((u : DifferentialPolynomial (Unit ⊕ Unit) F)) = 0 := by
    by_contra hcon
    have hmem : ((Sum.inr () : Unit ⊕ Unit), k) ∈
        (u : DifferentialPolynomial (Unit ⊕ Unit) F).vars :=
      MvPolynomial.mem_vars_iff_degreeOf_ne_zero.2 hcon
    have hsubset := mvPolynomial_vars_subset_of_dvd (Units.isUnit u).dvd
      (one_ne_zero (α := DifferentialPolynomial (Unit ⊕ Unit) F))
    have h1 : ((Sum.inr () : Unit ⊕ Unit), k) ∈
        (1 : DifferentialPolynomial (Unit ⊕ Unit) F).vars := hsubset hmem
    simp at h1
  have hu0 : (u : DifferentialPolynomial (Unit ⊕ Unit) F) ≠ 0 := u.ne_zero
  calc MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) Cc.polynomial
      = MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k)
          (differentialPolynomialTwoBlockSwap F Cc.polynomial) := hswapdeg.symm
    _ = MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k)
          (Cc.polynomial * (u : DifferentialPolynomial (Unit ⊕ Unit) F)) := by rw [hu]
    _ = MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k) Cc.polynomial := by
        rw [MvPolynomial.degreeOf_mul_eq Cc.ne_zero hu0, hudeg, Nat.add_zero]

end

end GaloisForLFunctions
