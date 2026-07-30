import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRank
import GaloisForLFunctions.HTGeometry.DifferentialHopfPrimitive

/-!
# Characteristic polynomials of scalar differential relation kernels

For a differential intermediate field `G` inside a free scalar differential field, this file
constructs the kernel of jet evaluation over `G`.  The kernel is a proper prime ideal.  A single
non-base element of `G` already supplies a nonzero relation, without any finite-generation
hypothesis on `G`: write that element as a rational function of finitely many source jets and
clear its nonzero denominator.

The characteristic polynomial is selected by the repaired scalar Ritt rank: order, leader degree,
then total degree.  The final total-degree tie-break is essential for the irreducibility proof.
This file does not assume the later Ritt coefficient-ratio or pseudo-reduction theorem.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The scalar differential-polynomial relations of `y` with coefficients in an intermediate
field `G`. -/
def differentialIntermediateRelationIdeal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (y : E) :
    Ideal (DifferentialPolynomial Unit G) :=
  differentialRelationIdealOver (K := G) (fun _ : Unit ↦ y)

@[simp]
theorem mem_differentialIntermediateRelationIdeal_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (y : E) (P : DifferentialPolynomial Unit G) :
    P ∈ differentialIntermediateRelationIdeal G y ↔
      differentialPolynomialEvalOver (K := G) (fun _ : Unit ↦ y) P = 0 :=
  Iff.rfl

/-- An evaluation relation kernel into a field is prime. -/
theorem differentialIntermediateRelationIdeal_isPrime
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (y : E) :
    (differentialIntermediateRelationIdeal G y).IsPrime :=
  RingHom.ker_isPrime _

/-- An evaluation relation kernel into a nontrivial field is proper. -/
theorem differentialIntermediateRelationIdeal_ne_top
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (y : E) :
    differentialIntermediateRelationIdeal G y ≠ ⊤ :=
  RingHom.ker_ne_top _

/-- Base-changing scalar differential-polynomial coefficients from `F` to an intermediate field
does not change evaluation in the ambient field. -/
theorem differentialPolynomialEvalOver_map_intermediate
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (y : E)
    (P : DifferentialPolynomial Unit F) :
    differentialPolynomialEvalOver (K := G) (fun _ : Unit ↦ y)
        (MvPolynomial.map (algebraMap F G) P) =
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) P := by
  change MvPolynomial.eval₂ (algebraMap G E)
      (fun a : Unit × ℕ ↦ differentialJet a.2 y)
        (MvPolynomial.map (algebraMap F G) P) =
    MvPolynomial.eval₂ (algebraMap F E)
      (fun a : Unit × ℕ ↦ differentialJet a.2 y) P
  rw [MvPolynomial.eval₂_map]
  rfl

/-- If clearing a nonzero polynomial denominator with a coefficient `u : G` produced the zero
polynomial, one nonzero denominator coefficient would force `u` back into the base field.  This is
the reusable coefficient contradiction behind relation construction. -/
theorem map_sub_C_mul_map_ne_zero_of_not_mem_bot
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (G : IntermediateField F E) (u : G)
    (huF : (u : E) ∉ (⊥ : IntermediateField F E))
    {p q : DifferentialPolynomial Unit F} (hq : q ≠ 0) :
    MvPolynomial.map (algebraMap F G) p -
        MvPolynomial.C u * MvPolynomial.map (algebraMap F G) q ≠ 0 := by
  intro hzero
  obtain ⟨s, hqs⟩ := MvPolynomial.exists_coeff_ne_zero hq
  have hcoeff := congrArg (MvPolynomial.coeff s) hzero
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_map,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] at hcoeff
  have hqG : algebraMap F G (q.coeff s) ≠ 0 := by
    exact (map_ne_zero (algebraMap F G)).mpr hqs
  have huEq : u = algebraMap F G (p.coeff s / q.coeff s) := by
    rw [map_div₀]
    apply (eq_div_iff hqG).mpr
    exact (sub_eq_zero.mp hcoeff).symm
  apply huF
  rw [IntermediateField.mem_bot]
  refine ⟨p.coeff s / q.coeff s, ?_⟩
  simpa using congrArg Subtype.val huEq.symm

/-- One non-base element in `G ≤ F⟨y⟩` supplies a nonzero scalar differential relation for
`y` over `G`.  No finite-generation hypothesis on `G` is used. -/
theorem exists_nonzero_differentialIntermediateRelation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (u : G) (huF : (u : E) ∉ (⊥ : IntermediateField F E)) :
    ∃ P : DifferentialPolynomial Unit G,
      P ∈ differentialIntermediateRelationIdeal G y ∧ P ≠ 0 := by
  let j : Unit × ℕ → E := fun a ↦ differentialJet a.2 y
  have hjets : differentialJetSet ({y} : Set E) = Set.range j := by
    ext z
    constructor
    · rintro ⟨x, hx, n, rfl⟩
      have hxy : x = y := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨((), n), rfl⟩
    · rintro ⟨⟨a, n⟩, rfl⟩
      exact ⟨y, Set.mem_singleton y, n, rfl⟩
  have huJets : (u : E) ∈ IntermediateField.adjoin F (Set.range j) := by
    rw [← hjets]
    exact hG u.2
  obtain ⟨p, q, hu⟩ :=
    (IntermediateField.mem_adjoin_range_iff F j (u : E)).mp huJets
  have hu0 : (u : E) ≠ 0 := by
    intro huZero
    apply huF
    rw [huZero]
    exact (⊥ : IntermediateField F E).zero_mem
  have hqEval : MvPolynomial.aeval j q ≠ 0 := by
    intro hqZero
    apply hu0
    rw [hu, hqZero, div_zero]
  have hq : q ≠ 0 := by
    intro hqZero
    apply hqEval
    simp [hqZero]
  let P : DifferentialPolynomial Unit G :=
    MvPolynomial.map (algebraMap F G) p -
      MvPolynomial.C u * MvPolynomial.map (algebraMap F G) q
  refine ⟨P, ?_, ?_⟩
  · rw [mem_differentialIntermediateRelationIdeal_iff]
    simp only [P, map_sub, map_mul, differentialPolynomialEvalOver_C]
    rw [differentialPolynomialEvalOver_map_intermediate,
      differentialPolynomialEvalOver_map_intermediate]
    change MvPolynomial.aeval j p - (u : E) * MvPolynomial.aeval j q = 0
    rw [hu, div_mul_cancel₀ _ hqEval, sub_self]
  · exact map_sub_C_mul_map_ne_zero_of_not_mem_bot G u huF hq

/-- The relation kernel is nonzero as soon as the intermediate field contains one non-base
element and lies inside the scalar differential adjunction. -/
theorem differentialIntermediateRelationIdeal_ne_bot
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (u : G) (huF : (u : E) ∉ (⊥ : IntermediateField F E)) :
    differentialIntermediateRelationIdeal G y ≠ ⊥ := by
  obtain ⟨P, hPI, hP0⟩ :=
    exists_nonzero_differentialIntermediateRelation G hG u huF
  intro hbot
  rw [hbot, Ideal.mem_bot] at hPI
  exact hP0 hPI

/-- A nonzero left factor cannot have larger scalar differential order than its product. -/
theorem scalarDifferentialPolynomialOrder_left_le_mul
    {K : Type*} [Field K] {A B : DifferentialPolynomial Unit K}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    scalarDifferentialPolynomialOrder A ≤
      scalarDifferentialPolynomialOrder (A * B) := by
  classical
  unfold scalarDifferentialPolynomialOrder
  refine Finset.sup_le fun j hj ↦ ?_
  have hjA : MvPolynomial.degreeOf j A ≠ 0 := by
    rwa [← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  have hjAB : j ∈ (A * B).vars := by
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero,
      MvPolynomial.degreeOf_mul_eq hA hB]
    omega
  exact Finset.le_sup hjAB

/-- A nonzero right factor cannot have larger scalar differential order than its product. -/
theorem scalarDifferentialPolynomialOrder_right_le_mul
    {K : Type*} [Field K] {A B : DifferentialPolynomial Unit K}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    scalarDifferentialPolynomialOrder B ≤
      scalarDifferentialPolynomialOrder (A * B) := by
  simpa [mul_comm] using
    (scalarDifferentialPolynomialOrder_left_le_mul hB hA)

/-- Once a left factor has the same differential order as the product, its leader degree is no
larger than the product's leader degree. -/
theorem scalarDifferentialPolynomialLeaderDegree_left_le_mul
    {K : Type*} [Field K] {A B : DifferentialPolynomial Unit K}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hOrder : scalarDifferentialPolynomialOrder A =
      scalarDifferentialPolynomialOrder (A * B)) :
    scalarDifferentialPolynomialLeaderDegree A ≤
      scalarDifferentialPolynomialLeaderDegree (A * B) := by
  unfold scalarDifferentialPolynomialLeaderDegree scalarDifferentialPolynomialLeader
  rw [← hOrder, MvPolynomial.degreeOf_mul_eq hA hB]
  omega

/-- Right-factor form of `scalarDifferentialPolynomialLeaderDegree_left_le_mul`. -/
theorem scalarDifferentialPolynomialLeaderDegree_right_le_mul
    {K : Type*} [Field K] {A B : DifferentialPolynomial Unit K}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hOrder : scalarDifferentialPolynomialOrder B =
      scalarDifferentialPolynomialOrder (A * B)) :
    scalarDifferentialPolynomialLeaderDegree B ≤
      scalarDifferentialPolynomialLeaderDegree (A * B) := by
  rw [mul_comm A B] at hOrder ⊢
  exact scalarDifferentialPolynomialLeaderDegree_left_le_mul hB hA hOrder

/-- If a repaired-rank-minimal element of a proper prime ideal factors and its left factor lies in
the ideal, the right factor is a unit.  The conclusion uses the total-degree tie-break after order
and leader degree have tied. -/
theorem IsMinimalScalarDifferentialPolynomialRank.isUnit_right_of_mem_left_factor
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)} (hI : I.IsPrime)
    {P A B : DifferentialPolynomial Unit K}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P)
    (hfac : P = A * B) (hAI : A ∈ I) : IsUnit B := by
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hP.2.1
    rw [hfac, hzero, zero_mul]
  have hB0 : B ≠ 0 := by
    intro hzero
    apply hP.2.1
    rw [hfac, hzero, mul_zero]
  by_cases hAvars : A.vars.Nonempty
  · have hminA := hP.2.2.2 hAI hA0 hAvars
    have hAOrderLe : scalarDifferentialPolynomialOrder A ≤
        scalarDifferentialPolynomialOrder P := by
      have h := scalarDifferentialPolynomialOrder_left_le_mul hA0 hB0
      rwa [← hfac] at h
    have hOrder : scalarDifferentialPolynomialOrder P =
        scalarDifferentialPolynomialOrder A :=
      Nat.le_antisymm hminA.1 hAOrderLe
    have hALeaderLe : scalarDifferentialPolynomialLeaderDegree A ≤
        scalarDifferentialPolynomialLeaderDegree P := by
      rw [hfac]
      apply scalarDifferentialPolynomialLeaderDegree_left_le_mul hA0 hB0
      rw [← hfac]
      exact hOrder.symm
    have hLeader : scalarDifferentialPolynomialLeaderDegree P =
        scalarDifferentialPolynomialLeaderDegree A :=
      Nat.le_antisymm (hminA.2.1 hOrder) hALeaderLe
    have hTotalLe : P.totalDegree ≤ A.totalDegree :=
      hminA.2.2 hOrder hLeader
    have hTotalEq := MvPolynomial.totalDegree_mul_of_isDomain hA0 hB0
    rw [← hfac] at hTotalEq
    have hBTotal : B.totalDegree = 0 := by omega
    have hBC : B = MvPolynomial.C (B.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hBTotal
    have hBc : B.coeff 0 ≠ 0 := by
      intro hc
      apply hB0
      rw [hBC, hc]
      simp
    rw [hBC]
    exact IsUnit.map MvPolynomial.C hBc.isUnit
  · have hAvars0 : A.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAvars
    have hAC : A = MvPolynomial.C (A.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hAvars0
    have hAc : A.coeff 0 ≠ 0 := by
      intro hc
      apply hA0
      rw [hAC, hc]
      simp
    have hAunit : IsUnit A := by
      rw [hAC]
      exact IsUnit.map MvPolynomial.C hAc.isUnit
    exact (hI.ne_top (I.eq_top_of_isUnit_mem hAI hAunit)).elim

/-- A repaired-rank-minimal member of a prime scalar differential relation ideal is irreducible,
up to the ordinary units of the multivariable polynomial ring. -/
theorem IsMinimalScalarDifferentialPolynomialRank.irreducible_of_isPrime
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)} (hI : I.IsPrime)
    {P : DifferentialPolynomial Unit K}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P) :
    Irreducible P := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    exact hI.ne_top (I.eq_top_of_isUnit_mem hP.1 hunit)
  · intro A B hfac
    have hmem : A ∈ I ∨ B ∈ I := hI.mem_or_mem (hfac ▸ hP.1)
    rcases hmem with hAI | hBI
    · exact Or.inr (hP.isUnit_right_of_mem_left_factor hI hfac hAI)
    · apply Or.inl
      apply hP.isUnit_right_of_mem_left_factor hI
        (hfac.trans (mul_comm A B)) hBI

/-- Every nontrivial intermediate field inside a scalar differential adjunction has a repaired
minimal characteristic relation, and that relation is irreducible. -/
theorem exists_irreducible_minimal_differentialKernelCharacteristic
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (u : G) (huF : (u : E) ∉ (⊥ : IntermediateField F E)) :
    ∃ P : DifferentialPolynomial Unit G,
      IsMinimalScalarDifferentialPolynomialRank
          (differentialIntermediateRelationIdeal G y : Set _) P ∧
        Irreducible P := by
  have hI0 := differentialIntermediateRelationIdeal_ne_bot G hG u huF
  have hItop := differentialIntermediateRelationIdeal_ne_top G y
  obtain ⟨P, hP⟩ :=
    Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero hI0 hItop
  exact ⟨P, hP,
    hP.irreducible_of_isPrime (differentialIntermediateRelationIdeal_isPrime G y)⟩

/-- The total differential-polynomial derivation over a derivation-closed intermediate field,
using the derivation induced from the ambient differential field. -/
def differentialIntermediatePolynomialDerivation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (hG : DerivationClosed G) :
    Derivation ℤ (DifferentialPolynomial Unit G) (DifferentialPolynomial Unit G) := by
  letI : Differential G := derivationClosedDifferential G hG
  exact differentialPolynomialOverDerivation Unit G

/-- The scalar relation kernel over a derivation-closed intermediate coefficient field is stable
under its induced total differential-polynomial derivation. -/
theorem differentialIntermediatePolynomialDerivation_mem_relationIdeal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) (hG : DerivationClosed G) (y : E)
    {P : DifferentialPolynomial Unit G}
    (hP : P ∈ differentialIntermediateRelationIdeal G y) :
    differentialIntermediatePolynomialDerivation G hG P ∈
      differentialIntermediateRelationIdeal G y := by
  letI : Differential G := derivationClosedDifferential G hG
  letI : DifferentialAlgebra G E :=
    ⟨fun c ↦ derivationClosedDifferential_apply G hG c⟩
  exact differentialPolynomialOverDerivation_mem_relationIdeal
    (fun _ : Unit ↦ y) hP

/-- Singling out a variable turns a multivariable polynomial into a univariate polynomial over
the polynomial ring in all the remaining variables. -/
def mvPolynomialAsPolynomialAt
    {K σ : Type*} [CommSemiring K] (i : σ) (P : MvPolynomial σ K) :
    Polynomial (MvPolynomial {j : σ // j ≠ i} K) := by
  classical
  exact MvPolynomial.optionEquivLeft K {j : σ // j ≠ i}
    (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm P)

/-- A scalar differential polynomial viewed as a univariate polynomial in its leader. -/
def scalarDifferentialPolynomialAsPolynomial
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    Polynomial
      (MvPolynomial {j : Unit × ℕ // j ≠ scalarDifferentialPolynomialLeader P} K) :=
  mvPolynomialAsPolynomialAt (scalarDifferentialPolynomialLeader P) P

/-- The leading coefficient obtained by singling out an arbitrary variable, renamed back into the
original multivariable-polynomial ring. -/
def mvPolynomialInitialAt
    {K σ : Type*} [CommSemiring K] (i : σ) (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  MvPolynomial.rename Subtype.val (mvPolynomialAsPolynomialAt i P).leadingCoeff

/-- The initial is the leading coefficient after genuinely singling out the leader variable,
renamed back into the original scalar jet-variable type. -/
def scalarDifferentialPolynomialInitial
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    DifferentialPolynomial Unit K :=
  mvPolynomialInitialAt (scalarDifferentialPolynomialLeader P) P

/-- The separant is the partial derivative with respect to the scalar leader. -/
def scalarDifferentialPolynomialSeparant
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    DifferentialPolynomial Unit K :=
  MvPolynomial.pderiv (scalarDifferentialPolynomialLeader P) P

/-- Singling out any variable preserves nonzeroness. -/
theorem mvPolynomialAsPolynomialAt_ne_zero
    {K σ : Type*} [CommSemiring K] {i : σ} {P : MvPolynomial σ K}
    (hP : P ≠ 0) : mvPolynomialAsPolynomialAt i P ≠ 0 := by
  classical
  unfold mvPolynomialAsPolynomialAt
  intro hzero
  apply hP
  apply MvPolynomial.rename_injective _ (Equiv.optionSubtypeNe i).symm.injective
  apply (MvPolynomial.optionEquivLeft K {j : σ // j ≠ i}).injective
  simpa using hzero

/-- The correctly distinguished initial of a nonzero scalar differential polynomial is nonzero. -/
theorem scalarDifferentialPolynomialInitial_ne_zero
    {K : Type*} [CommSemiring K] {P : DifferentialPolynomial Unit K}
    (hP : P ≠ 0) : scalarDifferentialPolynomialInitial P ≠ 0 := by
  unfold scalarDifferentialPolynomialInitial mvPolynomialInitialAt
  intro hzero
  apply Polynomial.leadingCoeff_ne_zero.mpr
    (mvPolynomialAsPolynomialAt_ne_zero hP)
  apply MvPolynomial.rename_injective _ Subtype.val_injective
  simpa using hzero

/-- Partial differentiation cannot introduce a new multivariable-polynomial variable. -/
theorem mvPolynomial_vars_pderiv_subset
    {K σ : Type*} [CommSemiring K] (i : σ) (P : MvPolynomial σ K) :
    (MvPolynomial.pderiv i P).vars ⊆ P.vars := by
  classical
  rw [show MvPolynomial.pderiv i P =
      ∑ s ∈ P.support,
        MvPolynomial.pderiv i (MvPolynomial.monomial s (P.coeff s)) by
    rw [← map_sum, ← P.as_sum]]
  intro j hj
  have hj' := MvPolynomial.vars_sum_subset P.support
    (fun s ↦ MvPolynomial.pderiv i (MvPolynomial.monomial s (P.coeff s))) hj
  simp only [Finset.mem_biUnion] at hj'
  obtain ⟨s, hsP, hjs⟩ := hj'
  rw [MvPolynomial.pderiv_monomial] at hjs
  have hc : P.coeff s * (s i : K) ≠ 0 := by
    intro hc
    simp [hc] at hjs
  rw [MvPolynomial.vars_monomial hc] at hjs
  apply MvPolynomial.support_subset_vars_of_mem_support hsP
  rw [Finsupp.mem_support_iff] at hjs ⊢
  intro hsj
  apply hjs
  simp [hsj]

/-- A variable of the leading coefficient of `optionEquivLeft` lifts to a `some` variable of the
original multivariable polynomial. -/
theorem optionEquivLeft_leadingCoeff_some_mem_vars
    {K σ : Type*} [CommSemiring K] (P : MvPolynomial (Option σ) K) {b : σ}
    (hb : b ∈ (MvPolynomial.optionEquivLeft K σ P).leadingCoeff.vars) :
    some b ∈ P.vars := by
  classical
  obtain ⟨m, hm, hbm⟩ := (MvPolynomial.mem_vars_iff_mem_support b).mp hb
  have hmCoeff : m ∈
      ((MvPolynomial.optionEquivLeft K σ P).coeff
        (MvPolynomial.optionEquivLeft K σ P).natDegree).support := by
    simpa only [Polynomial.leadingCoeff] using hm
  have hmP : m.optionElim (MvPolynomial.optionEquivLeft K σ P).natDegree ∈
      P.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft K).mp hmCoeff
  have hsomeSupport : some b ∈
      (m.optionElim (MvPolynomial.optionEquivLeft K σ P).natDegree).support := by
    rw [Finsupp.mem_support_iff] at hbm ⊢
    simpa using hbm
  exact (MvPolynomial.mem_vars_iff_mem_support (some b)).mpr
    ⟨_, hmP, hsomeSupport⟩

/-- Every variable occurring in an arbitrary distinguished initial already occurred in the
original polynomial. -/
theorem mvPolynomialInitialAt_vars_subset
    {K σ : Type*} [CommSemiring K] (i : σ) (P : MvPolynomial σ K) :
    (mvPolynomialInitialAt i P).vars ⊆ P.vars := by
  classical
  intro j hj
  obtain ⟨b, hb, hbj⟩ := MvPolynomial.mem_vars_rename Subtype.val
    (mvPolynomialAsPolynomialAt i P).leadingCoeff hj
  have hsome : some b ∈
      (MvPolynomial.rename (Equiv.optionSubtypeNe i).symm P).vars := by
    apply optionEquivLeft_leadingCoeff_some_mem_vars
    exact hb
  obtain ⟨k, hkP, hkb⟩ :=
    MvPolynomial.mem_vars_rename (Equiv.optionSubtypeNe i).symm P hsome
  have hk : k = b.1 := by
    calc
      k = Equiv.optionSubtypeNe i ((Equiv.optionSubtypeNe i).symm k) :=
        ((Equiv.optionSubtypeNe i).apply_symm_apply k).symm
      _ = Equiv.optionSubtypeNe i (some b) := congrArg (Equiv.optionSubtypeNe i) hkb
      _ = b.1 := by simp
  rw [← hbj, ← hk]
  exact hkP

/-- Every variable occurring in the distinguished scalar initial already occurred in the original
polynomial. -/
theorem scalarDifferentialPolynomialInitial_vars_subset
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    (scalarDifferentialPolynomialInitial P).vars ⊆ P.vars :=
  mvPolynomialInitialAt_vars_subset (scalarDifferentialPolynomialLeader P) P

/-- The leader itself cannot occur in its distinguished initial. -/
theorem scalarDifferentialPolynomialLeader_not_mem_initial_vars
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialLeader P ∉
      (scalarDifferentialPolynomialInitial P).vars := by
  intro hleader
  obtain ⟨b, _, hb⟩ := MvPolynomial.mem_vars_rename Subtype.val
    (mvPolynomialAsPolynomialAt (scalarDifferentialPolynomialLeader P) P).leadingCoeff hleader
  exact b.2 hb

/-- A variable of a scalar polynomial that is not its leader has strictly smaller jet order. -/
theorem scalarDifferentialPolynomial_var_order_lt
    {K : Type*} [CommSemiring K] {P : DifferentialPolynomial Unit K}
    {j : Unit × ℕ} (hj : j ∈ P.vars)
    (hne : j ≠ scalarDifferentialPolynomialLeader P) :
    j.2 < scalarDifferentialPolynomialOrder P := by
  have hjle : j.2 ≤ scalarDifferentialPolynomialOrder P := by
    exact Finset.le_sup (f := fun k : Unit × ℕ ↦ k.2) hj
  apply Nat.lt_of_le_of_ne hjle
  intro heq
  apply hne
  exact Prod.ext (Subsingleton.elim _ _) heq

/-- If the distinguished initial is nonconstant, its scalar differential order is strictly below
that of the original polynomial. -/
theorem scalarDifferentialPolynomialInitial_order_lt
    {K : Type*} [CommSemiring K] {P : DifferentialPolynomial Unit K}
    (hvars : (scalarDifferentialPolynomialInitial P).vars.Nonempty) :
    scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialInitial P) <
      scalarDifferentialPolynomialOrder P := by
  obtain ⟨j₀, hj₀⟩ := hvars
  have hj₀P := scalarDifferentialPolynomialInitial_vars_subset P hj₀
  have hj₀ne : j₀ ≠ scalarDifferentialPolynomialLeader P := by
    intro h
    subst j₀
    exact scalarDifferentialPolynomialLeader_not_mem_initial_vars P hj₀
  have hj₀lt := scalarDifferentialPolynomial_var_order_lt hj₀P hj₀ne
  unfold scalarDifferentialPolynomialOrder
  apply (Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) hj₀lt)).mpr
  intro j hj
  exact scalarDifferentialPolynomial_var_order_lt
    (scalarDifferentialPolynomialInitial_vars_subset P hj)
    (by
      intro h
      subst j
      exact scalarDifferentialPolynomialLeader_not_mem_initial_vars P hj)

/-- A repaired-rank-minimal relation cannot contain its distinguished initial. -/
theorem IsMinimalScalarDifferentialPolynomialRank.initial_not_mem
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)} (hItop : I ≠ ⊤)
    {P : DifferentialPolynomial Unit K}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P) :
    scalarDifferentialPolynomialInitial P ∉ I := by
  intro hInitial
  have hInitial0 := scalarDifferentialPolynomialInitial_ne_zero hP.2.1
  by_cases hvars : (scalarDifferentialPolynomialInitial P).vars.Nonempty
  · have hmin := hP.2.2.2 hInitial hInitial0 hvars
    exact (Nat.not_le_of_lt (scalarDifferentialPolynomialInitial_order_lt hvars)) hmin.1
  · have hvars0 := Finset.not_nonempty_iff_eq_empty.mp hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars0
    have hc : (scalarDifferentialPolynomialInitial P).coeff 0 ≠ 0 := by
      intro hc
      apply hInitial0
      rw [hC, hc]
      simp
    have hunit : IsUnit (scalarDifferentialPolynomialInitial P) := by
      rw [hC]
      exact IsUnit.map MvPolynomial.C hc.isUnit
    exact hItop (I.eq_top_of_isUnit_mem hInitial hunit)

/-- Under `optionEquivLeft`, partial differentiation in the distinguished `none` variable is the
ordinary univariate polynomial derivative. -/
theorem optionEquivLeft_pderiv_none
    {K σ : Type*} [CommSemiring K] (P : MvPolynomial (Option σ) K) :
    MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv none P) =
      Polynomial.derivative (MvPolynomial.optionEquivLeft K σ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      cases j with
      | none => simp [hP, Polynomial.derivative_mul, mul_comm]
      | some j => simp [hP, Polynomial.derivative_mul, mul_comm]

/-- Singling out a variable intertwines its partial derivative with the univariate derivative. -/
theorem mvPolynomialAsPolynomialAt_pderiv
    {K σ : Type*} [CommSemiring K] (i : σ) (P : MvPolynomial σ K) :
    mvPolynomialAsPolynomialAt i (MvPolynomial.pderiv i P) =
      Polynomial.derivative (mvPolynomialAsPolynomialAt i P) := by
  classical
  unfold mvPolynomialAsPolynomialAt
  rw [← MvPolynomial.pderiv_rename (Equiv.optionSubtypeNe i).symm.injective i P,
    Equiv.optionSubtypeNe_symm_self]
  exact optionEquivLeft_pderiv_none _

/-- A nontrivial partial derivative has strictly lower degree in the differentiated variable. -/
theorem mvPolynomial_degreeOf_pderiv_lt
    {K σ : Type*} [CommSemiring K] {i : σ} {P : MvPolynomial σ K}
    (hi : MvPolynomial.degreeOf i P ≠ 0) :
    MvPolynomial.degreeOf i (MvPolynomial.pderiv i P) <
      MvPolynomial.degreeOf i P := by
  classical
  have hnat : (mvPolynomialAsPolynomialAt i P).natDegree ≠ 0 := by
    unfold mvPolynomialAsPolynomialAt
    rw [← MvPolynomial.degreeOf_eq_natDegree]
    exact hi
  calc
    MvPolynomial.degreeOf i (MvPolynomial.pderiv i P) =
        (mvPolynomialAsPolynomialAt i (MvPolynomial.pderiv i P)).natDegree :=
      MvPolynomial.degreeOf_eq_natDegree i _
    _ = (Polynomial.derivative (mvPolynomialAsPolynomialAt i P)).natDegree :=
      congrArg Polynomial.natDegree (mvPolynomialAsPolynomialAt_pderiv i P)
    _ < (mvPolynomialAsPolynomialAt i P).natDegree :=
      Polynomial.natDegree_derivative_lt hnat
    _ = MvPolynomial.degreeOf i P :=
      (MvPolynomial.degreeOf_eq_natDegree i P).symm

/-- In characteristic zero, the separant of a nonconstant scalar differential polynomial is
nonzero. -/
theorem scalarDifferentialPolynomialSeparant_ne_zero
    {K : Type*} [Field K] [CharZero K] {P : DifferentialPolynomial Unit K}
    (hP : P.vars.Nonempty) : scalarDifferentialPolynomialSeparant P ≠ 0 := by
  obtain ⟨s, hsP, hleader⟩ :=
    (MvPolynomial.mem_vars_iff_mem_support
      (scalarDifferentialPolynomialLeader P)).mp
      (scalarDifferentialPolynomialLeader_mem_vars hP)
  exact pderiv_ne_zero_of_mem_support hsP hleader

/-- The separant introduces no new scalar jet variables. -/
theorem scalarDifferentialPolynomialSeparant_vars_subset
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    (scalarDifferentialPolynomialSeparant P).vars ⊆ P.vars :=
  mvPolynomial_vars_pderiv_subset (scalarDifferentialPolynomialLeader P) P

/-- The separant has scalar differential order at most that of the original polynomial. -/
theorem scalarDifferentialPolynomialSeparant_order_le
    {K : Type*} [CommSemiring K] (P : DifferentialPolynomial Unit K) :
    scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialSeparant P) ≤
      scalarDifferentialPolynomialOrder P := by
  unfold scalarDifferentialPolynomialOrder
  exact Finset.sup_le fun j hj ↦ Finset.le_sup
    (scalarDifferentialPolynomialSeparant_vars_subset P hj)

/-- If taking the separant preserves scalar differential order, it strictly lowers the leader
degree. -/
theorem scalarDifferentialPolynomialSeparant_leaderDegree_lt
    {K : Type*} [CommSemiring K] {P : DifferentialPolynomial Unit K}
    (hP : P.vars.Nonempty)
    (hOrder : scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialSeparant P) =
      scalarDifferentialPolynomialOrder P) :
    scalarDifferentialPolynomialLeaderDegree (scalarDifferentialPolynomialSeparant P) <
      scalarDifferentialPolynomialLeaderDegree P := by
  unfold scalarDifferentialPolynomialLeaderDegree
  have hLeader :
      scalarDifferentialPolynomialLeader (scalarDifferentialPolynomialSeparant P) =
        scalarDifferentialPolynomialLeader P := by
    unfold scalarDifferentialPolynomialLeader
    exact congrArg (fun n : ℕ ↦ ((), n)) hOrder
  rw [hLeader]
  unfold scalarDifferentialPolynomialSeparant
  apply mvPolynomial_degreeOf_pderiv_lt
  rw [← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  exact scalarDifferentialPolynomialLeader_mem_vars hP

/-- In characteristic zero, a repaired-rank-minimal relation cannot contain its separant. -/
theorem IsMinimalScalarDifferentialPolynomialRank.separant_not_mem
    {K : Type*} [Field K] [CharZero K]
    {I : Ideal (DifferentialPolynomial Unit K)} (hItop : I ≠ ⊤)
    {P : DifferentialPolynomial Unit K}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P) :
    scalarDifferentialPolynomialSeparant P ∉ I := by
  intro hSeparant
  have hSeparant0 := scalarDifferentialPolynomialSeparant_ne_zero hP.2.2.1
  by_cases hvars : (scalarDifferentialPolynomialSeparant P).vars.Nonempty
  · have hmin := hP.2.2.2 hSeparant hSeparant0 hvars
    have hOrderLe := scalarDifferentialPolynomialSeparant_order_le P
    have hOrder : scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialSeparant P) =
        scalarDifferentialPolynomialOrder P :=
      Nat.le_antisymm hOrderLe hmin.1
    exact (Nat.not_le_of_lt
      (scalarDifferentialPolynomialSeparant_leaderDegree_lt hP.2.2.1 hOrder))
        (hmin.2.1 hOrder.symm)
  · have hvars0 := Finset.not_nonempty_iff_eq_empty.mp hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars0
    have hc : (scalarDifferentialPolynomialSeparant P).coeff 0 ≠ 0 := by
      intro hc
      apply hSeparant0
      rw [hC, hc]
      simp
    have hunit : IsUnit (scalarDifferentialPolynomialSeparant P) := by
      rw [hC]
      exact IsUnit.map MvPolynomial.C hc.isUnit
    exact hItop (I.eq_top_of_isUnit_mem hSeparant hunit)

/-- Full dependency-closed characteristic-polynomial package for a nontrivial intermediate field:
the selected relation is repaired-rank-minimal and irreducible, and its correctly distinguished
initial and separant are both nonzero and outside the prime relation kernel. -/
theorem exists_differentialKernelCharacteristic_with_initial_separant
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E] [CharZero E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (u : G) (huF : (u : E) ∉ (⊥ : IntermediateField F E)) :
    ∃ P : DifferentialPolynomial Unit G,
      IsMinimalScalarDifferentialPolynomialRank
          (differentialIntermediateRelationIdeal G y : Set _) P ∧
        Irreducible P ∧
        scalarDifferentialPolynomialInitial P ≠ 0 ∧
        scalarDifferentialPolynomialInitial P ∉
          differentialIntermediateRelationIdeal G y ∧
        scalarDifferentialPolynomialSeparant P ≠ 0 ∧
        scalarDifferentialPolynomialSeparant P ∉
          differentialIntermediateRelationIdeal G y := by
  obtain ⟨P, hP, hIrreducible⟩ :=
    exists_irreducible_minimal_differentialKernelCharacteristic G hG u huF
  have hItop := differentialIntermediateRelationIdeal_ne_top G y
  exact ⟨P, hP, hIrreducible,
    scalarDifferentialPolynomialInitial_ne_zero hP.2.1,
    hP.initial_not_mem hItop,
    scalarDifferentialPolynomialSeparant_ne_zero hP.2.2.1,
    hP.separant_not_mem hItop⟩

end

end GaloisForLFunctions
