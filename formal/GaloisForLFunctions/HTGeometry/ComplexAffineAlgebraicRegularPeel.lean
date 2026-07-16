import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicOperations
import GaloisForLFunctions.HTGeometry.LocalizationIdealClearing
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalJacobianCodimension
import GaloisForLFunctions.HTGeometry.MvPolynomialRegularPeel

/-!
# A regular peel of a reduced complex affine algebraic set

A nonempty reduced affine algebraic set contains a nonempty principal-open maximal-minor locus.
The locus is a real regular level set, and its complement in the original set remains algebraic.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_regularPeel_complex_zeroLocus_of_localJacobianChart {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (p : PrimeSpectrum ((MvPolynomial (Fin n) ℂ) ⧸ I))
    (x : Fin n → ℂ)
    (hxI : x ∈ MvPolynomial.zeroLocus ℂ I)
    (hQ : polynomialPointIdeal I p = MvPolynomial.vanishingIdeal ℂ {x})
    (relation : Fin m → MvPolynomial (Fin n) ℂ)
    (hrelation : ∀ i, relation i ∈ I)
    (hlocalGen : Ideal.span (Set.range (fun i ↦
        algebraMap (MvPolynomial (Fin n) ℂ) (localPolynomialRing I p) (relation i))) =
      localPresentationKernel I p)
    (hgrad : LinearIndependent ℂ
      (fun i j ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (relation i)))) :
    ∃ (R : Set (Fin n → ℂ)),
      R.Nonempty ∧ R ⊆ MvPolynomial.zeroLocus ℂ I ∧
      IsLocalRegularLevelSetOfCodimAtLeast R (2 * m) ∧
      IsComplexAffineAlgebraic (MvPolynomial.zeroLocus ℂ I \ R) := by
  let q : Ideal ((MvPolynomial (Fin n) ℂ) ⧸ I) := p.asIdeal
  let Q : Ideal (MvPolynomial (Fin n) ℂ) :=
    q.comap (Ideal.Quotient.mk I)
  let P := Localization.AtPrime Q
  let S := Localization.AtPrime q
  letI : q.LiesOver Q := ⟨rfl⟩
  letI : Algebra P S := Localization.AtPrime.algebraOfLiesOver Q q
  have hT : Submonoid.map (Ideal.Quotient.mk I) Q.primeCompl =
      q.primeCompl := by
    exact q.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap P S) =
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    simpa using IsLocalization.ker_map S (Ideal.Quotient.mk I) hT
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    Ideal.span (Set.range relation)
  have hJmap : J.map (algebraMap (MvPolynomial (Fin n) ℂ) P) =
      Ideal.span (Set.range (fun i ↦
        algebraMap (MvPolynomial (Fin n) ℂ) P (relation i))) := by
    change (Ideal.span (Set.range relation)).map
      (algebraMap (MvPolynomial (Fin n) ℂ) P) = _
    rw [Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨relation i, ⟨i, rfl⟩, rfl⟩
  have hmapEq : I.map (algebraMap (MvPolynomial (Fin n) ℂ) P) =
      J.map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
    rw [← hker, hJmap]
    exact hlocalGen.symm
  obtain ⟨s, hs⟩ := exists_denominator_mul_le_of_localized_ideal_le
    Q.primeCompl I J (Ideal.fg_of_isNoetherianRing I) hmapEq.le
  let O : Set (Fin n → ℂ) :=
    {y | MvPolynomial.eval y (s : MvPolynomial (Fin n) ℂ) ≠ 0}
  have hO : IsOpen O := by
    have hc : Continuous (fun y : Fin n → ℂ ↦
        MvPolynomial.eval y (s : MvPolynomial (Fin n) ℂ)) :=
      (contDiff_mvPolynomial_eval_complex_real
        (s : MvPolynomial (Fin n) ℂ)).continuous
    have hz : IsClosed ((fun y : Fin n → ℂ ↦
        MvPolynomial.eval y (s : MvPolynomial (Fin n) ℂ)) ⁻¹'
          ({0} : Set ℂ)) := isClosed_singleton.preimage hc
    have hOeq : O = ((fun y : Fin n → ℂ ↦
        MvPolynomial.eval y (s : MvPolynomial (Fin n) ℂ)) ⁻¹'
          ({0} : Set ℂ))ᶜ := by
      ext y
      simp [O]
    rw [hOeq]
    exact hz.isOpen_compl
  have hxO : x ∈ O := by
    change MvPolynomial.eval x (s : MvPolynomial (Fin n) ℂ) ≠ 0
    intro hsx
    apply s.2
    change (s : MvPolynomial (Fin n) ℂ) ∈ polynomialPointIdeal I p
    rw [hQ, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hsx
  have hzero_of_mem_I : ∀ {y : Fin n → ℂ},
      y ∈ MvPolynomial.zeroLocus ℂ I →
      y ∈ complexMvPolynomialFamilyZeroLocus relation := by
    intro y hy
    change complexMvPolynomialFamilyEval relation y = 0
    funext i
    simpa [complexMvPolynomialFamilyEval, MvPolynomial.aeval_def] using
      hy (relation i) (hrelation i)
  have hxzero : x ∈ complexMvPolynomialFamilyZeroLocus relation :=
    hzero_of_mem_I hxI
  have hrow : LinearIndependent ℂ
      (complexMvPolynomialFamilyJacobian relation x).row := by
    simpa [complexMvPolynomialFamilyJacobian, Matrix.row] using hgrad
  have hjac : Function.Surjective
      (complexMvPolynomialFamilyJacobian relation x).mulVec :=
    (matrix_mulVec_surjective_iff_linearIndependent_rows _).mpr hrow
  have hcomplex : Function.Surjective
      (fderiv ℂ (complexMvPolynomialFamilyEval relation) x) :=
    (surjective_fderiv_complexMvPolynomialFamilyEval_iff_jacobian
      relation x).mpr hjac
  have hreal : Function.Surjective
      (fderiv ℝ (complexMvPolynomialFamilyEval relation) x) :=
    (surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_complex
      relation x).mpr hcomplex
  have hxnotdefect :
      x ∉ complexMvPolynomialFamilyJacobianRankDefect relation :=
    (surjective_fderiv_complexMvPolynomialFamilyEval_real_iff_notMem_rankDefect
      relation x).mp hreal
  let R : Set (Fin n → ℂ) :=
    complexMvPolynomialFamilyMaximalMinorRegularLocus relation ∩ O
  have hxR : x ∈ R := by
    exact ⟨⟨hxzero, hxnotdefect⟩, hxO⟩
  have hRreg : IsLocalRegularLevelSetOfCodimAtLeast R (2 * m) := by
    exact (complexMvPolynomialFamilyMaximalMinorRegularLocus_isLocalRegularLevelSet
      relation).inter_isOpen hO
  have hRsub : R ⊆ MvPolynomial.zeroLocus ℂ I := by
    intro y hy
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro f hf
    have hJker : J ≤ RingHom.ker (MvPolynomial.aeval y) := by
      change Ideal.span (Set.range relation) ≤
        RingHom.ker (MvPolynomial.aeval y)
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.aeval y (relation i) = 0
      have hyzero := hy.1.1
      change complexMvPolynomialFamilyEval relation y = 0 at hyzero
      simpa [complexMvPolynomialFamilyEval, MvPolynomial.aeval_def] using
        congrFun hyzero i
    have hsf : (s : MvPolynomial (Fin n) ℂ) * f ∈ J := hs f hf
    have hprod : MvPolynomial.aeval y
        ((s : MvPolynomial (Fin n) ℂ) * f) = 0 :=
      RingHom.mem_ker.mp (hJker hsf)
    rw [map_mul] at hprod
    have hsne : MvPolynomial.aeval y
        (s : MvPolynomial (Fin n) ℂ) ≠ 0 := by
      simpa [O, MvPolynomial.aeval_def] using hy.2
    exact (mul_eq_zero.mp hprod).resolve_left hsne
  let Zs : Set (Fin n → ℂ) :=
    {y | MvPolynomial.eval y (s : MvPolynomial (Fin n) ℂ) = 0}
  have hZs : IsComplexAffineAlgebraic Zs := by
    have h := isComplexAffineAlgebraic_zeroLocus_finite_family
      (fun _ : Fin 1 ↦ (s : MvPolynomial (Fin n) ℂ))
    convert h using 1
    ext y
    simp [Zs]
  have hrem : MvPolynomial.zeroLocus ℂ I \ R =
      (MvPolynomial.zeroLocus ℂ I ∩ Zs) ∪
      (MvPolynomial.zeroLocus ℂ I ∩
        complexMvPolynomialFamilyJacobianRankDefect relation) := by
    ext y
    constructor
    · rintro ⟨hyI, hyR⟩
      by_cases hsy : MvPolynomial.eval y
          (s : MvPolynomial (Fin n) ℂ) = 0
      · exact Or.inl ⟨hyI, hsy⟩
      · apply Or.inr
        refine ⟨hyI, ?_⟩
        by_contra hydefect
        apply hyR
        exact ⟨⟨hzero_of_mem_I hyI, hydefect⟩, hsy⟩
    · rintro (hy | hy)
      · refine ⟨hy.1, ?_⟩
        intro hyR
        exact hyR.2 hy.2
      · refine ⟨hy.1, ?_⟩
        intro hyR
        exact hyR.1.2 hy.2
  refine ⟨R, ⟨x, hxR⟩, hRsub, hRreg, ?_⟩
  rw [hrem]
  exact IsComplexAffineAlgebraic.union
    ((isComplexAffineAlgebraic_zeroLocus I).inter hZs)
    ((isComplexAffineAlgebraic_zeroLocus I).inter
      (isComplexAffineAlgebraic_complexMvPolynomialFamilyJacobianRankDefect relation))

set_option maxHeartbeats 4000000 in
/-- Every nonempty reduced complex affine algebraic set has a nonempty regular peel whose
algebraic remainder is strictly smaller. -/
theorem exists_regularPeel_complex_zeroLocus_of_proper_radical {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : I ≠ ⊤) (hrad : I.IsRadical) :
    ∃ (m : ℕ) (R : Set (Fin n → ℂ)),
      R.Nonempty ∧ R ⊆ MvPolynomial.zeroLocus ℂ I ∧
      IsLocalRegularLevelSetOfCodimAtLeast R (2 * m) ∧
      IsComplexAffineAlgebraic (MvPolynomial.zeroLocus ℂ I \ R) := by
  obtain ⟨p, x, hxI, hQ, hlocal⟩ :=
    exists_complex_zero_formallySmooth_of_radicalIdeal I hI hrad
  obtain ⟨m, relation, hrelation, hlocalGen, hgrad⟩ :=
    exists_localJacobianChart_of_formallySmooth_point I p x hQ hlocal
  obtain ⟨R, hRne, hRsub, hRreg, hrem⟩ :=
    exists_regularPeel_complex_zeroLocus_of_localJacobianChart
      I p x hxI hQ relation hrelation hlocalGen hgrad
  exact ⟨m, R, hRne, hRsub, hRreg, hrem⟩

set_option maxHeartbeats 4000000 in
/-- A global complex Krull-codimension bound is inherited by a nonempty smooth peel.  The peel is
a real regular level set of at least twice the complex codimension, and its remainder stays
algebraic. -/
theorem exists_regularPeel_complex_zeroLocus_of_proper_radical_with_codim
    {n c : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : I ≠ ⊤) (hrad : I.IsRadical)
    (hdim : ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ I) + c ≤
      (n : WithBot ℕ∞)) :
    ∃ (m : ℕ) (R : Set (Fin n → ℂ)),
      c ≤ m ∧ R.Nonempty ∧ R ⊆ MvPolynomial.zeroLocus ℂ I ∧
      IsLocalRegularLevelSetOfCodimAtLeast R (2 * c) ∧
      IsComplexAffineAlgebraic (MvPolynomial.zeroLocus ℂ I \ R) := by
  obtain ⟨p, x, hxI, hQ, hlocal⟩ :=
    exists_complex_zero_formallySmooth_of_radicalIdeal I hI hrad
  obtain ⟨m, relation, hcm, hrelation, hlocalGen, hgrad⟩ :=
    exists_localJacobianChart_of_formallySmooth_point_with_codim
      I p x hQ hlocal hdim
  obtain ⟨R, hRne, hRsub, hRreg, hrem⟩ :=
    exists_regularPeel_complex_zeroLocus_of_localJacobianChart
      I p x hxI hQ relation hrelation hlocalGen hgrad
  have hRregc : IsLocalRegularLevelSetOfCodimAtLeast R (2 * c) := by
    intro y hy
    obtain ⟨k, hmk, U, hU, hyU, g, hg, hzero, hsurj⟩ := hRreg y hy
    exact ⟨k, (Nat.mul_le_mul_left 2 hcm).trans hmk,
      U, hU, hyU, g, hg, hzero, hsurj⟩
  exact ⟨m, R, hcm, hRne, hRsub, hRregc, hrem⟩

end

end GaloisForLFunctions.HTGeometry
