import GaloisForLFunctions.HTGeometry.MultipleSineAnnihilatorExact
import GaloisForLFunctions.HTGeometry.MultipleSineCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.DifferentialIndependentPerturbation
import GaloisForLFunctions.HTGeometry.DiffTranslateOperatorAction
import GaloisForLFunctions.HTGeometry.SourceBoundaryQuotientMatroid

/-!
# The differential matroid of a family of difference-differential operators on the multiple sine

Applying a difference-differential operator to the multiple-sine source produces, modulo the
differentially algebraic locus, a differential-operator row applied to translates of the proper-face
coordinates: the pair `(face, exponent)` is the coordinate, and the row entry is the signed
combinatorial coefficient of the operator.  Since the face translates are differentially independent
and differential independence is insensitive to differentially algebraic perturbations, the
nonlinear differential matroid of any finite family of such outputs is the ordinary row matroid over
the fraction field of `ℂ[∂]`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msomDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The action of a difference-differential operator -/

/-- The action of a difference-differential operator: difference monomials in the structural
directions carry differential operators as coefficients. -/
def xDiffApply (ω : ι → ℂ) (P : MvPolynomial ι (Polynomial ℂ))
    (y : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  ∑ d ∈ P.support,
    differentialOperatorApply (MvPolynomial.coeff d P) (xMonomialApply ω d y)

/-- The pair-coefficient row of a difference-differential operator: the coefficient carried by the
`(face, exponent)` coordinate. -/
def sinePairRow (P : MvPolynomial ι (Polynomial ℂ)) :
    (Finset ι × (ι →₀ ℕ)) →₀ Polynomial ℂ :=
  ∑ d ∈ P.support.filter (fun d => 2 ≤ ((d.support)ᶜ).card),
    ((-1 : Polynomial ℂ) ^ (d.support).card * MvPolynomial.coeff d P) •
      Finsupp.mapDomain (faceEmbed d.support)
        (Finsupp.mapRange (Polynomial.C : ℂ → Polynomial ℂ) Polynomial.C_0
          (listCoeff (multiDegreeList d)))

/-! ### Rational inputs stay rational -/

theorem differentialOperatorApply_mem_rationalCoordinateField (a : Polynomial ℂ)
    {r : meroField (Set.univ : Set ℂ)} (hr : r ∈ meromorphicRationalCoordinateField) :
    differentialOperatorApply a r ∈ meromorphicRationalCoordinateField := by
  classical
  rw [differentialOperatorApply, Polynomial.sum_def]
  refine sum_mem fun n _ => mul_mem ?_ ?_
  · exact meromorphicRationalCoordinateField.algebraMap_mem _
  · exact meromorphicRationalCoordinateField_derivationClosed.differentialJet_mem hr n

/-! ### One monomial, modulo the rational coordinate field -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The pair row of a single narrow monomial reproduces the operator action on it, modulo the
rational coordinate field. -/
theorem xMonomial_sub_pairRow_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (a : Polynomial ℂ) {d : ι →₀ ℕ} (hd : 2 ≤ ((d.support)ᶜ : Finset ι).card) :
    differentialOperatorApply a (xMonomialApply ω d (sineFaceCoord ω hω ∅))
        - (((-1 : Polynomial ℂ) ^ (d.support).card * a) •
            Finsupp.mapDomain (faceEmbed d.support)
              (Finsupp.mapRange (Polynomial.C : ℂ → Polynomial ℂ) Polynomial.C_0
                (listCoeff (multiDegreeList d)))).sum
          (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p))
      ∈ meromorphicRationalCoordinateField := by
  classical
  set c : (ι →₀ ℕ) →₀ ℂ := listCoeff (multiDegreeList d) with hc
  set α : Polynomial ℂ := (-1 : Polynomial ℂ) ^ (d.support).card * a with hα
  have hzero : ∀ p : Finset ι × (ι →₀ ℕ),
      differentialOperatorApply (0 : Polynomial ℂ) (sinePairTranslate ω hω p) = 0 :=
    fun p => differentialOperatorApply_zero _
  have hrow : ((α • Finsupp.mapDomain (faceEmbed d.support)
        (Finsupp.mapRange (Polynomial.C : ℂ → Polynomial ℂ) Polynomial.C_0 c)).sum
      (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p)))
      = ∑ n ∈ c.support, differentialOperatorApply (α * Polynomial.C (c n))
        (sineFaceTranslate ω hω d.support n) := by
    rw [Finsupp.sum_smul_index' (fun p => hzero p),
      Finsupp.sum_mapDomain_index_inj (faceEmbed_injective d.support),
      Finsupp.sum_mapRange_index (fun n => by simp)]
    rfl
  have hlin : ∑ n ∈ c.support, differentialOperatorApply (α * Polynomial.C (c n))
        (sineFaceTranslate ω hω d.support n)
      = differentialOperatorApply α (sineNatSynth ω hω d.support c) := by
    rw [sineNatSynth_eq_sum, differentialOperatorApply_finset_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_comm α (Polynomial.C (c n)), differentialOperatorApply_C_mul,
      differentialOperatorApply_algebraMap_complex_mul]
  have hsynth := listShiftDiff_sub_sineNatSynth_mem ω hω (multiDegreeList d)
    (by rw [multiDegreeList_toFinset d]; omega)
  rw [multiDegreeList_toFinset d, ← hc] at hsynth
  have hpow : ((-1 : meroField (Set.univ : Set ℂ)) ^ (d.support).card)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((-1 : ℂ) ^ (d.support).card) := by
    rw [map_pow, map_neg, map_one]
  have hsign : differentialOperatorApply α (sineNatSynth ω hω d.support c)
      = differentialOperatorApply a
        ((-1 : meroField (Set.univ : Set ℂ)) ^ (d.support).card *
          sineNatSynth ω hω d.support c) := by
    rw [hpow, differentialOperatorApply_algebraMap_complex_mul, hα,
      show ((-1 : Polynomial ℂ) ^ (d.support).card)
        = Polynomial.C ((-1 : ℂ) ^ (d.support).card) by rw [map_pow, map_neg, map_one],
      differentialOperatorApply_C_mul]
  rw [hrow, hlin, hsign, ← differentialOperatorApply_sub, xMonomialApply,
    listShiftDiff_eq_listShiftDiff]
  exact differentialOperatorApply_mem_rationalCoordinateField a hsynth


/-! ### The whole operator, modulo the differentially algebraic locus -/

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The operator action is a pair row, modulo differential algebraicity.** -/
theorem xDiffApply_sub_pairRowSum_differentialAlgebraic (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (P : MvPolynomial ι (Polynomial ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (xDiffApply ω P (sineFaceCoord ω hω ∅)
        - (sinePairRow P).sum
            (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p))) := by
  classical
  set narrow : Finset (ι →₀ ℕ) :=
    P.support.filter (fun d => 2 ≤ ((d.support)ᶜ : Finset ι).card) with hnarrow
  set wide : Finset (ι →₀ ℕ) :=
    P.support.filter (fun d => ¬ (2 ≤ ((d.support)ᶜ : Finset ι).card)) with hwide
  set rowOf : (ι →₀ ℕ) → ((Finset ι × (ι →₀ ℕ)) →₀ Polynomial ℂ) := fun d =>
    ((-1 : Polynomial ℂ) ^ (d.support).card * MvPolynomial.coeff d P) •
      Finsupp.mapDomain (faceEmbed d.support)
        (Finsupp.mapRange (Polynomial.C : ℂ → Polynomial ℂ) Polynomial.C_0
          (listCoeff (multiDegreeList d))) with hrowOf
  have hsplit : xDiffApply ω P (sineFaceCoord ω hω ∅)
      = (∑ d ∈ narrow, differentialOperatorApply (MvPolynomial.coeff d P)
            (xMonomialApply ω d (sineFaceCoord ω hω ∅)))
        + ∑ d ∈ wide, differentialOperatorApply (MvPolynomial.coeff d P)
            (xMonomialApply ω d (sineFaceCoord ω hω ∅)) := by
    rw [xDiffApply, hnarrow, hwide, Finset.sum_filter_add_sum_filter_not]
  have hrowsum : (sinePairRow P).sum
        (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p))
      = ∑ d ∈ narrow, (rowOf d).sum
        (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p)) := by
    rw [sinePairRow, ← hnarrow]
    exact (Finsupp.sum_finset_sum_index
      (fun p => differentialOperatorApply_zero (sinePairTranslate ω hω p))
      (fun p b₁ b₂ => differentialOperatorApply_add b₁ b₂ (sinePairTranslate ω hω p))).symm
  have hnarrowRat : (∑ d ∈ narrow, differentialOperatorApply (MvPolynomial.coeff d P)
          (xMonomialApply ω d (sineFaceCoord ω hω ∅)))
        - ∑ d ∈ narrow, (rowOf d).sum
          (fun p b => differentialOperatorApply b (sinePairTranslate ω hω p))
      ∈ meromorphicRationalCoordinateField := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun d hd => ?_
    exact xMonomial_sub_pairRow_mem ω hω (MvPolynomial.coeff d P)
      (Finset.mem_filter.mp hd).2
  have hwideDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (∑ d ∈ wide, differentialOperatorApply (MvPolynomial.coeff d P)
        (xMonomialApply ω d (sineFaceCoord ω hω ∅))) := by
    refine _root_.HTGeometry.differentialAlgebraicOver_finset_sum wide _ fun d hd => ?_
    refine differentialAlgebraicOver_differentialOperatorApply _ ?_
    have hle : (((multiDegreeList d).toFinset)ᶜ : Finset ι).card ≤ 1 := by
      rw [multiDegreeList_toFinset d]
      have hnot := (Finset.mem_filter.mp hd).2
      omega
    have hDA := differentialAlgebraicOver_listShiftDiff_of_compl_le_one ω hω
      (multiDegreeList d) hle
    rwa [xMonomialApply, listShiftDiff_eq_listShiftDiff]
  rw [hsplit, hrowsum]
  have hid : ∀ A B C : meroField (Set.univ : Set ℂ), A + B - C = (A - C) + B := by
    intro A B C
    ring
  rw [hid]
  exact differentialAlgebraicOver_add
    (differentialAlgebraicOver_ratFunc_of_mem_rationalCoordinateField hnarrowRat) hwideDA

/-! ### The pair index of a finite operator family -/

theorem pairCarried_of_mem_sinePairRow_support {P : MvPolynomial ι (Polynomial ℂ)}
    {p : Finset ι × (ι →₀ ℕ)} (hp : p ∈ (sinePairRow P).support) : PairCarried p := by
  classical
  rw [sinePairRow] at hp
  obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hp)
  have hpd' : p ∈ (Finsupp.mapDomain (faceEmbed d.support)
      (Finsupp.mapRange (Polynomial.C : ℂ → Polynomial ℂ) Polynomial.C_0
        (listCoeff (multiDegreeList d)))).support := Finsupp.support_smul hpd
  rw [Finsupp.mapDomain_support_of_injective (faceEmbed_injective d.support)] at hpd'
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hpd'
  refine ⟨(Finset.mem_filter.mp hd).2, ?_⟩
  have hn' : n ∈ (listCoeff (multiDegreeList d)).support := Finsupp.support_mapRange hn
  have hcar := carriedBy_listCoeff (multiDegreeList d) n hn'
  rwa [multiDegreeList_toFinset d] at hcar

/-- The finite set of `(face, exponent)` pairs carrying a finite operator family. -/
def sinePairIndex {ρ : Type} [Fintype ρ] (P : ρ → MvPolynomial ι (Polynomial ℂ)) :
    Finset (Finset ι × (ι →₀ ℕ)) :=
  Finset.univ.biUnion (fun k => (sinePairRow (P k)).support)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- **The complete matroid law for difference-differential operators on the multiple sine.**  For
every finite family of operators, the nonlinear differential matroid of the outputs is the ordinary
row matroid of the pair-coefficient rows over the fraction field of `ℂ[∂]`. -/
theorem multipleSineOperatorFamilyMatroid {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {ρ : Type} [Fintype ρ] [DecidableEq ρ] (P : ρ → MvPolynomial ι (Polynomial ℂ)) :
    GaloisForLFunctions.differentialFamilyMatroid (F := ℂ)
        (fun k => xDiffApply (fun k => μ * (rad k : ℂ)) (P k)
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅))
      = differentialOperatorRowMatroid
        (fun k (p : ↥(sinePairIndex P)) =>
          sinePairRow (P k) (p : Finset ι × (ι →₀ ℕ))) := by
  classical
  set x : ↥(sinePairIndex P) → meroField (Set.univ : Set ℂ) := fun p =>
    sinePairTranslate (fun k => μ * (rad k : ℂ)) hω (p : Finset ι × (ι →₀ ℕ)) with hx
  have hcarry : ∀ p : ↥(sinePairIndex P), PairCarried (p : Finset ι × (ι →₀ ℕ)) := by
    intro p
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp p.2
    exact pairCarried_of_mem_sinePairRow_support hk
  have hxmem : ∀ p : ↥(sinePairIndex P), x p ∈
      sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω {J : Finset ι | 2 ≤ (Jᶜ).card} :=
    fun p => sinePairTranslate_mem _ hω (hcarry p)
  have hxinj : Function.Injective x := by
    intro a b hab
    exact Subtype.ext (sinePairTranslate_inj hrad hind hω (hcarry a) (hcarry b) hab)
  have hrow : ∀ k : ρ,
      differentialOperatorRowApply
          (fun k (p : ↥(sinePairIndex P)) => sinePairRow (P k) (p : Finset ι × (ι →₀ ℕ))) x k
        = (sinePairRow (P k)).sum (fun p b =>
            differentialOperatorApply b
              (sinePairTranslate (fun k => μ * (rad k : ℂ)) hω p)) := by
    intro k
    rw [differentialOperatorRowApply, Finset.sum_coe_sort (sinePairIndex P)
      (fun p => differentialOperatorApply (sinePairRow (P k) p)
        (sinePairTranslate (fun k => μ * (rad k : ℂ)) hω p))]
    refine (Finsupp.sum_of_support_subset _ ?_ _ ?_).symm
    · intro p hp
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hp⟩
    · intro p _
      exact differentialOperatorApply_zero _
  have hDA : ∀ k : ρ, DifferentialAlgebraicOver ℂ
      (differentialOperatorRowApply
          (fun k (p : ↥(sinePairIndex P)) => sinePairRow (P k) (p : Finset ι × (ι →₀ ℕ))) x k
        - xDiffApply (fun k => μ * (rad k : ℂ)) (P k)
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)) := by
    intro k
    rw [hrow k]
    have hsub := xDiffApply_sub_pairRowSum_differentialAlgebraic
      (fun k => μ * (rad k : ℂ)) hω (P k)
    have hneg := differentialAlgebraicOver_neg hsub
    have hid : -(xDiffApply (fun k => μ * (rad k : ℂ)) (P k)
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)
        - (sinePairRow (P k)).sum (fun p b =>
            differentialOperatorApply b
              (sinePairTranslate (fun k => μ * (rad k : ℂ)) hω p)))
        = (sinePairRow (P k)).sum (fun p b =>
            differentialOperatorApply b
              (sinePairTranslate (fun k => μ * (rad k : ℂ)) hω p))
          - xDiffApply (fun k => μ * (rad k : ℂ)) (P k)
            (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅) := by ring
    rw [hid] at hneg
    exact HTGeometry.differentialAlgebraicOver_complex_of_ratFunc hneg
  rw [differentialFamilyMatroid_congr_of_sub_differentialAlgebraic (F := ℂ) hDA]
  exact multipleSineCompleteDifferentialMatroid hrad hind hω x hxmem hxinj _


end

end GaloisForLFunctions.HTGeometry
