import GaloisForLFunctions.HTGeometry.MultipleGammaMonomialCoefficients
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaDeepPacketFaithfulness

/-!
# The exact squarefree annihilator

Difference monomials of different width land in different face packets, and the pair
`(face, exponent)` is a faithful coordinate on the union of all packets retaining two periods.
Grading an operator by the support of its monomials therefore expresses its action as a single
combination over that faithful coordinate, so nothing can cancel between widths.

Combined with the common-support independence, an operator sends the source into the differentially
algebraic locus exactly when every monomial uses at least `r` distinct directions, that is exactly
when it lies in the squarefree Veronese ideal.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The pair coordinate -/

/-- The translate of a face coordinate indexed by a `(face, exponent)` pair. -/
def pairTranslate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (p : Finset ι × (ι →₀ ℕ)) : meroField (Set.univ : Set ℂ) :=
  faceTranslate τ hτ p.1 p.2

/-- A pair is admissible when its face retains two periods and its exponent is supported on the
deleted directions. -/
def PairCarried (p : Finset ι × (ι →₀ ℕ)) : Prop :=
  2 ≤ ((p.1)ᶜ).card ∧ p.2.support ⊆ p.1

theorem pairTranslate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {p : Finset ι × (ι →₀ ℕ)} (hp : PairCarried p) :
    pairTranslate τ hτ p ∈ facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} :=
  Set.mem_iUnion₂.mpr ⟨p.1, hp.1,
    ⟨natShift τ p.2, natShift_mem_faceShiftLattice τ hp.2, rfl⟩⟩

theorem pairTranslate_inj (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ)
    {p q : Finset ι × (ι →₀ ℕ)} (hp : PairCarried p) (hq : PairCarried q)
    (h : pairTranslate τ hτ p = pairTranslate τ hτ q) : p = q := by
  obtain ⟨hface, hshift⟩ :=
    multipleEllipticGammaDeepCoordinate_injective τ hτ hQ hp.1 hq.1
      (natShift_mem_faceShiftLattice τ hp.2) (natShift_mem_faceShiftLattice τ hq.2) h
  exact Prod.ext hface (natShift_injective τ hQ hshift)

/-- Synthesis from a coefficient function on `(face, exponent)` pairs. -/
def pairSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (pairTranslate τ hτ) C

/-- **A nonzero admissible pair coefficient synthesizes a hypertranscendental germ.** -/
theorem hypertranscendentalOver_pairSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ}
    (hcarry : ∀ p ∈ C.support, PairCarried p) (hC : C ≠ 0) :
    HypertranscendentalOver ℂ (pairSynth τ hτ C) := by
  classical
  have hmem : ∀ k : (C.support : Finset (Finset ι × (ι →₀ ℕ))),
      pairTranslate τ hτ (k : Finset ι × (ι →₀ ℕ)) ∈
        facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} :=
    fun k => pairTranslate_mem τ hτ (hcarry (k : Finset ι × (ι →₀ ℕ)) k.2)
  have hinj : Function.Injective
      (fun k : (C.support : Finset (Finset ι × (ι →₀ ℕ))) =>
        pairTranslate τ hτ (k : Finset ι × (ι →₀ ℕ))) := by
    intro a b hab
    exact Subtype.ext (pairTranslate_inj τ hτ hQ
      (hcarry (a : Finset ι × (ι →₀ ℕ)) a.2) (hcarry (b : Finset ι × (ι →₀ ℕ)) b.2) hab)
  have hindep : DifferentialIndependent ℂ
      (fun k : (C.support : Finset (Finset ι × (ι →₀ ℕ))) =>
        pairTranslate τ hτ (k : Finset ι × (ι →₀ ℕ))) :=
    multipleEllipticGammaSelectedFaces_differentialIndependent τ hτ hQ hι _ hmem hinj
  have hcne : (fun k : (C.support : Finset (Finset ι × (ι →₀ ℕ))) =>
      C (k : Finset ι × (ι →₀ ℕ))) ≠ 0 := by
    obtain ⟨p₀, hp₀⟩ := Finsupp.support_nonempty_iff.mpr hC
    intro hzero
    exact (Finsupp.mem_support_iff.mp hp₀) (congrFun hzero ⟨p₀, hp₀⟩)
  have hsum := hypertranscendentalOver_linearCombination_of_ne_zero
    (C := ℂ) (K := meroField (Set.univ : Set ℂ))
    meroField_deriv_algebraMap_complex_rationalBase _ hcne _ hindep
  have hval : ∑ k : (C.support : Finset (Finset ι × (ι →₀ ℕ))),
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (C (k : Finset ι × (ι →₀ ℕ))) *
          pairTranslate τ hτ (k : Finset ι × (ι →₀ ℕ)) = pairSynth τ hτ C := by
    rw [pairSynth, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort C.support]
    exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
  rwa [hval] at hsum

/-! ## Grading a monomial by its face -/

/-- Place an exponent coefficient function on one face. -/
def faceEmbed (S : Finset ι) (n : ι →₀ ℕ) : Finset ι × (ι →₀ ℕ) := (S, n)

omit [Fintype ι] [DecidableEq ι] in
theorem faceEmbed_injective (S : Finset ι) : Function.Injective (faceEmbed S) :=
  fun _ _ h => congrArg Prod.snd h

theorem natSynth_eq_pairSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) :
    natSynth τ hτ S c = pairSynth τ hτ (Finsupp.mapDomain (faceEmbed S) c) := by
  rw [pairSynth, Finsupp.linearCombination_mapDomain, natSynth]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem mapDomain_faceEmbed_apply (S : Finset ι) (c : (ι →₀ ℕ) →₀ ℂ) (n : ι →₀ ℕ) :
    Finsupp.mapDomain (faceEmbed S) c (S, n) = c n :=
  Finsupp.mapDomain_apply (f := faceEmbed S) (faceEmbed_injective S) c n

omit [Fintype ι] [DecidableEq ι] in
theorem mapDomain_faceEmbed_apply_of_ne {S S' : Finset ι} (hne : S ≠ S')
    (c : (ι →₀ ℕ) →₀ ℂ) (n : ι →₀ ℕ) :
    Finsupp.mapDomain (faceEmbed S) c (S', n) = 0 := by
  classical
  refine Finsupp.mapDomain_notin_range c _ ?_
  rintro ⟨m, hm⟩
  exact hne (congrArg Prod.fst hm)

/-! ## The exact annihilator -/

/-- **Reverse inclusion of the annihilator.**  If some monomial of a difference operator uses fewer
than the full number of directions needed to reach a face with at most one surviving period, the
operator does not send the source into the differentially algebraic locus. -/
theorem hypertranscendentalOver_xApply_of_notMem_veroneseIdeal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    {P : MvPolynomial ι ℂ} (hP : P ∉ veroneseIdeal ℂ ι r) :
    HypertranscendentalOver (RatFunc ℂ)
      (xApply τ P (multipleEllipticGammaLogDerivMero τ hτ)) := by
  classical
  have hι : 2 ≤ Fintype.card ι := by
    by_contra hlt
    exact hP (by
      have hr : r = 0 := by omega
      subst hr
      simp [veroneseIdeal, veroneseGens])
  -- narrow monomials: those whose support leaves at least two periods
  set narrow : Finset (ι →₀ ℕ) :=
    P.support.filter (fun d => 2 ≤ ((d.support)ᶜ).card) with hnarrow
  set wide : Finset (ι →₀ ℕ) :=
    P.support.filter (fun d => ¬ (2 ≤ ((d.support)ᶜ).card)) with hwide
  have hnarrowNonempty : narrow.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    refine hP ((mem_veroneseIdeal_iff P).mpr fun d hd => ?_)
    have hdmem : d ∈ P.support := MvPolynomial.mem_support_iff.mpr hd
    have hnot : ¬ (2 ≤ ((d.support)ᶜ).card) := by
      intro hc
      have hdn : d ∈ narrow := Finset.mem_filter.mpr ⟨hdmem, hc⟩
      rw [hempty] at hdn
      exact absurd hdn (Finset.notMem_empty d)
    have htotal := Finset.card_add_card_compl d.support
    rw [hcard] at htotal
    omega
  -- the wide part is differentially algebraic
  have hwideDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (∑ d ∈ wide, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
        xMonomialApply τ d (multipleEllipticGammaLogDerivMero τ hτ)) := by
    refine differentialAlgebraicOver_finset_sum _ fun d hd => ?_
    refine differentialAlgebraicOver_complexMul _ ?_
    refine differentialAlgebraicOver_xMonomialApply τ hτ d ?_
    have hnot := (Finset.mem_filter.mp hd).2
    have htotal := Finset.card_add_card_compl d.support
    rw [hcard] at htotal
    intro i j hi hj
    exact Finset.card_le_one.mp (by omega) i (Finset.mem_compl.mpr hi) j (Finset.mem_compl.mpr hj)
  -- the narrow part is a pair combination
  set C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ :=
    ∑ d ∈ narrow, MvPolynomial.coeff d P •
      Finsupp.mapDomain (faceEmbed d.support) (listCoeff (multiDegreeList d)) with hC
  have hface : ∀ d : ι →₀ ℕ, (multiDegreeList d).toFinset = d.support :=
    fun d => multiDegreeList_toFinset d
  have hnarrowVal : ∑ d ∈ narrow,
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
        xMonomialApply τ d (multipleEllipticGammaLogDerivMero τ hτ) = pairSynth τ hτ C := by
    rw [hC, pairSynth, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, ← pairSynth, ← natSynth_eq_pairSynth, xMonomialApply,
      listShiftDiff_eq_natSynth τ hτ, hface d, Algebra.smul_def]
  -- a maximal-degree narrow monomial witnesses a nonzero pair coefficient
  obtain ⟨d₀, hd₀mem, hd₀max⟩ :=
    narrow.exists_max_image (fun d => ∑ i, d i) hnarrowNonempty
  have hd₀P : MvPolynomial.coeff d₀ P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp hd₀mem).1
  have hd₀deep : 2 ≤ ((d₀.support)ᶜ).card := (Finset.mem_filter.mp hd₀mem).2
  set p₀ : Finset ι × (ι →₀ ℕ) := (d₀.support, listTop (multiDegreeList d₀)) with hp₀
  have hCp₀ : C p₀ = MvPolynomial.coeff d₀ P := by
    rw [hC]
    rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_single d₀ ?_ (fun h => absurd hd₀mem h) |>.trans ?_
    · intro d hd hne
      by_cases hsupp : d.support = d₀.support
      · have hzero : listCoeff (multiDegreeList d) (listTop (multiDegreeList d₀)) = 0 := by
          by_contra hnz
          have hmem : listTop (multiDegreeList d₀) ∈ (listCoeff (multiDegreeList d)).support :=
            Finsupp.mem_support_iff.mpr hnz
          have hle := listCoeff_support_le (multiDegreeList d) hmem
          have hdeg₀ := sum_listTop_multiDegreeList d₀
          have hdegd := sum_listTop_multiDegreeList d
          rw [hsupp] at hdegd
          have hmax := hd₀max d hd
          have hdegle : ∑ i, listTop (multiDegreeList d) i ≤
              ∑ i, listTop (multiDegreeList d₀) i := by omega
          have heq := natExp_eq_of_le_of_degree_le hle hdegle
          refine hne (Finsupp.ext fun i => ?_)
          have hi := congrArg (fun n : ι →₀ ℕ => n i) heq
          simp only [listTop_multiDegreeList_apply] at hi
          by_cases hiS : i ∈ d₀.support
          · have h1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr
              (Finsupp.mem_support_iff.mp (by rw [hsupp]; exact hiS))
            have h2 : 1 ≤ d₀ i := Nat.one_le_iff_ne_zero.mpr
              (Finsupp.mem_support_iff.mp hiS)
            omega
          · have h1 : d i = 0 := Finsupp.notMem_support_iff.mp (by rw [hsupp]; exact hiS)
            have h2 : d₀ i = 0 := Finsupp.notMem_support_iff.mp hiS
            rw [h1, h2]
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp₀]
        rw [hsupp, mapDomain_faceEmbed_apply, hzero, mul_zero]
      · simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp₀]
        rw [mapDomain_faceEmbed_apply_of_ne hsupp, mul_zero]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp₀]
      rw [mapDomain_faceEmbed_apply, listCoeff_top, mul_one]
  have hCne : C ≠ 0 := by
    intro hzero
    apply hd₀P
    rw [← hCp₀, hzero]
    rfl
  have hCcarry : ∀ p ∈ C.support, PairCarried p := by
    intro p hp
    rw [hC] at hp
    obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hp)
    have hpd' : p ∈ (Finsupp.mapDomain (faceEmbed d.support)
        (listCoeff (multiDegreeList d))).support := Finsupp.support_smul hpd
    rw [Finsupp.mapDomain_support_of_injective (faceEmbed_injective d.support)] at hpd'
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hpd'
    refine ⟨(Finset.mem_filter.mp hd).2, ?_⟩
    have hcar := carriedBy_listCoeff (multiDegreeList d) n hn
    rwa [hface d] at hcar
  -- assemble
  have hnarrowHT : HypertranscendentalOver ℂ (pairSynth τ hτ C) :=
    hypertranscendentalOver_pairSynth τ hτ hQ hι hCcarry hCne
  have hsplit : xApply τ P (multipleEllipticGammaLogDerivMero τ hτ) =
      pairSynth τ hτ C +
        ∑ d ∈ wide, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          xMonomialApply τ d (multipleEllipticGammaLogDerivMero τ hτ) := by
    rw [xApply, ← hnarrowVal, hnarrow, hwide, Finset.sum_filter_add_sum_filter_not]
  intro hDA
  rw [hsplit] at hDA
  have hnarrowDA : DifferentialAlgebraicOver (RatFunc ℂ) (pairSynth τ hτ C) := by
    have hsub := differentialAlgebraicOver_sub hDA hwideDA
    simpa using hsub
  exact hnarrowHT (HTGeometry.differentialAlgebraicOver_complex_of_ratFunc hnarrowDA)

/-- **Exact squarefree annihilator.**  For a period family of `r + 1` members, a difference
operator sends the source into the differentially algebraic locus exactly when it lies in the
squarefree Veronese ideal `I_r`. -/
theorem differentialAlgebraicOver_xApply_iff_mem_veroneseIdeal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (P : MvPolynomial ι ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (xApply τ P (multipleEllipticGammaLogDerivMero τ hτ)) ↔
      P ∈ veroneseIdeal ℂ ι r := by
  constructor
  · intro hDA
    by_contra hP
    exact hypertranscendentalOver_xApply_of_notMem_veroneseIdeal τ hτ hQ r hcard hP hDA
  · exact differentialAlgebraicOver_xApply_of_mem_veroneseIdeal_of_card τ hτ r hcard

end

end GaloisForLFunctions
