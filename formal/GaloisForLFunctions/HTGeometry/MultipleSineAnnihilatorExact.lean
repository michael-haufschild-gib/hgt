import GaloisForLFunctions.HTGeometry.MultipleSineMonomialCoefficients
import GaloisForLFunctions.HTGeometry.MultipleGammaAnnihilatorExact

/-!
# The exact squarefree annihilator of the multiple sine

Difference monomials of different width land in different face packets, and the pair
`(face, exponent)` is a faithful coordinate on the union of all packets retaining two periods.
Grading an operator by the support of its monomials therefore expresses its action, modulo the
rational coordinate field, as a single signed combination over that faithful coordinate, so nothing
can cancel between widths.

A difference operator sends the multiple-sine source into the differentially algebraic locus exactly
when every one of its monomials uses at least `r` distinct directions, where the period family has
`r + 1` members — that is, exactly when it lies in the squarefree Veronese ideal `I_{N-1}`.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher VeroneseIdeal

noncomputable section

noncomputable local instance msaeDecidableEq :
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

/-! ### Rational functions are differentially algebraic -/

theorem differentialAlgebraicOver_ratFunc_of_mem_rationalCoordinateField
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ meromorphicRationalCoordinateField) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨r, hr⟩ := (mem_meromorphicRationalCoordinateField_iff x).mp hx
  rw [← hr]
  exact differentialAlgebraicOver_algebraMap (E := meroField (Set.univ : Set ℂ)) r

theorem differentialAlgebraicOver_meroShiftDiff (q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) (meroShiftDiff q x) := by
  rw [meroShiftDiff]
  exact differentialAlgebraicOver_sub
    (GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_addTranslationMeroEquiv q hx) hx

/-! ### The boundary layer is differentially algebraic -/

theorem differentialAlgebraicOver_sineFaceTranslate_of_compl_card_one (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Finset ι} (h1 : (Sᶜ : Finset ι).card = 1) (n : ι →₀ ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (sineFaceTranslate ω hω S n) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hne : (Sᶜ : Finset ι).Nonempty := ⟨a, by rw [ha]; simp⟩
  have hsingle : ({a} : Finset ι).Nonempty := ⟨a, by simp⟩
  rw [sineFaceTranslate, sineFaceCoord_eq ω hω hne,
    frameSourceMero_congr ω hω ha hne hsingle]
  exact GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_addTranslationMeroEquiv _
    (differentialAlgebraicOver_frameSourceMero_singleton ω hω a hsingle)

theorem differentialAlgebraicOver_sineNatSynth_of_compl_card_one (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {S : Finset ι} (h1 : (Sᶜ : Finset ι).card = 1)
    (c : (ι →₀ ℕ) →₀ ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (sineNatSynth ω hω S c) := by
  rw [sineNatSynth_eq_sum]
  refine _root_.HTGeometry.differentialAlgebraicOver_finset_sum c.support _ fun n _ => ?_
  exact differentialAlgebraicOver_complexMul (c n)
    (differentialAlgebraicOver_sineFaceTranslate_of_compl_card_one ω hω h1 n)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Wide monomials annihilate.**  An iterated difference along a list of directions leaving at
most one surviving period sends the source into the differentially algebraic locus. -/
theorem differentialAlgebraicOver_listShiftDiff_of_compl_le_one (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) :
    ∀ l : List ι, ((l.toFinset)ᶜ : Finset ι).card ≤ 1 →
      DifferentialAlgebraicOver (RatFunc ℂ)
        (HTGeometry.listShiftDiff ω l (sineFaceCoord ω hω ∅)) := by
  classical
  intro l
  induction l with
  | nil =>
      intro hcard
      rw [List.toFinset_nil] at hcard
      show DifferentialAlgebraicOver (RatFunc ℂ) (sineFaceCoord ω hω ∅)
      by_cases hne : (∅ᶜ : Finset ι).Nonempty
      · have h1 : (∅ᶜ : Finset ι).card = 1 := by
          have hpos := Finset.card_pos.mpr hne
          omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        have hsingle : ({a} : Finset ι).Nonempty := ⟨a, by simp⟩
        rw [sineFaceCoord_eq ω hω hne, frameSourceMero_congr ω hω ha hne hsingle]
        exact differentialAlgebraicOver_frameSourceMero_singleton ω hω a hsingle
      · rw [sineFaceCoord, dif_neg hne]
        simpa using differentialAlgebraicOver_algebraMap
          (F := RatFunc ℂ) (E := meroField (Set.univ : Set ℂ)) 0
  | cons j l ih =>
      intro hcard
      have hstep : HTGeometry.listShiftDiff ω (j :: l) (sineFaceCoord ω hω ∅)
          = meroShiftDiff (ω j) (HTGeometry.listShiftDiff ω l (sineFaceCoord ω hω ∅)) := by
        rw [HTGeometry.listShiftDiff, meroShiftDiff]
      by_cases hprev : ((l.toFinset)ᶜ : Finset ι).card ≤ 1
      · rw [hstep]
        exact differentialAlgebraicOver_meroShiftDiff _ (ih hprev)
      · have hone : 1 ≤ (((j :: l).toFinset)ᶜ : Finset ι).card := by
          by_contra hlt
          have hzero : (((j :: l).toFinset)ᶜ : Finset ι).card = 0 := by omega
          have hsub : ((j :: l).toFinset)ᶜ ⊆ (l.toFinset)ᶜ := by
            intro x hx
            rw [Finset.mem_compl] at hx ⊢
            intro hcon
            exact hx (by rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem hcon)
          have hcompl : ((l.toFinset)ᶜ : Finset ι).card
              ≤ (((j :: l).toFinset)ᶜ : Finset ι).card + 1 := by
            have hins : (l.toFinset)ᶜ ⊆ insert j (((j :: l).toFinset)ᶜ) := by
              intro x hx
              rw [Finset.mem_compl] at hx
              by_cases hxj : x = j
              · rw [hxj]
                exact Finset.mem_insert_self j _
              · refine Finset.mem_insert_of_mem ?_
                rw [Finset.mem_compl, List.toFinset_cons, Finset.mem_insert]
                rintro (rfl | hcon)
                · exact hxj rfl
                · exact hx hcon
            have := Finset.card_le_card hins
            have hcardins := Finset.card_insert_le j (((j :: l).toFinset)ᶜ)
            omega
          omega
        have hsynth := listShiftDiff_sub_sineNatSynth_mem ω hω (j :: l) hone
        have hexact : (((j :: l).toFinset)ᶜ : Finset ι).card = 1 := by omega
        have hDA : DifferentialAlgebraicOver (RatFunc ℂ)
            ((-1 : meroField (Set.univ : Set ℂ)) ^ ((j :: l).toFinset).card *
              sineNatSynth ω hω (j :: l).toFinset (listCoeff (j :: l))) := by
          have hpow : DifferentialAlgebraicOver (RatFunc ℂ)
              ((-1 : meroField (Set.univ : Set ℂ)) ^ ((j :: l).toFinset).card) := by
            have hneg : ((-1 : meroField (Set.univ : Set ℂ)) ^ ((j :: l).toFinset).card)
                = algebraMap ℂ (meroField (Set.univ : Set ℂ))
                  ((-1 : ℂ) ^ ((j :: l).toFinset).card) := by
              rw [map_pow, map_neg, map_one]
            rw [hneg]
            exact differentialAlgebraicOver_algebraMap_complex _
          exact differentialAlgebraicOver_mul hpow
            (differentialAlgebraicOver_sineNatSynth_of_compl_card_one ω hω hexact _)
        have hsum := differentialAlgebraicOver_add
          (differentialAlgebraicOver_ratFunc_of_mem_rationalCoordinateField hsynth) hDA
        simpa using hsum

/-! ### The pair coordinate -/

/-- The translate of a multiple-sine face coordinate indexed by a `(face, exponent)` pair. -/
def sinePairTranslate (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (p : Finset ι × (ι →₀ ℕ)) : meroField (Set.univ : Set ℂ) :=
  sineFaceTranslate ω hω p.1 p.2

theorem sinePairTranslate_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {p : Finset ι × (ι →₀ ℕ)} (hp : PairCarried p) :
    sinePairTranslate ω hω p ∈ sineFacePacketUnion ω hω {L : Finset ι | 2 ≤ (Lᶜ).card} := by
  refine Set.mem_iUnion₂.mpr ⟨p.1, hp.1, ?_⟩
  exact translate_sineFaceCoord_mem_facePacket ω hω
    (Finset.card_pos.mp (by have := hp.1; omega))
    (natShift_mem_faceShiftLattice ω hp.2)

set_option synthInstance.maxHeartbeats 1000000 in
theorem sineDeepCoordinate_injective {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J K : Finset ι} (hJ : 2 ≤ (Jᶜ : Finset ι).card) (hK : 2 ≤ (Kᶜ : Finset ι).card)
    {g h : ℂ} (hg : g ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) J)
    (hh : h ∈ faceShiftLattice (fun k => μ * (rad k : ℂ)) K)
    (heq : addTranslationMeroEquiv g (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω J)
      = addTranslationMeroEquiv h (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω K)) :
    J = K ∧ g = h := by
  classical
  have hneJ : (Jᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  have hneK : (Kᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  rw [sineFaceCoord_eq _ hω hneJ, sineFaceCoord_eq _ hω hneK] at heq
  by_cases hJK : J = K
  · subst hJK
    exact ⟨rfl, frameSource_translate_injective hrad hind hω hJ hneJ hg hh heq⟩
  · refine absurd ?_ (frameSource_translate_sub_notMem_rational hrad hind hω hJK hJ hK
      hneJ hneK hg hh)
    rw [heq, sub_self]
    exact zero_mem _

theorem sinePairTranslate_inj {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {p q : Finset ι × (ι →₀ ℕ)} (hp : PairCarried p) (hq : PairCarried q)
    (h : sinePairTranslate (fun k => μ * (rad k : ℂ)) hω p
      = sinePairTranslate (fun k => μ * (rad k : ℂ)) hω q) : p = q := by
  obtain ⟨hface, hshift⟩ := sineDeepCoordinate_injective hrad hind hω hp.1 hq.1
    (natShift_mem_faceShiftLattice _ hp.2) (natShift_mem_faceShiftLattice _ hq.2) h
  exact Prod.ext hface (natShift_injective _
    (periodsIntegrallyIndependent_ray hrad hind hω) hshift)

/-- Synthesis from a coefficient function on `(face, exponent)` pairs. -/
def sinePairSynth (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    (C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (sinePairTranslate ω hω) C

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **A nonzero admissible pair coefficient synthesizes a hypertranscendental germ.** -/
theorem hypertranscendentalOver_sinePairSynth {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ}
    (hcarry : ∀ p ∈ C.support, PairCarried p) (hC : C ≠ 0) :
    HypertranscendentalOver ℂ (sinePairSynth (fun k => μ * (rad k : ℂ)) hω C) := by
  classical
  have hmem : ∀ k : (C.support : Finset (Finset ι × (ι →₀ ℕ))),
      sinePairTranslate (fun k => μ * (rad k : ℂ)) hω (k : Finset ι × (ι →₀ ℕ)) ∈
        sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω {L : Finset ι | 2 ≤ (Lᶜ).card} :=
    fun k => sinePairTranslate_mem _ hω (hcarry (k : Finset ι × (ι →₀ ℕ)) k.2)
  have hinj : Function.Injective
      (fun k : (C.support : Finset (Finset ι × (ι →₀ ℕ))) =>
        sinePairTranslate (fun k => μ * (rad k : ℂ)) hω (k : Finset ι × (ι →₀ ℕ))) := by
    intro a b hab
    exact Subtype.ext (sinePairTranslate_inj hrad hind hω
      (hcarry (a : Finset ι × (ι →₀ ℕ)) a.2) (hcarry (b : Finset ι × (ι →₀ ℕ)) b.2) hab)
  have hindep : DifferentialIndependent ℂ
      (fun k : (C.support : Finset (Finset ι × (ι →₀ ℕ))) =>
        sinePairTranslate (fun k => μ * (rad k : ℂ)) hω (k : Finset ι × (ι →₀ ℕ))) :=
    multipleSineSelectedFaces_differentialIndependent hrad hind hω _ hmem hinj
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
          sinePairTranslate (fun k => μ * (rad k : ℂ)) hω (k : Finset ι × (ι →₀ ℕ))
      = sinePairSynth (fun k => μ * (rad k : ℂ)) hω C := by
    rw [sinePairSynth, Finsupp.linearCombination_apply, Finsupp.sum,
      ← Finset.sum_coe_sort C.support]
    exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
  rwa [hval] at hsum

theorem sineNatSynth_eq_pairSynth (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) :
    sineNatSynth ω hω S c = sinePairSynth ω hω (Finsupp.mapDomain (faceEmbed S) c) := by
  rw [sinePairSynth, Finsupp.linearCombination_mapDomain, sineNatSynth]
  rfl


/-! ### The exact annihilator -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- **Reverse inclusion of the annihilator.**  If some monomial of a difference operator leaves at
least two surviving periods, the operator does not send the multiple-sine source into the
differentially algebraic locus. -/
theorem hypertranscendentalOver_xApply_multipleSine_of_notMem_veroneseIdeal
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    {P : MvPolynomial ι ℂ} (hP : P ∉ veroneseIdeal ℂ ι r) :
    HypertranscendentalOver (RatFunc ℂ)
      (xApply (fun k => μ * (rad k : ℂ)) P
        (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)) := by
  classical
  have hι : 2 ≤ Fintype.card ι := by
    by_contra hlt
    exact hP (by
      have hr : r = 0 := by omega
      subst hr
      simp [veroneseIdeal, veroneseGens])
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
  have hwideDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (∑ d ∈ wide, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
        xMonomialApply (fun k => μ * (rad k : ℂ)) d
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)) := by
    refine _root_.HTGeometry.differentialAlgebraicOver_finset_sum wide _ fun d hd => ?_
    refine differentialAlgebraicOver_complexMul _ ?_
    have hle : (((multiDegreeList d).toFinset)ᶜ : Finset ι).card ≤ 1 := by
      rw [multiDegreeList_toFinset d]
      have hnot := (Finset.mem_filter.mp hd).2
      omega
    have hDA := differentialAlgebraicOver_listShiftDiff_of_compl_le_one
      (fun k => μ * (rad k : ℂ)) hω (multiDegreeList d) hle
    rwa [xMonomialApply, listShiftDiff_eq_listShiftDiff]
  set C : (Finset ι × (ι →₀ ℕ)) →₀ ℂ :=
    ∑ d ∈ narrow, ((-1 : ℂ) ^ (d.support).card * MvPolynomial.coeff d P) •
      Finsupp.mapDomain (faceEmbed d.support) (listCoeff (multiDegreeList d)) with hC
  have hnarrowVal : (∑ d ∈ narrow,
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          xMonomialApply (fun k => μ * (rad k : ℂ)) d
            (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅))
      - sinePairSynth (fun k => μ * (rad k : ℂ)) hω C
      ∈ meromorphicRationalCoordinateField := by
    rw [hC, sinePairSynth, map_sum, ← Finset.sum_sub_distrib]
    refine sum_mem fun d hd => ?_
    have hdeep : 2 ≤ ((d.support)ᶜ : Finset ι).card := (Finset.mem_filter.mp hd).2
    have hone : 1 ≤ (((multiDegreeList d).toFinset)ᶜ : Finset ι).card := by
      rw [multiDegreeList_toFinset d]
      omega
    have hsynth := listShiftDiff_sub_sineNatSynth_mem (fun k => μ * (rad k : ℂ)) hω
      (multiDegreeList d) hone
    rw [multiDegreeList_toFinset d] at hsynth
    have hpair : (Finsupp.linearCombination ℂ
          (sinePairTranslate (fun k => μ * (rad k : ℂ)) hω))
          (((-1 : ℂ) ^ (d.support).card * MvPolynomial.coeff d P) •
            Finsupp.mapDomain (faceEmbed d.support) (listCoeff (multiDegreeList d)))
        = algebraMap ℂ (meroField (Set.univ : Set ℂ))
            ((-1 : ℂ) ^ (d.support).card * MvPolynomial.coeff d P) *
          sineNatSynth (fun k => μ * (rad k : ℂ)) hω d.support (listCoeff (multiDegreeList d)) := by
      rw [map_smul, ← sinePairSynth, ← sineNatSynth_eq_pairSynth, Algebra.smul_def]
    rw [hpair, xMonomialApply, listShiftDiff_eq_listShiftDiff]
    have hcoe : algebraMap ℂ (meroField (Set.univ : Set ℂ))
          ((-1 : ℂ) ^ (d.support).card * MvPolynomial.coeff d P)
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          (-1 : meroField (Set.univ : Set ℂ)) ^ (d.support).card := by
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    rw [hcoe]
    have hid : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          HTGeometry.listShiftDiff (fun k => μ * (rad k : ℂ)) (multiDegreeList d)
            (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)
        - algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
            (-1 : meroField (Set.univ : Set ℂ)) ^ (d.support).card *
          sineNatSynth (fun k => μ * (rad k : ℂ)) hω d.support (listCoeff (multiDegreeList d))
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          (HTGeometry.listShiftDiff (fun k => μ * (rad k : ℂ)) (multiDegreeList d)
              (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)
            - (-1 : meroField (Set.univ : Set ℂ)) ^ (d.support).card *
              sineNatSynth (fun k => μ * (rad k : ℂ)) hω d.support
                (listCoeff (multiDegreeList d))) := by ring
    rw [hid]
    exact mul_mem (meromorphicRationalCoordinateField.algebraMap_mem _) hsynth
  obtain ⟨d₀, hd₀mem, hd₀max⟩ :=
    narrow.exists_max_image (fun d => ∑ i, d i) hnarrowNonempty
  have hd₀P : MvPolynomial.coeff d₀ P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp hd₀mem).1
  have hd₀deep : 2 ≤ ((d₀.support)ᶜ : Finset ι).card := (Finset.mem_filter.mp hd₀mem).2
  set p₀ : Finset ι × (ι →₀ ℕ) := (d₀.support, listTop (multiDegreeList d₀)) with hp₀
  have hCp₀ : C p₀ = (-1 : ℂ) ^ (d₀.support).card * MvPolynomial.coeff d₀ P := by
    rw [hC, Finsupp.coe_finsetSum, Finset.sum_apply]
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
    have hval : C p₀ = 0 := by rw [hzero]; rfl
    rw [hCp₀] at hval
    rcases mul_eq_zero.mp hval with h | h
    · exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h
    · exact hd₀P h
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
    rwa [multiDegreeList_toFinset d] at hcar
  have hnarrowHT : HypertranscendentalOver ℂ
      (sinePairSynth (fun k => μ * (rad k : ℂ)) hω C) :=
    hypertranscendentalOver_sinePairSynth hrad hind hω hCcarry hCne
  have hsplit : xApply (fun k => μ * (rad k : ℂ)) P
        (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)
      = (∑ d ∈ narrow, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          xMonomialApply (fun k => μ * (rad k : ℂ)) d
            (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅))
        + ∑ d ∈ wide, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
          xMonomialApply (fun k => μ * (rad k : ℂ)) d
            (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅) := by
    rw [xApply, hnarrow, hwide, Finset.sum_filter_add_sum_filter_not]
  intro hDA
  rw [hsplit] at hDA
  have hnarrowDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (∑ d ∈ narrow, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (MvPolynomial.coeff d P) *
        xMonomialApply (fun k => μ * (rad k : ℂ)) d
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)) := by
    have hsub := differentialAlgebraicOver_sub hDA hwideDA
    simpa using hsub
  have hpairDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (sinePairSynth (fun k => μ * (rad k : ℂ)) hω C) := by
    have hdiff := differentialAlgebraicOver_sub hnarrowDA
      (differentialAlgebraicOver_ratFunc_of_mem_rationalCoordinateField hnarrowVal)
    simpa using hdiff
  exact hnarrowHT (HTGeometry.differentialAlgebraicOver_complex_of_ratFunc hpairDA)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- **The exact squarefree annihilator of the multiple sine.**  For a ray period family of `r + 1`
members with rationally independent radii, a difference operator sends the multiple-sine source into
the differentially algebraic locus exactly when it lies in the squarefree Veronese ideal `I_r`. -/
theorem differentialAlgebraicOver_xApply_multipleSine_iff_mem_veroneseIdeal
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (P : MvPolynomial ι ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (xApply (fun k => μ * (rad k : ℂ)) P
          (sineFaceCoord (fun k => μ * (rad k : ℂ)) hω ∅)) ↔
      P ∈ veroneseIdeal ℂ ι r := by
  classical
  constructor
  · intro hDA
    by_contra hP
    exact hypertranscendentalOver_xApply_multipleSine_of_notMem_veroneseIdeal
      hrad hind hω r hcard hP hDA
  · intro hP
    rw [xApply]
    refine _root_.HTGeometry.differentialAlgebraicOver_finset_sum P.support _ fun d hd => ?_
    refine differentialAlgebraicOver_complexMul _ ?_
    have hwidth : r ≤ (d.support).card :=
      (mem_veroneseIdeal_iff P).mp hP d (MvPolynomial.mem_support_iff.mp hd)
    have htotal := Finset.card_add_card_compl d.support
    rw [hcard] at htotal
    have hle : (((multiDegreeList d).toFinset)ᶜ : Finset ι).card ≤ 1 := by
      rw [multiDegreeList_toFinset d]
      omega
    have hDA := differentialAlgebraicOver_listShiftDiff_of_compl_le_one
      (fun k => μ * (rad k : ℂ)) hω (multiDegreeList d) hle
    rwa [xMonomialApply, listShiftDiff_eq_listShiftDiff]

end

end GaloisForLFunctions.HTGeometry
