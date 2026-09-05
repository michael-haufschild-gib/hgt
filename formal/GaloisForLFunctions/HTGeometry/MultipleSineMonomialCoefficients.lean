import GaloisForLFunctions.HTGeometry.MultipleSineAllProperFaces
import GaloisForLFunctions.HTGeometry.MultipleSineBoundaryFaceDA
import GaloisForLFunctions.HTGeometry.MultipleGammaMonomialCoefficients

/-!
# Monomial coefficients of the multiple-sine difference calculus

A difference monomial applied to the multiple-sine source is, modulo the rational coordinate field,
a signed combination of translates of one face coordinate: the face is the support of the monomial,
and the coefficient function is the purely combinatorial `listCoeff` of the corpus.  Two structural
steps produce it — a difference in an already deleted direction shifts the exponent, and a
difference in a surviving direction deletes that direction, flips the sign and leaves a rational
remainder.

The sign and the remainder are the two places where the multiple sine differs from the elliptic
gamma; both are invisible to differential algebraicity, which is what the annihilator statement
measures.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance msmcDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The two iterated-difference operators agree -/

omit [Fintype ι] [DecidableEq ι] in
theorem listShiftDiff_eq_listShiftDiff (ω : ι → ℂ) :
    ∀ (l : List ι) (x : meroField (Set.univ : Set ℂ)),
      GaloisForLFunctions.listShiftDiff ω l x = HTGeometry.listShiftDiff ω l x := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons j l ih =>
      intro x
      show meroShiftDiff (ω j) (GaloisForLFunctions.listShiftDiff ω l x) = _
      rw [ih, meroShiftDiff]
      rfl

/-! ### The coordinate of a face -/

/-- The multiple-sine coordinate of a face: the source of the complementary frame. -/
def sineFaceCoord (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  if h : (Sᶜ : Finset ι).Nonempty then frameSourceMero ω hω (Sᶜ : Finset ι) h else 0

theorem sineFaceCoord_eq (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {S : Finset ι}
    (h : (Sᶜ : Finset ι).Nonempty) :
    sineFaceCoord ω hω S = frameSourceMero ω hω (Sᶜ : Finset ι) h :=
  dif_pos h

theorem translate_sineFaceCoord_mem_facePacket (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {S : Finset ι} (h : (Sᶜ : Finset ι).Nonempty) {g : ℂ} (hg : g ∈ faceShiftLattice ω S) :
    addTranslationMeroEquiv g (sineFaceCoord ω hω S) ∈ facePacket ω hω S := by
  rw [sineFaceCoord_eq ω hω h]
  exact translate_mem_facePacket ω hω h hg

/-! ### Synthesis of a coefficient function on one face -/

/-- The face coordinate translated by an exponent vector. -/
def sineFaceTranslate (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι) (n : ι →₀ ℕ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (natShift ω n) (sineFaceCoord ω hω S)

/-- Synthesis of a finitely supported exponent coefficient function. -/
def sineNatSynth (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (sineFaceTranslate ω hω S) c

theorem sineNatSynth_eq_sum (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (c : (ι →₀ ℕ) →₀ ℂ) :
    sineNatSynth ω hω S c =
      ∑ n ∈ c.support,
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c n) * sineFaceTranslate ω hω S n := by
  rw [sineNatSynth, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun n _ => Algebra.smul_def _ _

theorem sineNatSynth_sub (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (a b : (ι →₀ ℕ) →₀ ℂ) :
    sineNatSynth ω hω S (a - b) = sineNatSynth ω hω S a - sineNatSynth ω hω S b := by
  rw [sineNatSynth, sineNatSynth, sineNatSynth, map_sub]

theorem sineNatSynth_single_zero (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι) :
    sineNatSynth ω hω S (Finsupp.single 0 1) = sineFaceCoord ω hω S := by
  rw [sineNatSynth, Finsupp.linearCombination_single, one_smul, sineFaceTranslate]
  have hzero : natShift ω (0 : ι →₀ ℕ) = 0 := by simp [natShift]
  rw [hzero, addTranslationMeroEquiv_zero_apply]

theorem sineFaceTranslate_monomialExpShift (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (j : ι) (n : ι →₀ ℕ) :
    sineFaceTranslate ω hω S (monomialExpShift j n) =
      addTranslationMeroEquiv (ω j) (sineFaceTranslate ω hω S n) := by
  rw [sineFaceTranslate, sineFaceTranslate, addTranslationMeroEquiv_add, monomialExpShift,
    natShift_add_single, add_comm]

/-! ### The two structural steps -/

/-- **Face-preserving step.**  A difference in an already deleted direction is the exponent shift
minus the identity on coefficients. -/
theorem meroShiftDiff_sineNatSynth (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (S : Finset ι)
    (j : ι) (c : (ι →₀ ℕ) →₀ ℂ) :
    meroShiftDiff (ω j) (sineNatSynth ω hω S c) =
      sineNatSynth ω hω S (Finsupp.mapDomain (monomialExpShift j) c - c) := by
  classical
  have hsupp : (Finsupp.mapDomain (monomialExpShift j) c).support
      = c.support.image (monomialExpShift j) :=
    Finsupp.mapDomain_support_of_injective (monomialExpShift_injective j) c
  have htrans : addTranslationMeroEquiv (ω j) (sineNatSynth ω hω S c) =
      sineNatSynth ω hω S (Finsupp.mapDomain (monomialExpShift j) c) := by
    rw [sineNatSynth_eq_sum, sineNatSynth_eq_sum, hsupp, map_sum,
      Finset.sum_image fun a _ b _ h => monomialExpShift_injective j h]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
      Finsupp.mapDomain_apply (monomialExpShift_injective j),
      sineFaceTranslate_monomialExpShift]
  rw [meroShiftDiff, sineNatSynth_sub, htrans]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Face-growing step.**  A difference in a surviving direction deletes that direction, flips the
sign and leaves a rational remainder. -/
theorem meroShiftDiff_sineNatSynth_notMem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {S : Finset ι}
    (h2 : 2 ≤ (Sᶜ : Finset ι).card) {j : ι} (hj : j ∉ S) (c : (ι →₀ ℕ) →₀ ℂ) :
    meroShiftDiff (ω j) (sineNatSynth ω hω S c) + sineNatSynth ω hω (insert j S) c
      ∈ meromorphicRationalCoordinateField := by
  classical
  have hne : (Sᶜ : Finset ι).Nonempty := Finset.card_pos.mp (by omega)
  have hne' : ((insert j S)ᶜ : Finset ι).Nonempty := by
    refine Finset.card_pos.mp ?_
    have hins := Finset.card_insert_of_notMem hj
    have h1 := Finset.card_add_card_compl S
    have h2' := Finset.card_add_card_compl (insert j S)
    omega
  rw [meroShiftDiff, sineNatSynth_eq_sum, sineNatSynth_eq_sum, map_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_mem fun n _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex, ← mul_sub, ← mul_add]
  refine mul_mem (meromorphicRationalCoordinateField.algebraMap_mem (c n)) ?_
  rw [sineFaceTranslate, sineFaceTranslate, sineFaceCoord_eq ω hω hne,
    sineFaceCoord_eq ω hω hne']
  exact frameSource_translation_defect_mem ω hω hj h2 hne hne' (natShift ω n)

/-! ### The iterated difference, modulo the rational coordinate field -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The monomial synthesis identity.**  Iterating the structural differences along a list of
directions produces, modulo `ℂ(z)`, the signed synthesis of the combinatorial coefficient function
on the face spanned by the list. -/
theorem listShiftDiff_sub_sineNatSynth_mem (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) :
    ∀ l : List ι, 1 ≤ ((l.toFinset)ᶜ : Finset ι).card →
      HTGeometry.listShiftDiff ω l (sineFaceCoord ω hω ∅)
          - (-1 : meroField (Set.univ : Set ℂ)) ^ (l.toFinset).card *
            sineNatSynth ω hω l.toFinset (listCoeff l)
        ∈ meromorphicRationalCoordinateField := by
  classical
  intro l
  induction l with
  | nil =>
      intro _
      rw [HTGeometry.listShiftDiff, List.toFinset_nil, listCoeff, Finset.card_empty, pow_zero,
        one_mul, sineNatSynth_single_zero, sub_self]
      exact zero_mem _
  | cons j l ih =>
      intro hcard
      have hstep : HTGeometry.listShiftDiff ω (j :: l) (sineFaceCoord ω hω ∅)
          = meroShiftDiff (ω j) (HTGeometry.listShiftDiff ω l (sineFaceCoord ω hω ∅)) := by
        rw [HTGeometry.listShiftDiff, meroShiftDiff]
      have hmono : ((l.toFinset)ᶜ : Finset ι).card
          ≥ (((j :: l).toFinset)ᶜ : Finset ι).card := by
        refine Finset.card_le_card ?_
        intro x hx
        rw [Finset.mem_compl] at hx ⊢
        intro hcon
        exact hx (by rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem hcon)
      have hIH := ih (by omega)
      set S : Finset ι := l.toFinset with hS
      set c : (ι →₀ ℕ) →₀ ℂ := listCoeff l with hc
      set ε : meroField (Set.univ : Set ℂ) := (-1 : meroField (Set.univ : Set ℂ)) ^ S.card with hε
      set ρ : meroField (Set.univ : Set ℂ) :=
        HTGeometry.listShiftDiff ω l (sineFaceCoord ω hω ∅) - ε * sineNatSynth ω hω S c with hρ
      have hεmem : ε ∈ meromorphicRationalCoordinateField :=
        pow_mem (neg_mem (one_mem meromorphicRationalCoordinateField)) _
      have hshiftρ : meroShiftDiff (ω j) ρ ∈ meromorphicRationalCoordinateField := by
        rw [meroShiftDiff]
        exact sub_mem (addTranslationMeroAlgEquiv_mem_rationalCoordinateField (ω j) hIH) hIH
      have hsplit : HTGeometry.listShiftDiff ω (j :: l) (sineFaceCoord ω hω ∅)
          = ε * meroShiftDiff (ω j) (sineNatSynth ω hω S c) + meroShiftDiff (ω j) ρ := by
        rw [hstep, hρ, meroShiftDiff, meroShiftDiff, meroShiftDiff, map_sub, map_mul, map_pow,
          map_neg, map_one]
        ring
      by_cases hj : j ∈ S
      · have htoFinset : (j :: l).toFinset = S := by
          rw [List.toFinset_cons, hS]
          exact Finset.insert_eq_self.mpr hj
        have hlc : listCoeff (j :: l)
            = Finsupp.mapDomain (monomialExpShift j) c - c := by
          rw [listCoeff, if_pos (by rw [← hS]; exact hj)]
        rw [hsplit, meroShiftDiff_sineNatSynth ω hω S j c, htoFinset, ← hlc]
        have hid : ε * sineNatSynth ω hω S (listCoeff (j :: l)) + meroShiftDiff (ω j) ρ
            - ε * sineNatSynth ω hω S (listCoeff (j :: l)) = meroShiftDiff (ω j) ρ := by ring
        rw [hid]
        exact hshiftρ
      · have htoFinset : (j :: l).toFinset = insert j S := by
          rw [List.toFinset_cons]
        have hlc : listCoeff (j :: l) = c := by
          rw [listCoeff, if_neg (by rw [← hS]; exact hj)]
        have hcardins : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hj
        have h2 : 2 ≤ (Sᶜ : Finset ι).card := by
          have hins := Finset.card_insert_of_notMem hj
          have h1 := Finset.card_add_card_compl S
          have h2' := Finset.card_add_card_compl (insert j S)
          rw [htoFinset] at hcard
          omega
        have hgrow := meroShiftDiff_sineNatSynth_notMem ω hω h2 hj c
        set r : meroField (Set.univ : Set ℂ) :=
          meroShiftDiff (ω j) (sineNatSynth ω hω S c) + sineNatSynth ω hω (insert j S) c with hr
        have hval : meroShiftDiff (ω j) (sineNatSynth ω hω S c)
            = r - sineNatSynth ω hω (insert j S) c := by rw [hr]; ring
        rw [hsplit, hval, htoFinset, hlc, hcardins, pow_succ]
        have hid : ε * (r - sineNatSynth ω hω (insert j S) c) + meroShiftDiff (ω j) ρ
            - ε * (-1 : meroField (Set.univ : Set ℂ)) * sineNatSynth ω hω (insert j S) c
            = ε * r + meroShiftDiff (ω j) ρ := by ring
        rw [← hε, hid]
        exact add_mem (mul_mem hεmem hgrow) hshiftρ

/-! ### Selected face coordinates are independent -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- Every injectively selected family of translated proper-face coordinates is differentially
independent over the constants. -/
theorem multipleSineSelectedFaces_differentialIndependent {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k) (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {κ : Type} (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω
      {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x) :
    DifferentialIndependent ℂ x := by
  have hall := multipleSineProperFacePackets_diffIndepOn hrad hind hω
  unfold DiffIndepOn at hall
  exact hall.comp (fun k => ⟨x k, hxmem k⟩)
    (fun a b hab => hxinj (congrArg Subtype.val hab))

end

end GaloisForLFunctions.HTGeometry
