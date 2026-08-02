import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDifference
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.DifferentialOperatorRowHypertranscendence
import GaloisForLFunctions.HTGeometry.FaceTranslateInjective
import GaloisForLFunctions.HTGeometry.EllipticCompositumMatroidTransport

/-!
# Necessity half of the transverse-depth law

If the distinct directions of an iterated structural difference still leave at least two surviving
periods, the difference is hypertranscendental.

Reordering the list puts the repetition-free part first, which reaches the face `S` of deleted
directions; every remaining entry is a direction already deleted by `S`, so it acts on the face
packet as a translation difference.  Indexing the packet by its external shift subgroup turns those
remaining differences into the group-algebra operators `t ↦ t + τ_q` minus the identity, acting on
finitely supported coefficient functions.  Since each `τ_q` has infinite order, such an operator
never kills a nonzero finitely supported function, so the result is a nonzero linear combination of
the jointly independent packet coordinates and therefore hypertranscendental.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

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

/-! ## The external shift lattice as an additive subgroup -/

/-- The external lattice of a face, as an additive subgroup of `ℂ`. -/
def faceShiftSubgroup (τ : ι → ℂ) (J : Finset ι) : AddSubgroup ℂ where
  carrier := faceShiftLattice τ J
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  add_mem' := by
    rintro a b ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    refine ⟨n + m, fun i hi => by simp [hn i hi, hm i hi], ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; push_cast; ring
  neg_mem' := by
    rintro a ⟨n, hn, rfl⟩
    refine ⟨-n, fun i hi => by simp [hn i hi], ?_⟩
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.neg_apply]; push_cast; ring

omit [DecidableEq ι] in
@[simp] theorem mem_faceShiftSubgroup {τ : ι → ℂ} {J : Finset ι} {g : ℂ} :
    g ∈ faceShiftSubgroup τ J ↔ g ∈ faceShiftLattice τ J := Iff.rfl

theorem faceShiftSubgroup_period_mem (τ : ι → ℂ) (J : Finset ι) {q : ι} (hq : q ∈ J) :
    τ q ∈ faceShiftSubgroup τ J := by
  have hzero : (0 : ℂ) ∈ faceShiftLattice τ J := ⟨0, fun _ _ => rfl, by simp⟩
  simpa using faceShiftLattice_add_zsmul τ J hq hzero 1

/-! ## The packet indexed by its shift -/

/-- The packet of a face, indexed faithfully by its external shift. -/
def facePacketFamily (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    ↥(faceShiftSubgroup τ J) → meroField (Set.univ : Set ℂ) :=
  fun g => addTranslationMeroEquiv (g : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ J)

theorem facePacketFamily_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (hJ : 2 ≤ (Jᶜ).card) (g : ↥(faceShiftSubgroup τ J)) :
    facePacketFamily τ hτ J g ∈ facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} :=
  Set.mem_iUnion₂.mpr ⟨J, hJ, ⟨(g : ℂ), g.2, rfl⟩⟩

theorem facePacketFamily_injective (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) (hJ : 2 ≤ (Jᶜ).card) :
    Function.Injective (facePacketFamily τ hτ J) := by
  intro g h hgh
  exact Subtype.ext (faceShiftLattice_translate_injective τ hτ hQ J hJ g.2 h.2 hgh)

theorem facePacketFamily_differentialIndependent (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) (hJ : 2 ≤ (Jᶜ).card) :
    DifferentialIndependent ℂ (facePacketFamily τ hτ J) :=
  multipleEllipticGammaSelectedFaces_differentialIndependent τ hτ hQ hι _
    (facePacketFamily_mem τ hτ J hJ) (facePacketFamily_injective τ hτ hQ J hJ)

theorem facePacketFamily_translate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (t g : ↥(faceShiftSubgroup τ J)) :
    facePacketFamily τ hτ J (g + t) =
      addTranslationMeroEquiv (t : ℂ) (facePacketFamily τ hτ J g) := by
  show addTranslationMeroEquiv ((g : ℂ) + (t : ℂ))
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
    addTranslationMeroEquiv (t : ℂ)
      (addTranslationMeroEquiv (g : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ J))
  rw [addTranslationMeroEquiv_add, add_comm]

/-! ## Coefficient calculus on the shift subgroup -/

/-- Synthesis of a finitely supported coefficient function into the packet span. -/
def facePacketSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (c : (↥(faceShiftSubgroup τ J)) →₀ ℂ) : meroField (Set.univ : Set ℂ) :=
  Finsupp.linearCombination ℂ (facePacketFamily τ hτ J) c

theorem facePacketSynth_translate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (t : ↥(faceShiftSubgroup τ J)) (c : (↥(faceShiftSubgroup τ J)) →₀ ℂ) :
    facePacketSynth τ hτ J (Finsupp.mapDomain (fun g => g + t) c) =
      addTranslationMeroEquiv (t : ℂ) (facePacketSynth τ hτ J c) := by
  classical
  rw [facePacketSynth, facePacketSynth, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Function.comp_apply, facePacketFamily_translate τ hτ J t g, Algebra.smul_def,
    Algebra.smul_def, map_mul, addTranslationMeroEquiv_algebraMap_complex]

theorem meroShiftDiff_facePacketSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (t : ↥(faceShiftSubgroup τ J)) (c : (↥(faceShiftSubgroup τ J)) →₀ ℂ) :
    meroShiftDiff (t : ℂ) (facePacketSynth τ hτ J c) =
      facePacketSynth τ hτ J (Finsupp.mapDomain (fun g => g + t) c - c) := by
  rw [meroShiftDiff, ← facePacketSynth_translate τ hτ J t c, facePacketSynth, facePacketSynth,
    facePacketSynth, map_sub]

/-- A translation operator with an infinite-order step never annihilates a nonzero finitely
supported coefficient function. -/
theorem mapDomain_add_sub_ne_zero {G : Type*} [AddCommGroup G] (t : G)
    (ht : ∀ k : ℕ, 0 < k → k • t ≠ 0)
    {c : G →₀ ℂ} (hc : c ≠ 0) :
    Finsupp.mapDomain (fun g => g + t) c - c ≠ 0 := by
  classical
  intro hzero
  have hinj : Function.Injective (fun g : G => g + t) := fun a b hab => by
    simpa using hab
  have h0 : Finsupp.mapDomain (fun x : G => x + t) c = c := sub_eq_zero.mp hzero
  have hshift : ∀ g : G, c (g + t) = c g := by
    intro g
    have hmap : Finsupp.mapDomain (fun x : G => x + t) c (g + t) = c (g + t) := by
      rw [h0]
    rw [Finsupp.mapDomain_apply hinj] at hmap
    exact hmap.symm
  obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hiter : ∀ k : ℕ, c (g₀ + k • t) = c g₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have : g₀ + (k + 1) • t = (g₀ + k • t) + t := by
          rw [succ_nsmul]
          abel
        rw [this, hshift, ih]
  have hne : c g₀ ≠ 0 := Finsupp.mem_support_iff.mp hg₀
  have hsub : Set.range (fun k : ℕ => g₀ + k • t) ⊆ (c.support : Set G) := by
    rintro _ ⟨k, rfl⟩
    exact Finsupp.mem_support_iff.mpr (by rw [hiter k]; exact hne)
  have hinjRange : Function.Injective (fun k : ℕ => g₀ + k • t) := by
    have hstep : ∀ a d : ℕ, 0 < d → g₀ + a • t ≠ g₀ + (a + d) • t := by
      intro a d hd heq
      have h1 : a • t = (a + d) • t := add_left_cancel heq
      rw [add_nsmul] at h1
      refine ht d hd ?_
      have h2 : a • t + (0 : G) = a • t + d • t := by simpa using h1
      exact (add_left_cancel h2).symm
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd (by simpa [Nat.add_sub_cancel' (le_of_lt h)] using hab)
        (hstep a (b - a) (by omega))
    · exact h
    · exact absurd (by simpa [Nat.add_sub_cancel' (le_of_lt h)] using hab.symm)
        (hstep b (a - b) (by omega))
  exact (Set.infinite_range_of_injective hinjRange).mono hsub (c.support.finite_toSet)

/-! ## Repetitions produce a nonzero packet combination -/

theorem faceShiftSubgroup_nsmul_ne_zero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    {q : ι} (hq : q ∈ J) (k : ℕ) (hk : 0 < k) :
    k • (⟨τ q, faceShiftSubgroup_period_mem τ J hq⟩ : ↥(faceShiftSubgroup τ J)) ≠ 0 := by
  intro hzero
  have hcoe : (k : ℂ) * τ q = 0 := by
    have := congrArg (Subtype.val) hzero
    simpa [nsmul_eq_mul] using this
  have hτq : τ q ≠ 0 := by
    intro h0
    have := hτ q
    rw [h0] at this
    simp at this
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero hk0 hτq) hcoe

/-- Iterating structural differences in already deleted directions produces a nonzero finitely
supported combination of the face packet. -/
theorem exists_facePacketSynth_listShiftDiff (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    ∀ l : List ι, (∀ q ∈ l, q ∈ J) →
      ∃ c : (↥(faceShiftSubgroup τ J)) →₀ ℂ, c ≠ 0 ∧
        listShiftDiff τ l (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
          facePacketSynth τ hτ J c := by
  intro l
  induction l with
  | nil =>
      intro _
      refine ⟨Finsupp.single 0 1, Finsupp.single_ne_zero.mpr one_ne_zero, ?_⟩
      rw [listShiftDiff_nil, facePacketSynth, Finsupp.linearCombination_single, one_smul,
        facePacketFamily]
      simpa using (addTranslationMeroEquiv_zero_apply
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)).symm
  | cons q l ih =>
      intro hmem
      obtain ⟨c, hc, hval⟩ := ih fun p hp => hmem p (List.mem_cons_of_mem q hp)
      have hqJ : q ∈ J := hmem q (List.mem_cons_self)
      set t : ↥(faceShiftSubgroup τ J) := ⟨τ q, faceShiftSubgroup_period_mem τ J hqJ⟩ with ht
      refine ⟨Finsupp.mapDomain (fun g => g + t) c - c,
        mapDomain_add_sub_ne_zero t (faceShiftSubgroup_nsmul_ne_zero τ hτ J hqJ) hc, ?_⟩
      rw [listShiftDiff_cons, hval]
      exact meroShiftDiff_facePacketSynth τ hτ J t c

/-! ## Nonzero packet combinations are hypertranscendental -/

theorem hypertranscendentalOver_facePacketSynth (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) (hJ : 2 ≤ (Jᶜ).card)
    {c : (↥(faceShiftSubgroup τ J)) →₀ ℂ} (hc : c ≠ 0) :
    HypertranscendentalOver ℂ (facePacketSynth τ hτ J c) := by
  classical
  have hindep : DifferentialIndependent ℂ
      (fun k : (c.support : Finset _) => facePacketFamily τ hτ J (k : ↥(faceShiftSubgroup τ J))) :=
    (facePacketFamily_differentialIndependent τ hτ hQ hι J hJ).comp
      (fun k : (c.support : Finset _) => (k : ↥(faceShiftSubgroup τ J)))
      (fun a b hab => Subtype.ext hab)
  have hcne : (fun k : (c.support : Finset _) => c (k : ↥(faceShiftSubgroup τ J))) ≠ 0 := by
    obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr hc
    intro hzero
    have := congrFun hzero ⟨g₀, hg₀⟩
    exact (Finsupp.mem_support_iff.mp hg₀) this
  have hsum := hypertranscendentalOver_linearCombination_of_ne_zero
    (C := ℂ) (K := meroField (Set.univ : Set ℂ))
    meroField_deriv_algebraMap_complex_rationalBase _ hcne _ hindep
  have hval : ∑ k : (c.support : Finset _),
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c (k : ↥(faceShiftSubgroup τ J))) *
          facePacketFamily τ hτ J (k : ↥(faceShiftSubgroup τ J)) =
      facePacketSynth τ hτ J c := by
    rw [facePacketSynth, Finsupp.linearCombination_apply, Finsupp.sum,
      ← Finset.sum_coe_sort c.support]
    exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
  rwa [hval] at hsum

/-! ## The necessity half -/

/-- **Transverse depth is necessary.**  If the distinct directions of an iterated structural
difference still leave at least two surviving periods, the difference is hypertranscendental over
the rational coordinate field, and hence over `ℂ(z)`. -/
theorem hypertranscendentalOver_listShiftDiff_multipleEllipticGammaLogDerivMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (l : List ι) (hdeep : 2 ≤ (((l.toFinset))ᶜ).card) :
    HypertranscendentalOver (RatFunc ℂ)
      (listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)) := by
  classical
  set S : Finset ι := l.toFinset with hS
  have hsubset : S.toList ⊆ l := by
    intro i hi
    exact List.mem_toFinset.mp (Finset.mem_toList.mp hi)
  obtain ⟨l₁, hperm₁, hsub₁⟩ := List.Nodup.subperm (S.nodup_toList) hsubset
  obtain ⟨l₂, hl⟩ := hsub₁.exists_perm_append
  have hlperm : l.Perm (l₂ ++ l₁) := hl.trans (List.perm_append_comm)
  have hnodup₁ : l₁.Nodup := hperm₁.nodup_iff.mpr (S.nodup_toList)
  have htoFinset : l₁.toFinset = S := by
    ext a
    rw [List.mem_toFinset, hperm₁.mem_iff, Finset.mem_toList]
  have hl₂ : ∀ q ∈ l₂, q ∈ S := by
    intro q hq
    have : q ∈ l₂ ++ l₁ := List.mem_append_left _ hq
    exact List.mem_toFinset.mpr (hlperm.mem_iff.mpr this)
  have hvalue : listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ) =
      listShiftDiff τ l₂ (multipleEllipticGammaLogDerivFaceMero τ hτ S) := by
    rw [listShiftDiff_perm τ hlperm, listShiftDiff_append,
      listShiftDiff_nodup τ hτ hnodup₁, htoFinset]
  obtain ⟨c, hc, hsynth⟩ := exists_facePacketSynth_listShiftDiff τ hτ S l₂ hl₂
  have hHTC : HypertranscendentalOver ℂ
      (listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)) := by
    rw [hvalue, hsynth]
    exact hypertranscendentalOver_facePacketSynth τ hτ hQ hι S hdeep hc
  exact fun hDA => hHTC (HTGeometry.differentialAlgebraicOver_complex_of_ratFunc hDA)

/-! ## The exact transverse-depth law -/

/-- **Exact transverse-depth law.**  An iterated structural difference of the multiple elliptic
gamma logarithmic derivative is differentially algebraic over `ℂ(z)` exactly when the distinct
directions occurring in it leave at most one surviving period.  Repetitions never help: only the
set of distinct directions matters. -/
theorem differentialAlgebraicOver_listShiftDiff_multipleEllipticGammaLogDerivMero_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) (l : List ι) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)) ↔
      (((l.toFinset))ᶜ).card ≤ 1 := by
  constructor
  · intro hDA
    by_contra hcard
    exact hypertranscendentalOver_listShiftDiff_multipleEllipticGammaLogDerivMero
      τ hτ hQ hι l (by omega) hDA
  · intro hcard
    refine differentialAlgebraicOver_listShiftDiff_multipleEllipticGammaLogDerivMero
      τ hτ l l.toFinset (le_refl _) ?_
    intro i j hi hj
    have hi' : i ∈ ((l.toFinset)ᶜ) := Finset.mem_compl.mpr hi
    have hj' : j ∈ ((l.toFinset)ᶜ) := Finset.mem_compl.mpr hj
    exact Finset.card_le_one.mp hcard i hi' j hj'

/-- **Exact transverse-depth law, hypertranscendence form.** -/
theorem hypertranscendentalOver_listShiftDiff_multipleEllipticGammaLogDerivMero_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) (l : List ι) :
    HypertranscendentalOver (RatFunc ℂ)
        (listShiftDiff τ l (multipleEllipticGammaLogDerivMero τ hτ)) ↔
      2 ≤ (((l.toFinset))ᶜ).card := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_listShiftDiff_multipleEllipticGammaLogDerivMero_iff τ hτ hQ hι l]
  omega

end

end GaloisForLFunctions
