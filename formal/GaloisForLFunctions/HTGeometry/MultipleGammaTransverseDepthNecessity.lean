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
      exact ht d hd (by
        have := h1.symm
        exact add_right_eq_self.mp this.symm)
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd (by simpa [Nat.add_sub_cancel' (le_of_lt h)] using hab)
        (hstep a (b - a) (by omega))
    · exact h
    · exact absurd (by simpa [Nat.add_sub_cancel' (le_of_lt h)] using hab.symm)
        (hstep b (a - b) (by omega))
  exact (Set.infinite_range_of_injective hinjRange).mono hsub (c.support.finite_toSet)

end

end GaloisForLFunctions
