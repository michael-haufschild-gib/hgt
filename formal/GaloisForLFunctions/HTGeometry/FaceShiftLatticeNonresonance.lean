import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaBottomFace

/-!
# Nonresonance of the external face lattice

The bottom-layer packet of the all-order hierarchy is the set of translates of the order-one
elliptic gamma by the external lattice shifted by the fixed half period `-(1 + tau_b)/2`.  Rational
independence of `1` and the periods makes every such shift nonresonant and separates distinct
shifts, which is exactly the hypothesis of the order-one packet theorem.

Both proofs use only *integer* coefficients: clearing the half period by a factor `2` leaves an
integral relation whose coefficient of `1` is odd.

* `PeriodsIntegrallyIndependent` — the standing genericity hypothesis;
* **`thetaTranslationNonresonant_faceShiftLattice_add_half`** — half-shifted lattice points are
  nonresonant;
* **`thetaTranslationNonresonant_faceShiftLattice_sub`** — distinct lattice points are separated.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `1` together with the periods admits no nontrivial integral relation.  This is the standing
genericity hypothesis of the card, written without rational casts. -/
def PeriodsIntegrallyIndependent (τ : ι → ℂ) : Prop :=
  ∀ (m : ℤ) (n : ι → ℤ), (m : ℂ) + ∑ i, (n i : ℂ) * τ i = 0 → m = 0 ∧ ∀ i, n i = 0

/-- **Half-shifted lattice points are nonresonant.**  Doubling the relation clears the half period
and leaves an integral relation whose coefficient of `1` is odd. -/
theorem thetaTranslationNonresonant_faceShiftLattice_add_half
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) (a b : ι)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ J) :
    ThetaTranslationNonresonant (τ b) (τ a) (g + -(1 + τ b) / 2) := by
  classical
  rintro ⟨p, q, r, hpqr⟩
  obtain ⟨n, -, rfl⟩ := hg
  have hterm : ∀ i : ι,
      ((2 * n i - (if i = b then 2 * q + 1 else 0) - (if i = a then 2 * r else 0) : ℤ) : ℂ) *
          τ i =
        2 * ((n i : ℂ) * τ i) - (if i = b then ((2 * q + 1 : ℤ) : ℂ) * τ i else 0) -
          (if i = a then ((2 * r : ℤ) : ℂ) * τ i else 0) := by
    intro i
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ i, ((2 * n i - (if i = b then 2 * q + 1 else 0) -
        (if i = a then 2 * r else 0) : ℤ) : ℂ) * τ i =
      2 * (∑ i, (n i : ℂ) * τ i) - ((2 * q + 1 : ℤ) : ℂ) * τ b -
        ((2 * r : ℤ) : ℂ) * τ a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ b fun i => ((2 * q + 1 : ℤ) : ℂ) * τ i,
      Finset.sum_ite_eq' Finset.univ a fun i => ((2 * r : ℤ) : ℂ) * τ i]
    simp
  have hrel : ((-(2 * p + 1) : ℤ) : ℂ) +
      ∑ i, ((2 * n i - (if i = b then 2 * q + 1 else 0) -
        (if i = a then 2 * r else 0) : ℤ) : ℂ) * τ i = 0 := by
    rw [hsum]
    push_cast
    linear_combination 2 * hpqr
  obtain ⟨hm, -⟩ := hQ _ _ hrel
  omega

/-- **Distinct lattice points are separated.**  Their difference has no component along the two
surviving periods, so an integral relation forces the two points to coincide. -/
theorem thetaTranslationNonresonant_faceShiftLattice_sub
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J)
    {g g' : ℂ} (hg : g ∈ faceShiftLattice τ J) (hg' : g' ∈ faceShiftLattice τ J)
    (hne : g ≠ g') :
    ThetaTranslationNonresonant (τ b) (τ a) (g - g') := by
  classical
  rintro ⟨p, q, r, hpqr⟩
  obtain ⟨n, hn, rfl⟩ := hg
  obtain ⟨n', hn', rfl⟩ := hg'
  have hterm : ∀ i : ι,
      ((n i - n' i - (if i = b then q else 0) - (if i = a then r else 0) : ℤ) : ℂ) * τ i =
        (n i : ℂ) * τ i - (n' i : ℂ) * τ i - (if i = b then (q : ℂ) * τ i else 0) -
          (if i = a then (r : ℂ) * τ i else 0) := by
    intro i
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ i, ((n i - n' i - (if i = b then q else 0) -
        (if i = a then r else 0) : ℤ) : ℂ) * τ i =
      (∑ i, (n i : ℂ) * τ i) - (∑ i, (n' i : ℂ) * τ i) - (q : ℂ) * τ b - (r : ℂ) * τ a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ b fun i => (q : ℂ) * τ i,
      Finset.sum_ite_eq' Finset.univ a fun i => (r : ℂ) * τ i]
    simp
  have hrel : ((-p : ℤ) : ℂ) +
      ∑ i, ((n i - n' i - (if i = b then q else 0) -
        (if i = a then r else 0) : ℤ) : ℂ) * τ i = 0 := by
    rw [hsum]
    push_cast
    linear_combination hpqr
  obtain ⟨-, hcz⟩ := hQ _ _ hrel
  refine hne (Finset.sum_congr rfl fun i _ => ?_)
  have hci := hcz i
  by_cases hiJ : i ∈ J
  · have hib : i ≠ b := fun h => hbJ (h ▸ hiJ)
    have hia : i ≠ a := fun h => haJ (h ▸ hiJ)
    rw [if_neg hib, if_neg hia] at hci
    have hnn : n i = n' i := by omega
    rw [hnn]
  · rw [hn i hiJ, hn' i hiJ]

/-! ## The bottom-layer packet -/

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Bottom-layer atomicity.**  The packet of a face with exactly two surviving parameters is
differentially independent over every differentially algebraic extension of the constants. -/
theorem multipleEllipticGammaFacePacket_diffIndepOn_bottom
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {a b : ι} (haJ : a ∉ J) (hbJ : b ∉ J) (hab : a ≠ b)
    (hJ : ∀ i, i ∉ J → i = a ∨ i = b)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b)))
    {G : Set (meroField (Set.univ : Set ℂ))}
    (hG : ∀ g ∈ G, DifferentialAlgebraicOver ℂ g) :
    DiffIndepOn ↥(differentialAdjoin ℂ G) (multipleEllipticGammaFacePacket τ hτ J) := by
  classical
  set Ψ := ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b) with hΨdef
  set c : ℂ := -(1 + τ b) / 2 with hcdef
  have hbridge : ∀ g : ℂ,
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        addTranslationMeroEquiv (g + c) Ψ := by
    intro g
    rw [multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ J haJ hbJ hab hJ,
      addTranslationMeroEquiv_add]
  refine diffIndepOn_of_forall_finite ?_
  intro T hTsub hTfin
  have hchoice : ∀ y ∈ T, ∃ g : ℂ, g ∈ faceShiftLattice τ J ∧
      addTranslationMeroEquiv (g + c) Ψ = y := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := hTsub hy
    refine ⟨g, hg, ?_⟩
    rw [← hbridge g]
    exact hgy
  let shift : meroField (Set.univ : Set ℂ) → ℂ :=
    fun y => if h : y ∈ T then (hchoice y h).choose else 0
  have hshift : ∀ y (hy : y ∈ T), shift y ∈ faceShiftLattice τ J ∧
      addTranslationMeroEquiv (shift y + c) Ψ = y := by
    intro y hy
    have hd : shift y = (hchoice y hy).choose := dif_pos hy
    rw [hd]
    exact (hchoice y hy).choose_spec
  set A : Finset ℂ := hTfin.toFinset.image (fun y => shift y + c) with hAdef
  have hAmem : ∀ s ∈ A, ∃ g ∈ faceShiftLattice τ J, g + c = s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := Finset.mem_image.mp hs
    exact ⟨shift y, (hshift y (hTfin.mem_toFinset.mp hy)).1, hys⟩
  have hAnonres : ∀ s ∈ A, ThetaTranslationNonresonant (τ b) (τ a) s := by
    intro s hs
    obtain ⟨g, hg, rfl⟩ := hAmem s hs
    exact thetaTranslationNonresonant_faceShiftLattice_add_half τ hQ J a b hg
  have hAsep : ∀ s ∈ A, ∀ s' ∈ A, s ≠ s' →
      ThetaTranslationNonresonant (τ b) (τ a) (s - s') := by
    intro s hs s' hs' hne
    obtain ⟨g, hg, rfl⟩ := hAmem s hs
    obtain ⟨g', hg', rfl⟩ := hAmem s' hs'
    have hgne : g ≠ g' := fun h => hne (by rw [h])
    have hdiff : g + c - (g' + c) = g - g' := by ring
    rw [hdiff]
    exact thetaTranslationNonresonant_faceShiftLattice_sub τ hQ J haJ hbJ hg hg' hgne
  have hpacket := ellipticGammaTranslatePacket_diffIndepOn_daExtension_of_separated
    (hτ a) (hτ b) hperiods A hAnonres hAsep hG
  refine hpacket.subset ?_
  intro y hy
  refine Set.mem_insert_of_mem _ ?_
  refine ⟨⟨shift y + c, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨y, hTfin.mem_toFinset.mpr hy, rfl⟩
  · exact (hshift y hy).2

end

end GaloisForLFunctions
