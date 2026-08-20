import GaloisForLFunctions.HTGeometry.AllDepthBottomCharge
import GaloisForLFunctions.HTGeometry.FaceOneSurvivingTheta
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTerminalFace
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaUnitPeriod

/-!
# The universal carrier of the all-depth class

The logarithmic derivative of the multiple elliptic gamma function with exactly the parameters of a
finite direction set is a member of the all-depth mixed-constraint class of that set: it is
`1`-periodic, and its full difference cube deletes every parameter, leaving the terminal constant
`-2πi`.  Its bottom witness — the cube of all but one direction — is the theta logarithmic
derivative of the surviving direction, so its bottom charge is the unit divisor.

* `diffCubeMero_face` — the difference cube of a face coordinate deletes exactly its directions;
* `universalCarrierMero`, **`diffCubeMero_universalCarrier`**;
* **`mixedConstGermSet_universalCarrier`**, `periodicOneGerm_universalCarrier`;
* **`bottomWitnessMero_universalCarrier`** — the bottom witness is a translated theta coordinate.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The difference cube of a face coordinate deletes exactly its own directions.** -/
theorem diffCubeMero_face (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    ∀ t : Finset ι, Disjoint t J →
      diffCubeMero τ t (multipleEllipticGammaLogDerivFaceMero τ hτ J)
        = multipleEllipticGammaLogDerivFaceMero τ hτ (J ∪ t) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | @insert q t' hq ih =>
      intro hdisj
      have hdisj' : Disjoint t' J :=
        Finset.disjoint_left.mpr fun m hm =>
          Finset.disjoint_left.mp hdisj (Finset.mem_insert_of_mem hm)
      have hqJ : q ∉ J := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self q t')
      have hqJt : q ∉ J ∪ t' := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hqJ, hq⟩
      rw [diffCubeMero_insert τ hq, ih hdisj',
        multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ (J ∪ t') q hqJt]
      congr 1
      ext m
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

/-- The universal carrier of the class of a finite direction set: the logarithmic derivative of the
multiple elliptic gamma with exactly those parameters. -/
def universalCarrierMero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaLogDerivFaceMero τ hτ (Finset.univ \ s)

/-- **The full cube of the universal carrier is the terminal constant.** -/
theorem diffCubeMero_universalCarrier (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) :
    diffCubeMero τ s (universalCarrierMero τ hτ s)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (-(2 * Real.pi * I)) := by
  classical
  have hdisj : Disjoint s (Finset.univ \ s) :=
    Finset.disjoint_left.mpr fun m hm hm' => (Finset.mem_sdiff.mp hm').2 hm
  have hunion : (Finset.univ \ s) ∪ s = (Finset.univ : Finset ι) := by
    ext m
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  rw [universalCarrierMero, diffCubeMero_face τ hτ _ s hdisj, hunion]
  haveI : IsEmpty (MultipleEllipticGammaFaceIndex (Finset.univ : Finset ι)) :=
    ⟨fun i => i.2 (Finset.mem_univ _)⟩
  rw [multipleEllipticGammaLogDerivFaceMero, multipleEllipticGammaLogDerivMero_isEmpty]

theorem addTranslationMeroEquiv_one_universalCarrier
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) :
    addTranslationMeroEquiv 1 (universalCarrierMero τ hτ s) = universalCarrierMero τ hτ s :=
  addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero τ hτ _

/-- **The bottom witness of the universal carrier is the face with one surviving direction.** -/
theorem bottomWitnessMero_universalCarrier (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) {k : ι} (hk : k ∈ s) :
    bottomWitnessMero τ s k (universalCarrierMero τ hτ s)
      = multipleEllipticGammaLogDerivFaceMero τ hτ ((Finset.univ : Finset ι) \ {k}) := by
  classical
  have hdisj : Disjoint (s \ {k}) (Finset.univ \ s) :=
    Finset.disjoint_left.mpr fun m hm hm' =>
      (Finset.mem_sdiff.mp hm').2 (Finset.mem_sdiff.mp hm).1
  have hunion : (Finset.univ \ s) ∪ (s \ {k}) = (Finset.univ : Finset ι) \ {k} := by
    ext m
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro (hm | hm)
      · intro hmk
        exact hm (hmk ▸ hk)
      · exact hm.2
    · intro hm
      by_cases hms : m ∈ s
      · exact Or.inr ⟨hms, hm⟩
      · exact Or.inl hms
  rw [bottomWitnessMero, universalCarrierMero, diffCubeMero_face τ hτ _ _ hdisj, hunion]

/-! ## The carrier is a member of the class -/

theorem periodicOneGerm_universalCarrier (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    {f : ℂ → ℂ} (hf : RealizesMero (universalCarrierMero τ hτ s) f) : PeriodicOneGerm f :=
  periodicOneGerm_of_realizesMero hf (addTranslationMeroEquiv_one_universalCarrier τ hτ s)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The universal carrier lies in the all-depth mixed-constraint class.** -/
theorem mixedConstGermSet_universalCarrier (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    {f : ℂ → ℂ} (hf : RealizesMero (universalCarrierMero τ hτ s) f) :
    MixedConstGermSet τ s f (-(2 * Real.pi * I)) := by
  intro z
  have hreal : RealizesMero
      (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (-(2 * Real.pi * I)))
      (HTGeometry.diffCube τ s f) := by
    rw [← diffCubeMero_universalCarrier τ hτ s]
    exact realizesMero_diffCubeMero τ s hf
  exact realizesMero_congr hreal (realizesMero_const _) z

/-- **The bottom witness of the universal carrier is a translated theta logarithmic derivative.**
Its bottom charge is therefore the unit divisor of the surviving direction. -/
theorem exists_bottomWitnessMero_universalCarrier_theta (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) {k : ι} (hk : k ∈ s) {a : ι} (hak : a ≠ k) :
    ∃ c : ℂ, bottomWitnessMero τ s k (universalCarrierMero τ hτ s)
      = addTranslationMeroEquiv (-(1 + τ k) / 2) (thetaLogDerivMero (τ k) (hτ k))
        + algebraMap (analyticSubring Set.univ) (meroField Set.univ)
            (constToAnalytic Set.univ c) := by
  classical
  have haL : a ∈ (Finset.univ : Finset ι) \ {k} :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, by simpa using hak⟩
  have hbL : k ∉ (Finset.univ : Finset ι) \ {k} := by simp
  have hL : ∀ i : ι, i ∉ (Finset.univ : Finset ι) \ {k} → i = k := by
    intro i hi
    by_contra hik
    exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simpa using hik⟩)
  rw [bottomWitnessMero_universalCarrier τ hτ s hk]
  exact multipleEllipticGammaLogDerivFaceMero_one_surviving τ hτ _ haL hbL hL

end

end GaloisForLFunctions
