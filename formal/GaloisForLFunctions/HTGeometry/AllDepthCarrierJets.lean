import GaloisForLFunctions.HTGeometry.AllDepthUniversalCarrier
import GaloisForLFunctions.HTGeometry.AllDepthBottomRealization
import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDifferentialOperator
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative

/-!
# Jets of the universal carrier realize every prescribed bottom charge

The bottom witness of the universal carrier is a translated theta logarithmic derivative, so the
bottom witness of a finite combination of jets of translates of the carrier is the corresponding
finite combination of line-atom jets.  Since an atom sum realizes an arbitrary finite divisor of
bounded order on the elliptic quotient, the bottom-charge map is surjective.

* `realizesMero_thetaLogDerivMero`;
* `diffCubeMero_add`, `diffCubeMero_finsetSum`, `diffCubeMero_algebraMap_mul`,
  `diffCubeMero_differentialJet` — the cube is a constant-coefficient differential operator;
* `carrierAtomCombination` and its cube and bottom laws;
* **`exists_class_member_with_prescribed_bottomCharge`**.
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

/-! ## The theta coordinate is realized by the theta source -/

theorem realizesMero_thetaLogDerivMero (σ : ℂ) (hσ : 0 < σ.im) :
    RealizesMero (thetaLogDerivMero σ hσ) (thetaSource σ) := by
  refine realizesMero_fraction (A := fun z => jacobiTheta₂' z σ) (B := fun z => jacobiTheta₂ z σ)
    (jacobiTheta₂'_analyticOnNhd_fst σ hσ) (jacobiTheta₂_analyticOnNhd_fst σ hσ)
    (thetaAnalytic_ne_zero σ hσ) ?_
  intro z hz
  rw [thetaSource, logDeriv_apply]
  congr 1
  exact (hasDerivAt_jacobiTheta₂_fst z hσ).deriv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The difference cube is a constant-coefficient operator -/

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_add (τ : ι → ℂ) (t : Finset ι) (x y : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (x + y) = diffCubeMero τ t x + diffCubeMero τ t y := by
  classical
  rw [diffCubeMero, diffCubeMero, diffCubeMero, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun E _ => by rw [map_add, smul_add]

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_finsetSum (τ : ι → ℂ) (t : Finset ι) {κ : Type*} (s : Finset κ)
    (x : κ → meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (∑ i ∈ s, x i) = ∑ i ∈ s, diffCubeMero τ t (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [diffCubeMero]
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, diffCubeMero_add, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_algebraMap_mul (τ : ι → ℂ) (t : Finset ι) (α : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (algebraMap ℂ (meroField (Set.univ : Set ℂ)) α * x)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) α * diffCubeMero τ t x := by
  classical
  rw [diffCubeMero, diffCubeMero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex, Algebra.smul_def, Algebra.smul_def]
  ring

omit [Fintype ι] in
theorem diffCubeMero_differentialJet (τ : ι → ℂ) (j : ℕ) :
    ∀ (t : Finset ι) (x : meroField (Set.univ : Set ℂ)),
      diffCubeMero τ t (differentialJet j x) = differentialJet j (diffCubeMero τ t x) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => intro x; simp
  | @insert q t' hq ih =>
      intro x
      rw [diffCubeMero_insert τ hq, ih x, diffCubeMero_insert τ hq,
        addTranslationMeroEquiv_differentialJet]
      exact (differentialJet_sub j _ _).symm

/-! ## The carrier jet combination -/

/-- A finite combination of jets of translates of the universal carrier, placed so that its bottom
witness is the atom sum with the prescribed coefficients. -/
def carrierAtomCombination (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) (k : ι)
    (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) : meroField (Set.univ : Set ℂ) :=
  ∑ j ∈ Finset.range N, ∑ q ∈ R,
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
      differentialJet j (addTranslationMeroEquiv ((1 + τ k) - q) (universalCarrierMero τ hτ s))

theorem diffCubeMero_carrierAtomCombination (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    (k : ι) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) (t : Finset ι) :
    diffCubeMero τ t (carrierAtomCombination τ hτ s k N R c)
      = ∑ j ∈ Finset.range N, ∑ q ∈ R,
          algebraMap ℂ (meroField (Set.univ : Set ℂ))
              (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
            differentialJet j (addTranslationMeroEquiv ((1 + τ k) - q)
              (diffCubeMero τ t (universalCarrierMero τ hτ s))) := by
  classical
  rw [carrierAtomCombination, diffCubeMero_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diffCubeMero_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [diffCubeMero_algebraMap_mul, diffCubeMero_differentialJet, diffCubeMero_translate_comm]

theorem addTranslationMeroEquiv_one_carrierAtomCombination (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) (k : ι) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    addTranslationMeroEquiv 1 (carrierAtomCombination τ hτ s k N R c)
      = carrierAtomCombination τ hτ s k N R c := by
  classical
  rw [carrierAtomCombination, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
    addTranslationMeroEquiv_differentialJet, addTranslationMeroEquiv_add,
    show (1 : ℂ) + ((1 + τ k) - q) = ((1 + τ k) - q) + 1 from by ring,
    ← addTranslationMeroEquiv_add, addTranslationMeroEquiv_one_universalCarrier]

/-- **The carrier jet combination lies in the all-depth class.** -/
theorem exists_mixedConst_carrierAtomCombination (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) (k : ι) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    ∃ Cst : ℂ, diffCubeMero τ s (carrierAtomCombination τ hτ s k N R c)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst := by
  classical
  refine ⟨∑ j ∈ Finset.range N, ∑ q ∈ R,
    (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) * differentialJet j (-(2 * Real.pi * I)), ?_⟩
  rw [diffCubeMero_carrierAtomCombination, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [diffCubeMero_universalCarrier, addTranslationMeroEquiv_algebraMap_complex,
    differentialJet_algebraMap_apply, ← map_mul]

/-! ## The bottom witness is an atom sum -/

/-- The germ of the atom sum with prescribed coefficients. -/
def atomSumMero (σ : ℂ) (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    meroField (Set.univ : Set ℂ) :=
  ∑ j ∈ Finset.range N, ∑ q ∈ R,
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
      differentialJet j (addTranslationMeroEquiv (thetaHalfPeriod σ - q) (thetaLogDerivMero σ hσ))

set_option maxHeartbeats 800000 in
/-- **The atom sum germ is realized by the atom sum function.** -/
theorem realizesMero_atomSumMero (σ : ℂ) (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) :
    RealizesMero (atomSumMero σ hσ N R c) (multiAtomRealization σ N R c) := by
  classical
  have hterm : ∀ (j : ℕ) (q : ℂ),
      RealizesMero
        (algebraMap ℂ (meroField (Set.univ : Set ℂ))
            (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          differentialJet j (addTranslationMeroEquiv (thetaHalfPeriod σ - q)
            (thetaLogDerivMero σ hσ)))
        (fun z => (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          jetAtom σ (q - thetaHalfPeriod σ) j z) := by
    intro j q
    have htrans := HTGeometry.realizesMero_translate (realizesMero_thetaLogDerivMero σ hσ)
      (thetaHalfPeriod σ - q)
    have hfun : (fun z => thetaSource σ (z + (thetaHalfPeriod σ - q)))
        = lineAtom σ (q - thetaHalfPeriod σ) := by
      funext z
      rw [lineAtom]
      congr 1
      ring
    rw [hfun] at htrans
    exact realizesMero_const_mul _ (realizesMero_iteratedDeriv htrans j)
  have hinner : ∀ j : ℕ,
      RealizesMero
        (∑ q ∈ R, algebraMap ℂ (meroField (Set.univ : Set ℂ))
            (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
          differentialJet j (addTranslationMeroEquiv (thetaHalfPeriod σ - q)
            (thetaLogDerivMero σ hσ)))
        (atomRealization σ j R (c j)) := by
    intro j
    have h := realizesMero_sum R _ _ (fun q _ => hterm j q)
    have hfun : (∑ q ∈ R, fun z => (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) *
        jetAtom σ (q - thetaHalfPeriod σ) j z) = atomRealization σ j R (c j) := by
      funext z
      simp only [atomRealization, Finset.sum_apply]
    rwa [hfun] at h
  have h := realizesMero_sum (Finset.range N) _ _ (fun j _ => hinner j)
  have hfun : (∑ j ∈ Finset.range N, atomRealization σ j R (c j))
      = multiAtomRealization σ N R c := by
    funext z
    simp only [multiAtomRealization, Finset.sum_apply]
  rwa [hfun] at h

set_option maxHeartbeats 800000 in
/-- **The bottom witness of the carrier jet combination is an atom sum up to a constant.** -/
theorem exists_bottomWitnessMero_carrierAtomCombination (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) {k : ι} (hk : k ∈ s) {a : ι} (hak : a ≠ k)
    (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    ∃ C : ℂ, bottomWitnessMero τ s k (carrierAtomCombination τ hτ s k N R c)
      = atomSumMero (τ k) (hτ k) N R c + algebraMap ℂ (meroField (Set.univ : Set ℂ)) C := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_bottomWitnessMero_universalCarrier_theta τ hτ s hk hak
  have hbot : diffCubeMero τ (s \ {k}) (universalCarrierMero τ hτ s)
      = addTranslationMeroEquiv (-(1 + τ k) / 2) (thetaLogDerivMero (τ k) (hτ k))
        + algebraMap ℂ (meroField (Set.univ : Set ℂ)) c₀ := by
    rw [← bottomWitnessMero, hc₀]
    rfl
  refine ⟨∑ j ∈ Finset.range N, ∑ q ∈ R,
    (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) * differentialJet j c₀, ?_⟩
  rw [bottomWitnessMero, diffCubeMero_carrierAtomCombination, atomSumMero, map_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hbot, map_add, addTranslationMeroEquiv_algebraMap_complex,
    addTranslationMeroEquiv_add,
    show ((1 : ℂ) + τ k) - q + (-(1 + τ k) / 2) = thetaHalfPeriod (τ k) - q from by
      rw [thetaHalfPeriod]; ring,
    differentialJet_add_apply, differentialJet_algebraMap_apply, mul_add, ← map_mul]

/-! ## Surjectivity of the bottom charge -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The bottom-charge map is surjective onto atom-sum divisors.**  Every finite divisor of
bounded order on the elliptic quotient of the surviving direction is the bottom charge of a member
of the all-depth mixed-constraint class. -/
theorem exists_class_member_with_prescribed_bottomCharge
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) {k : ι} (hk : k ∈ s) {a : ι}
    (hak : a ≠ k) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    ∃ (x : meroField (Set.univ : Set ℂ)) (f : ℂ → ℂ) (Cst : ℂ),
      RealizesMero x f ∧ PeriodicOneGerm f ∧ MixedConstGermSet τ s f Cst ∧
      ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        laurentCoeff (bottomWitnessFun τ s k f) p ℓ
          = laurentCoeff (multiAtomRealization (τ k) N R c) p ℓ := by
  classical
  obtain ⟨f, hf⟩ := exists_realizesMero (carrierAtomCombination τ hτ s k N R c)
  obtain ⟨Cst, hCst⟩ := exists_mixedConst_carrierAtomCombination τ hτ s k N R c
  obtain ⟨C, hC⟩ := exists_bottomWitnessMero_carrierAtomCombination τ hτ s hk hak N R c
  refine ⟨carrierAtomCombination τ hτ s k N R c, f, Cst, hf, ?_, ?_, ?_⟩
  · exact periodicOneGerm_of_realizesMero hf
      (addTranslationMeroEquiv_one_carrierAtomCombination τ hτ s k N R c)
  · intro z
    have hreal : RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst)
        (HTGeometry.diffCube τ s f) := by
      rw [← hCst]
      exact realizesMero_diffCubeMero τ s hf
    exact realizesMero_congr hreal (realizesMero_const Cst) z
  · intro p ℓ hℓ
    have h1 : RealizesMero (bottomWitnessMero τ s k (carrierAtomCombination τ hτ s k N R c))
        (bottomWitnessFun τ s k f) := bottomWitnessFun_realizesMero τ s k hf
    have h2 : RealizesMero (bottomWitnessMero τ s k (carrierAtomCombination τ hτ s k N R c))
        (fun z => multiAtomRealization (τ k) N R c z + C) := by
      rw [hC]
      exact realizesMero_add (realizesMero_atomSumMero (τ k) (hτ k) N R c)
        (realizesMero_const C)
    have hVmero : MeromorphicOn (bottomWitnessFun τ s k f) (Set.univ : Set ℂ) :=
      meromorphicOn_of_realizesMero h1
    have hZmero : MeromorphicOn (multiAtomRealization (τ k) N R c) (Set.univ : Set ℂ) :=
      meromorphicOn_multiAtomRealization (hτ k) N R c
    have hgerm := realizesMero_congr h1 h2 p
    rw [laurentCoeff_congr (hVmero p (Set.mem_univ p)) hgerm ℓ]
    exact laurentCoeff_add_const (hZmero p (Set.mem_univ p)) C hℓ

end

end GaloisForLFunctions
