import GaloisForLFunctions.HTGeometry.AllDepthMeroClass
import GaloisForLFunctions.HTGeometry.TripticCompleteness
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.EllipticGammaFlatNonvanishing
import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness

/-!
# The pair-face signature and its vanishing on differentially algebraic members

For a member `x` of the all-depth mixed-constraint class `Q_d` and a pair `{i, j}` of parameters,
the *pair-face witness* is

```text
W_ij(x) = ∏_(k ∉ {i,j}) Δ_(τ k) x,
```

a member of the depth-two class `Q_2(τ i, τ j)`, and the *pair-face signature* `S_ij(x)` is its
complete triptic orbit-residue divisor `R_2^{ij}`.

This file constructs the witness at function level, transports the three structural hypotheses of
the corpus's depth-two completeness theorem to it, and proves the **forward half** of the all-depth
pair-face theorem: a differentially algebraic member has vanishing pair-face signatures.

* `realizesMero_const`, `diffCubeMero_translate_comm` — transport plumbing;
* `pairFaceWitnessFun`, `pairFaceWitnessFun_realizesMero`;
* `meromorphicOn_pairFaceWitnessFun`, `periodicOneGerm_pairFaceWitnessFun`,
  **`mixedConstGerm_pairFaceWitnessFun`**;
* `indepPeriods_of_periodsIntegrallyIndependent`;
* **`pairFaceSignature_eq_zero_of_differentialAlgebraicOver`** — the forward half.
-/

open Filter Set Topology
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

/-- **Constants are realized by constant functions.** -/
theorem realizesMero_const (c : ℂ) :
    RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) (fun _ : ℂ => c) := by
  refine ⟨constToAnalytic Set.univ c, 1, (fun _ : ℂ => c), (fun _ : ℂ => 1), one_ne_zero,
    analyticOnNhd_const, analyticOnNhd_const, rfl, map_one _, ?_, fun z _ => by simp⟩
  rw [map_one, div_one]
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **The germ cube commutes with translation.** -/
theorem diffCubeMero_translate_comm (τ : ι → ℂ) (s : Finset ι) (c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ s (addTranslationMeroEquiv c x) =
      addTranslationMeroEquiv c (diffCubeMero τ s x) := by
  classical
  rw [diffCubeMero, diffCubeMero, map_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    addTranslationMeroEquiv_algebraMap_complex, addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_add, add_comm c (∑ i ∈ E, τ i)]

/-- The pair-face witness at function level. -/
def pairFaceWitnessFun (τ : ι → ℂ) (i j : ι) (f : ℂ → ℂ) : ℂ → ℂ :=
  HTGeometry.diffCube τ ((Finset.univ : Finset ι) \ {i, j}) f

theorem pairFaceWitnessFun_realizesMero (τ : ι → ℂ) (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hf : RealizesMero x f) :
    RealizesMero (pairFaceWitnessMero τ i j x) (pairFaceWitnessFun τ i j f) :=
  realizesMero_diffCubeMero τ _ hf

theorem meromorphicOn_pairFaceWitnessFun (τ : ι → ℂ) (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hf : RealizesMero x f) :
    MeromorphicOn (pairFaceWitnessFun τ i j f) (Set.univ : Set ℂ) :=
  meromorphicOn_of_realizesMero (pairFaceWitnessFun_realizesMero τ i j hf)

theorem periodicOneGerm_pairFaceWitnessFun (τ : ι → ℂ) (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hf : RealizesMero x f)
    (h1 : addTranslationMeroEquiv 1 x = x) :
    PeriodicOneGerm (pairFaceWitnessFun τ i j f) := by
  refine periodicOneGerm_of_realizesMero (pairFaceWitnessFun_realizesMero τ i j hf) ?_
  rw [pairFaceWitnessMero, ← diffCubeMero_translate_comm, h1]

/-- **The pair-face witness lies in the depth-two class.** -/
theorem mixedConstGerm_pairFaceWitnessFun (τ : ι → ℂ) {i j : ι} (hij : i ≠ j)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hf : RealizesMero x f)
    (hmixed : diffCubeMero τ (Finset.univ : Finset ι) x =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst) :
    MixedConstGerm (pairFaceWitnessFun τ i j f) (τ j) (τ i) Cst := by
  classical
  have hunion : ({i, j} : Finset ι) ∪ ((Finset.univ : Finset ι) \ {i, j}) =
      (Finset.univ : Finset ι) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint ({i, j} : Finset ι) ((Finset.univ : Finset ι) \ {i, j}) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (Finset.mem_sdiff.mp hk').2 hk
  have hcube : diffCubeMero τ ({i, j} : Finset ι) (pairFaceWitnessMero τ i j x) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst := by
    rw [pairFaceWitnessMero, ← diffCubeMero_union τ hdisj, hunion]
    exact hmixed
  have hreal : RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst)
      (HTGeometry.diffCube τ ({i, j} : Finset ι) (pairFaceWitnessFun τ i j f)) := by
    rw [← hcube]
    exact realizesMero_diffCubeMero τ _ (pairFaceWitnessFun_realizesMero τ i j hf)
  have hset : MixedConstGermSet τ ({i, j} : Finset ι) (pairFaceWitnessFun τ i j f) Cst := by
    intro z
    have h := realizesMero_congr hreal (realizesMero_const Cst) z
    exact h
  exact (mixedConstGermSet_pair_iff hij).mp hset

omit [DecidableEq ι] in
/-- Two distinct parameters and `1` admit no nontrivial integral relation. -/
theorem indepPeriods_of_periodsIntegrallyIndependent (τ : ι → ℂ)
    (hQ : PeriodsIntegrallyIndependent τ) {i j : ι} (hij : i ≠ j) :
    IndepPeriods (τ j) (τ i) := by
  classical
  intro p q r hrel
  have hterm : ∀ k : ι,
      ((((if k = j then q else 0) + (if k = i then r else 0) : ℤ)) : ℂ) * τ k =
        (if k = j then (q : ℂ) * τ k else 0) + (if k = i then (r : ℂ) * τ k else 0) := by
    intro k
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ k, ((((if k = j then q else 0) + (if k = i then r else 0) : ℤ)) : ℂ) * τ k =
      (q : ℂ) * τ j + (r : ℂ) * τ i := by
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ j fun k => (q : ℂ) * τ k,
      Finset.sum_ite_eq' Finset.univ i fun k => (r : ℂ) * τ k]
    simp
  have hzero : (p : ℂ) +
      ∑ k, ((((if k = j then q else 0) + (if k = i then r else 0) : ℤ)) : ℂ) * τ k = 0 := by
    rw [hsum]
    linear_combination hrel
  obtain ⟨hp, hn⟩ := hQ _ _ hzero
  have hj := hn j
  have hi := hn i
  rw [if_pos rfl, if_neg (fun h => hij h.symm)] at hj
  rw [if_neg hij, if_pos rfl] at hi
  exact ⟨hp, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The forward half of the all-depth pair-face theorem.**  A differentially algebraic member of
the all-depth mixed-constraint class has vanishing pair-face signature at every pair. -/
theorem pairFaceSignature_eq_zero_of_differentialAlgebraicOver
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    {i j : ι} (hij : i ≠ j)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hf : RealizesMero x f)
    (h1 : addTranslationMeroEquiv 1 x = x)
    (hmixed : diffCubeMero τ (Finset.univ : Finset ι) x =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst)
    (hDA : DifferentialAlgebraicOver ℂ x) :
    ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      additiveOrbitalDivisorAt (pairFaceWitnessFun τ i j f) (τ i) p ℓ = 0 := by
  have hWDA : DifferentialAlgebraicOver ℂ (pairFaceWitnessMero τ i j x) :=
    differentialAlgebraicOver_pairFaceWitnessMero τ i j hDA
  have hWDA' : DifferentiallyAlgebraic
      (toMeromorphicNFOn (pairFaceWitnessFun τ i j f) (Set.univ : Set ℂ)) :=
    differentiallyAlgebraic_of_realizesMero (pairFaceWitnessFun_realizesMero τ i j hf)
      (differentialAlgebraicOver_ratFunc_of_complex hWDA)
  exact additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic
    (meromorphicOn_pairFaceWitnessFun τ i j hf)
    (periodicOneGerm_pairFaceWitnessFun τ i j hf h1)
    (mixedConstGerm_pairFaceWitnessFun τ hij hf hmixed)
    (hτ j) (hτ i) (indepPeriods_of_periodsIntegrallyIndependent τ hQ hij)
    (linearIndependent_one_of_im_pos (hτ j)) (linearIndependent_one_of_im_pos (hτ i))
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hij.symm)
    hWDA'

end

end GaloisForLFunctions
