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

omit [Fintype ι] [DecidableEq ι] in
/-- The difference cube of a meromorphic function is meromorphic. -/
theorem meromorphicOn_diffCube (τ : ι → ℂ) (t : Finset ι) {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) :
    MeromorphicOn (HTGeometry.diffCube τ t f) (Set.univ : Set ℂ) := by
  classical
  intro z _
  have hfun : HTGeometry.diffCube τ t f
      = ∑ E ∈ t.powerset, fun w => ((-1 : ℂ) ^ (t.card - E.card)) * f (w + ∑ i ∈ E, τ i) := by
    funext w
    simp only [HTGeometry.diffCube, Finset.sum_apply]
  rw [hfun]
  refine MeromorphicAt.sum fun E _ => ?_
  exact (analyticAt_const.meromorphicAt).mul
    (meromorphicAt_comp_add.mpr (hf _ (Set.mem_univ _)))

omit [Fintype ι] [DecidableEq ι] in
/-- The difference cube of a `1`-periodic germ is `1`-periodic. -/
theorem periodicOneGerm_diffCube (τ : ι → ℂ) (t : Finset ι) {f : ℂ → ℂ}
    (hf : PeriodicOneGerm f) : PeriodicOneGerm (HTGeometry.diffCube τ t f) := by
  classical
  intro z
  have hall : ∀ E ∈ t.powerset, ∀ᶠ w in 𝓝[≠] z,
      f (w + 1 + ∑ i ∈ E, τ i) = f (w + ∑ i ∈ E, τ i) := by
    intro E _
    have hpull := (tendsto_nhdsNE_add_const z (∑ i ∈ E, τ i)).eventually
      (hf (z + ∑ i ∈ E, τ i))
    filter_upwards [hpull] with w hw
    rw [show w + 1 + ∑ i ∈ E, τ i = w + ∑ i ∈ E, τ i + 1 from by ring]
    exact hw
  rw [← Filter.eventually_all_finset] at hall
  filter_upwards [hall] with w hw
  show ∑ E ∈ t.powerset, _ = ∑ E ∈ t.powerset, _
  exact Finset.sum_congr rfl fun E hE => by rw [hw E hE]

/-- The pair-face witness at function level. -/
def pairFaceWitnessFun (τ : ι → ℂ) (s : Finset ι) (i j : ι) (f : ℂ → ℂ) : ℂ → ℂ :=
  HTGeometry.diffCube τ (s \ {i, j}) f

omit [Fintype ι] in
theorem pairFaceWitnessFun_realizesMero (τ : ι → ℂ) (s : Finset ι) (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hf : RealizesMero x f) :
    RealizesMero (pairFaceWitnessMero τ s i j x) (pairFaceWitnessFun τ s i j f) :=
  realizesMero_diffCubeMero τ _ hf



omit [Fintype ι] in
/-- **The pair-face witness lies in the depth-two class.** -/
theorem mixedConstGerm_pairFaceWitnessFun (τ : ι → ℂ) (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) {Cst : ℂ} {f : ℂ → ℂ}
    (hmixed : MixedConstGermSet τ s f Cst) :
    MixedConstGerm (pairFaceWitnessFun τ s i j f) (τ j) (τ i) Cst := by
  classical
  have hunion : ({i, j} : Finset ι) ∪ (s \ {i, j}) = s := by
    ext k
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((rfl | rfl) | hk)
      · exact hi
      · exact hj
      · exact hk.1
    · intro hk
      by_cases hki : k = i
      · exact Or.inl (Or.inl hki)
      · by_cases hkj : k = j
        · exact Or.inl (Or.inr hkj)
        · exact Or.inr ⟨hk, by simp [hki, hkj]⟩
  have hdisj : Disjoint ({i, j} : Finset ι) (s \ {i, j}) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (Finset.mem_sdiff.mp hk').2 hk
  have hcube : HTGeometry.diffCube τ ({i, j} : Finset ι) (pairFaceWitnessFun τ s i j f)
      = HTGeometry.diffCube τ s f := by
    rw [pairFaceWitnessFun, ← HTGeometry.diffCube_union τ hdisj, hunion]
  have hset : MixedConstGermSet τ ({i, j} : Finset ι) (pairFaceWitnessFun τ s i j f) Cst := by
    intro z
    filter_upwards [hmixed z] with w hw
    rw [hcube]
    exact hw
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

set_option synthInstance.maxHeartbeats 800000 in
/-- **The forward half of the all-depth pair-face theorem.**  A differentially algebraic member of
the all-depth mixed-constraint class has vanishing pair-face signature at every pair. -/
theorem pairFaceSignature_eq_zero_of_differentialAlgebraicOver
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) {i j : ι} (hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hf : RealizesMero x f)
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst)
    (hDA : DifferentialAlgebraicOver ℂ x) :
    ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) p ℓ = 0 := by
  have hWDA : DifferentialAlgebraicOver ℂ (pairFaceWitnessMero τ s i j x) :=
    differentialAlgebraicOver_pairFaceWitnessMero τ s i j hDA
  have hWDA' : DifferentiallyAlgebraic
      (toMeromorphicNFOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ)) :=
    differentiallyAlgebraic_of_realizesMero (pairFaceWitnessFun_realizesMero τ s i j hf)
      (differentialAlgebraicOver_ratFunc_of_complex hWDA)
  exact additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic
    (meromorphicOn_diffCube τ _ (meromorphicOn_of_realizesMero hf))
    (periodicOneGerm_diffCube τ _ hper)
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed)
    (hτ j) (hτ i) (indepPeriods_of_periodsIntegrallyIndependent τ hQ hij)
    (linearIndependent_one_of_im_pos (hτ j)) (linearIndependent_one_of_im_pos (hτ i))
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hij.symm)
    hWDA'

end

end GaloisForLFunctions
