import GaloisForLFunctions.HTGeometry.AllDepthMixedConstraintClass
import GaloisForLFunctions.HTGeometry.MeromorphicFractionRealization
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid
import GaloisForLFunctions.HTGeometry.OrderTwoStructuralTranslateDecomposition

/-!
# The all-depth mixed-constraint class inside the meromorphic germ field

The pair-face signature theorem needs differential algebraicity to be closed under finite sums of
translates.  For functions with poles that is delicate; inside the meromorphic germ field
`meroField ℂ = Frac(analyticSubring ℂ)` it is field algebra.  This file therefore places the
all-depth class in the germ field, and records the bridge back to functions: every germ is a
quotient of entire germs, hence has a realization.

* **`exists_realizesMero`** — every germ of the meromorphic field is realized by a function;
* `diffCubeMero` — the difference cube on germs, and `diffCubeMero_insert`;
* `AllDepthMeroSource` — the class `Q_d` on germs;
* `pairFaceWitnessMero` — the pair-face witness `W_ij`;
* **`differentialAlgebraicOver_pairFaceWitnessMero`** — the forward half: a differentially
  algebraic member has differentially algebraic pair-face witnesses.
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

/-- **Every germ of the meromorphic field is realized by a function.**  It is a quotient of two
entire germs, and any pair of entire representatives realizes it. -/
theorem exists_realizesMero (x : meroField (Set.univ : Set ℂ)) :
    ∃ f : ℂ → ℂ, HTGeometry.RealizesMero x f := by
  classical
  obtain ⟨a, b, hbmem, hx⟩ :=
    IsFractionRing.div_surjective (A := analyticSubring (Set.univ : Set ℂ)) x
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  refine ⟨fun z => A z / B z, a, b, A, B, ?_, hA, hB, hAa, hBb, hx.symm, fun z _ => rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mp hbmem

variable {ι : Type*} [DecidableEq ι]

/-- The `s`-fold difference cube on meromorphic germs. -/
def diffCubeMero (τ : ι → ℂ) (s : Finset ι) (x : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  ∑ E ∈ s.powerset, ((-1 : ℂ) ^ (s.card - E.card)) •
    addTranslationMeroEquiv (∑ i ∈ E, τ i) x

omit [DecidableEq ι] in
@[simp] theorem diffCubeMero_empty (τ : ι → ℂ) (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ (∅ : Finset ι) x = x := by
  simp [diffCubeMero, addTranslationMeroEquiv_zero_apply]

/-- **The germ cube is the iterated one-step difference.** -/
theorem diffCubeMero_insert (τ : ι → ℂ) {s : Finset ι} {q : ι} (hq : q ∉ s)
    (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ (insert q s) x =
      addTranslationMeroEquiv (τ q) (diffCubeMero τ s x) - diffCubeMero τ s x := by
  classical
  rw [diffCubeMero, diffCubeMero, Finset.powerset_insert, Finset.sum_union,
    Finset.sum_image]
  · have hcard : (insert q s).card = s.card + 1 := Finset.card_insert_of_notMem hq
    have hleft : ∑ E ∈ s.powerset,
        ((-1 : ℂ) ^ ((insert q s).card - E.card)) •
          addTranslationMeroEquiv (∑ i ∈ E, τ i) x =
        -∑ E ∈ s.powerset, ((-1 : ℂ) ^ (s.card - E.card)) •
          addTranslationMeroEquiv (∑ i ∈ E, τ i) x := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEs : E.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hE)
      rw [hcard, show s.card + 1 - E.card = (s.card - E.card) + 1 by omega, pow_succ]
      module
    have hright : ∑ E ∈ s.powerset,
        ((-1 : ℂ) ^ ((insert q s).card - (insert q E).card)) •
          addTranslationMeroEquiv (∑ i ∈ insert q E, τ i) x =
        addTranslationMeroEquiv (τ q)
          (∑ E ∈ s.powerset, ((-1 : ℂ) ^ (s.card - E.card)) •
            addTranslationMeroEquiv (∑ i ∈ E, τ i) x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEsub : E ⊆ s := Finset.mem_powerset.mp hE
      have hqE : q ∉ E := fun h => hq (hEsub h)
      have hpow : (insert q s).card - (insert q E).card = s.card - E.card := by
        rw [Finset.card_insert_of_notMem hqE, hcard]
        omega
      rw [hpow, Finset.sum_insert hqE, ← addTranslationMeroEquiv_add,
        Algebra.smul_def, Algebra.smul_def, map_mul,
        addTranslationMeroEquiv_algebraMap_complex]
    rw [hleft, hright]
    abel
  · intro E hE E' hE' hEE'
    have hqE : q ∉ E := fun h => hq (Finset.mem_powerset.mp hE h)
    have hqE' : q ∉ E' := fun h => hq (Finset.mem_powerset.mp hE' h)
    have h1 : (insert q E).erase q = E := Finset.erase_insert hqE
    have h2 : (insert q E').erase q = E' := Finset.erase_insert hqE'
    rw [← h1, hEE', h2]
  · rw [Finset.disjoint_right]
    intro E hE hEs
    obtain ⟨E', -, rfl⟩ := Finset.mem_image.mp hE
    exact hq (Finset.mem_powerset.mp hEs (Finset.mem_insert_self q E'))

/-- The all-depth mixed-constraint class on germs: `1`-periodic with constant full mixed
difference. -/
def AllDepthMeroSource (τ : ι → ℂ) [Fintype ι] (x : meroField (Set.univ : Set ℂ))
    (Cst : ℂ) : Prop :=
  addTranslationMeroEquiv 1 x = x ∧
    diffCubeMero τ (Finset.univ : Finset ι) x =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst

/-- The pair-face witness `W_ij(F) = ∏_(k ∉ {i,j}) Δ_k F`. -/
def pairFaceWitnessMero (τ : ι → ℂ) [Fintype ι] (i j : ι)
    (x : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  diffCubeMero τ ((Finset.univ : Finset ι) \ {i, j}) x

omit [DecidableEq ι] in
/-- The difference cube preserves differential algebraicity. -/
theorem differentialAlgebraicOver_diffCubeMero (τ : ι → ℂ) (s : Finset ι)
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver ℂ x) :
    DifferentialAlgebraicOver ℂ (diffCubeMero τ s x) := by
  classical
  rw [diffCubeMero]
  refine differentialAlgebraicOver_finset_sum _ fun E _ => ?_
  rw [Algebra.smul_def]
  exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap _)
    (differentialAlgebraicOver_addTranslationMeroEquiv _ hx)

/-- **The forward half.**  A differentially algebraic member of the class has differentially
algebraic pair-face witnesses. -/
theorem differentialAlgebraicOver_pairFaceWitnessMero (τ : ι → ℂ) [Fintype ι] (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver ℂ x) :
    DifferentialAlgebraicOver ℂ (pairFaceWitnessMero τ i j x) :=
  differentialAlgebraicOver_diffCubeMero τ _ hx

section Transport

open Filter

/-- **Realization commutes with translation.** -/
theorem realizesMero_translate (c : ℂ) {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (hx : RealizesMero x f) :
    RealizesMero (addTranslationMeroEquiv c x) (fun z => f (z + c)) := by
  classical
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hx
  have htr : Filter.Tendsto (addTranslation c) (𝓟 (Set.univ : Set ℂ))
      (𝓟 (Set.univ : Set ℂ)) :=
    Filter.tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  have hcoe : ∀ (u : analyticSubring (Set.univ : Set ℂ)) (U : ℂ → ℂ),
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) U = (u : Germ (𝓟 Set.univ) ℂ) →
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun z => U (z + c)) =
        ((addTranslationAnalyticEquiv c u : analyticSubring (Set.univ : Set ℂ)) :
          Germ (𝓟 Set.univ) ℂ) := by
    intro u U hU
    change _ = (u : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation c) htr
    rw [← hU]
    rfl
  have hanal : ∀ U : ℂ → ℂ, AnalyticOnNhd ℂ U (Set.univ : Set ℂ) →
      AnalyticOnNhd ℂ (fun z => U (z + c)) (Set.univ : Set ℂ) := by
    intro U hU
    have h := hU.comp (analyticOnNhd_addTranslation c (Set.univ : Set ℂ))
      (Set.mapsTo_univ _ _)
    exact h
  refine ⟨addTranslationAnalyticEquiv c a, addTranslationAnalyticEquiv c b,
    (fun z => A (z + c)), (fun z => B (z + c)), ?_, hanal A hA, hanal B hB,
    hcoe a A hAa, hcoe b B hBb, ?_, fun z hz => hfAB (z + c) hz⟩
  · intro h
    exact hb0 ((addTranslationAnalyticEquiv c).injective (by simpa using h))
  · rw [hxab, map_div₀, addTranslationMeroEquiv_algebraMap,
      addTranslationMeroEquiv_algebraMap]

/-- **Two realizations of the same germ agree punctured-locally everywhere.** -/
theorem realizesMero_congr {x : meroField (Set.univ : Set ℂ)} {f g : ℂ → ℂ}
    (hf : RealizesMero x f) (hg : RealizesMero x g) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, f w = g w := by
  classical
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hf
  obtain ⟨c, d, C, D, hd0, hC, hD, hCc, hDd, hxcd, hgCD⟩ := hg
  have hcross : a * d = c * b := by
    have h := hxab.symm.trans hxcd
    have hbne := algebraMap_analyticSubring_ne_zero hb0
    have hdne := algebraMap_analyticSubring_ne_zero hd0
    rw [div_eq_div_iff hbne hdne] at h
    have h2 : (algebraMap (analyticSubring (Set.univ : Set ℂ))
        (meroField Set.univ)) (a * d) =
        (algebraMap (analyticSubring (Set.univ : Set ℂ))
          (meroField Set.univ)) (c * b) := by
      rw [map_mul, map_mul]
      exact h
    exact IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
      (meroField Set.univ) h2
  have hgermAD : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (A * D) =
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (C * B) := by
    have hval : ((a * d : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
        ((c * b : analyticSubring (Set.univ : Set ℂ)) :
          Germ (𝓟 (Set.univ : Set ℂ)) ℂ) := by rw [hcross]
    rw [map_mul, map_mul, hAa, hDd, hCc, hBb]
    simpa using hval
  have hAD : ∀ w : ℂ, A w * D w = C w * B w := by
    have h := Germ.coe_eq.mp hgermAD
    have h' := Filter.eventually_principal.mp h
    intro w
    exact h' w (Set.mem_univ w)
  have hBne : ∀ᶠ w in 𝓝[≠] z, B w ≠ 0 :=
    eventually_nhdsNE_ne_zero_of_germ_ne_zero hb0 hB hBb z
  have hDne : ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
    eventually_nhdsNE_ne_zero_of_germ_ne_zero hd0 hD hDd z
  filter_upwards [hBne, hDne] with w hw hw'
  rw [hfAB w hw, hgCD w hw']
  field_simp
  linear_combination (hAD w)

/-- **The unit period transports to the realization.** -/
theorem periodicOneGerm_of_realizesMero {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (hf : RealizesMero x f) (h1 : addTranslationMeroEquiv 1 x = x) :
    PeriodicOneGerm f := by
  intro z
  have hshift : RealizesMero x (fun w => f (w + 1)) := by
    have h := realizesMero_translate 1 hf
    rwa [h1] at h
  exact realizesMero_congr hshift hf z

/-- **The germ cube of a disjoint union is the composite of the two cubes.** -/
theorem diffCubeMero_union (τ : ι → ℂ) {s t : Finset ι} (hd : Disjoint s t)
    (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ (s ∪ t) x = diffCubeMero τ s (diffCubeMero τ t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
      have hqt : q ∉ t := fun hqt =>
        (Finset.disjoint_left.mp hd (Finset.mem_insert_self q s)) hqt
      have hst : Disjoint s t := hd.mono_left (Finset.subset_insert q s)
      have hunion : insert q s ∪ t = insert q (s ∪ t) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      have hqst : q ∉ s ∪ t := by
        simp only [Finset.mem_union]
        tauto
      rw [hunion, diffCubeMero_insert τ hqst x, ih hst,
        diffCubeMero_insert τ hq (diffCubeMero τ t x)]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The germ cube is realized by the function cube.** -/
theorem realizesMero_diffCubeMero (τ : ι → ℂ) (s : Finset ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hx : RealizesMero x f) :
    RealizesMero (diffCubeMero τ s x) (HTGeometry.diffCube τ s f) := by
  classical
  have hterm : ∀ E ∈ s.powerset,
      RealizesMero (((-1 : ℂ) ^ (s.card - E.card)) •
          addTranslationMeroEquiv (∑ i ∈ E, τ i) x)
        (fun z => ((-1 : ℂ) ^ (s.card - E.card)) * f (z + ∑ i ∈ E, τ i)) := by
    intro E _
    have h := realizesMero_const_mul ((-1 : ℂ) ^ (s.card - E.card))
      (realizesMero_translate (∑ i ∈ E, τ i) hx)
    have hsmul : ((-1 : ℂ) ^ (s.card - E.card)) •
        addTranslationMeroEquiv (∑ i ∈ E, τ i) x =
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
            (constToAnalytic Set.univ ((-1 : ℂ) ^ (s.card - E.card))) *
          addTranslationMeroEquiv (∑ i ∈ E, τ i) x := by
      rw [Algebra.smul_def]
      rfl
    rw [hsmul]
    exact h
  have hsum := realizesMero_sum s.powerset
    (fun E => ((-1 : ℂ) ^ (s.card - E.card)) •
      addTranslationMeroEquiv (∑ i ∈ E, τ i) x)
    (fun E => fun z => ((-1 : ℂ) ^ (s.card - E.card)) * f (z + ∑ i ∈ E, τ i))
    hterm
  have hfun : (∑ E ∈ s.powerset, fun z : ℂ =>
      ((-1 : ℂ) ^ (s.card - E.card)) * f (z + ∑ i ∈ E, τ i)) =
      HTGeometry.diffCube τ s f := by
    funext z
    rw [Finset.sum_apply]
    rfl
  have hgerm : (∑ E ∈ s.powerset, ((-1 : ℂ) ^ (s.card - E.card)) •
      addTranslationMeroEquiv (∑ i ∈ E, τ i) x) = diffCubeMero τ s x := rfl
  rw [← hfun, ← hgerm]
  exact hsum

end Transport

end

end GaloisForLFunctions
