import GaloisForLFunctions.HTGeometry.AllDepthPairFaceSignature
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentLeading
import GaloisForLFunctions.HTGeometry.EllipticRegularPoint
import GaloisForLFunctions.HTGeometry.TripticEntireRigidity

/-!
# The bottom charge of an all-depth mixed-constraint member

Fix one distinguished direction `k`.  The *bottom witness* of `F ∈ Q_d` is

```text
V = ∏_(m ≠ k) Δ_(τ m) F,
```

the `(d−1)`-fold difference in every direction but `k`.  It is `1`-periodic and changes by the
class constant under `τ k`, so it is quasi-elliptic for `Λ_k = ℤ + ℤ τ k`, and its *bottom charge*
is its principal part

```text
ρ_k(F)(p, ℓ) = laurentCoeff V p ℓ,        ℓ < 0,
```

which is invariant along `Λ_k`.

Two facts make the all-depth descent run.  First, the pair-face signature at the pair `{i, k}` is
literally the `τ i`-orbit sum of the bottom charge — the pair-face witness differs from the bottom
witness by exactly the missing `Δ_(τ i)`.  Second, the bottom charge has trivial kernel modulo the
next class: a bottom witness with no principal part is entire, hence constant by the corpus's
rigidity theorem, which is precisely membership in `Q_(d−1)`.

* `bottomWitnessFun`, **`shiftDiffFun_pairFaceWitnessFun`**;
* **`additiveOrbitalDivisorAt_pairFaceWitnessFun`** — the signature is the orbit sum of the charge;
* `periodicOneGerm_bottomWitnessFun`, `shiftConstGerm_bottomWitnessFun`;
* **`mixedConstGermSet_erase_of_bottomCharge_eq_zero`** — the kernel of the bottom charge is the
  next class.
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

variable {ι : Type} [DecidableEq ι]

/-- The bottom witness in the distinguished direction `k`. -/
def bottomWitnessFun (τ : ι → ℂ) (s : Finset ι) (k : ι) (f : ℂ → ℂ) : ℂ → ℂ :=
  HTGeometry.diffCube τ (s \ {k}) f

/-- The germ-level bottom witness. -/
def bottomWitnessMero (τ : ι → ℂ) (s : Finset ι) (k : ι) (x : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  diffCubeMero τ (s \ {k}) x

theorem bottomWitnessFun_realizesMero (τ : ι → ℂ) (s : Finset ι) (k : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hf : RealizesMero x f) :
    RealizesMero (bottomWitnessMero τ s k x) (bottomWitnessFun τ s k f) :=
  realizesMero_diffCubeMero τ _ hf

/-- **The bottom witness is the missing difference of the pair-face witness.** -/
theorem shiftDiffFun_pairFaceWitnessFun (τ : ι → ℂ) (s : Finset ι) {i k : ι} (hik : i ≠ k)
    (hi : i ∈ s) (f : ℂ → ℂ) :
    HTGeometry.shiftDiffFun (τ i) (pairFaceWitnessFun τ s i k f) = bottomWitnessFun τ s k f := by
  classical
  have hdisj : Disjoint ({i} : Finset ι) (s \ {i, k}) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    have hmi : m = i := by simpa using hm
    refine (Finset.mem_sdiff.mp hm').2 ?_
    rw [hmi]
    exact Finset.mem_insert_self i {k}
  have hunion : ({i} : Finset ι) ∪ (s \ {i, k}) = s \ {k} := by
    ext m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff,
      Finset.mem_insert]
    constructor
    · rintro (rfl | hm)
      · exact ⟨hi, hik⟩
      · exact ⟨hm.1, fun h => hm.2 (Or.inr h)⟩
    · intro hm
      by_cases hmi : m = i
      · exact Or.inl hmi
      · exact Or.inr ⟨hm.1, fun h => h.elim hmi hm.2⟩
  rw [bottomWitnessFun, ← hunion, HTGeometry.diffCube_union τ hdisj,
    HTGeometry.diffCube_singleton]
  rfl

/-- **The pair-face signature is the orbit sum of the bottom charge.** -/
theorem additiveOrbitalDivisorAt_pairFaceWitnessFun (τ : ι → ℂ) (s : Finset ι) {i k : ι}
    (hik : i ≠ k) (hi : i ∈ s) (f : ℂ → ℂ) (p : ℂ) (ℓ : ℤ) :
    additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i k f) (τ i) p ℓ =
      ∑ᶠ m : ℤ, laurentCoeff (bottomWitnessFun τ s k f) (p + (m : ℂ) * τ i) ℓ := by
  rw [additiveOrbitalDivisorAt]
  refine finsum_congr fun m => ?_
  rw [← shiftDiffFun_pairFaceWitnessFun τ s hik hi f]
  rfl

theorem periodicOneGerm_bottomWitnessFun (τ : ι → ℂ) (s : Finset ι) (k : ι)
    {f : ℂ → ℂ} (hper : PeriodicOneGerm f) :
    PeriodicOneGerm (bottomWitnessFun τ s k f) :=
  periodicOneGerm_diffCube τ _ hper

/-- **The bottom witness changes by the class constant along the distinguished direction.** -/
theorem shiftConstGerm_bottomWitnessFun (τ : ι → ℂ) (s : Finset ι) (k : ι) (hk : k ∈ s)
    {Cst : ℂ} {f : ℂ → ℂ} (hmixed : MixedConstGermSet τ s f Cst) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,
      bottomWitnessFun τ s k f (w + τ k) - bottomWitnessFun τ s k f w = Cst := by
  classical
  have hdisj : Disjoint ({k} : Finset ι) (s \ {k}) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    exact (Finset.mem_sdiff.mp hm').2 hm
  have hunion : ({k} : Finset ι) ∪ (s \ {k}) = s := by
    ext m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
    constructor
    · rintro (rfl | hm)
      · exact hk
      · exact hm.1
    · intro hm
      by_cases hmk : m = k
      · exact Or.inl hmk
      · exact Or.inr ⟨hm, hmk⟩
  have hcube : HTGeometry.diffCube τ ({k} : Finset ι) (bottomWitnessFun τ s k f)
      = HTGeometry.diffCube τ s f := by
    rw [bottomWitnessFun, ← HTGeometry.diffCube_union τ hdisj, hunion]
  have h := hmixed z
  filter_upwards [h] with w hw
  have hw' : HTGeometry.diffCube τ ({k} : Finset ι) (bottomWitnessFun τ s k f) w = Cst := by
    rw [hcube]
    exact hw
  rw [HTGeometry.diffCube_singleton] at hw'
  exact hw'

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The kernel of the bottom charge is the next class.**  A bottom witness with no principal
part is entire; being `1`-periodic with a constant `τ k`-step it is constant, and the class
constant vanishes.  Constancy of the bottom witness is exactly membership in `Q_(d−1)`. -/
theorem exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero
    (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im) (s : Finset ι) (k : ι) (hk : k ∈ s)
    {Cst : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst)
    (hzero : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 → laurentCoeff (bottomWitnessFun τ s k f) p ℓ = 0) :
    Cst = 0 ∧ ∃ c : ℂ, MixedConstGermSet τ (s \ {k}) f c := by
  classical
  set V : ℂ → ℂ := bottomWitnessFun τ s k f with hVdef
  have hVmero : MeromorphicOn V (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  set W : ℂ → ℂ := toMeromorphicNFOn V (Set.univ : Set ℂ) with hWdef
  have hWNF : MeromorphicNFOn W (Set.univ : Set ℂ) :=
    meromorphicNFOn_toMeromorphicNFOn V (Set.univ : Set ℂ)
  have hWmero : MeromorphicOn W (Set.univ : Set ℂ) := hWNF.meromorphicOn
  have hWeq : ∀ z : ℂ, W =ᶠ[𝓝[≠] z] V := fun z =>
    hVmero.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hWan : ∀ z : ℂ, AnalyticAt ℂ W z := by
    intro z
    refine analyticAt_of_nonneg_meromorphicOrderAt hWNF ?_
    refine meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero
      (hWmero z (Set.mem_univ z)) fun ℓ hℓ => ?_
    rw [laurentCoeff_congr (hWmero z (Set.mem_univ z)) (hWeq z) ℓ]
    exact hzero z ℓ hℓ
  have hWdiff : Differentiable ℂ W := fun z => (hWan z).differentiableAt
  -- the unit period, pointwise
  have hWper : Function.Periodic W 1 := by
    intro z
    have hpull : ∀ᶠ w in 𝓝[≠] z, W (w + 1) = V (w + 1) := by
      have hmap := tendsto_nhdsNE_add_const z 1
      exact hmap.eventually (hWeq (z + 1))
    have hVper : ∀ᶠ w in 𝓝[≠] z, V (w + 1) = V w :=
      periodicOneGerm_bottomWitnessFun τ s k hper z
    have hbase : ∀ᶠ w in 𝓝[≠] z, W w = V w := hWeq z
    have heq : (fun w => W (w + 1)) =ᶠ[𝓝[≠] z] W := by
      filter_upwards [hpull, hVper, hbase] with w hw hw' hw''
      rw [hw, hw', ← hw'']
    have hc1 : ContinuousAt (fun w => W (w + 1)) z :=
      (analyticAt_comp_add_const (hWan (z + 1))).continuousAt
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt heq hc1 (hWan z).continuousAt).eq_of_nhds
  -- the distinguished step, pointwise
  have hWshift : ∀ z : ℂ, W (z + τ k) = W z + Cst := by
    intro z
    have hpull : ∀ᶠ w in 𝓝[≠] z, W (w + τ k) = V (w + τ k) := by
      have hmap := tendsto_nhdsNE_add_const z (τ k)
      exact hmap.eventually (hWeq (z + τ k))
    have hVshift : ∀ᶠ w in 𝓝[≠] z, V (w + τ k) - V w = Cst :=
      shiftConstGerm_bottomWitnessFun τ s k hk hmixed z
    have hbase : ∀ᶠ w in 𝓝[≠] z, W w = V w := hWeq z
    have heq : (fun w => W (w + τ k)) =ᶠ[𝓝[≠] z] (fun w => W w + Cst) := by
      filter_upwards [hpull, hVshift, hbase] with w hw hw' hw''
      rw [hw, hw'']
      linear_combination hw'
    have hc1 : ContinuousAt (fun w => W (w + τ k)) z :=
      (analyticAt_comp_add_const (hWan (z + τ k))).continuousAt
    have hc2 : ContinuousAt (fun w => W w + Cst) z := (hWan z).continuousAt.add continuousAt_const
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt heq hc1 hc2).eq_of_nhds
  obtain ⟨hWconst, hCst⟩ :=
    const_of_entire_periodic_of_shift_const (linearIndependent_one_of_im_pos (hτ k))
      hWdiff hWper hWshift
  refine ⟨hCst, W 0, ?_⟩
  intro z
  filter_upwards [hWeq z] with w hw
  show V w = W 0
  rw [← hw]
  exact hWconst w 0

/-! ## The bottom charge is a divisor on the elliptic quotient -/

set_option maxHeartbeats 800000 in
/-- **The bottom charge is invariant under the unit period.** -/
theorem laurentCoeff_bottomWitnessFun_add_one (τ : ι → ℂ) (s : Finset ι) (k : ι)
    {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm f) (a : ℂ) (ℓ : ℤ) :
    laurentCoeff (bottomWitnessFun τ s k f) (a + 1) ℓ =
      laurentCoeff (bottomWitnessFun τ s k f) a ℓ := by
  set V : ℂ → ℂ := bottomWitnessFun τ s k f with hVdef
  have hVmero : MeromorphicOn V (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hmero : MeromorphicAt (fun z => V (z + 1)) a :=
    meromorphicAt_comp_add.mpr (hVmero (a + 1) (Set.mem_univ _))
  calc laurentCoeff V (a + 1) ℓ
      = laurentCoeff (fun z => V (z + 1)) a ℓ := (laurentCoeff_comp_add V a 1 ℓ).symm
    _ = laurentCoeff V a ℓ :=
        laurentCoeff_congr hmero (periodicOneGerm_bottomWitnessFun τ s k hper a) ℓ

set_option maxHeartbeats 800000 in
/-- **The bottom charge is invariant under the distinguished period.** -/
theorem laurentCoeff_bottomWitnessFun_add_tau (τ : ι → ℂ) (s : Finset ι) (k : ι) (hk : k ∈ s)
    {Cst : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hmixed : MixedConstGermSet τ s f Cst)
    (a : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (bottomWitnessFun τ s k f) (a + τ k) ℓ =
      laurentCoeff (bottomWitnessFun τ s k f) a ℓ := by
  set V : ℂ → ℂ := bottomWitnessFun τ s k f with hVdef
  have hVmero : MeromorphicOn V (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hmero : MeromorphicAt (fun z => V (z + τ k)) a :=
    meromorphicAt_comp_add.mpr (hVmero (a + τ k) (Set.mem_univ _))
  have hstep : (fun z => V (z + τ k)) =ᶠ[𝓝[≠] a] (fun z => V z + Cst) := by
    filter_upwards [shiftConstGerm_bottomWitnessFun τ s k hk hmixed a] with w hw
    linear_combination hw
  calc laurentCoeff V (a + τ k) ℓ
      = laurentCoeff (fun z => V (z + τ k)) a ℓ := (laurentCoeff_comp_add V a (τ k) ℓ).symm
    _ = laurentCoeff (fun z => V z + Cst) a ℓ := laurentCoeff_congr hmero hstep ℓ
    _ = laurentCoeff V a ℓ := laurentCoeff_add_const (hVmero a (Set.mem_univ a)) Cst hℓ

set_option maxHeartbeats 1000000 in
/-- **The bottom charge has finite support on the elliptic quotient.**  Its poles are invariant
under `Λ_k = ℤ + ℤ τ k`, so they meet only finitely many classes. -/
theorem exists_finset_bottomCharge_pole_classes (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (s : Finset ι) (k : ι) (hk : k ∈ s)
    {Cst : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst) :
    ∃ P : Finset ℂ, ∀ z : ℂ, meromorphicOrderAt (bottomWitnessFun τ s k f) z < 0 →
      ∃ m n : ℤ, z - (m • (1 : ℂ) + n • τ k) ∈ P := by
  set V : ℂ → ℂ := bottomWitnessFun τ s k f with hVdef
  have hVmero : MeromorphicOn V (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hinvOne : ∀ (ℓ : ℤ), ℓ < 0 → ∀ z : ℂ,
      laurentCoeff V (z + 1) ℓ = laurentCoeff V z ℓ := fun ℓ _ z =>
    laurentCoeff_bottomWitnessFun_add_one τ s k hmero hper z ℓ
  have hinvTau : ∀ (ℓ : ℤ), ℓ < 0 → ∀ z : ℂ,
      laurentCoeff V (z + τ k) ℓ = laurentCoeff V z ℓ := fun ℓ hℓ z =>
    laurentCoeff_bottomWitnessFun_add_tau τ s k hk hmero hmixed z hℓ
  have hstepOne : ∀ z : ℂ, meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z + 1) < 0 :=
    fun z hz => pole_invariant_of_laurentCoeff_invariant hVmero hinvOne hz
  have hstepTau : ∀ z : ℂ, meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z + τ k) < 0 :=
    fun z hz => pole_invariant_of_laurentCoeff_invariant hVmero hinvTau hz
  have hstepOneNeg : ∀ z : ℂ, meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z - 1) < 0 := by
    intro z hz
    have := hstepOne (z - 1)
    by_contra hcon
    push Not at hcon
    have hle : ¬ meromorphicOrderAt V (z - 1) < 0 := not_lt.mpr hcon
    have hback : ∀ (ℓ : ℤ), ℓ < 0 → laurentCoeff V z ℓ = laurentCoeff V (z - 1) ℓ := by
      intro ℓ hℓ
      have := hinvOne ℓ hℓ (z - 1)
      rw [sub_add_cancel] at this
      exact this
    obtain ⟨ℓ, hℓ, hne⟩ :=
      (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hVmero z (Set.mem_univ z))).mp hz
    refine hle ((meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
      (hVmero (z - 1) (Set.mem_univ _))).mpr ⟨ℓ, hℓ, ?_⟩)
    rw [← hback ℓ hℓ]
    exact hne
  have hstepTauNeg : ∀ z : ℂ, meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z - τ k) < 0 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have hle : ¬ meromorphicOrderAt V (z - τ k) < 0 := not_lt.mpr hcon
    have hback : ∀ (ℓ : ℤ), ℓ < 0 → laurentCoeff V z ℓ = laurentCoeff V (z - τ k) ℓ := by
      intro ℓ hℓ
      have := hinvTau ℓ hℓ (z - τ k)
      rw [sub_add_cancel] at this
      exact this
    obtain ⟨ℓ, hℓ, hne⟩ :=
      (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hVmero z (Set.mem_univ z))).mp hz
    refine hle ((meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
      (hVmero (z - τ k) (Set.mem_univ _))).mpr ⟨ℓ, hℓ, ?_⟩)
    rw [← hback ℓ hℓ]
    exact hne
  have hinv : ∀ (m n : ℤ) (z : ℂ), meromorphicOrderAt V z < 0 →
      meromorphicOrderAt V (z - (m • (1 : ℂ) + n • τ k)) < 0 := by
    intro m n z hz
    have hone : ∀ (j : ℤ) (w : ℂ), meromorphicOrderAt V w < 0 →
        meromorphicOrderAt V (w - j • (1 : ℂ)) < 0 := by
      intro j
      induction j using Int.induction_on with
      | zero => intro w hw; simpa using hw
      | succ p ih =>
          intro w hw
          have h1 := ih w hw
          have := hstepOneNeg _ h1
          have harg : w - (p : ℤ) • (1 : ℂ) - 1 = w - ((p : ℤ) + 1) • (1 : ℂ) := by
            ring
          rwa [harg] at this
      | pred p ih =>
          intro w hw
          have h1 := ih w hw
          have := hstepOne _ h1
          have harg : w - (-(p : ℤ)) • (1 : ℂ) + 1 = w - (-(p : ℤ) - 1) • (1 : ℂ) := by
            ring
          rwa [harg] at this
    have htau : ∀ (j : ℤ) (w : ℂ), meromorphicOrderAt V w < 0 →
        meromorphicOrderAt V (w - j • τ k) < 0 := by
      intro j
      induction j using Int.induction_on with
      | zero => intro w hw; simpa using hw
      | succ p ih =>
          intro w hw
          have h1 := ih w hw
          have := hstepTauNeg _ h1
          have harg : w - (p : ℤ) • τ k - τ k = w - ((p : ℤ) + 1) • τ k := by
            ring
          rwa [harg] at this
      | pred p ih =>
          intro w hw
          have h1 := ih w hw
          have := hstepTau _ h1
          have harg : w - (-(p : ℤ)) • τ k + τ k = w - (-(p : ℤ) - 1) • τ k := by
            ring
          rwa [harg] at this
    have hmn := htau n _ (hone m z hz)
    have harg : z - m • (1 : ℂ) - n • τ k = z - (m • (1 : ℂ) + n • τ k) := by ring
    rwa [harg] at hmn
  exact exists_finset_pole_classes hVmero
    (linearIndependent_one_of_im_pos (hτ k)) hinv

end

end GaloisForLFunctions
