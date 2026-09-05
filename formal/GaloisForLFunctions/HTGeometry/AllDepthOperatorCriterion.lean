import GaloisForLFunctions.HTGeometry.AllDepthExactImage
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative
import GaloisForLFunctions.HTGeometry.AllDepthCarrierJets

/-!
# The constant-coefficient differential-translation criterion

The pair-face signature is equivariant for complex translation and turns the derivation into the
order shift with the jet factor.  Consequently a finite constant-coefficient
differential-translation operator applied to a member of the all-depth class is differentially
algebraic exactly when the corresponding operator kills every pair-face signature.

* `diffCube_comp_add`, `pairSig_translate`;
* `pairSig_deriv`.
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

variable {ι : Type} [DecidableEq ι]

/-- The difference cube commutes with translation. -/
theorem diffCube_comp_add (τ : ι → ℂ) (t : Finset ι) (f : ℂ → ℂ) (h : ℂ) :
    HTGeometry.diffCube τ t (fun z => f (z + h))
      = fun z => HTGeometry.diffCube τ t f (z + h) := by
  classical
  funext z
  show ∑ E ∈ t.powerset, _ = ∑ E ∈ t.powerset, _
  refine Finset.sum_congr rfl fun E _ => ?_
  congr 2
  ring

/-- **The signature is translation equivariant.** -/
theorem pairSig_translate (τ : ι → ℂ) (s : Finset ι) (i j : ι) (f : ℂ → ℂ) (h : ℂ)
    (ℓ : ℤ) (p : ℂ) :
    pairSig τ s (fun z => f (z + h)) i j ℓ p = pairSig τ s f i j ℓ (p + h) := by
  have hw : pairFaceWitnessFun τ s i j (fun z => f (z + h))
      = fun z => pairFaceWitnessFun τ s i j f (z + h) :=
    diffCube_comp_add τ _ f h
  rw [pairSig, pairSig, hw]
  exact additiveOrbitalDivisorAt_comp_add (pairFaceWitnessFun τ s i j f) (τ i) h p ℓ

section Deriv

variable [Fintype ι]

set_option synthInstance.maxHeartbeats 800000 in
/-- **The signature turns the derivation into the order shift with the jet factor.** -/
theorem pairSig_deriv (τ : ι → ℂ) (s : Finset ι) (i j : ι)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (ℓ : ℤ) (p : ℂ) :
    pairSig τ s (deriv f) i j ℓ p = ((ℓ : ℂ) + 1) * pairSig τ s f i j (ℓ + 1) p := by
  classical
  set y : meroField (Set.univ : Set ℂ) := diffCubeMero τ (s \ {i, j}) x with hy
  have hW : RealizesMero y (pairFaceWitnessFun τ s i j f) := realizesMero_diffCubeMero τ _ hx
  have hcomm : diffCubeMero τ (s \ {i, j}) (x′) = y′ := by
    have h := diffCubeMero_differentialJet τ 1 (s \ {i, j}) x
    simpa [differentialJet_succ, differentialJet_zero] using h
  have hW' : RealizesMero (y′) (pairFaceWitnessFun τ s i j (deriv f)) := by
    rw [← hcomm]
    exact realizesMero_diffCubeMero τ _ (realizesMero_deriv hx)
  -- boundary functions
  have hU : RealizesMero (addTranslationMeroEquiv (τ i) y - y)
      (fun z => pairFaceWitnessFun τ s i j f (z + τ i)
        - pairFaceWitnessFun τ s i j f z) :=
    realizesMero_sub (HTGeometry.realizesMero_translate hW (τ i)) hW
  have hU' : RealizesMero (addTranslationMeroEquiv (τ i) (y′) - (y′))
      (fun z => pairFaceWitnessFun τ s i j (deriv f) (z + τ i)
        - pairFaceWitnessFun τ s i j (deriv f) z) :=
    realizesMero_sub (HTGeometry.realizesMero_translate hW' (τ i)) hW'
  have hderiv : addTranslationMeroEquiv (τ i) (y′) - (y′)
      = (addTranslationMeroEquiv (τ i) y - y)′ := by
    rw [addTranslationMeroEquiv_deriv]
    have h := differentialJet_sub 1 (addTranslationMeroEquiv (τ i) y) y
    simpa [differentialJet_succ, differentialJet_zero] using h.symm
  have hUd : RealizesMero ((addTranslationMeroEquiv (τ i) y - y)′)
      (deriv (fun z => pairFaceWitnessFun τ s i j f (z + τ i)
        - pairFaceWitnessFun τ s i j f z)) := realizesMero_deriv hU
  have hUmero : MeromorphicOn (fun z => pairFaceWitnessFun τ s i j f (z + τ i)
      - pairFaceWitnessFun τ s i j f z) (Set.univ : Set ℂ) :=
    meromorphicOn_of_realizesMero hU
  have hterm : ∀ q : ℂ,
      laurentCoeff (fun z => pairFaceWitnessFun τ s i j (deriv f) (z + τ i)
          - pairFaceWitnessFun τ s i j (deriv f) z) q ℓ
        = ((ℓ : ℂ) + 1) * laurentCoeff (fun z => pairFaceWitnessFun τ s i j f (z + τ i)
          - pairFaceWitnessFun τ s i j f z) q (ℓ + 1) := by
    intro q
    have hgerm := realizesMero_congr (hderiv ▸ hU') hUd q
    have hmero' : MeromorphicAt (fun z => pairFaceWitnessFun τ s i j (deriv f) (z + τ i)
        - pairFaceWitnessFun τ s i j (deriv f) z) q :=
      (meromorphicOn_of_realizesMero hU') q (Set.mem_univ q)
    rw [laurentCoeff_congr hmero' hgerm ℓ]
    have hjet := laurentCoeff_iteratedDeriv_eq (hUmero q (Set.mem_univ q)) 1 ℓ
    rw [iteratedDeriv_one] at hjet
    rw [hjet]
    congr 1
    simp
  rw [pairSig, pairSig, additiveOrbitalDivisorAt, additiveOrbitalDivisorAt,
    finsum_congr (fun m : ℤ => hterm (p + (m : ℂ) * τ i)), ← mul_finsum]

/-! ## Closure of the class under the generators -/

theorem mixedConstGermSet_comp_add (τ : ι → ℂ) (s : Finset ι) {Cst : ℂ} {f : ℂ → ℂ}
    (hf : MixedConstGermSet τ s f Cst) (h : ℂ) :
    MixedConstGermSet τ s (fun z => f (z + h)) Cst := by
  intro z
  have hpull := (tendsto_nhdsNE_add_const z h).eventually (hf (z + h))
  filter_upwards [hpull] with wv hw
  rw [diffCube_comp_add τ s f h]
  exact hw

theorem periodicOneGerm_const_mul' {f : ℂ → ℂ} (hf : PeriodicOneGerm f) (c : ℂ) :
    PeriodicOneGerm (fun z => c * f z) := periodicOneGerm_const_mul hf c

theorem mixedConstGermSet_const_mul (τ : ι → ℂ) (s : Finset ι) {Cst : ℂ} {f : ℂ → ℂ}
    (hf : MixedConstGermSet τ s f Cst) (c : ℂ) :
    MixedConstGermSet τ s (fun z => c * f z) (c * Cst) := by
  classical
  intro z
  filter_upwards [hf z] with wv hw
  have hsplit : HTGeometry.diffCube τ s (fun z => c * f z) wv
      = c * HTGeometry.diffCube τ s f wv := by
    show ∑ E ∈ s.powerset, _ = c * ∑ E ∈ s.powerset, _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun E _ => by ring
  rw [hsplit, hw]

theorem mixedConstGermSet_add (τ : ι → ℂ) (s : Finset ι) {Cst₁ Cst₂ : ℂ} {f g : ℂ → ℂ}
    (hf : MixedConstGermSet τ s f Cst₁) (hg : MixedConstGermSet τ s g Cst₂) :
    MixedConstGermSet τ s (fun z => f z + g z) (Cst₁ + Cst₂) := by
  intro z
  filter_upwards [hf z, hg z] with wv h1 h2
  have hsplit : HTGeometry.diffCube τ s (fun z => f z + g z) wv
      = HTGeometry.diffCube τ s f wv + HTGeometry.diffCube τ s g wv :=
    congrFun (HTGeometry.diffCube_add τ s f g) wv
  rw [hsplit, h1, h2]

/-- **The signature commutes with constant multiples.** -/
theorem pairSig_const_mul (τ : ι → ℂ) (s : Finset ι) (i j : ι) {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) (c : ℂ) (ℓ : ℤ) (p : ℂ) :
    pairSig τ s (fun z => c * f z) i j ℓ p = c * pairSig τ s f i j ℓ p := by
  classical
  have hsplit : pairFaceWitnessFun τ s i j (fun z => c * f z)
      = fun z => c * pairFaceWitnessFun τ s i j f z := by
    funext z
    show ∑ E ∈ (s \ {i, j}).powerset, _ = c * ∑ E ∈ (s \ {i, j}).powerset, _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun E _ => by ring
  rw [pairSig, pairSig, hsplit]
  exact additiveOrbitalDivisorAt_const_mul (meromorphicOn_diffCube τ _ hf) c (τ i) p ℓ

/-! ## Closure under the derivation, at germ level -/

theorem periodicOneGerm_deriv {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (hx : RealizesMero x f) (h1 : addTranslationMeroEquiv 1 x = x) :
    PeriodicOneGerm (deriv f) :=
  periodicOneGerm_of_realizesMero (realizesMero_deriv hx)
    (by rw [addTranslationMeroEquiv_deriv, h1])

set_option synthInstance.maxHeartbeats 400000 in
theorem mixedConstGermSet_deriv (τ : ι → ℂ) (s : Finset ι) {x : meroField (Set.univ : Set ℂ)}
    {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (hmixed : diffCubeMero τ s x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst) :
    MixedConstGermSet τ s (deriv f) 0 := by
  have hcube : diffCubeMero τ s (x′) = algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0 := by
    have h := diffCubeMero_differentialJet τ 1 s x
    have h1 : diffCubeMero τ s (differentialJet 1 x) = differentialJet 1 (diffCubeMero τ s x) := h
    simp only [differentialJet_succ, differentialJet_zero] at h1
    rw [h1, hmixed]
    have h2 := differentialJet_algebraMap_apply (F := ℂ) (K := meroField (Set.univ : Set ℂ)) 1 Cst
    simp only [differentialJet_succ, differentialJet_zero] at h2
    rw [h2]
    congr 1
  intro z
  have hreal : RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) 0)
      (HTGeometry.diffCube τ s (deriv f)) := by
    rw [← hcube]
    exact realizesMero_diffCubeMero τ s (realizesMero_deriv hx)
  exact realizesMero_congr hreal (realizesMero_const 0) z

/-- **The signature turns iterated derivation into the shifted order with the jet factor.** -/
theorem pairSig_iteratedDeriv (τ : ι → ℂ) (s : Finset ι) (i j : ι) :
    ∀ (n : ℕ) {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}, RealizesMero x f →
      ∀ (ℓ : ℤ) (p : ℂ), pairSig τ s (iteratedDeriv n f) i j ℓ p
        = (∏ t ∈ Finset.range n, ((ℓ : ℂ) + t + 1)) * pairSig τ s f i j (ℓ + n) p := by
  intro n
  induction n with
  | zero =>
      intro x f hx ℓ p
      simp
  | succ m ihm =>
      intro x f hx ℓ p
      have hstep : iteratedDeriv (m + 1) f = iteratedDeriv m (deriv f) := by
        rw [iteratedDeriv_succ']
      rw [hstep, ihm (realizesMero_deriv hx) ℓ p,
        pairSig_deriv τ s i j hx (ℓ + m) p]
      rw [Finset.prod_range_succ,
        show (ℓ : ℤ) + ((m + 1 : ℕ) : ℤ) = ℓ + (m : ℤ) + 1 from by push_cast; ring]
      push_cast
      ring

/-! ## Finite sums -/

theorem meromorphicOn_finsetSum {κ : Type*} (M : Finset κ) (g : κ → ℂ → ℂ)
    (h : ∀ m ∈ M, MeromorphicOn (g m) (Set.univ : Set ℂ)) :
    MeromorphicOn (fun z => ∑ m ∈ M, g m z) (Set.univ : Set ℂ) := by
  classical
  intro z _
  have hfun : (fun z => ∑ m ∈ M, g m z) = ∑ m ∈ M, g m := by
    funext w
    simp only [Finset.sum_apply]
  rw [hfun]
  exact MeromorphicAt.sum fun m hm => h m hm z (Set.mem_univ z)

theorem mixedConstGermSet_finsetSum (τ : ι → ℂ) (s : Finset ι) {κ : Type*} (M : Finset κ)
    (g : κ → ℂ → ℂ) (Cs : κ → ℂ) (h : ∀ m ∈ M, MixedConstGermSet τ s (g m) (Cs m)) :
    MixedConstGermSet τ s (fun z => ∑ m ∈ M, g m z) (∑ m ∈ M, Cs m) := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      intro z
      filter_upwards with w
      show HTGeometry.diffCube τ s (fun _ => (0 : ℂ)) w = 0
      simp [HTGeometry.diffCube]
  | @insert m M' hm ihM =>
      have hrest := ihM fun r hr => h r (Finset.mem_insert_of_mem hr)
      have hhead := h m (Finset.mem_insert_self m M')
      have hsum := mixedConstGermSet_add τ s hhead hrest
      rw [Finset.sum_insert hm]
      intro z
      filter_upwards [hsum z] with w hw
      have harg : HTGeometry.diffCube τ s (fun z => ∑ r ∈ insert m M', g r z) w
          = HTGeometry.diffCube τ s (fun z => g m z + ∑ r ∈ M', g r z) w := by
        congr 1
        funext u
        rw [Finset.sum_insert hm]
      rw [harg]
      exact hw

set_option synthInstance.maxHeartbeats 800000 in
/-- **The signature is additive over finite families.** -/
theorem pairSig_finsetSum (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) {κ : Type*} (M : Finset κ) (g : κ → ℂ → ℂ) (Cs : κ → ℂ)
    (hmero : ∀ m ∈ M, MeromorphicOn (g m) (Set.univ : Set ℂ))
    (hper : ∀ m ∈ M, PeriodicOneGerm (g m))
    (hmixed : ∀ m ∈ M, MixedConstGermSet τ s (g m) (Cs m)) {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s (fun z => ∑ m ∈ M, g m z) i j ℓ p
      = ∑ m ∈ M, pairSig τ s (g m) i j ℓ p := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      have hz : pairSig τ s (fun _ : ℂ => (0 : ℂ)) i j ℓ p = 0 := by
        have hw : pairFaceWitnessFun τ s i j (fun _ : ℂ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
          funext z
          show ∑ E ∈ (s \ {i, j}).powerset, _ = (0 : ℂ)
          exact Finset.sum_eq_zero fun E _ => by ring
        rw [pairSig, hw, additiveOrbitalDivisorAt]
        refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
        have : (fun z : ℂ => (0 : ℂ)) = fun z : ℂ => (0 : ℂ) - (0 : ℂ) := by
          funext z
          ring
        exact laurentCoeff_eq_zero_of_analyticAt analyticAt_const hℓ
      simpa using hz
  | @insert m M' hm ihM =>
      have hrest := ihM (fun r hr => hmero r (Finset.mem_insert_of_mem hr))
        (fun r hr => hper r (Finset.mem_insert_of_mem hr))
        (fun r hr => hmixed r (Finset.mem_insert_of_mem hr))
      have hsplit : pairSig τ s (fun z => ∑ r ∈ insert m M', g r z) i j ℓ p
          = pairSig τ s (fun z => g m z + ∑ r ∈ M', g r z) i j ℓ p := by
        congr 1
        funext u
        rw [Finset.sum_insert hm]
      rw [hsplit, pairSig_add τ hτ hQ s hij hi hj (hmero m (Finset.mem_insert_self m M'))
        (hper m (Finset.mem_insert_self m M')) (hmixed m (Finset.mem_insert_self m M'))
        (meromorphicOn_finsetSum M' g fun r hr => hmero r (Finset.mem_insert_of_mem hr))
        (by
          have h := periodicOneGerm_finsetSum M' g
            fun r hr => hper r (Finset.mem_insert_of_mem hr)
          have hfun : (∑ r ∈ M', g r) = fun z => ∑ r ∈ M', g r z := by
            funext u
            simp only [Finset.sum_apply]
          rwa [hfun] at h)
        (mixedConstGermSet_finsetSum τ s M' g Cs
          fun r hr => hmixed r (Finset.mem_insert_of_mem hr)) hℓ p,
        hrest, Finset.sum_insert hm]

/-! ## The operator criterion -/

/-- A finite constant-coefficient differential-translation operator, applied to a function. -/
def transOpFun {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ) (f : ℂ → ℂ) :
    ℂ → ℂ := fun z => ∑ m ∈ M, c m * iteratedDeriv (jj m) (fun w => f (w + hh m)) z

/-- The same operator, on germs. -/
def transOpMero {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    (x : meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) :=
  ∑ m ∈ M, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
    differentialJet (jj m) (addTranslationMeroEquiv (hh m) x)

/-- The same operator, on divisors. -/
def transOpDiv {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    (Dv : ℤ → ℂ → ℂ) : ℤ → ℂ → ℂ :=
  fun ℓ p => ∑ m ∈ M, c m * (∏ t ∈ Finset.range (jj m), ((ℓ : ℂ) + t + 1))
      * Dv (ℓ + (jj m : ℤ)) (p + hh m)

theorem realizesMero_transOpTerm {κ : Type*} (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hx : RealizesMero x f) (m : κ) :
    RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
        differentialJet (jj m) (addTranslationMeroEquiv (hh m) x))
      (fun z => c m * iteratedDeriv (jj m) (fun w => f (w + hh m)) z) :=
  realizesMero_const_mul (c m)
    (realizesMero_iteratedDeriv (HTGeometry.realizesMero_translate hx (hh m)) (jj m))

theorem realizesMero_transOp {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ} (hx : RealizesMero x f) :
    RealizesMero (transOpMero M c jj hh x) (transOpFun M c jj hh f) := by
  classical
  have h := realizesMero_sum M _ _ (fun m _ => realizesMero_transOpTerm c jj hh hx m)
  have hfun : (∑ m ∈ M, fun z => c m * iteratedDeriv (jj m) (fun w => f (w + hh m)) z)
      = transOpFun M c jj hh f := by
    funext z
    simp only [transOpFun, Finset.sum_apply]
  rwa [hfun] at h

theorem addTranslationMeroEquiv_one_transOpTerm {κ : Type*} (c : κ → ℂ) (jj : κ → ℕ)
    (hh : κ → ℂ) {x : meroField (Set.univ : Set ℂ)} (h1 : addTranslationMeroEquiv 1 x = x)
    (m : κ) :
    addTranslationMeroEquiv 1 (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
        differentialJet (jj m) (addTranslationMeroEquiv (hh m) x))
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
        differentialJet (jj m) (addTranslationMeroEquiv (hh m) x) := by
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex,
    addTranslationMeroEquiv_differentialJet, addTranslationMeroEquiv_add,
    show (1 : ℂ) + hh m = hh m + 1 from by ring, ← addTranslationMeroEquiv_add, h1]

set_option synthInstance.maxHeartbeats 400000 in
theorem diffCubeMero_transOpTerm (τ : ι → ℂ) (s : Finset ι) {κ : Type*} (c : κ → ℂ)
    (jj : κ → ℕ) (hh : κ → ℂ) {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ}
    (hmixed : diffCubeMero τ s x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst) (m : κ) :
    diffCubeMero τ s (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
        differentialJet (jj m) (addTranslationMeroEquiv (hh m) x))
      = algebraMap ℂ (meroField (Set.univ : Set ℂ))
          (c m * differentialJet (jj m) Cst) := by
  rw [diffCubeMero_algebraMap_mul, diffCubeMero_differentialJet, diffCubeMero_translate_comm,
    hmixed, addTranslationMeroEquiv_algebraMap_complex, differentialJet_algebraMap_apply,
    ← map_mul]

set_option synthInstance.maxHeartbeats 800000 in
/-- **The signature of an operator output is the operator applied to the signature.** -/
theorem pairSig_transOp (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (h1 : addTranslationMeroEquiv 1 x = x)
    (hmixed : diffCubeMero τ s x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst)
    {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s (transOpFun M c jj hh f) i j ℓ p
      = transOpDiv M c jj hh (pairSig τ s f i j) ℓ p := by
  classical
  set g : κ → ℂ → ℂ :=
    fun m z => c m * iteratedDeriv (jj m) (fun w => f (w + hh m)) z with hg
  have hgreal : ∀ m : κ, RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c m) *
      differentialJet (jj m) (addTranslationMeroEquiv (hh m) x)) (g m) :=
    fun m => realizesMero_transOpTerm c jj hh hx m
  have hgmero : ∀ m ∈ M, MeromorphicOn (g m) (Set.univ : Set ℂ) :=
    fun m _ => meromorphicOn_of_realizesMero (hgreal m)
  have hgper : ∀ m ∈ M, PeriodicOneGerm (g m) := fun m _ =>
    periodicOneGerm_of_realizesMero (hgreal m)
      (addTranslationMeroEquiv_one_transOpTerm c jj hh h1 m)
  have hgmixed : ∀ m ∈ M, MixedConstGermSet τ s (g m) (c m * differentialJet (jj m) Cst) := by
    intro m _ z
    have hreal : RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ))
        (c m * differentialJet (jj m) Cst)) (HTGeometry.diffCube τ s (g m)) := by
      rw [← diffCubeMero_transOpTerm τ s c jj hh hmixed m]
      exact realizesMero_diffCubeMero τ s (hgreal m)
    exact realizesMero_congr hreal (realizesMero_const _) z
  have hfun : transOpFun M c jj hh f = fun z => ∑ m ∈ M, g m z := rfl
  rw [hfun, pairSig_finsetSum τ hτ hQ s hij hi hj M g
    (fun m => c m * differentialJet (jj m) Cst) hgmero hgper hgmixed hℓ p, transOpDiv]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hg]
  have hterm : pairSig τ s (fun z => c m * iteratedDeriv (jj m) (fun w => f (w + hh m)) z)
      i j ℓ p = c m * pairSig τ s (iteratedDeriv (jj m) (fun w => f (w + hh m))) i j ℓ p := by
    refine pairSig_const_mul τ s i j ?_ (c m) ℓ p
    exact meromorphicOn_of_realizesMero
      (realizesMero_iteratedDeriv (HTGeometry.realizesMero_translate hx (hh m)) (jj m))
  rw [hterm, pairSig_iteratedDeriv τ s i j (jj m)
    (HTGeometry.realizesMero_translate hx (hh m)) ℓ p,
    pairSig_translate τ s i j f (hh m) (ℓ + (jj m : ℤ)) p]
  ring

theorem addTranslationMeroEquiv_one_transOp {κ : Type*} (M : Finset κ) (c : κ → ℂ)
    (jj : κ → ℕ) (hh : κ → ℂ) {x : meroField (Set.univ : Set ℂ)}
    (h1 : addTranslationMeroEquiv 1 x = x) :
    addTranslationMeroEquiv 1 (transOpMero M c jj hh x) = transOpMero M c jj hh x := by
  classical
  rw [transOpMero, map_sum]
  exact Finset.sum_congr rfl fun m _ => addTranslationMeroEquiv_one_transOpTerm c jj hh h1 m

set_option synthInstance.maxHeartbeats 400000 in
theorem diffCubeMero_transOp (τ : ι → ℂ) (s : Finset ι) {κ : Type*} (M : Finset κ) (c : κ → ℂ)
    (jj : κ → ℕ) (hh : κ → ℂ) {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ}
    (hmixed : diffCubeMero τ s x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst) :
    diffCubeMero τ s (transOpMero M c jj hh x)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ))
          (∑ m ∈ M, c m * differentialJet (jj m) Cst) := by
  classical
  rw [transOpMero, diffCubeMero_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun m _ => diffCubeMero_transOpTerm τ s c jj hh hmixed m

set_option synthInstance.maxHeartbeats 800000 in
/-- **The constant-coefficient differential-translation criterion.**  A finite operator applied to
a member of the all-depth class is differentially algebraic exactly when the corresponding operator
annihilates every pair-face signature. -/
theorem differentialAlgebraicOver_transOp_iff (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) (hs : 2 ≤ s.card)
    {κ : Type*} (M : Finset κ) (c : κ → ℂ) (jj : κ → ℕ) (hh : κ → ℂ)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (h1 : addTranslationMeroEquiv 1 x = x)
    (hmixed : diffCubeMero τ s x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Cst) :
    DifferentialAlgebraicOver ℂ (transOpMero M c jj hh x) ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        transOpDiv M c jj hh (pairSig τ s f i j) ℓ p = 0 := by
  classical
  have hreal := realizesMero_transOp M c jj hh hx
  have hper : PeriodicOneGerm (transOpFun M c jj hh f) :=
    periodicOneGerm_of_realizesMero hreal (addTranslationMeroEquiv_one_transOp M c jj hh h1)
  have hmixedFun : MixedConstGermSet τ s (transOpFun M c jj hh f)
      (∑ m ∈ M, c m * differentialJet (jj m) Cst) := by
    intro z
    have hr : RealizesMero (algebraMap ℂ (meroField (Set.univ : Set ℂ))
        (∑ m ∈ M, c m * differentialJet (jj m) Cst))
        (HTGeometry.diffCube τ s (transOpFun M c jj hh f)) := by
      rw [← diffCubeMero_transOp τ s M c jj hh hmixed]
      exact realizesMero_diffCubeMero τ s hreal
    exact realizesMero_congr hr (realizesMero_const _) z
  rw [differentialAlgebraicOver_iff_pairFace_eq_zero τ hτ hQ s hs hreal hper hmixedFun]
  constructor
  · intro h i hi j hj hij ℓ hℓ p
    rw [← pairSig_transOp τ hτ hQ s hij hi hj M c jj hh hx h1 hmixed hℓ p]
    exact h i hi j hj hij p ℓ hℓ
  · intro h i hi j hj hij p ℓ hℓ
    have := h i hi j hj hij ℓ hℓ p
    rw [← pairSig_transOp τ hτ hQ s hij hi hj M c jj hh hx h1 hmixed hℓ p] at this
    exact this

end Deriv

end

end GaloisForLFunctions
