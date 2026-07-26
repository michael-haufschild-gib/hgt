import GaloisForLFunctions.HTGeometry.LocalAnalyticExponentialClock
import GaloisForLFunctions.HTGeometry.RationalCoefficientClearing
import GaloisForLFunctions.HTGeometry.GlobalToUpperEndDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The jet bridge between analytic functions and their meromorphic differential field

An analytic function on a nonempty connected open set is an element of the meromorphic function
field of that set, and its algebraic jets there are exactly the germs of its ordinary iterated
derivatives.  Because germs along a principal filter are functions up to equality on the set
itself, a polynomial relation in the field is *equivalent* to the corresponding pointwise relation
on the set — no identity theorem and no limiting argument is needed in either direction.

* **`differentialAlgebraicOver_analyticMeroElement_iff`** — an analytic function satisfies an
  algebraic differential equation on the set exactly when its meromorphic realization is
  differentially algebraic over the embedded rational coordinate field.

The bridge transports the field-level closure properties of differential algebraicity back to
functions:

* **`differentiallyAlgebraic_mul`**, **`differentiallyAlgebraic_add`**,
  **`differentiallyAlgebraic_sub`**, **`differentiallyAlgebraic_pow`** — the differentially
  algebraic entire functions form a ring.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

variable {U : Set ℂ}

/-! ## Jets of an analytic function as germs -/

/-- The `n`-th derivative of an analytic function, as an element of the analytic germ domain. -/
def analyticJetElement (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    analyticSubring U :=
  analyticFunctionElement (iteratedDeriv n f) (analyticOnNhd_iteratedDeriv hf n)

@[simp]
theorem analyticJetElement_coe (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    ((analyticJetElement f hf n : analyticSubring U) : Germ (Filter.principal U) ℂ) =
      ((iteratedDeriv n f : ℂ → ℂ) : Germ (Filter.principal U) ℂ) := rfl

theorem analyticJetElement_zero (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    analyticJetElement f hf 0 = analyticFunctionElement f hf := by
  apply Subtype.ext
  change ((iteratedDeriv 0 f : ℂ → ℂ) : Germ (Filter.principal U) ℂ) =
    ((f : ℂ → ℂ) : Germ (Filter.principal U) ℂ)
  rw [iteratedDeriv_zero]

/-- Germ differentiation advances the analytic jet. -/
theorem analyticSubringDeriv_analyticJetElement (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    analyticSubringDeriv hUo (analyticJetElement f hf n) = analyticJetElement f hf (n + 1) := by
  apply Subtype.ext
  change ((deriv (iteratedDeriv n f) : ℂ → ℂ) : Germ (Filter.principal U) ℂ) =
    ((iteratedDeriv (n + 1) f : ℂ → ℂ) : Germ (Filter.principal U) ℂ)
  rw [iteratedDeriv_succ]

/-- An analytic function as an element of the meromorphic function field of its domain. -/
def analyticMeroElement (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) : meroField U :=
  algebraMap (analyticSubring U) (meroField U) (analyticFunctionElement f hf)

/-- The algebraic jets of the meromorphic realization are the germs of the ordinary iterated
derivatives. -/
theorem differentialJet_analyticMeroElement (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI := meroFieldDifferential hUo hUc hUne
    differentialJet n (analyticMeroElement f hf) =
      algebraMap (analyticSubring U) (meroField U) (analyticJetElement f hf n) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI := meroFieldDifferential hUo hUc hUne
  induction n with
  | zero =>
      rw [differentialJet_zero, analyticJetElement_zero]
      rfl
  | succ n ih =>
      rw [differentialJet_succ, ih, meroFieldDifferential_algebraMap,
        analyticSubringDeriv_analyticJetElement]

/-! ## Polynomial relations: germ form and pointwise form -/

/-- Polynomial-coefficient evaluation on analytic jets is the germ of the pointwise evaluation. -/
theorem analyticJetRelation_coe (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) :
    ((MvPolynomial.eval₂ (polyToAnalytic U)
        (fun j : Fin m => analyticJetElement f hf (j : ℕ)) G : analyticSubring U) :
          Germ (Filter.principal U) ℂ) =
      ((fun z => MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin m => iteratedDeriv (j : ℕ) f z) G) : Germ (Filter.principal U) ℂ) := by
  induction G using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ (polyToAnalytic U)
          (fun j : Fin m => analyticJetElement f hf (j : ℕ)) P :
            analyticSubring U) : Germ (Filter.principal U) ℂ) +
        ((MvPolynomial.eval₂ (polyToAnalytic U)
          (fun j : Fin m => analyticJetElement f hf (j : ℕ)) Q :
            analyticSubring U) : Germ (Filter.principal U) ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp
  | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ (polyToAnalytic U)
          (fun k : Fin m => analyticJetElement f hf (k : ℕ)) P :
            analyticSubring U) : Germ (Filter.principal U) ℂ) *
          ((analyticJetElement f hf (j : ℕ) : analyticSubring U) :
            Germ (Filter.principal U) ℂ) = _
      rw [hP, analyticJetElement_coe, ← Germ.coe_mul]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by simp

/-- A polynomial-coefficient jet relation holds in the analytic germ domain exactly when it holds
pointwise on the domain. -/
theorem eval₂_analyticJetElement_eq_zero_iff (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) :
    MvPolynomial.eval₂ (polyToAnalytic U)
        (fun j : Fin m => analyticJetElement f hf (j : ℕ)) G = 0 ↔
      ∀ z ∈ U, MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin m => iteratedDeriv (j : ℕ) f z) G = 0 := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    rw [ZeroMemClass.coe_zero, analyticJetRelation_coe, ← Germ.coe_zero, Germ.coe_eq] at hval
    intro z hz
    exact eventually_principal.mp hval z hz
  · intro h
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, analyticJetRelation_coe, ← Germ.coe_zero, Germ.coe_eq]
    exact eventually_principal.mpr fun z hz => h z hz

/-- The polynomial embedding into the meromorphic field factors through the rational coordinate
field. -/
theorem polyToMero_eq_comp (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) :
    polyToMero U =
      (ratfuncToMero U hUo hUc hUne hUinf).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
  apply DFunLike.ext _ _
  intro p
  exact (ratfuncToMero_algebraMap_polynomial U hUo hUc hUne hUinf p).symm

/-! ## The two directions of the bridge -/

/-- A pointwise algebraic differential relation survives in the meromorphic differential field. -/
theorem differentialAlgebraicOver_analyticMeroElement_of_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0)
    (hrel : ∀ z ∈ U, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    letI := meroFieldDifferential hUo hUc hUne
    DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  set G : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := reshapeJet n P with hG
  set Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G with hQdef
  have hG0 : G ≠ 0 := fun hzero => hP (reshapeJet_injective n (by simpa [hG] using hzero))
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hG0
    apply MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    simpa [hQdef] using hzero
  have hanalytic : MvPolynomial.eval₂ (polyToAnalytic U)
      (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G = 0 := by
    rw [eval₂_analyticJetElement_eq_zero_iff]
    intro z hz
    rw [hG, eval₂_reshapeJet]
    exact hrel z hz
  have hmap : algebraMap (analyticSubring U) (meroField U)
      (MvPolynomial.eval₂ (polyToAnalytic U)
        (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G) = 0 := by
    rw [hanalytic, map_zero]
  rw [MvPolynomial.eval₂_comp_right] at hmap
  rw [MvPolynomial.eval₂_map] at hmap
  change MvPolynomial.eval₂ (polyToMero U)
      (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) G = 0 at hmap
  have hfield : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) Q = 0 := by
    rw [MvPolynomial.aeval_def]
    rw [hQdef, MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂
      ((ratfuncToMero U hUo hUc hUne hUinf).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) G = 0
    rw [← polyToMero_eq_comp hUo hUc hUne hUinf]
    rw [show (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) =
        (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
          (analyticJetElement f hf (j : ℕ))) by
      funext j
      exact differentialJet_analyticMeroElement hUo hUc hUne f hf (j : ℕ)]
    exact hmap
  unfold DifferentialAlgebraicOver DifferentialIndependent
  intro hindependent
  let e : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ))
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg Prod.snd hij)
  have hrename : MvPolynomial.rename e Q ≠ 0 := fun hzero =>
    hQ0 (MvPolynomial.rename_injective e he hzero)
  apply hrename
  apply hindependent.eq_zero_of_aeval_eq_zero
  rw [MvPolynomial.aeval_rename]
  simpa [e, Function.comp_def] using hfield

/-- Differential algebraicity over a base field is witnessed by a nonzero polynomial in a finite
initial segment of the jet family.  This is the base-field-general form of the rational extraction
`exists_rational_jet_relation_of_differentialAlgebraicOver`. -/
theorem exists_jet_relation_of_differentialAlgebraicOver
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K] {x : K}
    (hx : DifferentialAlgebraicOver F x) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) F), Q ≠ 0 ∧
      MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q = 0 := by
  unfold DifferentialAlgebraicOver DifferentialIndependent at hx
  rw [algebraicIndependent_iff] at hx
  push Not at hx
  obtain ⟨P, hPann, hP0⟩ := hx
  obtain ⟨m, a, ha, R, hP⟩ := MvPolynomial.exists_fin_rename P
  subst hP
  have hR0 : R ≠ 0 := by
    intro hR
    apply hP0
    simp [hR]
  let N : ℕ := Finset.univ.sup fun i : Fin m => (a i).2
  have haN (i : Fin m) : (a i).2 ≤ N :=
    Finset.le_sup (f := fun i : Fin m => (a i).2) (Finset.mem_univ i)
  let e : Fin m → Fin (N + 1) := fun i => ⟨(a i).2, Nat.lt_succ_of_le (haN i)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply ha
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact congrArg Fin.val hij
  refine ⟨N, MvPolynomial.rename e R, ?_, ?_⟩
  · exact fun h => hR0 (MvPolynomial.rename_injective e he h)
  · rw [MvPolynomial.aeval_rename]
    rw [MvPolynomial.aeval_rename] at hPann
    simpa [e, Function.comp_def] using hPann

/-- A differential relation in the meromorphic field descends to a pointwise algebraic differential
equation for the function. -/
theorem exists_relation_of_differentialAlgebraicOver_analyticMeroElement
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hx :
      letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      letI := meroFieldDifferential hUo hUc hUne
      DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf)) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
      ∀ z ∈ U, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℤ (analyticSubring U) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  obtain ⟨n, Q, hQ0, hQ⟩ := exists_jet_relation_of_differentialAlgebraicOver hx
  set G : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := clearRatFuncCoefficients Q with hGdef
  have hG0 : G ≠ 0 := clearRatFuncCoefficients_ne_zero Q hQ0
  have hfield : MvPolynomial.eval₂ (polyToMero U)
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) G = 0 := by
    have hmapG : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G =
        MvPolynomial.C ((algebraMap (Polynomial ℂ) (RatFunc ℂ))
          (ratFuncCommonDenominator Q)) * Q := map_clearRatFuncCoefficients Q
    have hQ' : MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (meroField U))
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) Q = 0 := by
      rw [← MvPolynomial.aeval_def]
      exact hQ
    calc
      MvPolynomial.eval₂ (polyToMero U)
          (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) G =
          MvPolynomial.eval₂ (algebraMap (RatFunc ℂ) (meroField U))
            (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf))
            (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G) := by
          rw [MvPolynomial.eval₂_map]
          rw [polyToMero_eq_comp hUo hUc hUne hUinf]
          rfl
      _ = 0 := by
          rw [hmapG, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hQ', mul_zero]
  have hmap : algebraMap (analyticSubring U) (meroField U)
      (MvPolynomial.eval₂ (polyToAnalytic U)
        (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G) = 0 := by
    rw [MvPolynomial.eval₂_comp_right, MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ (polyToMero U)
      (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) G = 0
    rw [show (fun j : Fin (n + 1) => algebraMap (analyticSubring U) (meroField U)
        (analyticJetElement f hf (j : ℕ))) =
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement f hf)) by
      funext j
      exact (differentialJet_analyticMeroElement hUo hUc hUne f hf (j : ℕ)).symm]
    exact hfield
  have hanalytic : MvPolynomial.eval₂ (polyToAnalytic U)
      (fun j : Fin (n + 1) => analyticJetElement f hf (j : ℕ)) G = 0 :=
    (IsFractionRing.injective (analyticSubring U) (meroField U)) (by simpa using hmap)
  have hpoint := (eval₂_analyticJetElement_eq_zero_iff f hf G).mp hanalytic
  refine ⟨n, reshapeJetInv n G, ?_, ?_⟩
  · exact fun hzero => hG0 (reshapeJetInv_injective n (by simpa using hzero))
  · intro z hz
    have hre : reshapeJet n (reshapeJetInv n G) = G :=
      RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) G
    have := hpoint z hz
    rw [← hre, eval₂_reshapeJet] at this
    exact this

/-- **The jet bridge.**  An analytic function satisfies an algebraic differential equation on its
domain exactly when its meromorphic realization is differentially algebraic over the embedded
rational coordinate field. -/
theorem differentialAlgebraicOver_analyticMeroElement_iff
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    (letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
     letI : Algebra (RatFunc ℂ) (meroField U) :=
       (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
     letI := meroFieldDifferential hUo hUc hUne
     DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf)) ↔
      ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
        ∀ z ∈ U, MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0 := by
  constructor
  · intro hx
    exact exists_relation_of_differentialAlgebraicOver_analyticMeroElement
      hUo hUc hUne hUinf hf hx
  · rintro ⟨n, P, hP, hrel⟩
    exact differentialAlgebraicOver_analyticMeroElement_of_relation
      hUo hUc hUne hUinf hf hP hrel

/-! ## The global bridge and the ring of differentially algebraic entire functions -/

/-- **The global jet bridge, forward.**  A differentially algebraic entire function has a
differentially algebraic global meromorphic realization. -/
theorem differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hfDA : DifferentiallyAlgebraic f) :
    letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
      isPreconnected_univ Set.univ_nonempty
    letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
      (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ).toAlgebra
    letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
      Set.univ_nonempty
    DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf) := by
  obtain ⟨n, P, hP, hrel⟩ := hfDA
  exact differentialAlgebraicOver_analyticMeroElement_of_relation isOpen_univ
    isPreconnected_univ Set.univ_nonempty Set.infinite_univ hf hP (fun z _ => hrel z)

/-- **The global jet bridge, backward.**  An entire function whose global meromorphic realization
is differentially algebraic over `ℂ(z)` is differentially algebraic. -/
theorem differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ))
    (hx :
      letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
        isPreconnected_univ Set.univ_nonempty
      letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
        (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ).toAlgebra
      letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
        Set.univ_nonempty
      DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement f hf)) :
    DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP, hrel⟩ := exists_relation_of_differentialAlgebraicOver_analyticMeroElement
    isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ hf hx
  exact ⟨n, P, hP, fun z => hrel z (Set.mem_univ z)⟩

/-- Multiplication of entire germs is realized by pointwise multiplication. -/
theorem analyticMeroElement_mul {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) :
    analyticMeroElement (fun z => f z * g z) (hf.mul hg) =
      analyticMeroElement f hf * analyticMeroElement g hg := by
  rw [analyticMeroElement, analyticMeroElement, analyticMeroElement, ← map_mul]
  congr 1

/-- Addition of entire germs is realized by pointwise addition. -/
theorem analyticMeroElement_add {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) :
    analyticMeroElement (fun z => f z + g z) (hf.add hg) =
      analyticMeroElement f hf + analyticMeroElement g hg := by
  rw [analyticMeroElement, analyticMeroElement, analyticMeroElement, ← map_add]
  congr 1

/-- **Differential algebraicity of entire functions is closed under multiplication.** -/
theorem differentiallyAlgebraic_mul {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ))
    (hfDA : DifferentiallyAlgebraic f) (hgDA : DifferentiallyAlgebraic g) :
    DifferentiallyAlgebraic (fun z => f z * g z) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
  letI : CharZero (meroField (Set.univ : Set ℂ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  refine differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (hf.mul hg) ?_
  rw [analyticMeroElement_mul hf hg]
  exact differentialAlgebraicOver_mul
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hfDA)
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hg hgDA)

/-- **Differential algebraicity of entire functions is closed under addition.** -/
theorem differentiallyAlgebraic_add {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ))
    (hfDA : DifferentiallyAlgebraic f) (hgDA : DifferentiallyAlgebraic g) :
    DifferentiallyAlgebraic (fun z => f z + g z) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
  letI : CharZero (meroField (Set.univ : Set ℂ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  refine differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (hf.add hg) ?_
  rw [analyticMeroElement_add hf hg]
  exact differentialAlgebraicOver_add
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hfDA)
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hg hgDA)

/-- Subtraction of analytic germs is realized by pointwise subtraction. -/
theorem analyticMeroElement_sub {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) :
    analyticMeroElement (fun z => f z - g z) (hf.sub hg) =
      analyticMeroElement f hf - analyticMeroElement g hg := by
  rw [analyticMeroElement, analyticMeroElement, analyticMeroElement, ← map_sub]
  congr 1

/-- Powers of analytic germs are realized by pointwise powers. -/
theorem analyticMeroElement_pow {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    analyticMeroElement (fun z => f z ^ n) (hf.pow n) = analyticMeroElement f hf ^ n := by
  rw [analyticMeroElement, analyticMeroElement, ← map_pow]
  congr 1

/-- **Differential algebraicity of entire functions is closed under subtraction.** -/
theorem differentiallyAlgebraic_sub {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ))
    (hfDA : DifferentiallyAlgebraic f) (hgDA : DifferentiallyAlgebraic g) :
    DifferentiallyAlgebraic (fun z => f z - g z) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
  letI : CharZero (meroField (Set.univ : Set ℂ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  refine differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (hf.sub hg) ?_
  rw [analyticMeroElement_sub hf hg]
  exact differentialAlgebraicOver_sub
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hfDA)
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hg hgDA)

/-- **Differential algebraicity of entire functions is closed under natural powers.** -/
theorem differentiallyAlgebraic_pow {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hfDA : DifferentiallyAlgebraic f) (n : ℕ) :
    DifferentiallyAlgebraic (fun z => f z ^ n) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
  letI : CharZero (meroField (Set.univ : Set ℂ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  refine differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (hf.pow n) ?_
  rw [analyticMeroElement_pow hf n]
  exact differentialAlgebraicOver_pow
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hfDA) n

end

end GaloisForLFunctions.HTGeometry
