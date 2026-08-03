import GaloisForLFunctions.HTGeometry.DiscretePeriodGaugeClassification
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.RatFuncCoordinateScaling
import GaloisForLFunctions.HTGeometry.OddPowerCanonicalProductGammaRay
import GaloisForLFunctions.HTGeometry.OnePowerCanonicalProductHypertranscendence

/-!
# Gamma at an arbitrary complex scale, and the odd-exponent open core

The corpus carries `Γ(z+b)` and `Γ(nz+a)` for a natural scale `n` as elements of the global
meromorphic differential field.  An arbitrary nonzero complex scale is obtained by transporting the
shift element along the scaling automorphism `z ↦ a z`, which is already available as
`complexScaleMeroEquiv`.

The point of the construction is the odd-exponent canonical product: the ray-product identity
`W_p(z^p) = ∏_{j<p} Γ(ω^j z + 1)⁻¹` places the remaining open core of the integer-exponent
dichotomy inside the meromorphic differential field, as the hypertranscendence over `ℂ(X)` of a
finite product of reciprocal Gamma elements at the `p` distinct scales `ω^j`.  The corpus's
superselection layer settles the common-scale and natural-scale cases; this file is the substrate on
which the root-of-unity scale case has to be decided.
-/

namespace HTGeometry

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher Filter Set Topology

noncomputable section

open scoped UnivMeroFieldInstances

/-- The entire germ of `z ↦ Γ(a z + b)⁻¹`. -/
def reciprocalGammaScaleShiftAnalytic (a b : ℂ) : analyticSubring (Set.univ : Set ℂ) :=
  univAnalytic (fun z => reciprocalGammaEntire (a * z + b)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
      ((differentiable_const a).mul differentiable_id |>.add (differentiable_const b)))

@[simp] theorem univGermEval_reciprocalGammaScaleShiftAnalytic (a b z : ℂ) :
    univGermEval z
        ((reciprocalGammaScaleShiftAnalytic a b : analyticSubring Set.univ) :
          Germ (Filter.principal Set.univ) ℂ)
      = reciprocalGammaEntire (a * z + b) := rfl

/-- Scaling the coordinate carries the reciprocal-Gamma shift germ to the reciprocal-Gamma
scale-shift germ. -/
theorem complexScaleAnalyticEquiv_reciprocalGammaShiftAnalytic
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    complexScaleAnalyticEquiv a ha (reciprocalGammaShiftAnalytic b)
      = reciprocalGammaScaleShiftAnalytic a b := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_complexScaleAnalyticEquiv]
  rfl

/-- **Gamma at an arbitrary nonzero complex scale**, as an element of the global meromorphic
differential field: the class of `z ↦ Γ(a z + b)`. -/
def gammaScaleShiftMero (a : ℂ) (ha : a ≠ 0) (b : ℂ) : meroField (Set.univ : Set ℂ) :=
  complexScaleMeroEquiv a ha (gammaShiftMero b)

theorem gammaScaleShiftMero_eq (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    gammaScaleShiftMero a ha b
      = (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (reciprocalGammaScaleShiftAnalytic a b))⁻¹ := by
  rw [gammaScaleShiftMero, gammaShiftMero, map_inv₀, complexScaleMeroEquiv_algebraMap,
    complexScaleAnalyticEquiv_reciprocalGammaShiftAnalytic]

theorem gammaScaleShiftMero_ne_zero (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    gammaScaleShiftMero a ha b ≠ 0 := by
  rw [gammaScaleShiftMero]
  exact (map_ne_zero_iff _ (complexScaleMeroEquiv a ha).injective).mpr
    (gammaShiftMero_ne_zero b)

/-- The reciprocal-Gamma ray product at the `p`-th roots of unity, as a meromorphic element. -/
def gammaRayProductMero (p : ℕ) (ω : ℂ) (hω : ω ≠ 0) : meroField (Set.univ : Set ℂ) :=
  ∏ j ∈ Finset.range p, (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1)⁻¹

/-- The analytic ray product `z ↦ ∏_{j<p} Γ(ω^j z + 1)⁻¹` is entire. -/
theorem analyticOnNhd_gammaRayProduct (p : ℕ) (ω : ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹) Set.univ := by
  intro z _
  refine Finset.analyticAt_fun_prod (Finset.range p) fun j _ => ?_
  have hd : Differentiable ℂ (fun z : ℂ => (Complex.Gamma (ω ^ j * z + 1))⁻¹) := by
    have h : Differentiable ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) :=
      Complex.differentiable_one_div_Gamma
    exact h.comp ((differentiable_const _).mul differentiable_id |>.add (differentiable_const 1))
  exact ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) z (Set.mem_univ z))

/-- The meromorphic realization of the analytic ray product is the meromorphic ray product. -/
theorem analyticMeroElement_gammaRayProduct (p : ℕ) {ω : ℂ} (hω : ω ≠ 0) :
    analyticMeroElement
        (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
        (analyticOnNhd_gammaRayProduct p ω)
      = gammaRayProductMero p ω hω := by
  have hfac : ∀ j : ℕ,
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (reciprocalGammaScaleShiftAnalytic (ω ^ j) 1))
        = (gammaScaleShiftMero (ω ^ j) (pow_ne_zero j hω) 1)⁻¹ := by
    intro j
    rw [gammaScaleShiftMero_eq, inv_inv]
  have hprodGerm : ∀ (s : Finset ℕ) (F : ℕ → analyticSubring (Set.univ : Set ℂ)) (z : ℂ),
      univGermEval z ((∏ j ∈ s, F j : analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
        = ∏ j ∈ s, univGermEval z ((F j : analyticSubring (Set.univ : Set ℂ)) :
            Germ (Filter.principal (Set.univ : Set ℂ)) ℂ) := by
    classical
    intro s F z
    induction s using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih]
        exact univGermEval_analyticSubring_mul z _ _
  have hel : analyticFunctionElement
      (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹)
      (analyticOnNhd_gammaRayProduct p ω)
      = ∏ j ∈ Finset.range p, reciprocalGammaScaleShiftAnalytic (ω ^ j) 1 := by
    apply Subtype.ext
    apply univGerm_ext
    intro z
    rw [hprodGerm]
    change (fun z : ℂ => ∏ j ∈ Finset.range p, (Complex.Gamma (ω ^ j * z + 1))⁻¹) z
      = ∏ j ∈ Finset.range p, reciprocalGammaEntire (ω ^ j * z + 1)
    exact Finset.prod_congr rfl fun j _ => rfl
  rw [gammaRayProductMero, Finset.prod_congr rfl fun j _ => (hfac j).symm,
    ← map_prod, analyticMeroElement, hel]

/-! ## The scaled translation law -/

theorem complexScaleAnalyticEquiv_polyToAnalytic (a : ℂ) (ha : a ≠ 0) (P : Polynomial ℂ) :
    complexScaleAnalyticEquiv a ha (polyToAnalytic Set.univ P)
      = polyToAnalytic Set.univ (P.comp (Polynomial.C a * Polynomial.X)) := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_complexScaleAnalyticEquiv]
  have hL : univGermEval (a * z)
      ((polyToAnalytic Set.univ P : analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ) = P.eval (a * z) := rfl
  have hR : univGermEval z
      ((polyToAnalytic Set.univ (P.comp (Polynomial.C a * Polynomial.X)) :
        analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
      = (P.comp (Polynomial.C a * Polynomial.X)).eval z := rfl
  rw [hL, hR, Polynomial.eval_comp]
  simp

theorem complexScaleMeroEquiv_polyToMero (a : ℂ) (ha : a ≠ 0) (P : Polynomial ℂ) :
    complexScaleMeroEquiv a ha (polyToMero Set.univ P)
      = polyToMero Set.univ (P.comp (Polynomial.C a * Polynomial.X)) := by
  have hp : ∀ R : Polynomial ℂ, polyToMero (Set.univ : Set ℂ) R
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (polyToAnalytic Set.univ R) := fun R => rfl
  rw [hp, hp, complexScaleMeroEquiv_algebraMap, complexScaleAnalyticEquiv_polyToAnalytic]

/-- The coordinate dilation on the meromorphic field restricts to the dilation of rational
functions. -/
theorem complexScaleMeroEquiv_ratfuncToMero (a : ℂ) (ha : a ≠ 0) (r : RatFunc ℂ) :
    complexScaleMeroEquiv a ha
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ r)
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ (ratScaleBy a ha r) := by
  obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial ℂ) r
  rw [map_div₀, map_div₀, map_div₀,
    ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial,
    complexScaleMeroEquiv_polyToMero, complexScaleMeroEquiv_polyToMero,
    ratScaleBy_algebraMap, ratScaleBy_algebraMap, map_div₀,
    ratfuncToMero_algebraMap_polynomial, ratfuncToMero_algebraMap_polynomial]

/-- **The scaled Gamma recurrence.**  Translating by `1/a` multiplies `Γ(a z + b)` by the dilated
coordinate `a z + b`. -/
theorem addTranslationMeroEquiv_gammaScaleShiftMero (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    addTranslationMeroEquiv a⁻¹ (gammaScaleShiftMero a ha b)
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
            Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b))
        * gammaScaleShiftMero a ha b := by
  rw [gammaScaleShiftMero, addTranslationMeroEquiv_complexScaleMeroEquiv,
    mul_inv_cancel₀ ha, addTranslationMeroEquiv_gammaShiftMero, map_mul,
    complexScaleMeroEquiv_ratfuncToMero]

/-- The digamma element at an arbitrary nonzero complex scale. -/
def digammaScaleShiftMero (a : ℂ) (ha : a ≠ 0) (b : ℂ) : meroField (Set.univ : Set ℂ) :=
  Differential.logDeriv (gammaScaleShiftMero a ha b)

/-- **The scaled digamma recurrence.**  Translating by `1/a` adds a rational increment. -/
theorem addTranslationMeroEquiv_digammaScaleShiftMero (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    addTranslationMeroEquiv a⁻¹ (digammaScaleShiftMero a ha b)
      = digammaScaleShiftMero a ha b
        + Differential.logDeriv
            (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
              Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b))) := by
  have hg : gammaScaleShiftMero a ha b ≠ 0 := gammaScaleShiftMero_ne_zero a ha b
  have hu : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b)) ≠ 0 := by
    refine (map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).injective).mpr ?_
    refine (map_ne_zero_iff _ (ratScaleBy a ha).injective).mpr ?_
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero b)
  simp only [digammaScaleShiftMero]
  have hcomm : addTranslationMeroEquiv a⁻¹ (Differential.logDeriv (gammaScaleShiftMero a ha b))
      = Differential.logDeriv (addTranslationMeroEquiv a⁻¹ (gammaScaleShiftMero a ha b)) := by
    rw [Differential.logDeriv, Differential.logDeriv, map_div₀, addTranslationMeroEquiv_deriv]
  have hsplit : Differential.logDeriv
      ((ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b)))
        * gammaScaleShiftMero a ha b)
      = Differential.logDeriv
          (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
            Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b)))
        + Differential.logDeriv (gammaScaleShiftMero a ha b) :=
    Differential.logDeriv_mul _ _ hu hg
  rw [hcomm, addTranslationMeroEquiv_gammaScaleShiftMero, hsplit]
  ring

/-! ## Parameter translation -/

/-- Translating the coordinate translates the shift parameter of the reciprocal-Gamma germ. -/
theorem addTranslationAnalyticEquiv_reciprocalGammaShiftAnalytic (h b : ℂ) :
    addTranslationAnalyticEquiv h (reciprocalGammaShiftAnalytic b)
      = reciprocalGammaShiftAnalytic (b + h) := by
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_addTranslationAnalyticEquiv]
  have hL : univGermEval (z + h)
      ((reciprocalGammaShiftAnalytic b : analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
      = reciprocalGammaEntire (z + h + b) := rfl
  have hR : univGermEval z
      ((reciprocalGammaShiftAnalytic (b + h) : analyticSubring (Set.univ : Set ℂ)) :
        Germ (Filter.principal (Set.univ : Set ℂ)) ℂ)
      = reciprocalGammaEntire (z + (b + h)) := rfl
  rw [hL, hR]
  congr 1
  ring

theorem addTranslationMeroEquiv_gammaShiftMero_param (h b : ℂ) :
    addTranslationMeroEquiv h (gammaShiftMero b) = gammaShiftMero (b + h) := by
  rw [gammaShiftMero, gammaShiftMero, map_inv₀, addTranslationMeroEquiv_algebraMap,
    addTranslationAnalyticEquiv_reciprocalGammaShiftAnalytic]

/-- **Parameter translation at an arbitrary scale.**  Translating the coordinate by `h` moves the
shift parameter of `Γ(a z + b)` by `a h`. -/
theorem addTranslationMeroEquiv_gammaScaleShiftMero_param (a : ℂ) (ha : a ≠ 0) (h b : ℂ) :
    addTranslationMeroEquiv h (gammaScaleShiftMero a ha b)
      = gammaScaleShiftMero a ha (b + a * h) := by
  rw [gammaScaleShiftMero, addTranslationMeroEquiv_complexScaleMeroEquiv,
    addTranslationMeroEquiv_gammaShiftMero_param, gammaScaleShiftMero]

/-- **The parameter recurrence.**  Raising the shift parameter by one multiplies `Γ(a z + b)` by the
dilated coordinate. -/
theorem gammaScaleShiftMero_param_succ (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    gammaScaleShiftMero a ha (b + 1)
      = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
            Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b))
        * gammaScaleShiftMero a ha b := by
  rw [← addTranslationMeroEquiv_gammaScaleShiftMero a ha b,
    addTranslationMeroEquiv_gammaScaleShiftMero_param a ha a⁻¹ b, mul_inv_cancel₀ ha]

/-- **The digamma parameter recurrence.**  Raising the shift parameter by one changes the scaled
digamma by a rational function.  This is the atom of the difference tower: each translation
`T_(1/a)` rationalises exactly the factors of scale `a`. -/
theorem digammaScaleShiftMero_param_succ (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    digammaScaleShiftMero a ha (b + 1)
      = digammaScaleShiftMero a ha b
        + Differential.logDeriv
            (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
              Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b))) := by
  have hg : gammaScaleShiftMero a ha b ≠ 0 := gammaScaleShiftMero_ne_zero a ha b
  have hu : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ (ratScaleBy a ha (RatFunc.X + RatFunc.C b)) ≠ 0 := by
    refine (map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).injective).mpr ?_
    refine (map_ne_zero_iff _ (ratScaleBy a ha).injective).mpr ?_
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero b)
  simp only [digammaScaleShiftMero]
  rw [gammaScaleShiftMero_param_succ a ha b, Differential.logDeriv_mul _ _ hu hg]
  ring

/-! ## The difference tower -/

/-- Abbreviation for the rational subfield of the meromorphic field. -/
def IsRationalMero (x : meroField (Set.univ : Set ℂ)) : Prop :=
  ∃ r : RatFunc ℂ, x = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ r

theorem IsRationalMero.add {x y : meroField (Set.univ : Set ℂ)}
    (hx : IsRationalMero x) (hy : IsRationalMero y) : IsRationalMero (x + y) := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  exact ⟨r + s, (map_add _ _ _).symm⟩

theorem IsRationalMero.sub {x y : meroField (Set.univ : Set ℂ)}
    (hx : IsRationalMero x) (hy : IsRationalMero y) : IsRationalMero (x - y) := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hy
  exact ⟨r - s, (map_sub _ _ _).symm⟩

theorem IsRationalMero.neg {x : meroField (Set.univ : Set ℂ)} (hx : IsRationalMero x) :
    IsRationalMero (-x) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨-r, (map_neg _ _).symm⟩

theorem isRationalMero_zero : IsRationalMero (0 : meroField (Set.univ : Set ℂ)) :=
  ⟨0, (map_zero _).symm⟩

theorem IsRationalMero.sum {ι : Type*} (s : Finset ι) (f : ι → meroField (Set.univ : Set ℂ))
    (h : ∀ i ∈ s, IsRationalMero (f i)) : IsRationalMero (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isRationalMero_zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The parameter recurrence, in rational-membership form. -/
theorem isRationalMero_digammaScaleShiftMero_param_succ_sub (a : ℂ) (ha : a ≠ 0) (b : ℂ) :
    IsRationalMero (digammaScaleShiftMero a ha (b + 1) - digammaScaleShiftMero a ha b) := by
  rw [digammaScaleShiftMero_param_succ a ha b]
  refine ⟨HTGeometry.ratFuncCoordinateDerivation ℂ
      (ratScaleBy a ha (RatFunc.X + RatFunc.C b))
    / ratScaleBy a ha (RatFunc.X + RatFunc.C b), ?_⟩
  rw [add_sub_cancel_left, Differential.logDeriv, map_div₀]
  congr 1
  exact meroField_deriv_ratfuncToMero _

/-- **The difference tower rationalises one scale.**  Take the alternating sum of the scaled digamma
over all subsets of a finite family of translation steps `τ`.  If one step is *integral for the
scale* — that is, `a · τ j₀ = 1` — then the whole alternating sum is a rational function.

Applied to the ray product with `a = ω^j` and `τ k = ω^{-k}`, the step `k = j` is integral for the
`j`-th scale, so the `p`-fold difference operator `∏_k (T_{ω^{-k}} − 1)` rationalises every factor:
the `p` scales are coupled through the `p` translations. -/
theorem isRationalMero_alternating_digammaScaleShiftMero {ι : Type*} [DecidableEq ι]
    (a : ℂ) (ha : a ≠ 0) (b : ℂ) (τ : ι → ℂ) (K : Finset ι) {j₀ : ι} (hj₀ : j₀ ∈ K)
    (hstep : a * τ j₀ = 1) :
    IsRationalMero
      (∑ S ∈ K.powerset, (-1 : meroField (Set.univ : Set ℂ)) ^ S.card
        * digammaScaleShiftMero a ha (b + a * ∑ k ∈ S, τ k)) := by
  classical
  obtain ⟨K', hK', rfl⟩ : ∃ K' : Finset ι, j₀ ∉ K' ∧ K = insert j₀ K' :=
    ⟨K.erase j₀, Finset.notMem_erase _ _, (Finset.insert_erase hj₀).symm⟩
  rw [Finset.sum_powerset_insert hK']
  have hpair : ∀ S ∈ K'.powerset,
      (-1 : meroField (Set.univ : Set ℂ)) ^ (insert j₀ S).card
        * digammaScaleShiftMero a ha (b + a * ∑ k ∈ insert j₀ S, τ k)
      = -((-1 : meroField (Set.univ : Set ℂ)) ^ S.card
        * digammaScaleShiftMero a ha ((b + a * ∑ k ∈ S, τ k) + 1)) := by
    intro S hS
    have hSne : j₀ ∉ S := fun hmem => hK' (Finset.mem_powerset.mp hS hmem)
    have hcard : (insert j₀ S).card = S.card + 1 := Finset.card_insert_of_notMem hSne
    have hsum : ∑ k ∈ insert j₀ S, τ k = τ j₀ + ∑ k ∈ S, τ k :=
      Finset.sum_insert hSne
    have hparam : b + a * ∑ k ∈ insert j₀ S, τ k = (b + a * ∑ k ∈ S, τ k) + 1 := by
      rw [hsum, mul_add, hstep]
      ring
    rw [hcard, hparam, pow_succ]
    ring
  rw [Finset.sum_congr rfl hpair, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine IsRationalMero.sum _ _ fun S _ => ?_
  have hdiff := isRationalMero_digammaScaleShiftMero_param_succ_sub a ha (b + a * ∑ k ∈ S, τ k)
  have hrw : (-1 : meroField (Set.univ : Set ℂ)) ^ S.card * digammaScaleShiftMero a ha (b + a * ∑ k ∈ S, τ k)
      + -((-1 : meroField (Set.univ : Set ℂ)) ^ S.card
        * digammaScaleShiftMero a ha ((b + a * ∑ k ∈ S, τ k) + 1))
      = -((-1 : meroField (Set.univ : Set ℂ)) ^ S.card) * (digammaScaleShiftMero a ha ((b + a * ∑ k ∈ S, τ k) + 1)
        - digammaScaleShiftMero a ha (b + a * ∑ k ∈ S, τ k)) := by
    ring
  rw [hrw]
  rcases Nat.even_or_odd S.card with hev | hod
  · rw [hev.neg_one_pow, neg_one_mul]
    exact hdiff.neg
  · rw [hod.neg_one_pow, neg_neg, one_mul]
    exact hdiff

/-- **The odd-exponent open core, in the meromorphic differential field.**  For odd `p ≥ 3` the
canonical product `W_p` with zeros `-n^p` is hypertranscendental exactly when the reciprocal-Gamma
ray product at the `p`-th roots of unity is hypertranscendental over `ℂ(X)`.

This is the last gate of the integer-exponent dichotomy.  The corpus settles the analogous statement
for a common scale and for natural scales; here the `p` scales are the `p`-th roots of unity, whose
pole rays are pairwise distinct precisely because `p` is odd. -/
theorem hypertranscendental_powerCanonicalProduct_odd_iff_mero {p : ℕ} (hp : 1 < p) (hodd : Odd p)
    {ω : ℂ} (hω : IsPrimitiveRoot ω p) :
    Hypertranscendental (powerCanonicalProduct (p : ℝ))
      ↔ HypertranscendentalOver (RatFunc ℂ)
          (gammaRayProductMero p ω (hω.ne_zero (by omega))) := by
  have hωne : ω ≠ 0 := hω.ne_zero (by omega)
  have hbridge := analyticMeroElement_gammaRayProduct p hωne
  rw [hypertranscendental_powerCanonicalProduct_odd_iff hp hodd hω]
  constructor
  · intro hHT hmero
    refine hHT (differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
      (analyticOnNhd_gammaRayProduct p ω) ?_)
    rw [hbridge]
    exact hmero
  · intro hHT hDA
    refine hHT ?_
    rw [← hbridge]
    exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (analyticOnNhd_gammaRayProduct p ω) hDA

end

end HTGeometry


