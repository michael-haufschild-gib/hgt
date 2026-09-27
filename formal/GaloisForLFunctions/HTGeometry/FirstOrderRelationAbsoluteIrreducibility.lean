import GaloisForLFunctions.HTGeometry.FirstOrderRelationSpecialization
import GaloisForLFunctions.HTGeometry.RegularExtensionMinpoly
import GaloisForLFunctions.HTGeometry.MeromorphicRationalRelativeClosure
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalStateEmbedding

/-!
# The first-order relation of an entire function is absolutely irreducible

Let `f` be transcendental entire with irreducible first-order relation
`P = ∑_{i ∈ S} Aᵢ(U) V^(i₁) W^(i₂)`, `P(z, f, f') = 0`.  Then `P(U, V, W)` stays irreducible over
`K(V)` for every finite extension `K` of `ℂ(U)`, and hence (by specialisation) over `F(V)` for
every field `F ⊇ ℂ(U)`.

The proof takes place in an algebraic closure `Ω'` of the global meromorphic field, where the jet
`(z, f, f')` lives.  Put `B = ℂ(z, f) ⊆ Ω'` and let `θ` generate `K` over `ℂ(z)`.

* `ℂ(z)` is relatively algebraically closed in the meromorphic field, so the minimal polynomial of
  `θ` does not drop over `B(f')`: `deg_{B(f')} θ = deg_{ℂ(z)} θ ≥ deg_B θ`.
* Degree exchange in `B(f', θ)` then gives `deg_{B(θ)} f' ≥ deg_B f' = deg_W P`.
* `K(V)` maps into `B(θ)` with `V ↦ f`, carrying `P(U, V, W)` to the relation of `f'`; a
  factorization over `K(V)` would give `f'` a relation over `B(θ)` of smaller degree.
-/

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance absIrrDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

noncomputable local instance absIrrRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

noncomputable local instance absIrrComplexAlgebra :
    Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra

local instance absIrrScalarTower :
    IsScalarTower ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The algebraic closure of the global meromorphic field. -/
abbrev MeroClosure := AlgebraicClosure (meroField (Set.univ : Set ℂ))

/-- Constants of the meromorphic field are the constant germs. -/
theorem algebraMap_complex_mero (c : ℂ) :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = constToMero (Set.univ : Set ℂ) c := by
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c) = _
  rw [← ratfuncToMero_C_eq_constToMero]
  rfl

/-- The coordinate germ is the rational coordinate. -/
theorem analyticMeroElement_coord_eq_algebraMap_X :
    analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id =
      algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) RatFunc.X := by
  change _ = ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ RatFunc.X
  rw [← RatFunc.algebraMap_X, ratfuncToMero_algebraMap_polynomial]
  apply congrArg (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
  apply Subtype.ext
  change (Filter.Germ.ofFun (fun z : ℂ => z) : Filter.Germ (Filter.principal Set.univ) ℂ) =
    Filter.Germ.ofFun (fun z : ℂ => (Polynomial.X : Polynomial ℂ).eval z)
  congr 1
  funext z
  simp

variable {f : ℂ → ℂ}

theorem analyticOnNhd_of_transcendentalEntire'' (hf : TranscendentalEntire f) :
    AnalyticOnNhd ℂ f Set.univ :=
  hf.1.differentiableOn.analyticOnNhd isOpen_univ

/-- The jet `(z, f, f')` in the algebraic closure of the meromorphic field. -/
def wimanJet (hf : TranscendentalEntire f) : Fin 3 → MeroClosure :=
  ![algebraMap (meroField Set.univ) MeroClosure
      (algebraMap (RatFunc ℂ) (meroField Set.univ) RatFunc.X),
    algebraMap (meroField Set.univ) MeroClosure
      (analyticMeroElement f (analyticOnNhd_of_transcendentalEntire'' hf)),
    algebraMap (meroField Set.univ) MeroClosure
      (analyticMeroElement (deriv f) (analyticOnNhd_of_transcendentalEntire'' hf).deriv)]

/-- The jet in the meromorphic field. -/
theorem wimanJet_eq (hf : TranscendentalEntire f) :
    wimanJet hf = fun i => algebraMap (meroField Set.univ) MeroClosure
      (analyticMeroElement (![fun z => z, f, deriv f] i)
        (by fin_cases i
            · exact analyticOnNhd_id
            · exact analyticOnNhd_of_transcendentalEntire'' hf
            · exact (analyticOnNhd_of_transcendentalEntire'' hf).deriv)) := by
  funext i
  fin_cases i
  · simp [wimanJet, analyticMeroElement_coord_eq_algebraMap_X]
  · rfl
  · rfl

/-- The analytic realization of the jet `(z, f, f')` in the meromorphic field. -/
theorem analyticOnNhd_wimanVec (hf : TranscendentalEntire f) (i : Fin 3) :
    AnalyticOnNhd ℂ (![fun z => z, f, deriv f] i) Set.univ := by
  fin_cases i
  · exact analyticOnNhd_id
  · exact analyticOnNhd_of_transcendentalEntire'' hf
  · exact (analyticOnNhd_of_transcendentalEntire'' hf).deriv

theorem constToMero_eq_algebraMap :
    constToMero (Set.univ : Set ℂ) = algebraMap ℂ (meroField (Set.univ : Set ℂ)) :=
  RingHom.ext fun c => (algebraMap_complex_mero c).symm

/-- **The relation of `f` holds for the jet.** -/
theorem aeval_wimanJet_eq_zero (hf : TranscendentalEntire f) (P : MvPolynomial (Fin 3) ℂ)
    (hrel : ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) P = 0) :
    MvPolynomial.aeval (wimanJet hf) P = 0 := by
  have hbase := analyticMeroElement_eval_mvPolynomial (U := Set.univ)
    (![fun z => z, f, deriv f]) (analyticOnNhd_wimanVec hf) P
  have hzero : (fun z : ℂ => MvPolynomial.eval (fun i => (![fun z => z, f, deriv f] i) z) P) =
      fun _ => (0 : ℂ) := by
    funext z
    have hv : (fun i => (![fun z => z, f, deriv f] i) z) =
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z : Fin 3 → ℂ) := by
      funext i
      fin_cases i
      · rfl
      · simp
      · show deriv f z = iteratedDeriv ((1 : Fin 2) : ℕ) f z
        simp [iteratedDeriv_one]
    rw [hv, hrel z]
  rw [analyticMeroElement_congr _ analyticOnNhd_const hzero, analyticMeroElement_zero,
    constToMero_eq_algebraMap] at hbase
  have hjet : wimanJet hf = fun i => algebraMap (meroField Set.univ) MeroClosure
      (analyticMeroElement (![fun z => z, f, deriv f] i) (analyticOnNhd_wimanVec hf i)) :=
    wimanJet_eq hf
  rw [hjet]
  change MvPolynomial.aeval (algebraMap (meroField Set.univ) MeroClosure ∘
    fun i => analyticMeroElement (![fun z => z, f, deriv f] i)
      (analyticOnNhd_wimanVec hf i)) P = 0
  rw [MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_def, ← hbase, map_zero]

/-- **The coordinate and `f` are algebraically independent over `ℂ`.** -/
theorem algebraicIndependent_wimanJet_state (hf : TranscendentalEntire f) :
    AlgebraicIndependent ℂ (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ wimanJet hf j.1) := by
  rw [algebraicIndependent_iff]
  intro Q hQ
  by_contra hQ0
  let Q₂ : MvPolynomial (Fin 2) ℂ := MvPolynomial.rename firstOrderStateIndexEquiv Q
  have hQ₂ : Q₂ ≠ 0 := by
    intro h0
    apply hQ0
    have := congrArg (MvPolynomial.rename firstOrderStateIndexEquiv.symm) h0
    rwa [map_zero, MvPolynomial.rename_rename, Equiv.symm_comp_self,
      MvPolynomial.rename_id] at this
  apply not_differentiallyAlgebraicOfOrder_zero_of_transcendental hf.1 hf.2
  refine ⟨Q₂, hQ₂, ?_⟩
  -- the relation in the meromorphic field, then pointwise
  have hbase := analyticMeroElement_eval_mvPolynomial (U := Set.univ)
    (![fun z => z, f]) (fun i => by
      fin_cases i
      · exact analyticOnNhd_id
      · exact analyticOnNhd_of_transcendentalEntire'' hf) Q₂
  have hmero : MvPolynomial.eval₂ (constToMero Set.univ) (fun i => analyticMeroElement
      (![fun z => z, f] i) (by
        fin_cases i
        · exact analyticOnNhd_id
        · exact analyticOnNhd_of_transcendentalEntire'' hf)) Q₂ = 0 := by
    apply (algebraMap (meroField Set.univ) MeroClosure).injective
    have hfun : (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ wimanJet hf j.1) =
        (⇑(algebraMap (meroField Set.univ) MeroClosure) ∘ fun i => analyticMeroElement
          (![fun z => z, f] i) (by
            fin_cases i
            · exact analyticOnNhd_id
            · exact analyticOnNhd_of_transcendentalEntire'' hf)) ∘ ⇑firstOrderStateIndexEquiv := by
      funext j
      obtain ⟨j, hj⟩ := j
      fin_cases j
      · simp [firstOrderStateIndexEquiv, wimanJet, analyticMeroElement_coord_eq_algebraMap_X]
      · simp [firstOrderStateIndexEquiv, wimanJet]
      · exact absurd rfl hj
    rw [map_zero, ← hQ, constToMero_eq_algebraMap, ← MvPolynomial.aeval_def,
      ← MvPolynomial.aeval_algebraMap_apply, MvPolynomial.aeval_rename, hfun]
  rw [hmero] at hbase
  have hpt := (analyticMeroElement_eq_zero_iff _).mp hbase
  intro z
  have hz := hpt z (Set.mem_univ z)
  have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) f z : Fin 2 → ℂ) =
      fun i => (![fun z => z, f] i) z := by
    funext j
    fin_cases j <;> simp
  rw [hvec]
  exact hz

local instance absIrrComplexRatFuncClosureTower :
    IsScalarTower ℂ (RatFunc ℂ) MeroClosure :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (meroField Set.univ) MeroClosure,
      IsScalarTower.algebraMap_apply (RatFunc ℂ) (meroField Set.univ) MeroClosure]
    rfl

/-- The jet `(z, f, f')` in the meromorphic field. -/
def meroJet (hf : TranscendentalEntire f) : Fin 3 → meroField (Set.univ : Set ℂ) :=
  ![algebraMap (RatFunc ℂ) (meroField Set.univ) RatFunc.X,
    analyticMeroElement f (analyticOnNhd_of_transcendentalEntire'' hf),
    analyticMeroElement (deriv f) (analyticOnNhd_of_transcendentalEntire'' hf).deriv]

theorem wimanJet_eq_comp (hf : TranscendentalEntire f) :
    wimanJet hf = algebraMap (meroField Set.univ) MeroClosure ∘ meroJet hf := by
  funext i
  fin_cases i <;> rfl

/-- The coordinate of the jet is the image of the rational coordinate. -/
theorem wimanJet_zero (hf : TranscendentalEntire f) :
    wimanJet hf 0 = algebraMap (RatFunc ℂ) MeroClosure RatFunc.X := by
  rw [IsScalarTower.algebraMap_apply (RatFunc ℂ) (meroField Set.univ) MeroClosure]
  rfl

/-- `ℂ(z)` acts on the closure through evaluation at the coordinate. -/
theorem algebraMap_ratFunc_polynomial (hf : TranscendentalEntire f) (p : Polynomial ℂ) :
    algebraMap (RatFunc ℂ) MeroClosure (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      Polynomial.aeval (wimanJet hf 0) p := by
  rw [wimanJet_zero, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

/-- Evaluation of the rational state field `ℂ(U, V)` at `(z, f)`. -/
def wimanStateEval (hf : TranscendentalEntire f) :
    FirstOrderRationalStateField →ₐ[ℂ] MeroClosure :=
  firstOrderRationalStateEval (wimanJet hf)
    (firstOrderStatePolynomialEval_injective_of_algebraicIndependent _
      (algebraicIndependent_wimanJet_state hf))

theorem wimanStateEval_V (hf : TranscendentalEntire f) :
    wimanStateEval hf (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
      (Polynomial.C Polynomial.X)) = wimanJet hf 1 := by
  rw [wimanStateEval, firstOrderRationalStateEval_algebraMap,
    ← firstOrderStatePolynomialEquiv_X_one, firstOrderStatePolynomialEval_equiv,
    MvPolynomial.aeval_X]

/-- A polynomial in `U` alone evaluates at the coordinate. -/
theorem wimanStateEval_polynomial (hf : TranscendentalEntire f) (p : Polynomial ℂ) :
    wimanStateEval hf (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField
      (p.map Polynomial.C)) = Polynomial.aeval (wimanJet hf 0) p := by
  rw [wimanStateEval, firstOrderRationalStateEval_algebraMap]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, hp, hq, map_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_mul, map_pow, map_mul, map_pow,
      Polynomial.aeval_C, Polynomial.aeval_X]
    have hC : firstOrderStatePolynomialEval (wimanJet hf) (Polynomial.C (Polynomial.C c)) =
        algebraMap ℂ MeroClosure c := by
      have hCC : (Polynomial.C (Polynomial.C c) : FirstOrderStatePolynomialRing) =
          algebraMap ℂ FirstOrderStatePolynomialRing c := by
        rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_eq]
      rw [hCC]
      exact (firstOrderStatePolynomialEval (wimanJet hf)).commutes c
    have hX : firstOrderStatePolynomialEval (wimanJet hf) Polynomial.X = wimanJet hf 0 := by
      rw [← firstOrderStatePolynomialEquiv_X_zero, firstOrderStatePolynomialEval_equiv,
        MvPolynomial.aeval_X]
    rw [hC, hX]

/-- The values of the state evaluation are meromorphic. -/
theorem wimanStateEval_mem_range (hf : TranscendentalEntire f)
    (x : FirstOrderRationalStateField) :
    wimanStateEval hf x ∈ (algebraMap (meroField Set.univ) MeroClosure).fieldRange := by
  have key : ∀ c : FirstOrderStatePolynomialRing, wimanStateEval hf
      (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField c) ∈
        (algebraMap (meroField Set.univ) MeroClosure).fieldRange := by
    intro c
    obtain ⟨c, rfl⟩ := firstOrderStatePolynomialEquiv.surjective c
    rw [wimanStateEval, firstOrderRationalStateEval_algebraMap,
      firstOrderStatePolynomialEval_equiv]
    refine ⟨MvPolynomial.aeval (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ meroJet hf j.1) c, ?_⟩
    rw [← MvPolynomial.aeval_algebraMap_apply, wimanJet_eq_comp]
    rfl
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective FirstOrderStatePolynomialRing x
  rw [map_div₀]
  exact div_mem (key a) (key b)

/-- **`f` is transcendental over `ℂ(z)`.** -/
theorem transcendental_wimanJet_one (hf : TranscendentalEntire f) :
    Transcendental (RatFunc ℂ) (wimanJet hf 1) := by
  let j₀ : {j : Fin 3 // j ≠ (2 : Fin 3)} := ⟨0, by decide⟩
  let j₁ : {j : Fin 3 // j ≠ (2 : Fin 3)} := ⟨1, by decide⟩
  have hj : j₁ ∉ ({j₀} : Set {j : Fin 3 // j ≠ (2 : Fin 3)}) := by
    simp [j₀, j₁]
  have h1 := (algebraicIndependent_wimanJet_state hf).transcendental_adjoin hj
  rw [Set.image_singleton, ← IntermediateField.transcendental_adjoin_iff] at h1
  let L := IntermediateField.adjoin ℂ {wimanJet hf 0}
  have hmem : ∀ r : RatFunc ℂ, algebraMap (RatFunc ℂ) MeroClosure r ∈ L := by
    intro r
    let φ := IsScalarTower.toAlgHom ℂ (RatFunc ℂ) MeroClosure
    have hr : r ∈ IntermediateField.adjoin ℂ {(RatFunc.X : RatFunc ℂ)} := by
      rw [RatFunc.adjoin_X]
      trivial
    have h2 : φ r ∈ (IntermediateField.adjoin ℂ {(RatFunc.X : RatFunc ℂ)}).map φ :=
      (IntermediateField.mem_map _).mpr ⟨r, hr, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have h3 : φ RatFunc.X = wimanJet hf 0 := (wimanJet_zero hf).symm
    rw [h3] at h2
    exact h2
  refine Transcendental.of_ringHom_of_comp_eq (S := L) (B := MeroClosure)
    ((algebraMap (RatFunc ℂ) MeroClosure).codRestrict L hmem) (RingHom.id MeroClosure) ?_
    (RingHom.injective _) ?_
  · exact h1
  · ext r
    rfl

/-- **Regularity.**  A meromorphic function integral over `ℂ(z)` is rational. -/
theorem mem_range_of_isIntegral_ratFunc (y : meroField (Set.univ : Set ℂ))
    (hy : IsIntegral (RatFunc ℂ) y) :
    y ∈ Set.range (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) :=
  exists_ratfuncToMero_eq_of_isAlgebraic y hy.isAlgebraic

/-- The derivative polynomial of `P`, pushed forward along a state evaluation, is `P(x₀, x₁, W)`. -/
theorem map_firstOrderDerivativePolynomial {M : Type*} [Field M] [Algebra ℂ M] (x : Fin 3 → M)
    (hinj : Function.Injective (firstOrderStatePolynomialEval x)) (P : MvPolynomial (Fin 3) ℂ) :
    (firstOrderDerivativePolynomial P).map
        (firstOrderRationalStateEval x hinj : FirstOrderRationalStateField →+* M) =
      MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap ℂ M))
        (fun j : Fin 3 => ![Polynomial.C (x 0), Polynomial.C (x 1), Polynomial.X] j) P := by
  classical
  have hcomp : (firstOrderRationalStateEval x hinj : FirstOrderRationalStateField →+* M).comp
      (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField) =
        (firstOrderStatePolynomialEval x : FirstOrderStatePolynomialRing →+* M) :=
    RingHom.ext fun p => firstOrderRationalStateEval_algebraMap x hinj p
  have hcomp₂ : (firstOrderStatePolynomialEval x : FirstOrderStatePolynomialRing →+* M).comp
      firstOrderStatePolynomialEquiv.toRingHom =
        (MvPolynomial.aeval (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)).toRingHom :=
    RingHom.ext fun c => firstOrderStatePolynomialEval_equiv x c
  rw [firstOrderDerivativePolynomial, Polynomial.map_map, hcomp,
    firstOrderDerivativePolynomialOverStateRing, Polynomial.map_map, hcomp₂]
  have hext : (Polynomial.mapRingHom (MvPolynomial.aeval
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)).toRingHom).comp
        ((mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)) :
          MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] _).toAlgHom.toRingHom =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap ℂ M))
        (fun j : Fin 3 => ![Polynomial.C (x 0), Polynomial.C (x 1), Polynomial.X] j) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · have hC : (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)) (MvPolynomial.C r) =
          Polynomial.C (MvPolynomial.C r) := by
        simpa using (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)).commutes r
      simp [hC]
    · by_cases hq : q = (2 : Fin 3)
      · subst hq
        change Polynomial.map _ (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)
          (MvPolynomial.X 2)) = MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 2)
        rw [mvPolynomialPolynomialEquivAt_X_self, Polynomial.map_X, MvPolynomial.eval₂Hom_X']
        rfl
      · change Polynomial.map _ (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)
          (MvPolynomial.X q)) = MvPolynomial.eval₂Hom _ _ (MvPolynomial.X q)
        rw [mvPolynomialPolynomialEquivAt_X_ne hq, Polynomial.map_C, MvPolynomial.eval₂Hom_X']
        change Polynomial.C (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
        rw [MvPolynomial.aeval_X]
        fin_cases q
        · rfl
        · rfl
        · exact absurd rfl hq
  exact congrArg (fun φ => φ P) hext

/-- The first-order relation pushed along `K[V] → ℂ̄(z, f)`, `V ↦ f`, over any embedding of `K`
over `ℂ(U)`, is `P(z, f, W)`. -/
theorem relPolyVia_map_eval₂_wiman (hf : TranscendentalEntire f)
    (data : EntireFirstOrderWimanInitialData f) {K : Type*} [Field K]
    (ψ : RatFunc ℂ →+* K) (j : K →+* MeroClosure)
    (hj : j.comp ψ = algebraMap (RatFunc ℂ) MeroClosure) :
    (relPolyVia data.indexSupport data.coeff ψ).map
        (Polynomial.eval₂RingHom j (wimanJet hf 1)) =
      (firstOrderDerivativePolynomial data.P).map
        (wimanStateEval hf : FirstOrderRationalStateField →+* MeroClosure) := by
  rw [wimanStateEval, map_firstOrderDerivativePolynomial, ← data.coefficient_reconstruction,
    eval₂_firstOrderMvPoly, relPolyVia, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, ← RingHom.comp_apply j ψ, hj, algebraMap_ratFunc_polynomial hf,
    Polynomial.aeval_def, ← Polynomial.hom_eval₂, Polynomial.C_mul, Polynomial.C_pow]

/-- `ℂ(U) → ℂ(U, V)`, compatible with the evaluations at `(z, f)`. -/
theorem exists_ratFunc_hom_wimanStateEval (hf : TranscendentalEntire f) :
    ∃ g₁ : RatFunc ℂ →+* FirstOrderRationalStateField,
      (wimanStateEval hf : FirstOrderRationalStateField →+* MeroClosure).comp g₁ =
        algebraMap (RatFunc ℂ) MeroClosure := by
  have hu₀ : Function.Injective ((algebraMap FirstOrderStatePolynomialRing
      FirstOrderRationalStateField).comp (Polynomial.mapRingHom Polynomial.C)) :=
    (IsFractionRing.injective FirstOrderStatePolynomialRing FirstOrderRationalStateField).comp
      (Polynomial.map_injective _ Polynomial.C_injective)
  refine ⟨IsFractionRing.lift (K := RatFunc ℂ) hu₀, ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
  refine RingHom.ext fun p => ?_
  change wimanStateEval hf (IsFractionRing.lift (K := RatFunc ℂ) hu₀
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)) =
    algebraMap (RatFunc ℂ) MeroClosure (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
  rw [IsFractionRing.lift_algebraMap, algebraMap_ratFunc_polynomial hf]
  exact wimanStateEval_polynomial hf p

/-- **Absolute irreducibility of the first-order relation.**  The relation `P(U, V, W)` of a
transcendental entire function stays irreducible over `K(V)` for every finite extension `K` of
`ℂ(U)`. -/
theorem relIrrVia_wiman_of_finite (hf : TranscendentalEntire f)
    (data : EntireFirstOrderWimanInitialData f) (K : Type) [Field K] (ψ : RatFunc ℂ →+* K)
    (hψ : ψ.Finite) : RelIrrVia data.indexSupport data.coeff ψ := by
  letI : Algebra (RatFunc ℂ) K := ψ.toAlgebra
  haveI : Module.Finite (RatFunc ℂ) K := hψ
  obtain ⟨g₁, hg₁⟩ := exists_ratFunc_hom_wimanStateEval hf
  exact irreducible_map_of_regular_embedding (M := meroField (Set.univ : Set ℂ))
    mem_range_of_isIntegral_ratFunc
    (wimanStateEval hf : FirstOrderRationalStateField →+* MeroClosure) g₁ hg₁
    (wimanStateEval_mem_range hf) (transcendental_wimanJet_one hf) ⟨_, wimanStateEval_V hf⟩
    (RingHom.mem_fieldRange.mpr ⟨meroJet hf 2, by rw [wimanJet_eq_comp]; rfl⟩)
    (firstOrderDerivativePolynomial_irreducible data)
    ((firstOrderDerivativePolynomial_eval (wimanJet hf) _ data.P).trans
      (aeval_wimanJet_eq_zero hf data.P data.relation))
    (relPolyVia data.indexSupport data.coeff ψ)
    (fun j => relPolyVia_map_eval₂_wiman hf data ψ j (RingHom.ext fun r => j.commutes r))

/-- **Irreducibility over every field.**  The first-order relation of a transcendental entire
function is irreducible over `F(V)` for every field `F ⊇ ℂ(U)`. -/
theorem relIrrVia_wiman (hf : TranscendentalEntire f) (data : EntireFirstOrderWimanInitialData f)
    {F : Type} [Field F] (φ : RatFunc ℂ →+* F) : RelIrrVia data.indexSupport data.coeff φ := by
  classical
  have hne : data.indexSupport.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply data.polynomial_ne_zero
    rw [← data.coefficient_reconstruction, firstOrderMvPoly, h, Finset.sum_empty]
  obtain ⟨i₀, hi₀, hmax⟩ := data.indexSupport.exists_max_image (fun i => i.2) hne
  refine relIrrVia_of_finite data.coefficient_ne_zero hi₀ ?_ hmax
    (fun K _ ψ hψ => relIrrVia_wiman_of_finite hf data K ψ hψ) φ
  by_contra h0
  have hid := relPolyVia_map_eval₂_wiman hf data (RingHom.id (RatFunc ℂ))
    (algebraMap (RatFunc ℂ) MeroClosure) (RingHom.comp_id _)
  have h1 : ((relPolyVia data.indexSupport data.coeff (RingHom.id (RatFunc ℂ))).map
      (Polynomial.eval₂RingHom (algebraMap (RatFunc ℂ) MeroClosure) (wimanJet hf 1))).natDegree ≤
        i₀.2 :=
    Polynomial.natDegree_map_le.trans (natDegree_relPolyVia_le _ i₀.2 hmax)
  rw [hid, natDegree_map_eq_of_injective (RingHom.injective _)] at h1
  have := firstOrderDerivativePolynomial_natDegree_pos data
  omega

end

end GaloisForLFunctions.HTGeometry
