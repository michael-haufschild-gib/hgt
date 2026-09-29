import GaloisForLFunctions.HTGeometry.AbelIterateJetRelation
import GaloisForLFunctions.HTGeometry.ParabolicFormalFlow
import GaloisForLFunctions.HTGeometry.RittTreeChannelLinearizer
import GaloisForLFunctions.HTGeometry.LocalAnalyticExponentialClock
import GaloisForLFunctions.HTGeometry.DomainTranslationSlopeMinor
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicPropagation
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum

/-!
# Abel functions at a parabolic fixed point are hypertranscendental

Let `R` be a rational map of degree at least two with a parabolic fixed point at `0`
(`R(0) = 0`, `R'(0) = 1`), let `D` be an open connected set without poles of `R` with `R(D) ⊆ D`,
and let `A` be a nonconstant analytic Abel function on `D`, `A ∘ R = A + 1`.

**Theorem.**  If `A` satisfies an algebraic differential equation on `D`, then `R` carries a
rational cocycle `B(R)·R'^N = β·B`.

Boshernitzan–Rubel coherence (`AbelIterateJetRelation`) gives one polynomial relation among the
jets of every iterate `Rⁿ` on `D`.  The iterates are rational, so the relation holds between
rational functions, and hence between their expansions at the parabolic point `0`, where
`R = X(1 + aX^k + X^{k+1}w)` with `a ≠ 0`.  The formal flow of this germ (`ParabolicFormalFlow`)
turns the relation into a differentially algebraic eigen-coordinate and a cocycle.

For an interior tree channel at the parabolic parameter `p(u − v)/2 = 1` no cocycle exists
(`treeRG_no_cocycle_interior`).  So every nonconstant Abel function on such a `D` — in particular
every Fatou coordinate on an attracting petal — and its velocity field `1/A'` satisfy no algebraic
differential equation on any nonempty open subset of `D`.
-/

open Filter Topology Set PowerSeries Bottcher
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Rational functions on a pole-free domain -/

theorem analyticAt_ratValue_of_regular {Q : RatFunc ℂ} {z : ℂ} (hQ : 0 ≤ ratOrder Q z) :
    AnalyticAt ℂ (fun w => ratValue Q w) z :=
  ((Q.num.differentiable).analyticAt z).div ((Q.denom.differentiable).analyticAt z)
    (denom_eval_ne_zero_of_regular hQ)

theorem analyticOnNhd_ratValue {Q : RatFunc ℂ} {D : Set ℂ} (hQ : ∀ z ∈ D, 0 ≤ ratOrder Q z) :
    AnalyticOnNhd ℂ (fun w => ratValue Q w) D := fun z hz =>
  analyticAt_ratValue_of_regular (hQ z hz)

variable {D : Set ℂ}

theorem polyToMero_eq_analyticMeroElement (p : Polynomial ℂ) :
    polyToMero D p
      = analyticMeroElement (fun z => p.eval z) (fun z _ => p.differentiable.analyticAt z) :=
  rfl

/-- **A rational function without poles on `D` is the meromorphic function it defines.** -/
theorem ratfuncToMero_eq_analyticMeroElement (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hDne : D.Nonempty) (hDinf : D.Infinite) {Q : RatFunc ℂ} (hQ : ∀ z ∈ D, 0 ≤ ratOrder Q z) :
    letI := Bottcher.isDomain_analyticSubring D hDo hDc hDne
    ratfuncToMero D hDo hDc hDne hDinf Q
      = analyticMeroElement (fun z => ratValue Q z) (analyticOnNhd_ratValue hQ) := by
  letI := Bottcher.isDomain_analyticSubring D hDo hDc hDne
  have hden : polyToMero D Q.denom ≠ 0 := by
    rw [← ratfuncToMero_algebraMap_polynomial D hDo hDc hDne hDinf]
    exact (map_ne_zero _).mpr
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr (RatFunc.denom_ne_zero Q))
  rw [ratfuncToMero_eq_div, div_eq_iff hden, polyToMero_eq_analyticMeroElement,
    polyToMero_eq_analyticMeroElement, ← analyticMeroElement_mul]
  refine analyticMeroElement_congr_eqOn _ _ fun z hz => ?_
  show Q.num.eval z = Q.num.eval z / Q.denom.eval z * Q.denom.eval z
  rw [div_mul_cancel₀ _ (denom_eval_ne_zero_of_regular (hQ z hz))]

/-- The coordinate derivation of `ℂ(z)` is the derivation `ratFuncDeriv`. -/
theorem ratFuncCoordinateDerivation_eq_ratFuncDeriv (Q : RatFunc ℂ) :
    ratFuncCoordinateDerivation ℂ Q = ratFuncDeriv Q := by
  have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr (RatFunc.denom_ne_zero Q)
  conv_lhs => rw [← RatFunc.num_div_denom Q]
  conv_rhs => rw [← RatFunc.num_div_denom Q]
  rw [ratFuncDeriv_div_general hden, ratFuncDeriv_algebraMap, ratFuncDeriv_algebraMap,
    Derivation.leibniz_div, ratFuncCoordinateDerivation_algebraMap,
    ratFuncCoordinateDerivation_algebraMap, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp

/-! ### Rational iterates -/

variable {R : RatFunc ℂ}

/-- The `n`-th iterate `R ∘ ⋯ ∘ R` of a rational map, as a rational function. -/
def ratFuncIterate (R : RatFunc ℂ) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (n : ℕ) : RatFunc ℂ :=
  (ratFuncSubstitutionAlgHom R hR)^[n] RatFunc.X

theorem ratFuncIterate_succ (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (n : ℕ) :
    ratFuncIterate R hR (n + 1) = ratFuncSubstitutionAlgHom R hR (ratFuncIterate R hR n) :=
  Function.iterate_succ_apply' _ _ _

/-- On a pole-free forward-invariant domain the rational iterates are regular and evaluate to the
iterates of the map. -/
theorem ratFuncIterate_regular (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hreg : ∀ z ∈ D, 0 ≤ ratOrder R z) (hmaps : MapsTo (fun z => ratValue R z) D D) (n : ℕ) :
    ∀ z ∈ D, 0 ≤ ratOrder (ratFuncIterate R hR n) z ∧
      ratValue (ratFuncIterate R hR n) z = (fun w => ratValue R w)^[n] z := by
  induction n with
  | zero =>
      intro z _
      refine ⟨ratOrder_nonneg_of_denom_eval ?_, ?_⟩
      · rw [ratFuncIterate, Function.iterate_zero_apply, RatFunc.denom_X]
        simp
      rw [ratFuncIterate, Function.iterate_zero_apply, Function.iterate_zero_apply, ratValue_X]
  | succ n ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := ratValue_ratFuncSubstitution hR (hreg z hz)
        (f := ratFuncIterate R hR n) (ih _ (hmaps hz)).1
      rw [ratFuncIterate_succ]
      refine ⟨h1, ?_⟩
      rw [h2, (ih _ (hmaps hz)).2, Function.iterate_succ_apply]

/-- **A jet relation of the iterates on `D` is a relation of rational functions.** -/
theorem ratFunc_relation_of_iterates (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hDne : D.Nonempty) (hreg : ∀ z ∈ D, 0 ≤ ratOrder R z)
    (hmaps : MapsTo (fun z => ratValue R z) D D) {r n : ℕ} {Q : MvPolynomial (Fin (r + 1)) ℂ}
    (hrel : ∀ z ∈ D, MvPolynomial.eval
      (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) ((fun w => ratValue R w)^[n]) z) Q = 0) :
    MvPolynomial.aeval
      (fun k : Fin (r + 1) => ratFuncDeriv^[(k : ℕ)] (ratFuncIterate R hR n)) Q = 0 := by
  obtain ⟨t₀, ht₀⟩ := hDne
  have hDinf : D.Infinite := infinite_of_mem_nhds t₀ (hDo.mem_nhds ht₀)
  letI := Bottcher.isDomain_analyticSubring D hDo hDc ⟨t₀, ht₀⟩
  letI : Algebra ℂ (meroField D) :=
    ((ratfuncToMero D hDo hDc ⟨t₀, ht₀⟩ hDinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  letI := meroFieldDifferential hDo hDc ⟨t₀, ht₀⟩
  set ρ := ratfuncToMero D hDo hDc ⟨t₀, ht₀⟩ hDinf with hρ
  set g : ℂ → ℂ := fun w => ratValue R w with hg
  have hgn : AnalyticOnNhd ℂ (g^[n]) D :=
    analyticOnNhd_iterate (analyticOnNhd_ratValue hreg) hmaps n
  have hzero := (aeval_analyticMeroElement_eq_zero_iff hDo hDc ⟨t₀, ht₀⟩ hDinf
    (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (g^[n]))
    (fun k => analyticOnNhd_iteratedDeriv hgn (k : ℕ)) Q).mpr hrel
  -- the iterate is the meromorphic function it defines
  have hiter : analyticMeroElement (g^[n]) hgn = ρ (ratFuncIterate R hR n) := by
    have hreg' := ratFuncIterate_regular hR hreg hmaps n
    rw [hρ, ratfuncToMero_eq_analyticMeroElement hDo hDc ⟨t₀, ht₀⟩ hDinf fun z hz => (hreg' z hz).1]
    exact analyticMeroElement_congr_eqOn _ _ fun z hz => ((hreg' z hz).2).symm
  have hderiv : ∀ (j : ℕ) (x : RatFunc ℂ), (⇑(Differential.deriv (R := meroField D)))^[j] (ρ x)
      = ρ (ratFuncDeriv^[j] x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', hρ]
        show (ratfuncToMero D hDo hDc ⟨t₀, ht₀⟩ hDinf (ratFuncDeriv^[j] x))′ = _
        rw [meroField_deriv_ratfuncToMero_on, ratFuncCoordinateDerivation_eq_ratFuncDeriv]
  have hjets : (fun k : Fin (r + 1) => analyticMeroElement (iteratedDeriv (k : ℕ) (g^[n]))
      (analyticOnNhd_iteratedDeriv hgn (k : ℕ)))
      = fun k : Fin (r + 1) => ρ (ratFuncDeriv^[(k : ℕ)] (ratFuncIterate R hR n)) := by
    funext k
    rw [← hderiv, ← hiter]
    exact (differentialJet_analyticMeroElement hDo hDc ⟨t₀, ht₀⟩ _ hgn k).symm
  set φ : RatFunc ℂ →ₐ[ℂ] meroField D := { ρ with commutes' := fun _ => rfl } with hφ
  rw [hjets] at hzero
  have h2 : φ (MvPolynomial.aeval
      (fun k : Fin (r + 1) => ratFuncDeriv^[(k : ℕ)] (ratFuncIterate R hR n)) Q) = 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    exact hzero
  exact (map_eq_zero_iff φ φ.toRingHom.injective).mp h2

/-! ### Expansion at the parabolic point -/

variable {k : ℕ} {a : ℂ} {w : ℂ⟦X⟧}

theorem ratExpandZero_ratFuncIterate (hk : 1 ≤ k) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) (n : ℕ) :
    ratExpandZero (ratFuncIterate R hR n)
      = algebraMap ℂ⟦X⟧ FormalLaurent ((parSubst k a w)^[n] X) := by
  induction n with
  | zero =>
      rw [ratFuncIterate, Function.iterate_zero_apply, Function.iterate_zero_apply,
        ← RatFunc.algebraMap_X, ratExpandZero_algebraMap, Polynomial.coe_X]
  | succ n ih =>
      rw [ratFuncIterate_succ, ← laurentSubst_ratExpandZero hk hR hRr, ih,
        laurentSubst_algebraMap hk, Function.iterate_succ_apply']

theorem ratExpandZero_iterate_ratFuncDeriv (Q : RatFunc ℂ) (j : ℕ) :
    ratExpandZero (ratFuncDeriv^[j] Q) = (⇑laurentDeriv)^[j] (ratExpandZero Q) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        laurentDeriv_ratExpandZero]

theorem laurentDeriv_iterate_algebraMap (f : ℂ⟦X⟧) (j : ℕ) :
    (⇑laurentDeriv)^[j] (algebraMap ℂ⟦X⟧ FormalLaurent f)
      = algebraMap ℂ⟦X⟧ FormalLaurent ((⇑(d⁄dX ℂ))^[j] f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        laurentDeriv_algebraMap]

/-- **A relation of rational iterates is a relation of formal iterates at the parabolic point.** -/
theorem formal_relation_of_ratFunc_relation (hk : 1 ≤ k) (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hRr : ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w)) {r n : ℕ}
    {Q : MvPolynomial (Fin (r + 1)) ℂ}
    (h : MvPolynomial.aeval
      (fun i : Fin (r + 1) => ratFuncDeriv^[(i : ℕ)] (ratFuncIterate R hR n)) Q = 0) :
    MvPolynomial.aeval
      (fun i : Fin (r + 1) => (⇑(d⁄dX ℂ))^[(i : ℕ)] ((parSubst k a w)^[n] X)) Q = 0 := by
  apply IsFractionRing.injective ℂ⟦X⟧ FormalLaurent
  rw [map_zero, ← map_zero ratExpandZero, ← h, MvPolynomial.aeval_def, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_eq_C, ratExpandZero_C,
      PowerSeries.algebraMap_apply]
    rfl
  · funext i
    rw [Function.comp_apply, Function.comp_apply, ratExpandZero_iterate_ratFuncDeriv,
      ratExpandZero_ratFuncIterate hk hR hRr, laurentDeriv_iterate_algebraMap]

/-- A rational function regular at `0` expands as a power series with its value as constant term. -/
theorem exists_expansion_of_regular {Q : RatFunc ℂ} (hQ : 0 ≤ ratOrder Q 0) :
    ∃ f : ℂ⟦X⟧, ratExpandZero Q = algebraMap ℂ⟦X⟧ FormalLaurent f ∧
      constantCoeff f = ratValue Q 0 := by
  have hd0 := denom_eval_ne_zero_of_regular hQ
  set den : ℂ⟦X⟧ := (Q.denom : ℂ⟦X⟧) with hdendef
  have hc : constantCoeff den = Q.denom.eval 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hdendef, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero]
  refine ⟨(Q.num : ℂ⟦X⟧) * den⁻¹, ?_, ?_⟩
  · conv_lhs => rw [← RatFunc.num_div_denom Q]
    rw [map_div₀, ratExpandZero_algebraMap, ratExpandZero_algebraMap, map_mul, div_eq_mul_inv]
    congr 1
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← map_mul, PowerSeries.mul_inv_cancel _ (by rw [hc]; exact hd0), map_one]
  · rw [map_mul, constantCoeff_inv, hc, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, ratValue, div_eq_mul_inv]

/-- **The normal form of a parabolic germ**: a rational map with `R(0) = 0`, `R'(0) = 1`, other
than the identity, expands at `0` as `X(1 + aX^k + X^{k+1}w)` with `k ≥ 1` and `a ≠ 0`. -/
theorem exists_parGerm_of_parabolic (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hR1 : ratValue (ratFuncDeriv R) 0 = 1) (hRX : R ≠ RatFunc.X) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ a : ℂ, a ≠ 0 ∧ ∃ w : ℂ⟦X⟧,
      ratExpandZero R = algebraMap ℂ⟦X⟧ FormalLaurent (parGerm k a w) := by
  set ι := algebraMap ℂ⟦X⟧ FormalLaurent with hι
  have hιinj : Function.Injective ι := IsFractionRing.injective ℂ⟦X⟧ FormalLaurent
  have h0' : 0 ≤ ratOrder (ratFuncDeriv R) 0 := ratOrder_nonneg_of_denom_eval fun h => by
    rw [ratValue, h, div_zero] at hR1
    exact zero_ne_one hR1
  obtain ⟨f, hf, hf0⟩ := exists_expansion_of_regular h0
  obtain ⟨g, hg, hg0⟩ := exists_expansion_of_regular h0'
  have hdf : d⁄dX ℂ f = g := hιinj (by
    rw [← laurentDeriv_algebraMap, ← hf, laurentDeriv_ratExpandZero, hg])
  have hf1 : coeff 1 f = 1 := by
    have := congrArg (coeff 0) hdf
    rw [coeff_derivative, coeff_zero_eq_constantCoeff_apply, hg0, hR1] at this
    simpa using this
  set h := f - X with hh
  have hh0 : h ≠ 0 := by
    intro h0
    apply hRX
    apply ratExpandZero.injective
    rw [hf, sub_eq_zero.mp h0, ← RatFunc.algebraMap_X, ratExpandZero_algebraMap, Polynomial.coe_X]
  have hc0 : coeff 0 h = 0 := by
    rw [hh, map_sub, coeff_zero_eq_constantCoeff_apply, hf0, hR0, coeff_zero_X, sub_zero]
  have hc1 : coeff 1 h = 0 := by
    rw [hh, map_sub, hf1, coeff_one_X, sub_self]
  set N := h.order.toNat with hN
  have hcN : coeff N h ≠ 0 := by
    rw [← constantCoeff_divXPowOrder]
    exact (constantCoeff_divXPowOrder_eq_zero_iff.not).mpr hh0
  have hN2 : 2 ≤ N := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · interval_cases N
      · exact absurd hc0 hcN
      · exact absurd hc1 hcN
    · exact hge
  set q := divXPowOrder h with hq
  refine ⟨N - 1, by omega, constantCoeff q, ?_, mk fun j => coeff (j + 1) q, ?_⟩
  · rw [hq, constantCoeff_divXPowOrder]
    exact hcN
  · rw [hf]
    congr 1
    have hqX := eq_X_mul_shift_add_const q
    have hfeq : f = X + X ^ N * q := by
      rw [hq, hN, X_pow_order_mul_divXPowOrder, hh, add_sub_cancel]
    rw [hfeq, parGerm, parUnit]
    conv_lhs => rw [hqX]
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 + 1 := ⟨N - 2, by omega⟩
    rw [hM, show M + 1 + 1 - 1 = M + 1 by omega]
    ring

/-! ### Ritt's implication for Abel functions -/

/-- **Ritt's implication for Abel functions at a parabolic fixed point.**  If `R` has degree at
least two and a parabolic fixed point at `0`, and a nonconstant analytic `A` with `A ∘ R = A + 1`
on a pole-free forward-invariant open connected `D` satisfies an algebraic differential equation
on `D`, then `R` carries a rational cocycle `B(R)·R'^N = β·B`. -/
theorem ratTransport_of_differentiallyAlgebraicOn_abel (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0)
    (hR1 : ratValue (ratFuncDeriv R) 0 = 1) (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hreg : ∀ z ∈ D, 0 ≤ ratOrder R z) (hmaps : MapsTo (fun z => ratValue R z) D D)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A D) (habel : ∀ t ∈ D, A (ratValue R t) = A t + 1)
    {t₀ : ℂ} (ht₀ : t₀ ∈ D) (hA' : deriv A t₀ ≠ 0) (hDA : DifferentiallyAlgebraicOn A D) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : ℂ, β ≠ 0 ∧ ∃ B : RatFunc ℂ, B ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 B := by
  have hRX : R ≠ RatFunc.X := by
    rintro rfl
    rw [ratFuncDegree_X] at hd
    omega
  obtain ⟨k, hk, a, ha, w, hRr⟩ := exists_parGerm_of_parabolic h0 hR0 hR1 hRX
  obtain ⟨r, Q, hQ0, hQ⟩ := exists_uniform_jet_relation_of_abel hDo hDc
    (analyticOnNhd_ratValue hreg) hmaps hA habel ht₀ hA' hDA
  have hT : MvPolynomial.rename Fin.succ Q ≠ 0 := fun h =>
    hQ0 (MvPolynomial.rename_injective _ (Fin.succ_injective _) (by rw [h, map_zero]))
  refine ratTransport_of_iterate_relation hk ha hR hd hRr hT Set.infinite_univ fun m _ => ?_
  rw [MvPolynomial.aeval_rename]
  exact formal_relation_of_ratFunc_relation hk hR hRr
    (ratFunc_relation_of_iterates hR hDo hDc ⟨t₀, ht₀⟩ hreg hmaps (hQ m))

/-! ### Interior tree channels at the parabolic parameter -/

variable {p : ℕ}

/-- **Abel functions of an interior tree channel at the parabolic parameter are
hypertranscendental.**  For `−1 < v < u < 1`, `p ≥ 2` and `p(u − v)/2 = 1`, let `D` be an open
connected set on which the tree channel map `R(y) = ((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)`
has no poles and which it maps into itself.  A nonconstant analytic `A` with `A(R(y)) = A(y) + 1`
on `D` satisfies no algebraic differential equation on any nonempty open subset of `D`, and neither
does its velocity field `1/A'` on any open subset where `A' ≠ 0`. -/
theorem treeRG_parabolic_abel_hypertranscendental (hp : 2 ≤ p) {u v : ℝ} (hv : -1 < v)
    (huv : v < u) (hu : u < 1) (hpar : (p : ℝ) * (u - v) / 2 = 1) (hDo : IsOpen D)
    (hDc : IsPreconnected D) (hden : ∀ y ∈ D, (1 + u * y) ^ p + (1 + v * y) ^ p ≠ 0)
    (hmaps : MapsTo (fun y : ℂ => ((1 + u * y) ^ p - (1 + v * y) ^ p)
      / ((1 + u * y) ^ p + (1 + v * y) ^ p)) D D)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A D)
    (habel : ∀ y ∈ D, A (((1 + u * y) ^ p - (1 + v * y) ^ p)
      / ((1 + u * y) ^ p + (1 + v * y) ^ p)) = A y + 1)
    (hAnc : ∃ t₀ ∈ D, deriv A t₀ ≠ 0) :
    (∀ W ⊆ D, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn A W) ∧
      (∀ W ⊆ D, IsOpen W → W.Nonempty → (∀ y ∈ W, deriv A y ≠ 0) →
        ¬ DifferentiallyAlgebraicOn (fun y => (deriv A y)⁻¹) W) := by
  obtain ⟨t₀, ht₀, hA'⟩ := hAnc
  set R := treeRG p (u : ℂ) (v : ℂ) with hRdef
  have hR := treeRG_not_const hp huv
  have hd : 2 ≤ ratFuncDegree R := by
    rw [hRdef, ratFuncDegree_treeRG (by omega) (by exact_mod_cast huv.ne')]
    exact hp
  have hR1 : ratValue (ratFuncDeriv R) 0 = 1 := by
    rw [hRdef, treeRG_multiplier]
    exact_mod_cast hpar
  have hdenD : ∀ y ∈ D, (treeDen p (u : ℂ) (v : ℂ)).eval y ≠ 0 := by
    intro y hy
    simpa [treeDen] using hden y hy
  have hvalD : ∀ y ∈ D, ratValue R y = ((1 + u * y) ^ p - (1 + v * y) ^ p)
      / ((1 + u * y) ^ p + (1 + v * y) ^ p) := by
    intro y hy
    rw [hRdef, treeRG, ratValue_div_algebraMap (hdenD y hy)]
    simp [treeNum, treeDen]
  have hreg : ∀ y ∈ D, 0 ≤ ratOrder R y := by
    intro y hy
    refine ratOrder_nonneg_of_denom_eval fun h0 => hdenD y hy ?_
    obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd (treeNum p (u : ℂ) (v : ℂ)) (treeDen p (u : ℂ) (v : ℂ))
    rw [hc, Polynomial.eval_mul]
    rw [hRdef, treeRG] at h0
    rw [h0, zero_mul]
  have hmaps' : MapsTo (fun z => ratValue R z) D D := fun y hy => by
    show ratValue R y ∈ D
    rw [hvalD y hy]
    exact hmaps hy
  have habel' : ∀ t ∈ D, A (ratValue R t) = A t + 1 := fun t ht => by
    rw [hvalD t ht]
    exact habel t ht
  have hnotD : ¬ DifferentiallyAlgebraicOn A D := fun hDA => by
    obtain ⟨N, hN, β, hβ, B, hB, htr⟩ := ratTransport_of_differentiallyAlgebraicOn_abel hR hd
      treeRG_regular_zero treeRG_value_zero hR1 hDo hDc hreg hmaps' hA habel' ht₀ hA' hDA
    exact treeRG_no_cocycle_interior hp hv huv hu (by exact_mod_cast hN.ne') hβ hB htr
  have hnotW : ∀ W ⊆ D, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn A W :=
    fun W hWD hWo hWne hDA =>
      hnotD (differentiallyAlgebraicOn_mono_of_isPreconnected hDc hA hWo hWne hWD hDA)
  refine ⟨hnotW, fun W hWD hWo hWne hA'W hβ => ?_⟩
  have hA'an : AnalyticOnNhd ℂ (fun y => (deriv A y)⁻¹) W := fun y hy =>
    (hA.deriv y (hWD hy)).inv (hA'W y hy)
  have hinv := differentiallyAlgebraicOn_inv hWo hA'an (fun y hy => inv_ne_zero (hA'W y hy)) hβ
  have hderiv : DifferentiallyAlgebraicOn (deriv A) W :=
    differentiallyAlgebraicOn_of_eqOn hWo (fun y _ => inv_inv (deriv A y)) hinv
  exact hnotW W hWD hWo hWne (differentiallyAlgebraicOn_of_deriv hderiv)

end

end GaloisForLFunctions.HTGeometry
