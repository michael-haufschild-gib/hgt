import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.PolynomialDriftExpansion
import GaloisForLFunctions.HTGeometry.AlgebraicOverStateFieldOrder
import GaloisForLFunctions.HTGeometry.FiniteOrderPolynomialDescent
import GaloisForLFunctions.RHTower.FiniteZeroHadamardProduct

/-!
# Polynomial-drift rational-outer-factor rigidity

A finite-order entire function `W` with a nonzero polynomial affine-symmetry drift

`W(σ z) - W(z) = Q(z)`,  `σ(z) = α z + b`,  `α ≠ 0`,  `Q ≠ 0`,

admits no genuinely order-two inner factor: if `W = P ∘ g` for an entire `g` and a polynomial `P`
of degree at least two, then `g` is differentially algebraic of order at most one.

## The mechanism

Put `A(z) = g(σ z) - g(z)`.  The drift relation reads `P(g + A) - P(g) = Q`, so every zero of `A`
is a zero of `Q`; since `Q ≠ 0`, the drift `A` is a nonzero entire function with finitely many
zeros, and it inherits `W`'s finite order through
`finiteOrderEnvelope_of_comp_polynomial`.  The finite-order Hadamard product
(`RHTower.exists_polynomial_mul_expPolynomial_of_envelope`) therefore writes

`A = p₁ · exp S`

with `p₁, S` polynomials.  The single hyperexponential generator `E = exp ∘ S` satisfies
`E′ = S′ E`, so the state field `ℂ(z)(E)` is closed under the derivation up to algebraicity, and
the drift expansion of `P` (`eval_driftCoeff_expansion`) exhibits `g` as a root of a polynomial of
degree `deg P - 1` over that field whose top coefficient `deg P · lead P · A` is nonzero.  One
state means transcendence degree one, so the two jets `g, g′` are algebraically dependent over
`ℂ(z)`: an order-one algebraic differential equation.

## Main results

* `aeval_analyticMeroElement_univ` — polynomial composition transfers to the meromorphic field;
* `drift_finite_zeroSet`, `finiteOrderEnvelope_drift` — the analytic input to Hadamard;
* `exists_state_algebraic_of_polynomial_drift` — the single hyperexponential state;
* `polynomial_drift_rigidity` — the card's theorem;
* `rational_outer_factor_rigidity` — the rational outer-function case.
-/

open Set Complex Filter
open scoped Differential
open scoped UnivMeroFieldInstances

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Bottcher GaloisForLFunctions

/-! ### Transporting polynomial identities to the meromorphic field -/

/-- The scalar embedding of the meromorphic field is the constant germ map. -/
theorem algebraMap_complex_meroField_univ (c : ℂ) :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = constToMero (Set.univ : Set ℂ) c := rfl

theorem analyticOnNhd_polyGerm (r : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => r.eval z) (Set.univ : Set ℂ) :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (Polynomial.differentiable r)

theorem analyticOnNhd_polyComp {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
    (P : Polynomial ℂ) : AnalyticOnNhd ℂ (fun z => P.eval (h z)) (Set.univ : Set ℂ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun : (fun z => (p + q).eval (h z))
          = fun z => p.eval (h z) + q.eval (h z) := by
        funext z; rw [Polynomial.eval_add]
      rw [hfun]; exact hp.add hq
  | monomial k c =>
      have hfun : (fun z => (Polynomial.monomial k c).eval (h z))
          = fun z => c * h z ^ k := by
        funext z; rw [Polynomial.eval_monomial]
      rw [hfun]
      exact analyticOnNhd_const.mul (hh.pow k)

/-- **Polynomial composition transfers to the field.** -/
theorem aeval_analyticMeroElement_univ {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
    (P : Polynomial ℂ) :
    Polynomial.aeval (analyticMeroElement h hh) P
      = analyticMeroElement (fun z => P.eval (h z)) (analyticOnNhd_polyComp hh P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq,
        ← analyticMeroElement_add (analyticOnNhd_polyComp hh p) (analyticOnNhd_polyComp hh q)]
      refine analyticMeroElement_congr _ _ ?_
      funext z; rw [Polynomial.eval_add]
  | monomial k c =>
      have hgk : AnalyticOnNhd ℂ (fun z => h z ^ k) (Set.univ : Set ℂ) :=
        fun z hz => (hh z hz).pow k
      rw [Polynomial.aeval_monomial, algebraMap_complex_meroField_univ,
        ← analyticMeroElement_const (Set.univ : Set ℂ) c,
        ← analyticMeroElement_pow hh k,
        ← analyticMeroElement_mul analyticOnNhd_const hgk]
      refine analyticMeroElement_congr _ _ ?_
      funext z; rw [Polynomial.eval_monomial]

/-- A polynomial germ is the image of the polynomial under the rational coordinate embedding. -/
theorem analyticMeroElement_polyGerm (r : Polynomial ℂ) :
    analyticMeroElement (fun z : ℂ => r.eval z) (analyticOnNhd_polyGerm r)
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) r) := by
  show _ = ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap (Polynomial ℂ) (RatFunc ℂ) r)
  rw [ratfuncToMero_algebraMap_polynomial, polyToMero, RingHom.comp_apply, analyticMeroElement]
  congr 1

/-! ### The analytic input -/

/-- The affine drift of an entire function. -/
def affineDrift (g : ℂ → ℂ) (α b : ℂ) : ℂ → ℂ := fun z => g (α * z + b) - g z

theorem differentiable_affineDrift {g : ℂ → ℂ} (hg : Differentiable ℂ g) (α b : ℂ) :
    Differentiable ℂ (affineDrift g α b) :=
  (hg.comp ((differentiable_id.const_mul α).add_const b)).sub hg

/-- The drift relation transported to the inner factor. -/
theorem drift_inner_relation {W g : ℂ → ℂ} {α b : ℂ} {P Q : Polynomial ℂ}
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z) (hcomp : ∀ z, W z = P.eval (g z)) (z : ℂ) :
    P.eval (g z + affineDrift g α b z) - P.eval (g z) = Q.eval z := by
  have h1 : g z + affineDrift g α b z = g (α * z + b) := by rw [affineDrift]; ring
  rw [h1, ← hcomp, ← hcomp]
  exact hdrift z

/-- **The drift has only finitely many zeros.**  Every zero of the drift is a zero of the
polynomial drift value. -/
theorem drift_finite_zeroSet {W g : ℂ → ℂ} {α b : ℂ} {P Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z) (hcomp : ∀ z, W z = P.eval (g z)) :
    {z : ℂ | affineDrift g α b z = 0}.Finite := by
  classical
  refine Set.Finite.subset (Q.roots.toFinset : Finset ℂ).finite_toSet (fun z hz => ?_)
  simp only [Set.mem_setOf_eq] at hz
  have hrel := drift_inner_relation hdrift hcomp z
  rw [hz, add_zero, sub_self] at hrel
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots']
  exact ⟨hQ, hrel.symm⟩

/-- The drift is not identically zero. -/
theorem drift_ne_zero {W g : ℂ → ℂ} {α b : ℂ} {P Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z) (hcomp : ∀ z, W z = P.eval (g z)) :
    ∃ z, affineDrift g α b z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hQ (Polynomial.funext (fun z => ?_))
  have hrel := drift_inner_relation hdrift hcomp z
  rw [hcon z, add_zero, sub_self] at hrel
  rw [Polynomial.eval_zero, ← hrel]

/-- **The drift inherits the finite order.** -/
theorem finiteOrderEnvelope_drift {W g : ℂ → ℂ} {α b : ℂ} {P : Polynomial ℂ}
    (hP : 1 ≤ P.natDegree) (henv : FiniteOrderEnvelope W) (hcomp : ∀ z, W z = P.eval (g z)) :
    FiniteOrderEnvelope (affineDrift g α b) := by
  have hPg : FiniteOrderEnvelope (fun z => P.eval (g z)) := by
    obtain ⟨C, d, hC, hb⟩ := henv
    refine ⟨C, d, hC, fun z => ?_⟩
    have hz : ‖P.eval (g z)‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d) := by
      rw [← hcomp z]; exact hb z
    exact hz
  have hgenv : FiniteOrderEnvelope g := finiteOrderEnvelope_of_comp_polynomial hP hPg
  obtain ⟨C, d, hC, hb⟩ := (hgenv.compAffine α b).sub hgenv
  exact ⟨C, d, hC, fun z => hb z⟩

/-! ### The state field of a polynomial drift -/

/-- **One hyperexponential state controls the inner factor.**  Under the polynomial-drift
hypotheses there is a single state `E = exp S` whose derivative stays algebraic over `ℂ(z)(E)` and
over which the inner factor `g` is algebraic. -/
theorem exists_state_algebraic_of_polynomial_drift
    {W g : ℂ → ℂ} {α b : ℂ} {P Q : Polynomial ℂ}
    (hg : Differentiable ℂ g) (henv : FiniteOrderEnvelope W)
    (hQ : Q ≠ 0) (hP : 2 ≤ P.natDegree)
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z)
    (hcomp : ∀ z, W z = P.eval (g z))
    (hgan : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) :
    ∃ st : Fin 1 → meroField (Set.univ : Set ℂ),
      (∀ y ∈ Set.range st, y′ ∈ algebraicClosure
          ((IntermediateField.adjoin (RatFunc ℂ) (Set.range st) :
            IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) : Type)
          (meroField (Set.univ : Set ℂ))) ∧
      analyticMeroElement g hgan ∈ algebraicClosure
          ((IntermediateField.adjoin (RatFunc ℂ) (Set.range st) :
            IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) : Type)
          (meroField (Set.univ : Set ℂ)) := by
  classical
  set L : Type := meroField (Set.univ : Set ℂ) with hL
  set A : ℂ → ℂ := affineDrift g α b with hAdef
  have hAdiff : Differentiable ℂ A := differentiable_affineDrift hg α b
  have hAan : AnalyticOnNhd ℂ A Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hAdiff
  have hrel : ∀ z, P.eval (g z + A z) - P.eval (g z) = Q.eval z :=
    fun z => drift_inner_relation hdrift hcomp z
  -- Hadamard normal form for the drift
  obtain ⟨p₁, S, hp₁ne, hAform⟩ :=
    RHTower.exists_polynomial_mul_expPolynomial_of_envelope hAdiff
      (finiteOrderEnvelope_drift (by omega) henv hcomp)
      (drift_finite_zeroSet hQ hdrift hcomp)
  -- the hyperexponential generator
  have hSan : AnalyticOnNhd ℂ (fun z : ℂ => S.eval z) Set.univ := analyticOnNhd_polyGerm S
  set Em : L := analyticMeroElement (fun z => Complex.exp (S.eval z)) hSan.cexp with hEm
  set st : Fin 1 → L := ![Em] with hst
  set M : IntermediateField (RatFunc ℂ) L :=
    IntermediateField.adjoin (RatFunc ℂ) (Set.range st) with hM
  have hEmM : Em ∈ M := by
    refine IntermediateField.subset_adjoin _ _ ⟨0, ?_⟩
    rw [hst]
    rfl
  have hMclosure : ∀ w : L, w ∈ M → w ∈ algebraicClosure ((M : Type)) L := by
    intro w hw
    have := mem_algebraicClosure_restrictScalars_of_mem M hw
    rwa [IntermediateField.mem_restrictScalars] at this
  -- the generator's derivative stays in the state field
  have hSderiv : (analyticMeroElement (fun z : ℂ => S.eval z) hSan)′ ∈ M := by
    rw [deriv_analyticMeroElement]
    have hfun : deriv (fun z : ℂ => S.eval z)
        = fun z : ℂ => (Polynomial.derivative S).eval z := by
      funext z; exact Polynomial.deriv S
    rw [analyticMeroElement_congr _ (analyticOnNhd_polyGerm (Polynomial.derivative S)) hfun,
      analyticMeroElement_polyGerm]
    exact IntermediateField.algebraMap_mem _ _
  have hgen : ∀ y ∈ Set.range st, y′ ∈ algebraicClosure ((M : Type)) L := by
    rintro y ⟨i, rfl⟩
    have hy : st i = Em := by
      rw [hst]
      fin_cases i
      rfl
    rw [hy, hEm, deriv_analyticMeroElement_exp _ hSan]
    exact hMclosure _ (mul_mem hSderiv hEmM)
  -- the drift as a field element
  have hp₁an : AnalyticOnNhd ℂ (fun z : ℂ => p₁.eval z) Set.univ := analyticOnNhd_polyGerm p₁
  set Am : L := analyticMeroElement A hAan with hAm
  have hAmM : Am ∈ M := by
    have hAeq : A = fun z => p₁.eval z * Complex.exp (S.eval z) := funext hAform
    rw [hAm, analyticMeroElement_congr hAan (hp₁an.mul hSan.cexp) hAeq,
      analyticMeroElement_mul hp₁an hSan.cexp, analyticMeroElement_polyGerm]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) hEmM
  have hAmne : Am ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := drift_ne_zero hQ hdrift hcomp
    rw [hAm, Ne, analyticMeroElement_eq_zero_iff]
    intro hall
    exact hz₀ (hall z₀ (Set.mem_univ z₀))
  -- the transported relation
  set x : L := analyticMeroElement g hgan with hx
  set qm : L := analyticMeroElement (fun z : ℂ => Q.eval z) (analyticOnNhd_polyGerm Q) with hqm
  have hqmM : qm ∈ M := by
    rw [hqm, analyticMeroElement_polyGerm]
    exact IntermediateField.algebraMap_mem _ _
  have hgA : AnalyticOnNhd ℂ (fun z => g z + A z) Set.univ := hgan.add hAan
  have hxA : x + Am = analyticMeroElement (fun z => g z + A z) hgA := by
    rw [hx, hAm]
    exact (analyticMeroElement_add hgan hAan).symm
  have hfield : Polynomial.aeval (x + Am) P - Polynomial.aeval x P = qm := by
    rw [hxA, hx, aeval_analyticMeroElement_univ hgA P, aeval_analyticMeroElement_univ hgan P,
      ← analyticMeroElement_sub (analyticOnNhd_polyComp hgA P)
        (analyticOnNhd_polyComp hgan P), hqm]
    refine analyticMeroElement_congr _ _ ?_
    funext z
    exact hrel z
  -- rewrite as a polynomial relation over the state field
  set PL : Polynomial L := P.map (algebraMap ℂ L) with hPL
  have hPLdeg : PL.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℂ L).injective P
  have hPLeval : ∀ y : L, PL.eval y = Polynomial.aeval y P := by
    intro y
    rw [hPL, Polynomial.eval_map, Polynomial.aeval_def]
  have hexpand : ∑ c ∈ Finset.range P.natDegree, ((driftCoeff PL c).eval Am) * x ^ c = qm := by
    rw [← hPLdeg, ← eval_driftCoeff_expansion PL x Am, hPLeval, hPLeval]
    exact hfield
  -- the coefficient family
  set Ac : ℕ → L := fun c => (driftCoeff PL c).eval Am - (if c = 0 then qm else 0) with hAc
  have hAcmem : ∀ c, Ac c ∈ algebraicClosure ((M : Type)) L := by
    intro c
    refine hMclosure _ (sub_mem ?_ ?_)
    · rw [driftCoeff, Polynomial.eval_finsetSum]
      refine sum_mem (fun k _ => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      refine mul_mem (mul_mem ?_ ?_) (pow_mem hAmM _)
      · rw [hPL, Polynomial.coeff_map, algebraMap_complex_meroField_univ]
        exact constToMero_mem M _
      · exact natCast_mem M _
    · by_cases hc : c = 0
      · rw [if_pos hc]; exact hqmM
      · rw [if_neg hc]; exact zero_mem _
  have hAcTop : Ac (P.natDegree - 1) ≠ 0 := by
    have hne0 : P.natDegree - 1 ≠ 0 := by omega
    rw [hAc]
    simp only [if_neg hne0, sub_zero]
    rw [← hPLdeg, eval_driftCoeff_pred PL (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hAmne
    · exact Nat.cast_ne_zero.mpr (by rw [hPLdeg]; omega)
    · rw [hPL, Polynomial.coeff_map]
      refine (map_ne_zero_iff _ (algebraMap ℂ L).injective).mpr ?_
      rw [hPLdeg, ← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr (fun hz => by simp [hz] at hP)
  have hrelsum : ∑ c ∈ Finset.range (P.natDegree - 1 + 1), Ac c * x ^ c = 0 := by
    have hn : P.natDegree - 1 + 1 = P.natDegree := by omega
    rw [hn, hAc]
    have hsplit : ∀ c ∈ Finset.range P.natDegree,
        ((driftCoeff PL c).eval Am - (if c = 0 then qm else 0)) * x ^ c
          = (driftCoeff PL c).eval Am * x ^ c - (if c = 0 then qm else 0) * x ^ c :=
      fun c _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hexpand]
    have hsecond : ∑ c ∈ Finset.range P.natDegree, (if c = 0 then qm else 0) * x ^ c = qm := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro c _ hc
        rw [if_neg hc, zero_mul]
      · intro h0
        exact absurd (Finset.mem_range.mpr (by omega)) h0
    rw [hsecond, sub_self]
  have hxclosure : x ∈ algebraicClosure ((M : Type)) L :=
    mem_algebraicClosure_of_root hAcmem hAcTop hrelsum
  exact ⟨st, hgen, hxclosure⟩

/-! ### The card theorem -/

set_option linter.unusedVariables false in
/-- **Polynomial-drift rational-outer-factor rigidity.**  A finite-order entire function with a
nonzero polynomial affine-symmetry drift has no order-two polynomial inner factor: every entire `g`
with `W = P ∘ g`, `deg P ≥ 2`, is differentially algebraic of order at most one.

The invertibility `α ≠ 0` of the affine symmetry is part of the card's hypotheses; the proof never
uses it, so the statement is in fact true for every affine drift map. -/
theorem polynomial_drift_rigidity
    {W g : ℂ → ℂ} {α b : ℂ} {P Q : Polynomial ℂ}
    (hg : Differentiable ℂ g) (henv : FiniteOrderEnvelope W)
    (hα : α ≠ 0) (hQ : Q ≠ 0) (hP : 2 ≤ P.natDegree)
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z)
    (hcomp : ∀ z, W z = P.eval (g z)) :
    DifferentiallyAlgebraicOfOrder g 1 := by
  have hgan : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  obtain ⟨st, hgen, hxclosure⟩ :=
    exists_state_algebraic_of_polynomial_drift hg henv hQ hP hdrift hcomp hgan
  exact differentiallyAlgebraicOfOrder_of_algebraic_over_states hgan st hgen hxclosure

/-! ### The rational outer factor -/

set_option linter.unusedVariables false in
/-- **Rational-outer-factor rigidity.**  A rational outer function with a single finite pole `a`
is a polynomial in `u = (g - a)⁻¹`.  If that polynomial composition carries the polynomial drift,
then `u` — and therefore `g = a + u⁻¹` — is differentially algebraic of order at most one. -/
theorem rational_outer_factor_rigidity
    {W g u : ℂ → ℂ} {α b a : ℂ} {P Q : Polynomial ℂ}
    (hg : Differentiable ℂ g) (hu : Differentiable ℂ u)
    (hinv : ∀ z, u z * (g z - a) = 1)
    (henv : FiniteOrderEnvelope W)
    (hα : α ≠ 0) (hQ : Q ≠ 0) (hP : 2 ≤ P.natDegree)
    (hdrift : ∀ z, W (α * z + b) - W z = Q.eval z)
    (hcomp : ∀ z, W z = P.eval (u z)) :
    DifferentiallyAlgebraicOfOrder g 1 := by
  classical
  have hgan : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have huan : AnalyticOnNhd ℂ u Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hu
  obtain ⟨st, hgen, huclosure⟩ :=
    exists_state_algebraic_of_polynomial_drift hu henv hQ hP hdrift hcomp huan
  set M : IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin (RatFunc ℂ) (Set.range st) with hM
  -- the Möbius relation in the field
  set Um : meroField (Set.univ : Set ℂ) := analyticMeroElement u huan with hUm
  set xm : meroField (Set.univ : Set ℂ) := analyticMeroElement g hgan with hxm
  set am : meroField (Set.univ : Set ℂ) :=
    analyticMeroElement (fun _ : ℂ => a) analyticOnNhd_const with ham
  have hsub : AnalyticOnNhd ℂ (fun z => g z - a) (Set.univ : Set ℂ) :=
    hgan.sub analyticOnNhd_const
  have hfield : Um * (xm - am) = 1 := by
    rw [hUm, hxm, ham, ← analyticMeroElement_sub hgan analyticOnNhd_const,
      ← analyticMeroElement_mul huan hsub]
    have hone : analyticMeroElement (fun _ : ℂ => (1 : ℂ)) analyticOnNhd_const
        = (1 : meroField (Set.univ : Set ℂ)) := by
      rw [analyticMeroElement_const]
      exact map_one _
    rw [← hone]
    refine analyticMeroElement_congr _ _ ?_
    funext z
    exact hinv z
  have hUmne : Um ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfield
    exact zero_ne_one hfield
  have hxeq : xm = am + Um⁻¹ := by
    have : xm - am = Um⁻¹ := by
      field_simp
      linear_combination hfield
    linear_combination this
  have hamMem : am ∈ algebraicClosure ((M : Type)) (meroField (Set.univ : Set ℂ)) := by
    have hmem : am ∈ M := by
      rw [ham, analyticMeroElement_const]
      exact constToMero_mem M a
    have := mem_algebraicClosure_restrictScalars_of_mem M hmem
    rwa [IntermediateField.mem_restrictScalars] at this
  have hxclosure : xm ∈ algebraicClosure ((M : Type)) (meroField (Set.univ : Set ℂ)) := by
    rw [hxeq]
    exact add_mem hamMem (inv_mem huclosure)
  exact differentiallyAlgebraicOfOrder_of_algebraic_over_states hgan st hgen hxclosure

end GaloisForLFunctions.HTGeometry
