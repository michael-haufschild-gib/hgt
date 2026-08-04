import GaloisForLFunctions.HTGeometry.CascadeRelationClearing

/-!
# Expressions in the cascade data

The functions reachable from the cascade states and the constituents' iterated derivatives *at those
states*, by sums and products.  Every derivative of every state lies in this class, so a differential
relation for the last state is a relation among these — and once each constituent's first-order
equation eliminates its derivative, a polynomial relation among the states themselves.

The class is defined inductively rather than as a `Subring.closure`, so that differentiability and
closure under `deriv` are both proved by the same structural induction.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Functions built from the cascade states and the constituents' iterated derivatives at those
states, by constants, sums and products. -/
inductive CascadeExpr (f : ℕ → ℂ → ℂ) (n : ℕ) : (ℂ → ℂ) → Prop
  | state (i : ℕ) (h : i ≤ n) : CascadeExpr f n (entireCascade f i)
  | constDeriv (i d : ℕ) (h : i ≤ n) :
      CascadeExpr f n (fun z => deriv^[d] (f i) (entireCascade f i z))
  | const (c : ℂ) : CascadeExpr f n (fun _ => c)
  | add {g h : ℂ → ℂ} : CascadeExpr f n g → CascadeExpr f n h →
      CascadeExpr f n (fun z => g z + h z)
  | mul {g h : ℂ → ℂ} : CascadeExpr f n g → CascadeExpr f n h →
      CascadeExpr f n (fun z => g z * h z)

variable {f : ℕ → ℂ → ℂ} {n : ℕ}

/-- Iterated derivatives of an entire function are entire. -/
theorem analyticOnNhd_iteratedDeriv {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) (d : ℕ) :
    AnalyticOnNhd ℂ (deriv^[d] g) Set.univ := by
  induction d generalizing g with
  | zero => simpa using hg
  | succ d ih =>
      have : deriv^[d + 1] g = deriv^[d] (deriv g) := by
        rw [Function.iterate_succ_apply]
      rw [this]
      exact ih hg.deriv

/-- **Every expression is entire.** -/
theorem differentiable_cascadeExpr (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {g : ℂ → ℂ} (hg : CascadeExpr f n g) : Differentiable ℂ g := by
  induction hg with
  | state i _ => exact differentiable_entireCascade hf i
  | constDeriv i d _ =>
      intro z
      have hcomp : AnalyticOnNhd ℂ (deriv^[d] (f i)) Set.univ :=
        analyticOnNhd_iteratedDeriv (hf i) d
      have hinner := (analyticOnNhd_entireCascade hf i) z (Set.mem_univ z)
      exact ((hcomp _ (Set.mem_univ _)).comp hinner).differentiableAt
  | const c => exact differentiable_const c
  | add _ _ ihg ihh => exact ihg.add ihh
  | mul _ _ ihg ihh => exact ihg.mul ihh

/-- **The derivative of a state is an expression.** -/
theorem cascadeExpr_deriv_state (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) :
    ∀ i : ℕ, i ≤ n → CascadeExpr f n (deriv (entireCascade f i)) := by
  intro i
  induction i with
  | zero =>
      intro _
      have hid : deriv (entireCascade f 0) = fun _ : ℂ => (1 : ℂ) := by
        funext z
        simp [entireCascade]
      rw [hid]
      exact CascadeExpr.const 1
  | succ i ih =>
      intro hi
      have hfun : deriv (entireCascade f (i + 1))
          = fun z => deriv^[1] (f i) (entireCascade f i z) * deriv (entireCascade f i) z := by
        funext z
        simpa using deriv_entireCascade_succ hf i z
      rw [hfun]
      exact CascadeExpr.mul (CascadeExpr.constDeriv i 1 (by omega)) (ih (by omega))

/-- **The class is closed under differentiation.**  The two generator cases are the chain rule; the
rest is Leibniz. -/
theorem cascadeExpr_deriv (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {g : ℂ → ℂ} (hg : CascadeExpr f n g) : CascadeExpr f n (deriv g) := by
  induction hg with
  | state i h => exact cascadeExpr_deriv_state hf i h
  | constDeriv i d h =>
      have hGan : AnalyticOnNhd ℂ (deriv^[d] (f i)) Set.univ :=
        analyticOnNhd_iteratedDeriv (hf i) d
      have hFan : AnalyticOnNhd ℂ (entireCascade f i) Set.univ :=
        analyticOnNhd_entireCascade hf i
      have hfun : deriv (fun z => deriv^[d] (f i) (entireCascade f i z))
          = fun z => deriv^[d + 1] (f i) (entireCascade f i z)
              * deriv (entireCascade f i) z := by
        funext z
        have hinner : HasDerivAt (entireCascade f i) (deriv (entireCascade f i) z) z :=
          (hFan z (Set.mem_univ z)).differentiableAt.hasDerivAt
        have houter : HasDerivAt (deriv^[d] (f i))
            (deriv (deriv^[d] (f i)) (entireCascade f i z)) (entireCascade f i z) :=
          (hGan _ (Set.mem_univ _)).differentiableAt.hasDerivAt
        have hcomp : HasDerivAt (fun w => deriv^[d] (f i) (entireCascade f i w))
            (deriv (deriv^[d] (f i)) (entireCascade f i z) * deriv (entireCascade f i) z) z :=
          houter.comp z hinner
        rw [hcomp.deriv]
        congr 1
        rw [Function.iterate_succ_apply']
      rw [hfun]
      exact CascadeExpr.mul (CascadeExpr.constDeriv i (d + 1) h)
        (cascadeExpr_deriv_state hf i h)
  | const c =>
      have hfun : deriv (fun _ : ℂ => c) = fun _ : ℂ => (0 : ℂ) := by
        funext z
        simp
      rw [hfun]
      exact CascadeExpr.const 0
  | @add g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      have hd₁ : Differentiable ℂ g₁ := differentiable_cascadeExpr hf hg₁
      have hd₂ : Differentiable ℂ g₂ := differentiable_cascadeExpr hf hg₂
      have hfun : deriv (fun z => g₁ z + g₂ z) = fun z => deriv g₁ z + deriv g₂ z := by
        funext z
        exact deriv_add (hd₁ z) (hd₂ z)
      rw [hfun]
      exact CascadeExpr.add ih₁ ih₂
  | @mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      have hd₁ : Differentiable ℂ g₁ := differentiable_cascadeExpr hf hg₁
      have hd₂ : Differentiable ℂ g₂ := differentiable_cascadeExpr hf hg₂
      have hfun : deriv (fun z => g₁ z * g₂ z)
          = fun z => deriv g₁ z * g₂ z + g₁ z * deriv g₂ z := by
        funext z
        exact deriv_mul (hd₁ z) (hd₂ z)
      rw [hfun]
      exact CascadeExpr.add (CascadeExpr.mul ih₁ hg₂) (CascadeExpr.mul hg₁ ih₂)

/-- **Every iterated derivative of a state is an expression.** -/
theorem cascadeExpr_iteratedDeriv_state (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {i : ℕ} (h : i ≤ n) (d : ℕ) :
    CascadeExpr f n (deriv^[d] (entireCascade f i)) := by
  induction d with
  | zero => simpa using CascadeExpr.state i h
  | succ d ih =>
      have hstep : deriv^[d + 1] (entireCascade f i)
          = deriv (deriv^[d] (entireCascade f i)) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact cascadeExpr_deriv hf ih

/-! ## Polynomials of the states, and the constituents' equations -/

/-- Powers of expressions are expressions. -/
theorem cascadeExpr_pow {g : ℂ → ℂ} (hg : CascadeExpr f n g) (k : ℕ) :
    CascadeExpr f n (fun z => (g z) ^ k) := by
  induction k with
  | zero =>
      have hfun : (fun z : ℂ => (g z) ^ 0) = fun _ : ℂ => (1 : ℂ) := by
        funext z
        simp
      rw [hfun]
      exact CascadeExpr.const 1
  | succ k ih =>
      have hfun : (fun z : ℂ => (g z) ^ (k + 1)) = fun z : ℂ => (g z) ^ k * g z := by
        funext z
        rw [pow_succ]
      rw [hfun]
      exact CascadeExpr.mul ih hg

/-- **Polynomials of a state are expressions.** -/
theorem cascadeExpr_polynomial {g : ℂ → ℂ} (hg : CascadeExpr f n g) (p : Polynomial ℂ) :
    CascadeExpr f n (fun z => p.eval (g z)) := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
      have hfun : (fun z : ℂ => (p + q).eval (g z))
          = fun z : ℂ => p.eval (g z) + q.eval (g z) := by
        funext z
        rw [Polynomial.eval_add]
      rw [hfun]
      exact CascadeExpr.add ihp ihq
  | monomial k c =>
      have hfun : (fun z : ℂ => (Polynomial.monomial k c).eval (g z))
          = fun z : ℂ => c * (g z) ^ k := by
        funext z
        rw [Polynomial.eval_monomial]
      rw [hfun]
      exact CascadeExpr.mul (CascadeExpr.const c) (cascadeExpr_pow hg k)

/-- **The constituent's equation, evaluated at the state.**  A first-order equation for `f_i`
becomes, at the argument `F_i w`, a polynomial relation between the two states and the constituent's
derivative there. -/
theorem cascade_constituent_relation {f : ℕ → ℂ → ℂ} {i : ℕ}
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ}
    (hP : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (f i u) ^ p.1 * (deriv (f i) u) ^ p.2 = 0)
    (w : ℂ) :
    ∑ p ∈ S, (A p).eval (entireCascade f i w) * (entireCascade f (i + 1) w) ^ p.1
      * (deriv (f i) (entireCascade f i w)) ^ p.2 = 0 :=
  hP (entireCascade f i w)

open scoped Classical in
/-- **The constituent's equation, grouped by the derivative's exponent.**  Collecting the terms of
each power of `f_i'(F_i)` turns the equation into a polynomial in that single quantity, with
coefficients that are expressions in the two states. -/
theorem cascade_constituent_grouped {f : ℕ → ℂ → ℂ} {i : ℕ}
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hd : ∀ p ∈ S, p.2 ∈ Finset.range (d + 1))
    (hP : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (f i u) ^ p.1 * (deriv (f i) u) ^ p.2 = 0)
    (w : ℂ) :
    ∑ c ∈ Finset.range (d + 1),
        (∑ p ∈ S.filter (fun p => p.2 = c),
          (A p).eval (entireCascade f i w) * (entireCascade f (i + 1) w) ^ p.1)
        * (deriv (f i) (entireCascade f i w)) ^ c = 0 := by
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.range (d + 1))
    (g := fun p : ℕ × ℕ => p.2) hd
    (f := fun p : ℕ × ℕ => (A p).eval (entireCascade f i w)
      * (entireCascade f (i + 1) w) ^ p.1
      * (deriv (f i) (entireCascade f i w)) ^ p.2)
  have hpull : ∀ c ∈ Finset.range (d + 1),
      (∑ p ∈ S.filter (fun p => p.2 = c),
        (A p).eval (entireCascade f i w) * (entireCascade f (i + 1) w) ^ p.1)
        * (deriv (f i) (entireCascade f i w)) ^ c
      = ∑ p ∈ S.filter (fun p => p.2 = c),
          ((A p).eval (entireCascade f i w) * (entireCascade f (i + 1) w) ^ p.1
            * (deriv (f i) (entireCascade f i w)) ^ p.2) := by
    intro c _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hpull, hfiber]
  exact cascade_constituent_relation hP w

open scoped Classical in
/-- **The relation among the states alone.**  Composing the grouping with the denominator clearing:
the constituent's first-order equation becomes a polynomial relation among two consecutive states and
their first derivatives, with no reference to the constituent's derivative.

Every quantity appearing is an expression in the cascade data, so a relation of this form is a
relation among the states — which polynomial independence forbids. -/
theorem cascade_state_relation {f : ℕ → ℂ → ℂ} {i : ℕ}
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hf : ∀ j : ℕ, AnalyticOnNhd ℂ (f j) Set.univ)
    (hd : ∀ p ∈ S, p.2 ∈ Finset.range (d + 1))
    (hP : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (f i u) ^ p.1 * (deriv (f i) u) ^ p.2 = 0)
    {w : ℂ} (hw : deriv (entireCascade f i) w ≠ 0) :
    ∑ c ∈ Finset.range (d + 1),
        (∑ p ∈ S.filter (fun p => p.2 = c),
          (A p).eval (entireCascade f i w) * (entireCascade f (i + 1) w) ^ p.1)
        * (deriv (entireCascade f (i + 1)) w) ^ c
        * (deriv (entireCascade f i) w) ^ (d - c) = 0 :=
  cascade_relation_cleared hf hw (cascade_constituent_grouped hd hP w)

/-- **The coefficients of the state relation are expressions.** -/
theorem cascadeExpr_state_relation_coeff {i : ℕ} (hi : i ≤ n) (hi1 : i + 1 ≤ n)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} (c : ℕ) :
    CascadeExpr f n (fun z => ∑ p ∈ S.filter (fun p => p.2 = c),
      (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1) := by
  classical
  induction S using Finset.induction with
  | empty =>
      have hfun : (fun z : ℂ => ∑ p ∈ (∅ : Finset (ℕ × ℕ)).filter (fun p => p.2 = c),
          (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        simp
      rw [hfun]
      exact CascadeExpr.const 0
  | insert q T hq ih =>
      by_cases hqc : q.2 = c
      · have hfun : (fun z : ℂ => ∑ p ∈ (insert q T).filter (fun p => p.2 = c),
            (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1)
            = fun z : ℂ => (A q).eval (entireCascade f i z)
                * (entireCascade f (i + 1) z) ^ q.1
              + ∑ p ∈ T.filter (fun p => p.2 = c),
                  (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1 := by
          funext z
          rw [Finset.filter_insert, if_pos hqc, Finset.sum_insert]
          simp only [Finset.mem_filter, not_and]
          intro hmem
          exact absurd hmem hq
        rw [hfun]
        exact CascadeExpr.add
          (CascadeExpr.mul (cascadeExpr_polynomial (CascadeExpr.state i hi) (A q))
            (cascadeExpr_pow (CascadeExpr.state (i + 1) hi1) q.1)) ih
      · have hfun : (fun z : ℂ => ∑ p ∈ (insert q T).filter (fun p => p.2 = c),
            (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1)
            = fun z : ℂ => ∑ p ∈ T.filter (fun p => p.2 = c),
                (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1 := by
          funext z
          rw [Finset.filter_insert, if_neg hqc]
        rw [hfun]
        exact ih

/-! ## The state's derivative is algebraic over the cascade data

Since every state's derivative is itself an expression, the relation of `cascade_state_relation` may
be read as a polynomial in `F_{i+1}'` whose coefficients are expressions.  No separate notion of
"algebraic over the states" is needed: the coefficients are already in the class. -/

open scoped Classical in
/-- The coefficient of the state relation, with the lower state's derivative absorbed. -/
noncomputable def stateRelationCoeff (f : ℕ → ℂ → ℂ) (i d c : ℕ)
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) : ℂ → ℂ :=
  fun z => (∑ p ∈ S.filter (fun p => p.2 = c),
      (A p).eval (entireCascade f i z) * (entireCascade f (i + 1) z) ^ p.1)
    * (deriv (entireCascade f i) z) ^ (d - c)

open scoped Classical in
/-- **The coefficients are expressions.** -/
theorem cascadeExpr_stateRelationCoeff (hf : ∀ j : ℕ, AnalyticOnNhd ℂ (f j) Set.univ)
    {i : ℕ} (hi : i ≤ n) (hi1 : i + 1 ≤ n) (d c : ℕ)
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) :
    CascadeExpr f n (stateRelationCoeff f i d c S A) := by
  refine CascadeExpr.mul (cascadeExpr_state_relation_coeff hi hi1 c) ?_
  have hderiv : CascadeExpr f n (deriv (entireCascade f i)) :=
    cascadeExpr_deriv_state hf i hi
  exact cascadeExpr_pow hderiv (d - c)

open scoped Classical in
/-- **The state's derivative satisfies a polynomial with expression coefficients.** -/
theorem cascade_deriv_poly_relation {f : ℕ → ℂ → ℂ} {i : ℕ}
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hf : ∀ j : ℕ, AnalyticOnNhd ℂ (f j) Set.univ)
    (hd : ∀ p ∈ S, p.2 ∈ Finset.range (d + 1))
    (hP : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (f i u) ^ p.1 * (deriv (f i) u) ^ p.2 = 0)
    {w : ℂ} (hw : deriv (entireCascade f i) w ≠ 0) :
    ∑ c ∈ Finset.range (d + 1),
        stateRelationCoeff f i d c S A w * (deriv (entireCascade f (i + 1)) w) ^ c = 0 := by
  have hbase := cascade_state_relation hf hd hP hw
  rw [← hbase]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [stateRelationCoeff]
  ring

end GaloisForLFunctions.HTGeometry
