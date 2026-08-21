import GaloisForLFunctions.HTGeometry.RationalPrefixDeckDescent

/-!
# Composing rational maps, and the degree of an iterate

The deck descent along a rational prefix is stated for one rational map `P/Q`.  The isogeny tail
needs it for every iterate, so the composite of two rational maps has to be exhibited as a rational
map again, with its degree.

Homogenising the outer map against the inner one does both at once: for `S` of degree at most `m`,

`ratComp S m P Q = ∑_{i ≤ m} S_i · P^i · Q^{m−i}`

evaluates to `Q(g)^m · S(P(g)/Q(g))`, so the two homogenisations of the outer numerator and
denominator present the composite as a rational map, and their degrees are at most `m` times the
degree of the inner map.  Iterating gives `deg αⁿ ≤ (deg α)ⁿ`, which is the degree bookkeeping the
deck descent consumes.

* `ratComp`, `natDegree_ratComp_le`, `aeval_ratComp`;
* `ratMapEval_ratComp` — **the composite of two rational maps is a rational map**;
* `ratIter`, `natDegree_ratIter_le`, `ratMapEval_ratIter` — **the iterates, with `deg ≤ dⁿ`**;
* `aeval_ratIter_snd_ne_zero` — the iterate's denominator does not vanish along the orbit;
* `ratMapWronskian_ratComp_ne_zero`, `ratMapWronskian_ratIter_ne_zero` — **noncriticality is
  inherited by every composite and every iterate**;
* `differentialAdjoin_ratIter_eq_fixedField` — **the deck descent for every iterate**.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- The homogenisation of `S` in degree `m` against the rational map `P/Q`. -/
def ratComp (S : Polynomial C) (m : ℕ) (P Q : Polynomial C) : Polynomial C :=
  ∑ i ∈ Finset.range (m + 1), Polynomial.C (S.coeff i) * P ^ i * Q ^ (m - i)

theorem natDegree_ratComp_le (S : Polynomial C) (m : ℕ) {P Q : Polynomial C} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) : (ratComp S m P Q).natDegree ≤ m * d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have him : i ≤ m := by
    have := Finset.mem_range.mp hi
    omega
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (Polynomial.C (S.coeff i) * P ^ i).natDegree ≤ i * d := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_le_mul_left i hP
  have h2 : ((Q : Polynomial C) ^ (m - i)).natDegree ≤ (m - i) * d := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_le_mul_left (m - i) hQ
  have : i * d + (m - i) * d = m * d := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

/-- **The homogenisation evaluates to the outer map, cleared by a power of the inner
denominator.** -/
theorem aeval_ratComp {S : Polynomial C} {m : ℕ} (hS : S.natDegree ≤ m) (P Q : Polynomial C)
    {g : E} (hQ : Polynomial.aeval g Q ≠ 0) :
    Polynomial.aeval g (ratComp S m P Q)
      = (Polynomial.aeval g Q) ^ m * Polynomial.aeval (ratMapEval P Q g) S := by
  rw [ratComp, map_sum]
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hS) (ratMapEval P Q g), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := by
    have := Finset.mem_range.mp hi
    omega
  rw [map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_C, ratMapEval, div_pow,
    Algebra.smul_def]
  have hsplit : (Polynomial.aeval g Q : E) ^ m
      = (Polynomial.aeval g Q) ^ (m - i) * (Polynomial.aeval g Q) ^ i := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

/-- **The composite of two rational maps is a rational map.** -/
theorem ratMapEval_ratComp {P' Q' : Polynomial C} {m : ℕ} (hP' : P'.natDegree ≤ m)
    (hQ' : Q'.natDegree ≤ m) (P Q : Polynomial C) {g : E} (hQ : Polynomial.aeval g Q ≠ 0) :
    ratMapEval (ratComp P' m P Q) (ratComp Q' m P Q) g
      = ratMapEval P' Q' (ratMapEval P Q g) := by
  rw [ratMapEval, aeval_ratComp hP' P Q hQ, aeval_ratComp hQ' P Q hQ,
    mul_div_mul_left _ _ (pow_ne_zero m hQ)]
  rfl

/-- The iterate of a rational map, as a pair of polynomials. -/
def ratIter (P Q : Polynomial C) (d : ℕ) : ℕ → Polynomial C × Polynomial C
  | 0 => (Polynomial.X, 1)
  | n + 1 => (ratComp (ratIter P Q d n).1 (d ^ n) P Q, ratComp (ratIter P Q d n).2 (d ^ n) P Q)

theorem natDegree_ratIter_le {P Q : Polynomial C} {d : ℕ} (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) (n : ℕ) :
    (ratIter P Q d n).1.natDegree ≤ d ^ n ∧ (ratIter P Q d n).2.natDegree ≤ d ^ n := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show (Polynomial.X : Polynomial C).natDegree ≤ d ^ 0
        simp
      · show (1 : Polynomial C).natDegree ≤ d ^ 0
        simp
  | succ n ih =>
      constructor
      · rw [ratIter]
        refine le_trans (natDegree_ratComp_le _ _ hP hQ) ?_
        rw [pow_succ]
      · rw [ratIter]
        refine le_trans (natDegree_ratComp_le _ _ hP hQ) ?_
        rw [pow_succ]

/-- **The iterate of a rational map is the rational map of the iterated pair.** -/
theorem ratMapEval_ratIter {P Q : Polynomial C} {d : ℕ} (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) :
    ∀ (n : ℕ) {g : E},
      (∀ k : ℕ, Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] g) Q ≠ 0) →
      ratMapEval (ratIter P Q d n).1 (ratIter P Q d n).2 g
        = (fun x => ratMapEval P Q x)^[n] g
  | 0, g, _ => by
      show ratMapEval (Polynomial.X : Polynomial C) 1 g = g
      simp [ratMapEval]
  | (n + 1), g, horb => by
      have hg : Polynomial.aeval g Q ≠ 0 := by simpa using horb 0
      have hstep : ratMapEval (ratIter P Q d (n + 1)).1 (ratIter P Q d (n + 1)).2 g
          = ratMapEval (ratIter P Q d n).1 (ratIter P Q d n).2 (ratMapEval P Q g) := by
        rw [ratIter]
        exact ratMapEval_ratComp (natDegree_ratIter_le hP hQ n).1
          (natDegree_ratIter_le hP hQ n).2 P Q hg
      rw [hstep]
      have horb' : ∀ k : ℕ,
          Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] (ratMapEval P Q g)) Q ≠ 0 := by
        intro k
        have := horb (k + 1)
        rwa [Function.iterate_succ_apply] at this
      rw [ratMapEval_ratIter hP hQ n horb', ← Function.iterate_succ_apply]

/-- The denominator of an iterate is a product of denominators along the orbit, so it does not
vanish as long as the orbit avoids the poles. -/
theorem aeval_ratIter_snd_ne_zero {P Q : Polynomial C} {d : ℕ} (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) :
    ∀ (n : ℕ) {g : E},
      (∀ k : ℕ, Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] g) Q ≠ 0) →
      Polynomial.aeval g (ratIter P Q d n).2 ≠ 0
  | 0, g, _ => by
      show Polynomial.aeval g (1 : Polynomial C) ≠ 0
      simp
  | (n + 1), g, horb => by
      have hg : Polynomial.aeval g Q ≠ 0 := by simpa using horb 0
      have horb' : ∀ k : ℕ,
          Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] (ratMapEval P Q g)) Q ≠ 0 := by
        intro k
        have := horb (k + 1)
        rwa [Function.iterate_succ_apply] at this
      have hstep : Polynomial.aeval g (ratIter P Q d (n + 1)).2
          = (Polynomial.aeval g Q) ^ (d ^ n)
            * Polynomial.aeval (ratMapEval P Q g) (ratIter P Q d n).2 := by
        rw [ratIter]
        exact aeval_ratComp (natDegree_ratIter_le hP hQ n).2 P Q hg
      rw [hstep]
      exact mul_ne_zero (pow_ne_zero _ hg) (aeval_ratIter_snd_ne_zero hP hQ n horb')

end

section Critical

open scoped Differential

variable {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E]

omit [Differential C] [DifferentialAlgebra C E] in
/-- **The composite of two noncritical rational maps is noncritical.**  The chain rule makes the
derivative of the composite a product of three nonzero factors, so its Wronskian cannot vanish. -/
theorem ratMapWronskian_ratComp_ne_zero (hC : ∀ c : C, (algebraMap C E c)′ = 0)
    {P' Q' : Polynomial C} {m : ℕ} (hP' : P'.natDegree ≤ m) (hQ' : Q'.natDegree ≤ m)
    (P Q : Polynomial C) {g : E} (hg' : g′ ≠ 0) (hQg : Polynomial.aeval g Q ≠ 0)
    (hQ'u : Polynomial.aeval (ratMapEval P Q g) Q' ≠ 0)
    (hW : ratMapWronskian P Q g ≠ 0)
    (hW' : ratMapWronskian P' Q' (ratMapEval P Q g) ≠ 0) :
    ratMapWronskian (ratComp P' m P Q) (ratComp Q' m P Q) g ≠ 0 := by
  intro h0
  have hcomp : ratMapEval (ratComp P' m P Q) (ratComp Q' m P Q) g
      = ratMapEval P' Q' (ratMapEval P Q g) := ratMapEval_ratComp hP' hQ' P Q hQg
  have h1 : (ratMapEval (ratComp P' m P Q) (ratComp Q' m P Q) g)′ = 0 := by
    rw [deriv_ratMapEval hC, h0, zero_mul, zero_mul]
  rw [hcomp, deriv_ratMapEval hC, deriv_ratMapEval hC] at h1
  exact mul_ne_zero (mul_ne_zero hW' (pow_ne_zero 2 (inv_ne_zero hQ'u)))
    (mul_ne_zero (mul_ne_zero hW (pow_ne_zero 2 (inv_ne_zero hQg))) hg') h1

omit [Differential C] [DifferentialAlgebra C E] in
/-- **Every iterate of a noncritical rational map is noncritical along its orbit.** -/
theorem ratMapWronskian_ratIter_ne_zero (hC : ∀ c : C, (algebraMap C E c)′ = 0)
    {P Q : Polynomial C} {d : ℕ} (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) :
    ∀ (n : ℕ) {g : E}, g′ ≠ 0 →
      (∀ k : ℕ, Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] g) Q ≠ 0) →
      (∀ k : ℕ, ratMapWronskian P Q ((fun x => ratMapEval P Q x)^[k] g) ≠ 0) →
      ratMapWronskian (ratIter P Q d n).1 (ratIter P Q d n).2 g ≠ 0
  | 0, g, _, _, _ => by
      show ratMapWronskian (Polynomial.X : Polynomial C) 1 g ≠ 0
      rw [ratMapWronskian]
      simp
  | (n + 1), g, hg', horb, hwr => by
      have hg : Polynomial.aeval g Q ≠ 0 := by simpa using horb 0
      have hW : ratMapWronskian P Q g ≠ 0 := by simpa using hwr 0
      have horb' : ∀ k : ℕ,
          Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] (ratMapEval P Q g)) Q ≠ 0 := by
        intro k
        have := horb (k + 1)
        rwa [Function.iterate_succ_apply] at this
      have hwr' : ∀ k : ℕ,
          ratMapWronskian P Q ((fun x => ratMapEval P Q x)^[k] (ratMapEval P Q g)) ≠ 0 := by
        intro k
        have := hwr (k + 1)
        rwa [Function.iterate_succ_apply] at this
      have hu' : (ratMapEval P Q g)′ ≠ 0 := by
        rw [deriv_ratMapEval hC]
        exact mul_ne_zero (mul_ne_zero hW (pow_ne_zero 2 (inv_ne_zero hg))) hg'
      have hQ'u : Polynomial.aeval (ratMapEval P Q g) (ratIter P Q d n).2 ≠ 0 :=
        aeval_ratIter_snd_ne_zero hP hQ n horb'
      have hW' : ratMapWronskian (ratIter P Q d n).1 (ratIter P Q d n).2 (ratMapEval P Q g) ≠ 0 :=
        ratMapWronskian_ratIter_ne_zero hC hP hQ n hu' horb' hwr'
      rw [ratIter]
      exact ratMapWronskian_ratComp_ne_zero hC (natDegree_ratIter_le hP hQ n).1
        (natDegree_ratIter_le hP hQ n).2 P Q hg' hg hQ'u hW hW'

/-- **The prefix image of every iterate is the fixed field of its deck group.**  For a noncritical
rational map whose forward orbit avoids the poles and the critical points, the differential field
generated by `αⁿ(g)` is exactly the fixed field of any finite automorphism group of order at least
`dⁿ` that fixes it.  This is the isogeny-tail statement `αⁿ*K = K^{Γₙ}` in the one-dimensional
case; the only remaining input is the geometric degree count `dⁿ ≤ |Γₙ|`. -/
theorem differentialAdjoin_ratIter_eq_fixedField (hC : ∀ c : C, (algebraMap C E c)′ = 0)
    {P Q : Polynomial C} {d : ℕ} (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    {g : E} (hg' : g′ ≠ 0)
    (horb : ∀ k : ℕ, Polynomial.aeval ((fun x => ratMapEval P Q x)^[k] g) Q ≠ 0)
    (hwr : ∀ k : ℕ, ratMapWronskian P Q ((fun x => ratMapEval P Q x)^[k] g) ≠ 0)
    (htop : differentialAdjoin C ({g} : Set E) = ⊤) (n : ℕ)
    (Γ : Subgroup (E ≃ₐ[C] E)) [Fintype Γ]
    (hfix : differentialAdjoin C ({(fun x => ratMapEval P Q x)^[n] g} : Set E)
      ≤ IntermediateField.fixedField Γ)
    (hcard : d ^ n ≤ Nat.card Γ) :
    differentialAdjoin C ({(fun x => ratMapEval P Q x)^[n] g} : Set E)
      = IntermediateField.fixedField Γ := by
  have hiter : (fun x => ratMapEval P Q x)^[n] g
      = ratMapEval (ratIter P Q d n).1 (ratIter P Q d n).2 g :=
    (ratMapEval_ratIter hP hQ n horb).symm
  rw [hiter] at hfix ⊢
  exact differentialAdjoin_ratMapEval_eq_fixedField hC
    (aeval_ratIter_snd_ne_zero hP hQ n horb)
    (ratMapWronskian_ratIter_ne_zero hC hP hQ n hg' horb hwr) htop Γ hfix
    (le_trans (max_le (natDegree_ratIter_le hP hQ n).1 (natDegree_ratIter_le hP hQ n).2) hcard)

end Critical

end GaloisForLFunctions.HTGeometry
