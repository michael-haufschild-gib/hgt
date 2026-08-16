import GaloisForLFunctions.HTGeometry.RationalBackwardOrbit
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Two quadratic maps carry no invariant rational differential

For `R(z) = z² + 1` and `R(z) = (z − 1)²` every relation

`Q ∘ R · (R')^k = μ Q`,  `Q ≠ 0`, `μ ≠ 0`,

has `k = 0` and constant `Q`.

The mechanism is the order transport.  Away from the critical point the order of `Q` is constant
along the map, and a point which is neither periodic nor in the forward orbit of the critical point
carries an injective critical-free backward orbit, so its order vanishes.  For `z² + 1` the
critical orbit is `0, 1, 2, 5, 26, …`, which misses `i` and `−1`; for `(z − 1)²` it is the two-cycle
`1, 0`, which misses `2`.  Chasing the vanishing order back to the critical point through one
transport with a ramification index of two leaves `k = 0`, and a weight-zero relation is impossible
for a nonconstant `Q` because substitution multiplies the degree by two.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-! ## Elementary complex facts -/

theorem natCast_ne_neg_one (k : ℕ) : (k : ℂ) ≠ -1 := by
  intro h
  have h1 : ((k + 1 : ℕ) : ℂ) = 0 := by push_cast; rw [h]; ring
  exact Nat.succ_ne_zero k (by exact_mod_cast h1)

theorem natCast_ne_I (k : ℕ) : (k : ℂ) ≠ Complex.I := by
  intro h
  have := congrArg Complex.im h
  simp at this

/-! ## The map `z ↦ z² + 1` -/

/-- The quadratic map `z ↦ z² + 1`. -/
def quadOne : Polynomial ℂ := X ^ 2 + Polynomial.C 1

@[simp]
theorem quadOne_eval (z : ℂ) : quadOne.eval z = z ^ 2 + 1 := by
  simp [quadOne]

@[simp]
theorem natDegree_quadOne : quadOne.natDegree = 2 := natDegree_X_pow_add_C

@[simp]
theorem derivative_quadOne : derivative quadOne = Polynomial.C 2 * X := by
  rw [quadOne, Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_C]
  norm_num

/-- The forward orbit of the critical point of `z ↦ z² + 1`, as natural numbers. -/
def quadOneOrbit : ℕ → ℕ
  | 0 => 0
  | n + 1 => quadOneOrbit n ^ 2 + 1

theorem iterate_quadOne_zero (n : ℕ) :
    (fun z => quadOne.eval z)^[n] 0 = (quadOneOrbit n : ℂ) := by
  induction n with
  | zero => simp [quadOneOrbit]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      show quadOne.eval _ = _
      rw [quadOne_eval, quadOneOrbit]
      push_cast
      ring

theorem critical_quadOne {a : ℂ} (ha : (derivative quadOne).eval a = 0) : a = 0 := by
  rw [derivative_quadOne] at ha
  simp only [eval_mul, eval_C, eval_X] at ha
  rcases mul_eq_zero.mp ha with h | h
  · exact absurd h (by norm_num)
  · exact h

theorem postcritical_quadOne_ne_I (a : ℂ) (ha : (derivative quadOne).eval a = 0) (n : ℕ) :
    (fun z => quadOne.eval z)^[n] a ≠ Complex.I := by
  rw [critical_quadOne ha, iterate_quadOne_zero]
  exact natCast_ne_I _

theorem postcritical_quadOne_ne_neg_one (a : ℂ) (ha : (derivative quadOne).eval a = 0) (n : ℕ) :
    (fun z => quadOne.eval z)^[n] a ≠ -1 := by
  rw [critical_quadOne ha, iterate_quadOne_zero]
  exact natCast_ne_neg_one _

theorem aperiodic_quadOne_I (n : ℕ) (hn : 1 ≤ n) :
    (fun z => quadOne.eval z)^[n] Complex.I ≠ Complex.I := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have hI : quadOne.eval Complex.I = 0 := by
    rw [quadOne_eval, Complex.I_sq]
    ring
  show (fun z => quadOne.eval z)^[m] (quadOne.eval Complex.I) ≠ Complex.I
  rw [hI, iterate_quadOne_zero]
  exact natCast_ne_I _

theorem iterate_quadOne_natCast (j n : ℕ) :
    (fun z => quadOne.eval z)^[n] (quadOneOrbit j : ℂ) = (quadOneOrbit (j + n) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      show quadOne.eval _ = _
      rw [quadOne_eval, show j + (n + 1) = (j + n) + 1 from by ring, quadOneOrbit]
      push_cast
      ring

theorem aperiodic_quadOne_neg_one (n : ℕ) (hn : 1 ≤ n) :
    (fun z => quadOne.eval z)^[n] (-1 : ℂ) ≠ -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have hval : quadOne.eval (-1 : ℂ) = (quadOneOrbit 2 : ℂ) := by
    rw [quadOne_eval]
    norm_num [quadOneOrbit]
  show (fun z => quadOne.eval z)^[m] (quadOne.eval (-1 : ℂ)) ≠ -1
  rw [hval, iterate_quadOne_natCast]
  exact natCast_ne_neg_one _

theorem rootMultiplicity_quadOne_crit :
    rootMultiplicity (0 : ℂ) (quadOne - Polynomial.C (quadOne.eval 0)) = 2 := by
  have hpoly : quadOne - Polynomial.C (quadOne.eval 0) = (X : Polynomial ℂ) ^ 2 := by
    rw [quadOne_eval, show ((0 : ℂ) ^ 2 + 1) = 1 from by ring, quadOne]
    ring
  rw [hpoly, rootMultiplicity_pow Polynomial.X_ne_zero 2 0]
  rw [show (X : Polynomial ℂ) = X - Polynomial.C 0 from by rw [map_zero, sub_zero]]
  rw [rootMultiplicity_X_sub_C_self]

theorem rootMultiplicity_derivative_quadOne :
    rootMultiplicity (0 : ℂ) (derivative quadOne) = 1 := by
  rw [derivative_quadOne]
  have hne : (Polynomial.C (2 : ℂ) * X) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 1) h
    simp at this
  rw [rootMultiplicity_mul hne,
    rootMultiplicity_eq_zero (by simp : ¬ (Polynomial.C (2 : ℂ)).IsRoot 0), zero_add]
  rw [show (X : Polynomial ℂ) = X - Polynomial.C 0 from by rw [map_zero, sub_zero]]
  rw [rootMultiplicity_X_sub_C_self]

/-- **The map `z ↦ z² + 1` carries no invariant rational differential.** -/
theorem quadOne_no_invariant_differential
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) = RatFunc.C c)
    {Q : RatFunc ℂ} (hQ : Q ≠ 0) {k : ℤ} {μ : ℂ} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) hR Q
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (derivative quadOne)) ^ k = RatFunc.C μ * Q) :
    k = 0 ∧ ∃ c : ℂ, Q = RatFunc.C c := by
  have hdeg : quadOne.natDegree ≠ 0 := by rw [natDegree_quadOne]; norm_num
  -- the order vanishes at `i`, hence at the critical point
  have hI : ratOrder Q Complex.I = 0 :=
    ratOrder_eq_zero_of_aperiodic hdeg hR hQ hμ hrel aperiodic_quadOne_I
      postcritical_quadOne_ne_I
  have hIcrit : (derivative quadOne).eval Complex.I ≠ 0 := by
    rw [derivative_quadOne]
    simp [Complex.I_ne_zero]
  have h0 : ratOrder Q 0 = 0 := by
    have h := ratOrder_eval_eq_of_deriv_ne_zero hdeg hR hQ hμ hrel hIcrit
    rw [quadOne_eval, Complex.I_sq, show (-1 : ℂ) + 1 = 0 from by ring, hI] at h
    exact h
  -- the order vanishes at `−1`, hence at `2`, hence at `1`
  have hm1 : ratOrder Q (-1 : ℂ) = 0 :=
    ratOrder_eq_zero_of_aperiodic hdeg hR hQ hμ hrel aperiodic_quadOne_neg_one
      postcritical_quadOne_ne_neg_one
  have hm1crit : (derivative quadOne).eval (-1 : ℂ) ≠ 0 := by
    rw [derivative_quadOne]
    norm_num
  have h2 : ratOrder Q 2 = 0 := by
    have h := ratOrder_eval_eq_of_deriv_ne_zero hdeg hR hQ hμ hrel hm1crit
    rw [quadOne_eval, show ((-1 : ℂ)) ^ 2 + 1 = 2 from by ring, hm1] at h
    exact h
  have h1crit : (derivative quadOne).eval (1 : ℂ) ≠ 0 := by
    rw [derivative_quadOne]
    norm_num
  have h1 : ratOrder Q 1 = 0 := by
    have h := ratOrder_eval_eq_of_deriv_ne_zero hdeg hR hQ hμ hrel h1crit
    rw [quadOne_eval, show ((1 : ℂ)) ^ 2 + 1 = 2 from by ring, h2] at h
    exact h.symm
  -- the transport at the critical point kills the weight
  have htrans := ratOrder_relation_transport hdeg hR hQ hμ hrel 0
  rw [rootMultiplicity_quadOne_crit, rootMultiplicity_derivative_quadOne, h0,
    quadOne_eval, show ((0 : ℂ)) ^ 2 + 1 = 1 from by ring, h1] at htrans
  have hk : k = 0 := by omega
  refine ⟨hk, ?_⟩
  subst hk
  rw [zpow_zero, mul_one] at hrel
  exact eq_C_of_weight_zero_relation (by rw [natDegree_quadOne]) hR hμ hrel

/-! ## The map `z ↦ (z − 1)²` -/

/-- The quadratic map `z ↦ (z − 1)²`. -/
def quadTwo : Polynomial ℂ := (X - Polynomial.C 1) ^ 2

@[simp]
theorem quadTwo_eval (z : ℂ) : quadTwo.eval z = (z - 1) ^ 2 := by
  simp [quadTwo]

@[simp]
theorem natDegree_quadTwo : quadTwo.natDegree = 2 := by
  rw [quadTwo, natDegree_pow, natDegree_X_sub_C]

@[simp]
theorem derivative_quadTwo : derivative quadTwo = Polynomial.C 2 * (X - Polynomial.C 1) := by
  rw [quadTwo, Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C]
  norm_num

theorem critical_quadTwo {a : ℂ} (ha : (derivative quadTwo).eval a = 0) : a = 1 := by
  rw [derivative_quadTwo] at ha
  simp only [eval_mul, eval_C, eval_sub, eval_X] at ha
  rcases mul_eq_zero.mp ha with h | h
  · exact absurd h (by norm_num)
  · linear_combination h

theorem iterate_quadTwo_one (n : ℕ) :
    (fun z => quadTwo.eval z)^[n] 1 = 1 ∨ (fun z => quadTwo.eval z)^[n] 1 = 0 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]
        exact Or.inr (by show quadTwo.eval 1 = 0; rw [quadTwo_eval]; ring)
      · rw [h]
        exact Or.inl (by show quadTwo.eval 0 = 1; rw [quadTwo_eval]; ring)

theorem postcritical_quadTwo_ne_two (a : ℂ) (ha : (derivative quadTwo).eval a = 0) (n : ℕ) :
    (fun z => quadTwo.eval z)^[n] a ≠ 2 := by
  rw [critical_quadTwo ha]
  rcases iterate_quadTwo_one n with h | h <;> rw [h] <;> norm_num

theorem aperiodic_quadTwo_two (n : ℕ) (hn : 1 ≤ n) :
    (fun z => quadTwo.eval z)^[n] (2 : ℂ) ≠ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have hval : quadTwo.eval (2 : ℂ) = 1 := by rw [quadTwo_eval]; ring
  show (fun z => quadTwo.eval z)^[m] (quadTwo.eval (2 : ℂ)) ≠ 2
  rw [hval]
  rcases iterate_quadTwo_one m with h | h <;> rw [h] <;> norm_num

theorem rootMultiplicity_quadTwo_crit :
    rootMultiplicity (1 : ℂ) (quadTwo - Polynomial.C (quadTwo.eval 1)) = 2 := by
  have hpoly : quadTwo - Polynomial.C (quadTwo.eval 1)
      = ((X : Polynomial ℂ) - Polynomial.C 1) ^ 2 := by
    rw [quadTwo_eval, quadTwo]
    norm_num
  rw [hpoly, rootMultiplicity_pow (Polynomial.X_sub_C_ne_zero 1) 2 1,
    rootMultiplicity_X_sub_C_self]

theorem rootMultiplicity_derivative_quadTwo :
    rootMultiplicity (1 : ℂ) (derivative quadTwo) = 1 := by
  rw [derivative_quadTwo]
  have hne : (Polynomial.C (2 : ℂ) * (X - Polynomial.C 1)) ≠ 0 :=
    mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)
  rw [rootMultiplicity_mul hne,
    rootMultiplicity_eq_zero (by simp : ¬ (Polynomial.C (2 : ℂ)).IsRoot 1), zero_add,
    rootMultiplicity_X_sub_C_self]

/-- **The map `z ↦ (z − 1)²` carries no invariant rational differential.** -/
theorem quadTwo_no_invariant_differential
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) = RatFunc.C c)
    {Q : RatFunc ℂ} (hQ : Q ≠ 0) {k : ℤ} {μ : ℂ} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) hR Q
        * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (derivative quadTwo)) ^ k = RatFunc.C μ * Q) :
    k = 0 ∧ ∃ c : ℂ, Q = RatFunc.C c := by
  have hdeg : quadTwo.natDegree ≠ 0 := by rw [natDegree_quadTwo]; norm_num
  have h2 : ratOrder Q 2 = 0 :=
    ratOrder_eq_zero_of_aperiodic hdeg hR hQ hμ hrel aperiodic_quadTwo_two
      postcritical_quadTwo_ne_two
  have h2crit : (derivative quadTwo).eval (2 : ℂ) ≠ 0 := by
    rw [derivative_quadTwo]
    norm_num
  have h1 : ratOrder Q 1 = 0 := by
    have h := ratOrder_eval_eq_of_deriv_ne_zero hdeg hR hQ hμ hrel h2crit
    rw [quadTwo_eval, show ((2 : ℂ) - 1) ^ 2 = 1 from by ring, h2] at h
    exact h
  have h0crit : (derivative quadTwo).eval (0 : ℂ) ≠ 0 := by
    rw [derivative_quadTwo]
    norm_num
  have h0 : ratOrder Q 0 = 0 := by
    have h := ratOrder_eval_eq_of_deriv_ne_zero hdeg hR hQ hμ hrel h0crit
    rw [quadTwo_eval, show ((0 : ℂ) - 1) ^ 2 = 1 from by ring, h1] at h
    exact h.symm
  have htrans := ratOrder_relation_transport hdeg hR hQ hμ hrel 1
  rw [rootMultiplicity_quadTwo_crit, rootMultiplicity_derivative_quadTwo, h1,
    quadTwo_eval, show ((1 : ℂ) - 1) ^ 2 = 0 from by ring, h0] at htrans
  have hk : k = 0 := by omega
  refine ⟨hk, ?_⟩
  subst hk
  rw [zpow_zero, mul_one] at hrel
  exact eq_C_of_weight_zero_relation (by rw [natDegree_quadTwo]) hR hμ hrel

end

end GaloisForLFunctions.HTGeometry
