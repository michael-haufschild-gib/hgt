import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Data.Nat.Choose.Cast

/-!
# Exponential and logarithm on a complete graded algebra

A complete graded algebra `H = ∏_{n ≥ 0} H_n` over a field `k` is presented by its homogeneous
projections `π_n`: every element is determined by its components, every homogeneous family
glues to an element, and `π_n(xy) = ∑_{i ≤ n} π_i(x) π_{n-i}(y)`.

For `Y` in the augmentation ideal `H_{≥1}` every power series `f ∈ k⟦X⟧` evaluates degreewise,
`π_n(f(Y)) = ∑_{m ≤ n} [X^m]f · π_n(Y^m)`; this is a `k`-algebra homomorphism compatible with
substitution.  With the power-series identities `exp(log(1+X)) = 1+X` and `log(exp X) = X`
(proved here from the chain rule) one obtains mutually inverse bijections
`exp : H_{≥1} ≃ 1 + H_{≥1} : log`, the law `exp(x+y) = exp x exp y` for commuting `x, y`,
compatibility with graded homomorphisms and anti-homomorphisms, and the truncations
`exp X ≡ 1 + X + X²/2`, `log(1+Z) ≡ Z - Z²/2` modulo `H_{≥3}`.
-/

noncomputable section

open PowerSeries Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Two power-series identities -/

section PowerSeriesIdentities

variable (k : Type*) [Field k] [CharZero k]

/-- The derivative of `log(1+X)` is the geometric series `G = ∑ (-1)^n X^n`. -/
theorem one_add_X_mul_deriv_log : (1 + X : k⟦X⟧) * d⁄dX k (log k) = 1 := by
  rw [deriv_log]
  ext n
  rcases n with _ | n
  · simp
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one]
    simp [pow_succ]

theorem natCast_succ_ne_zero (n : ℕ) : ((n : k) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero

/-- `exp(log(1+X)) = 1 + X`. -/
theorem exp_subst_log : (exp k).subst (log k) = 1 + X := by
  set E := (exp k).subst (log k) with hE
  have hl : HasSubst (log k) := HasSubst.log
  have hd : d⁄dX k E = E * d⁄dX k (log k) := by
    rw [hE, derivative_subst k hl, derivative_exp]
  have hODE : (1 + X) * d⁄dX k E = E := by
    rw [hd, mul_comm E, ← mul_assoc, one_add_X_mul_deriv_log, one_mul]
  have h1 : (1 : k⟦X⟧).subst (log k) = 1 := by
    have := map_one (substAlgHom (R := k) hl)
    rwa [coe_substAlgHom] at this
  have h0 : constantCoeff E = 1 := by
    have hsplit : E = (1 : k⟦X⟧) + (exp k - 1).subst (log k) := by
      rw [hE, subst_sub hl, h1]; abel
    rw [hsplit, map_add, map_one]
    have : constantCoeff ((exp k - 1).subst (log k)) = 0 :=
      constantCoeff_subst_eq_zero (constantCoeff_log : constantCoeff (log k) = 0) _
        (by rw [map_sub, constantCoeff_exp, map_one, sub_self])
    rw [this, add_zero]
  have hrec : ∀ n, coeff (n + 1) E * ((n : k) + 1) = (1 - n) * coeff n E := by
    intro n
    have h := congrArg (coeff n) hODE
    rcases n with _ | n
    · simp only [add_mul, one_mul, map_add, coeff_derivative, coeff_zero_X_mul, add_zero] at h
      simpa using h
    · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_derivative, coeff_derivative] at h
      push_cast at h ⊢
      linear_combination h
  have hc : ∀ n, coeff (n + 2) E = 0 := by
    intro n
    induction n with
    | zero =>
      have h := hrec 1
      have h1 := hrec 0
      simp only [Nat.cast_zero, zero_add, mul_one, sub_zero, one_mul] at h1
      push_cast at h
      have : coeff 2 E * 2 = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_right two_ne_zero
    | succ n ih =>
      have h := hrec (n + 2)
      rw [ih, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_right (natCast_succ_ne_zero k _)
  ext n
  rcases n with _ | _ | n
  · simpa using h0
  · have h := hrec 0
    rw [← coeff_zero_eq_constantCoeff_apply] at h0
    simp only [Nat.cast_zero, zero_add, mul_one, sub_zero, h0] at h
    simp [h]
  · rw [hc n]
    simp [coeff_X, coeff_one]

/-- `log(exp X) = X`. -/
theorem log_subst_exp_sub_one : (log k).subst (exp k - 1) = X := by
  set L := (log k).subst (exp k - 1) with hL
  have he : HasSubst (exp k - 1) := HasSubst.exp_sub_one
  have hG : (d⁄dX k (log k)).subst (exp k - 1) * exp k = 1 := by
    have h := congrArg (fun f : k⟦X⟧ => f.subst (exp k - 1)) (one_add_X_mul_deriv_log k)
    have h1 : (1 : k⟦X⟧).subst (exp k - 1) = 1 := by
      have := map_one (substAlgHom (R := k) he)
      rwa [coe_substAlgHom] at this
    rw [subst_mul he, subst_add he, subst_X he, h1, add_sub_cancel] at h
    rw [mul_comm]; exact h
  have hd : d⁄dX k L = 1 := by
    rw [hL, derivative_subst k he, map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero,
        hG]
  have h0 : constantCoeff L = 0 :=
    constantCoeff_subst_eq_zero
      (show MvPowerSeries.constantCoeff (exp k - 1) = 0 by
        rw [map_sub, show MvPowerSeries.constantCoeff (exp k) = constantCoeff (exp k) from rfl,
          constantCoeff_exp, map_one, sub_self]) _ (constantCoeff_log : constantCoeff (log k) = 0)
  ext n
  rcases n with _ | n
  · simpa using h0
  · have h := congrArg (coeff n) hd
    rw [coeff_derivative, coeff_one] at h
    rcases n with _ | n
    · rw [if_pos rfl] at h
      simp only [Nat.cast_zero, zero_add, mul_one] at h
      simp [coeff_X, h]
    · rw [if_neg (Nat.succ_ne_zero n)] at h
      have := (mul_eq_zero.1 h).resolve_right (natCast_succ_ne_zero k _)
      simp [this, coeff_X]

end PowerSeriesIdentities

/-! ## Complete graded algebras -/

/-- A complete graded algebra `H = ∏_n H_n`, presented by its homogeneous projections. -/
class CompleteGradedAlgebra (k : Type*) [Field k] (H : Type*) [Ring H] [Algebra k H] where
  /-- The projection onto `H_n`. -/
  comp : ℕ → H →ₗ[k] H
  comp_comp : ∀ m n (x : H), comp m (comp n x) = if m = n then comp n x else 0
  ext_comp : ∀ x y : H, (∀ n, comp n x = comp n y) → x = y
  /-- Gluing a homogeneous family. -/
  glue : (f : ℕ → H) → (∀ n, comp n (f n) = f n) → H
  comp_glue : ∀ (f : ℕ → H) (hf : ∀ n, comp n (f n) = f n) n, comp n (glue f hf) = f n
  comp_mul : ∀ n (x y : H), comp n (x * y) = ∑ i ∈ range (n + 1), comp i x * comp (n - i) y
  comp_one : ∀ n, comp n (1 : H) = if n = 0 then 1 else 0

namespace CompleteGradedAlgebra

variable (k : Type*) [Field k] {H : Type*} [Ring H] [Algebra k H] [CompleteGradedAlgebra k H] in
/-- The projection `π_n : H → H_n`. -/
abbrev proj (n : ℕ) : H →ₗ[k] H := CompleteGradedAlgebra.comp n

variable {k : Type*} [Field k] {H : Type*} [Ring H] [Algebra k H] [CompleteGradedAlgebra k H]

theorem comp_comp_self (n : ℕ) (x : H) : proj k n (proj k n x) = proj k n x := by
  rw [comp_comp, if_pos rfl]

theorem comp_comp_of_ne {m n : ℕ} (h : m ≠ n) (x : H) : proj k m (proj k n x) = 0 := by
  rw [comp_comp, if_neg h]

theorem comp_algebraMap (n : ℕ) (c : k) :
    proj k n (algebraMap k H c) = if n = 0 then algebraMap k H c else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, comp_one]
  split_ifs <;> simp

/-- Glue a family whose `n`-th member is the `n`-th projection of something. -/
def glueComp (f : ℕ → H) : H :=
  glue (k := k) (fun n => proj k n (f n)) fun n => comp_comp_self n (f n)

theorem comp_glueComp (f : ℕ → H) (n : ℕ) : proj k n (glueComp (k := k) f) = proj k n (f n) :=
  comp_glue _ _ n

variable (k H) in
/-- The decreasing filtration `H_{≥m}`. -/
def filtration (m : ℕ) : Submodule k H where
  carrier := {x | ∀ j < m, proj k j x = 0}
  add_mem' hx hy j hj := by rw [map_add, hx j hj, hy j hj, add_zero]
  zero_mem' j _ := map_zero _
  smul_mem' c x hx j hj := by rw [map_smul, hx j hj, smul_zero]

theorem mem_filtration {m : ℕ} {x : H} :
    x ∈ filtration k H m ↔ ∀ j < m, proj k j x = 0 := Iff.rfl

theorem filtration_antitone {m m' : ℕ} (h : m ≤ m') :
    filtration k H m' ≤ filtration k H m := fun _ hx j hj => hx j (lt_of_lt_of_le hj h)

theorem mem_filtration_zero (x : H)
    : x ∈ filtration k H 0 := fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem mul_mem_filtration {a b : ℕ} {x y : H} (hx : x ∈ filtration k H a)
    (hy : y ∈ filtration k H b) : x * y ∈ filtration k H (a + b) := by
  intro j hj
  rw [comp_mul]
  refine sum_eq_zero fun i hi => ?_
  rw [mem_range] at hi
  by_cases h : i < a
  · rw [hx i h, zero_mul]
  · rw [hy (j - i) (by omega), mul_zero]

theorem pow_mem_filtration {Y : H} (hY : Y ∈ filtration k H 1) (m : ℕ) :
    Y ^ m ∈ filtration k H m := by
  induction m with
  | zero => exact mem_filtration_zero _
  | succ m ih => rw [pow_succ]; exact mul_mem_filtration ih hY

theorem comp_pow_eq_zero {Y : H} (hY : Y ∈ filtration k H 1) {n m : ℕ} (h : n < m) :
    proj k n (Y ^ m) = 0 :=
  pow_mem_filtration hY m n h

theorem eq_zero_of_forall_comp {x : H} (h : ∀ n, proj k n x = 0) : x = 0 :=
  ext_comp (k := k) x 0 fun n => by rw [h n, map_zero]

/-! ## Degreewise evaluation of power series -/

/-- `π_n(f(Y)) = ∑_{m ≤ n} [X^m]f · π_n(Y^m)`. -/
def evalSeries (Y : H) (f : k⟦X⟧) : H :=
  glueComp (k := k) fun n => ∑ m ∈ range (n + 1), coeff m f • Y ^ m

theorem comp_evalSeries (Y : H) (f : k⟦X⟧) (n : ℕ) :
    proj k n (evalSeries Y f) = ∑ m ∈ range (n + 1), coeff m f • proj k n (Y ^ m) := by
  rw [evalSeries, comp_glueComp, map_sum]
  simp_rw [map_smul]

variable {Y : H}

/-- The coefficient sum may be extended past the degree. -/
theorem comp_evalSeries_eq_of_le (hY : Y ∈ filtration k H 1) (f : k⟦X⟧) {n N : ℕ} (h : n < N) :
    proj k n (evalSeries Y f) = ∑ m ∈ range N, coeff m f • proj k n (Y ^ m) := by
  rw [comp_evalSeries]
  refine sum_subset (range_subset_range.2 (by omega)) fun m hm hm' => ?_
  rw [mem_range] at hm hm'
  rw [comp_pow_eq_zero hY (by omega), smul_zero]

theorem comp_aeval_eq (p : Polynomial k) {n N : ℕ} (hN : p.natDegree < N) :
    proj k n (Polynomial.aeval Y p) = ∑ m ∈ range N, p.coeff m • proj k n (Y ^ m) := by
  rw [Polynomial.aeval_eq_sum_range' hN, map_sum]
  simp_rw [map_smul]

/-- The degree-`n` projection of `f(Y)` only sees the truncation of `f` below `N > n`. -/
theorem comp_evalSeries_eq_comp_aeval_trunc (hY : Y ∈ filtration k H 1) (f : k⟦X⟧) {n N : ℕ} (h
    : n < N) :
    proj k n (evalSeries Y f) = proj k n (Polynomial.aeval Y (trunc N f)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [comp_evalSeries_eq_of_le hY f h, comp_aeval_eq _ (natDegree_trunc_lt f M)]
  refine sum_congr rfl fun m hm => ?_
  rw [coeff_trunc, if_pos (mem_range.1 hm)]

theorem evalSeries_polynomial (hY : Y ∈ filtration k H 1) (p : Polynomial k) : evalSeries Y (p
    : k⟦X⟧) = Polynomial.aeval Y p := by
  refine ext_comp (k := k) _ _ fun n => ?_
  have h1 : n < max (n + 1) (p.natDegree + 1)
      := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
  have h2 : p.natDegree < max (n + 1) (p.natDegree + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  rw [comp_evalSeries_eq_of_le hY _ h1, comp_aeval_eq p h2]
  simp only [Polynomial.coeff_coe]

theorem evalSeries_mem_filtration (f : k⟦X⟧) (hf : constantCoeff f = 0) :
    evalSeries Y f ∈ filtration k H 1 := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [comp_evalSeries, sum_range_one, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]

theorem comp_evalSeries_eq_zero_of_coeff (f : k⟦X⟧) {n : ℕ} (hf : ∀ m ≤ n, coeff m f = 0) :
    proj k n (evalSeries Y f) = 0 := by
  rw [comp_evalSeries]
  exact sum_eq_zero fun m hm => by rw [hf m (by rw [mem_range] at hm; omega), zero_smul]

theorem comp_mul_eq_of_comp (x x' y y' : H) (n : ℕ)
    (hx : ∀ i ≤ n, proj k i x = proj k i x')
    (hy : ∀ i ≤ n, proj k i y = proj k i y') :
    proj k n (x * y) = proj k n (x' * y') := by
  rw [comp_mul, comp_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [hx i (by omega), hy (n - i) (by omega)]

/-- `f(Y)` agrees with the polynomial `trunc N f` evaluated at `Y` modulo `H_{≥N}`. -/
theorem evalSeries_sub_aeval_trunc_mem (hY : Y ∈ filtration k H 1) (f : k⟦X⟧) (N : ℕ) :
    evalSeries Y f - Polynomial.aeval Y (trunc N f) ∈ filtration k H N := by
  intro j hj
  rw [map_sub, comp_evalSeries_eq_comp_aeval_trunc hY f hj, sub_self]

theorem comp_aeval_trunc_eq (hY : Y ∈ filtration k H 1) (f : k⟦X⟧) {i n : ℕ} (hi : i ≤ n) :
    proj k i (Polynomial.aeval Y (trunc (n + 1) f)) =
      proj k i (evalSeries Y f) :=
  (comp_evalSeries_eq_comp_aeval_trunc hY f (by omega)).symm

theorem evalSeries_mul (hY : Y ∈ filtration k H 1) (f g : k⟦X⟧)
    : evalSeries Y (f * g) = evalSeries Y f * evalSeries Y g := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [comp_evalSeries_eq_comp_aeval_trunc hY _ (Nat.lt_succ_self n), ← trunc_trunc_mul_trunc,
    ← Polynomial.coe_mul, ← comp_evalSeries_eq_comp_aeval_trunc hY _ (Nat.lt_succ_self n),
    evalSeries_polynomial hY, map_mul]
  exact comp_mul_eq_of_comp _ _ _ _ n (fun i hi => comp_aeval_trunc_eq hY f hi)
    (fun i hi => comp_aeval_trunc_eq hY g hi)

theorem evalSeries_add (f g : k⟦X⟧) : evalSeries Y (f + g) = evalSeries Y f + evalSeries Y g :=
  ext_comp (k := k) _ _ fun n => by
    simp only [map_add, comp_evalSeries, add_smul, sum_add_distrib]

theorem evalSeries_smul (c : k) (f : k⟦X⟧) : evalSeries Y (c • f) = c • evalSeries Y f :=
  ext_comp (k := k) _ _ fun n => by
    simp only [map_smul, comp_evalSeries, smul_sum, smul_eq_mul, mul_smul]

theorem evalSeries_C (hY : Y ∈ filtration k H 1) (c : k)
    : evalSeries Y (C c) = algebraMap k H c := by
  rw [show (C c : k⟦X⟧) = ((Polynomial.C c : Polynomial k) : k⟦X⟧) by simp,
    evalSeries_polynomial hY, Polynomial.aeval_C]

theorem evalSeries_one (hY : Y ∈ filtration k H 1) : evalSeries Y (1 : k⟦X⟧) = 1 := by
  rw [← map_one (C (R := k)), evalSeries_C hY, map_one]

theorem evalSeries_X (hY : Y ∈ filtration k H 1) : evalSeries Y (X : k⟦X⟧) = Y := by
  rw [show (X : k⟦X⟧) = ((Polynomial.X : Polynomial k) : k⟦X⟧) by simp,
    evalSeries_polynomial hY, Polynomial.aeval_X]

/-- Evaluation at `Y ∈ H_{≥1}` as a `k`-algebra homomorphism. -/
def evalSeriesAlgHom (hY : Y ∈ filtration k H 1) : k⟦X⟧ →ₐ[k] H where
  toFun := evalSeries Y
  map_one' := evalSeries_one hY
  map_mul' := evalSeries_mul hY
  map_zero' := by
    rw [show (0 : k⟦X⟧) = (0 : k) • 0 by simp, evalSeries_smul, zero_smul]
  map_add' := evalSeries_add
  commutes' c := by
    rw [show algebraMap k k⟦X⟧ c = C c from rfl]
    exact evalSeries_C hY c

theorem evalSeriesAlgHom_apply (hY : Y ∈ filtration k H 1) (f : k⟦X⟧)
    : evalSeriesAlgHom hY f = evalSeries Y f := rfl

theorem evalSeries_sub (hY : Y ∈ filtration k H 1) (f g : k⟦X⟧)
    : evalSeries Y (f - g) = evalSeries Y f - evalSeries Y g :=
  map_sub (evalSeriesAlgHom hY) f g

theorem evalSeries_pow (hY : Y ∈ filtration k H 1) (f : k⟦X⟧) (m : ℕ)
    : evalSeries Y (f ^ m) = evalSeries Y f ^ m :=
  map_pow (evalSeriesAlgHom hY) f m

/-- Substitution is evaluation at the evaluated inner series. -/
theorem evalSeries_subst (hY : Y ∈ filtration k H 1) (f g : k⟦X⟧) (hg : constantCoeff g = 0) :
    evalSeries Y (f.subst g) = evalSeries (evalSeries Y g) f := by
  have hZ := evalSeries_mem_filtration (Y := Y) g hg
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  refine ext_comp (k := k) _ _ fun n => ?_
  have hdiff : proj k n (evalSeries Y ((f - (trunc (n + 1) f : k⟦X⟧)).subst g)) = 0 := by
    refine comp_evalSeries_eq_zero_of_coeff _ fun m hm => ?_
    refine coeff_of_lt_order m ?_
    refine lt_of_lt_of_le ?_ (le_order_subst_left' hg)
    refine lt_of_lt_of_le (show (m : ℕ∞) < ((n + 1 : ℕ)
        : ℕ∞) by exact_mod_cast Nat.lt_succ_of_le hm) ?_
    refine nat_le_order _ _ fun i hi => ?_
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hi, sub_self]
  rw [subst_sub hgs, evalSeries_sub hY, map_sub, sub_eq_zero] at hdiff
  have hpoly := Polynomial.aeval_algHom_apply (evalSeriesAlgHom hY) g (trunc (n + 1) f)
  simp only [evalSeriesAlgHom_apply] at hpoly
  rw [hdiff, subst_coe hgs, comp_evalSeries_eq_comp_aeval_trunc hZ _ (Nat.lt_succ_self n), hpoly]

/-! ## Graded maps and commuting evaluations -/

/-- A `k`-linear map commuting with the projections and with powers of `Y` commutes with
evaluation at `Y`. -/
theorem map_evalSeries {H' : Type*} [Ring H'] [Algebra k H'] [CompleteGradedAlgebra k H']
    (ψ : H →ₗ[k] H') (hψ : ∀ n x, proj k n (ψ x) = ψ (proj k n x))
    (hpow : ∀ m, ψ (Y ^ m) = ψ Y ^ m) (f : k⟦X⟧) :
    ψ (evalSeries Y f) = evalSeries (ψ Y) f := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [hψ, comp_evalSeries, comp_evalSeries, map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [map_smul, ← hψ, hpow]

/-- Graded algebra homomorphisms commute with evaluation. -/
theorem algHom_evalSeries {H' : Type*} [Ring H'] [Algebra k H'] [CompleteGradedAlgebra k H']
    (φ : H →ₐ[k] H') (hφ : ∀ n x, proj k n (φ x) = φ (proj k n x)) (f : k⟦X⟧) :
    φ (evalSeries Y f) = evalSeries (φ Y) f :=
  map_evalSeries φ.toLinearMap hφ (fun m => map_pow φ Y m) f

omit [CompleteGradedAlgebra k H] in
theorem commute_aeval {a b : H} (hab : Commute a b) (p q : Polynomial k) :
    Commute (Polynomial.aeval a p) (Polynomial.aeval b q) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  exact Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((hab.pow_pow i j).smul_left _).smul_right _

theorem commute_evalSeries {a b : H} (ha : a ∈ filtration k H 1) (hb : b ∈ filtration k H 1)
    (hab : Commute a b) (f g : k⟦X⟧) : Commute (evalSeries a f) (evalSeries b g) := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [comp_mul_eq_of_comp _ (Polynomial.aeval a (trunc (n + 1) f)) _
      (Polynomial.aeval b (trunc (n + 1) g)) n
      (fun i hi => (comp_aeval_trunc_eq ha f hi).symm)
        (fun i hi => (comp_aeval_trunc_eq hb g hi).symm),
    comp_mul_eq_of_comp _ (Polynomial.aeval b (trunc (n + 1) g)) _
      (Polynomial.aeval a (trunc (n + 1) f)) n
      (fun i hi => (comp_aeval_trunc_eq hb g hi).symm)
        (fun i hi => (comp_aeval_trunc_eq ha f hi).symm),
    (commute_aeval hab _ _).eq]

/-! ## Exponential and logarithm -/

variable [CharZero k]

variable (k) in
/-- The exponential `exp Y = ∑ Y^m/m!` of `Y ∈ H_{≥1}`. -/
def cexp (Y : H) : H := evalSeries Y (exp k)

variable (k) in
/-- The logarithm `log g = log(1 + (g - 1))` of `g ∈ 1 + H_{≥1}`. -/
def clog (g : H) : H := evalSeries (g - 1) (log k)

theorem constantCoeff_exp_sub_one : constantCoeff (exp k - 1) = 0 := by
  rw [map_sub, constantCoeff_exp, map_one, sub_self]

theorem cexp_sub_one (hY : Y ∈ filtration k H 1) : cexp k Y - 1 = evalSeries Y (exp k - 1) := by
  rw [evalSeries_sub hY, evalSeries_one hY, cexp]

theorem cexp_sub_one_mem (hY : Y ∈ filtration k H 1) : cexp k Y - 1 ∈ filtration k H 1 := by
  rw [cexp_sub_one hY]
  exact evalSeries_mem_filtration _ constantCoeff_exp_sub_one

theorem clog_mem (g : H) : clog k g ∈ filtration k H 1 :=
  evalSeries_mem_filtration _ (constantCoeff_log : constantCoeff (log k) = 0)

/-- `log (exp Y) = Y`. -/
theorem clog_cexp (hY : Y ∈ filtration k H 1) : clog k (cexp k Y) = Y := by
  rw [clog, cexp_sub_one hY, ← evalSeries_subst hY _ _ constantCoeff_exp_sub_one,
    log_subst_exp_sub_one, evalSeries_X hY]

/-- `exp (log g) = g`. -/
theorem cexp_clog {g : H} (hg : g - 1 ∈ filtration k H 1) : cexp k (clog k g) = g := by
  rw [cexp, clog, ← evalSeries_subst hg _ _ (constantCoeff_log : constantCoeff (log k) = 0),
    exp_subst_log, evalSeries_add, evalSeries_one hg, evalSeries_X hg, add_sub_cancel]

theorem cexp_injective {Y Y' : H} (hY : Y ∈ filtration k H 1) (hY' : Y' ∈ filtration k H 1)
    (h : cexp k Y = cexp k Y') : Y = Y' := by
  rw [← clog_cexp hY, h, clog_cexp hY']

theorem clog_injective {g g' : H} (hg : g - 1 ∈ filtration k H 1) (hg' : g' - 1 ∈ filtration k H 1)
    (h : clog k g = clog k g') : g = g' := by
  rw [← cexp_clog hg, h, cexp_clog hg']

theorem cexp_zero : cexp k (0 : H) = 1 := by
  refine ext_comp (k := k) _ _ fun n => ?_
  rw [cexp, comp_evalSeries, sum_eq_single 0]
  · rw [pow_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_exp, one_smul]
  · intro m _ hm
    rw [zero_pow hm, map_zero, smul_zero]
  · intro h; exact absurd (mem_range.2 (Nat.succ_pos n)) h

theorem comp_zero_cexp (Y : H) : proj k 0 (cexp k Y) = 1 := by
  rw [cexp, comp_evalSeries, sum_range_one, pow_zero, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_exp, one_smul, comp_one, if_pos rfl]

/-- Graded algebra homomorphisms commute with `exp` and `log`. -/
theorem algHom_cexp {H' : Type*} [Ring H'] [Algebra k H'] [CompleteGradedAlgebra k H']
    (φ : H →ₐ[k] H') (hφ : ∀ n x, proj k n (φ x) = φ (proj k n x)) (Y : H) :
    φ (cexp k Y) = cexp k (φ Y) :=
  algHom_evalSeries φ hφ _

theorem algHom_clog {H' : Type*} [Ring H'] [Algebra k H'] [CompleteGradedAlgebra k H']
    (φ : H →ₐ[k] H') (hφ : ∀ n x, proj k n (φ x) = φ (proj k n x)) (g : H) :
    φ (clog k g) = clog k (φ g) := by
  rw [clog, algHom_evalSeries φ hφ, map_sub, map_one, clog]

omit [CompleteGradedAlgebra k H] in
theorem coeff_exp_mul_choose (i j : ℕ) :
    ((i + j).choose i : k) * coeff (i + j) (exp k) = coeff i (exp k) * coeff j (exp k) := by
  simp only [coeff_exp]
  rw [← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  rw [Nat.cast_choose ℚ (Nat.le_add_right i j), Nat.add_sub_cancel_left]
  have h1 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h3 : ((i + j).factorial : ℚ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  field_simp

/-- `exp(x + y) = exp x · exp y` for commuting `x, y ∈ H_{≥1}`. -/
theorem cexp_add_of_commute {x y : H} (hx : x ∈ filtration k H 1) (hy : y ∈ filtration k H 1)
    (hxy : Commute x y) : cexp k (x + y) = cexp k x * cexp k y := by
  refine ext_comp (k := k) _ _ fun n => ?_
  set c : ℕ → k := fun i => coeff i (exp k)
  set g : ℕ × ℕ → H := fun p => (c p.1 * c p.2) • proj k n (x ^ p.1 * y ^ p.2)
  have hvan : ∀ p : ℕ × ℕ, n < p.1 + p.2 → g p = 0 := fun p hp => by
    simp only [g]
    rw [mul_mem_filtration (pow_mem_filtration hx p.1) (pow_mem_filtration hy p.2) n hp, smul_zero]
  -- the product side
  have hL : proj k n (cexp k x * cexp k y) = ∑ p ∈ range (n + 1) ×ˢ range (n + 1), g p := by
    rw [cexp, cexp, comp_mul_eq_of_comp _ (Polynomial.aeval x (trunc (n + 1) (exp k))) _
        (Polynomial.aeval y (trunc (n + 1) (exp k))) n
        (fun i hi => (comp_aeval_trunc_eq hx _ hi).symm)
          (fun i hi => (comp_aeval_trunc_eq hy _ hi).symm),
      Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt _ n),
      Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt _ n), sum_mul_sum]
    simp only [map_sum]
    rw [sum_product]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    rw [coeff_trunc, coeff_trunc, if_pos (mem_range.1 hi), if_pos (mem_range.1 hj), smul_mul_smul,
      map_smul]
  -- the sum side
  have hR : proj k n (cexp k (x + y)) =
      ∑ m ∈ range (n + 1), ∑ p ∈ antidiagonal m, g p := by
    rw [cexp, comp_evalSeries_eq_of_le (add_mem hx hy) _ (Nat.lt_succ_self n)]
    refine sum_congr rfl fun m _ => ?_
    rw [hxy.add_pow', map_sum, smul_sum]
    refine sum_congr rfl fun p hp => ?_
    rw [mem_antidiagonal] at hp
    subst hp
    simp only [g, ← Nat.cast_smul_eq_nsmul k]
    rw [map_smul, smul_smul, mul_comm, coeff_exp_mul_choose]
  rw [hR, hL, sum_sigma']
  rw [← sum_filter_add_sum_filter_not (range (n + 1) ×ˢ range (n + 1))
    (fun p : ℕ × ℕ => p.1 + p.2 < n + 1)]
  rw [sum_eq_zero (s := filter (fun p : ℕ × ℕ => ¬ p.1 + p.2 < n + 1)
    (range (n + 1) ×ˢ range (n + 1)))
    (fun p hp => hvan p (by rw [mem_filter] at hp; omega)), add_zero]
  refine sum_bij' (fun q _ => q.2) (fun p _ => ⟨p.1 + p.2, p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, p⟩ hq
    rw [mem_sigma, mem_range, mem_antidiagonal] at hq
    rw [mem_filter, mem_product, mem_range, mem_range]
    omega
  · rintro p hp
    rw [mem_filter, mem_product, mem_range, mem_range] at hp
    rw [mem_sigma, mem_range, mem_antidiagonal]
    exact ⟨hp.2, rfl⟩
  · rintro ⟨m, p⟩ hq
    rw [mem_sigma, mem_antidiagonal] at hq
    simp [hq.2]
  · rintro p _; rfl
  · rintro ⟨m, p⟩ _; rfl

theorem cexp_neg_mul_cexp (hY : Y ∈ filtration k H 1) : cexp k (-Y) * cexp k Y = 1 := by
  rw [← cexp_add_of_commute (neg_mem hY) hY (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    cexp_zero]

theorem cexp_mul_cexp_neg (hY : Y ∈ filtration k H 1) : cexp k Y * cexp k (-Y) = 1 := by
  rw [← cexp_add_of_commute hY (neg_mem hY) (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
    cexp_zero]

/-- `log (gh) = log g + log h` for commuting `g, h ∈ 1 + H_{≥1}`. -/
theorem clog_mul_of_commute {g h : H} (hg : g - 1 ∈ filtration k H 1) (hh
    : h - 1 ∈ filtration k H 1)
    (hgh : Commute g h) : clog k (g * h) = clog k g + clog k h := by
  have hc : Commute (clog k g) (clog k h) :=
    commute_evalSeries hg hh ((hgh.sub_left (Commute.one_left h)).sub_right
      (Commute.one_right _)) _ _
  have hmul : g * h - 1 ∈ filtration k H 1 := by
    have : g * h - 1 = (g - 1) * h + (h - 1) := by noncomm_ring
    rw [this]
    exact add_mem (by simpa using mul_mem_filtration hg (mem_filtration_zero h)) hh
  refine cexp_injective (clog_mem (g * h)) (add_mem (clog_mem g) (clog_mem h)) ?_
  rw [cexp_clog hmul, cexp_add_of_commute (clog_mem g) (clog_mem h) hc, cexp_clog hg, cexp_clog hh]

/-- A left inverse of `g ∈ 1 + H_{≥1}` has the negated logarithm. -/
theorem clog_eq_neg_of_mul_eq_one {g g' : H} (hg : g - 1 ∈ filtration k H 1) (h : g' * g = 1) :
    clog k g' = -clog k g := by
  have hL := clog_mem (k := k) g
  have he1 : g * cexp k (-clog k g) = 1 := by
    have := cexp_mul_cexp_neg hL
    rwa [cexp_clog hg] at this
  have hg' : g' = cexp k (-clog k g) := by
    calc g' = g' * (g * cexp k (-clog k g)) := by rw [he1, mul_one]
      _ = (g' * g) * cexp k (-clog k g) := by rw [mul_assoc]
      _ = cexp k (-clog k g) := by rw [h, one_mul]
  rw [hg', clog_cexp (neg_mem hL)]

/-! ## Truncations modulo `H_{≥3}` -/

omit [CompleteGradedAlgebra k H] [CharZero k] in
theorem aeval_trunc_three (f : k⟦X⟧) (Z : H) :
    Polynomial.aeval Z (trunc 3 f) =
      algebraMap k H (coeff 0 f) + coeff 1 f • Z + coeff 2 f • Z ^ 2 := by
  rw [Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt f 2)]
  simp only [sum_range_succ, sum_range_zero, zero_add, coeff_trunc, pow_zero, pow_one]
  norm_num [Algebra.smul_def]

omit [CompleteGradedAlgebra k H] in
theorem coeff_exp_low : coeff 0 (exp k) = 1 ∧ coeff 1 (exp k) = 1 ∧ coeff 2 (exp k) = (2
    : k)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_exp, Nat.factorial]

omit [CompleteGradedAlgebra k H] in
theorem coeff_log_low : coeff 0 (log k) = 0 ∧ coeff 1 (log k) = 1 ∧ coeff 2 (log k) = -(2
    : k)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_log]; norm_num

/-- `exp Y ≡ 1 + Y + Y²/2` modulo `H_{≥3}`. -/
theorem cexp_sub_mem_filtration_three (hY : Y ∈ filtration k H 1) :
    cexp k Y - (1 + Y + (2 : k)⁻¹ • Y ^ 2) ∈ filtration k H 3 := by
  have h := evalSeries_sub_aeval_trunc_mem hY (exp k) 3
  obtain ⟨h0, h1, h2⟩ := coeff_exp_low (k := k)
  rw [aeval_trunc_three, h0, h1, h2, map_one, one_smul] at h
  exact h

/-- `log(1 + Z) ≡ Z - Z²/2` modulo `H_{≥3}`. -/
theorem clog_sub_mem_filtration_three {g : H} (hg : g - 1 ∈ filtration k H 1) :
    clog k g - ((g - 1) - (2 : k)⁻¹ • (g - 1) ^ 2) ∈ filtration k H 3 := by
  have h := evalSeries_sub_aeval_trunc_mem hg (log k) 3
  obtain ⟨h0, h1, h2⟩ := coeff_log_low (k := k)
  rw [aeval_trunc_three, h0, h1, h2, map_zero, zero_add, one_smul, neg_smul,
    ← sub_eq_add_neg] at h
  exact h

/-- The Baker–Campbell–Hausdorff element `log(exp X exp Y)`. -/
def bch (X' Y' : H) : H := clog k (cexp k X' * cexp k Y')

omit [CharZero k] in
theorem mul_mem_filtration_three {a b c : H} (ha : a ∈ filtration k H 1) (hb : b ∈ filtration k H 1)
    (hc : c ∈ filtration k H 1) : a * b * c ∈ filtration k H 3 :=
  mul_mem_filtration (mul_mem_filtration ha hb) hc

omit [CharZero k] in
theorem mem_filtration_three_of_mul {a b : H} {i j : ℕ} (hij : 3 ≤ i + j)
    (ha : a ∈ filtration k H i) (hb : b ∈ filtration k H j) : a * b ∈ filtration k H 3 :=
  filtration_antitone hij (mul_mem_filtration ha hb)

/-- **BCH modulo degree three**: `log(exp X exp Y) ≡ X + Y + ½[X, Y]` modulo `H_{≥3}`. -/
theorem bch_sub_mem_filtration_three {X' Y' : H} (hX : X' ∈ filtration k H 1)
    (hY : Y' ∈ filtration k H 1) :
    bch (k := k) X' Y' - (X' + Y' + (2 : k)⁻¹ • (X' * Y' - Y' * X')) ∈ filtration k H 3 := by
  set h : k := (2 : k)⁻¹
  set g := cexp k X' * cexp k Y'
  set Z := g - 1
  set S := X' + Y' + X' * Y' + h • X' ^ 2 + h • Y' ^ 2
  have hall : ∀ a : H, a ∈ filtration k H 0 := mem_filtration_zero
  have hZ : Z ∈ filtration k H 1 := by
    have : Z = (cexp k X' - 1) * cexp k Y' + (cexp k Y' - 1) := by simp only [Z, g]; noncomm_ring
    rw [this]
    exact add_mem (by simpa using mul_mem_filtration (cexp_sub_one_mem hX) (hall (cexp k Y')))
      (cexp_sub_one_mem hY)
  have hRX := cexp_sub_mem_filtration_three hX
  have hRY := cexp_sub_mem_filtration_three hY
  set RX := cexp k X' - (1 + X' + h • X' ^ 2)
  set RY := cexp k Y' - (1 + Y' + h • Y' ^ 2)
  have hX2 : X' ^ 2 ∈ filtration k H 2 := pow_mem_filtration hX 2
  have hY2 : Y' ^ 2 ∈ filtration k H 2 := pow_mem_filtration hY 2
  -- `Z ≡ S`
  have hZS : Z - S ∈ filtration k H 3 := by
    have key : Z - S = RX * cexp k Y' + (1 + X' + h • X' ^ 2) * RY +
        (h • (X' * Y' ^ 2) + h • (X' ^ 2 * Y') + (h * h) • (X' ^ 2 * Y' ^ 2)) := by
      simp only [Z, g, S, RX, RY, mul_add, add_mul, mul_one, one_mul, mul_sub, sub_mul,
        smul_mul_assoc, mul_smul_comm, sq, mul_assoc]
      module
    rw [key]
    refine add_mem (add_mem (mem_filtration_three_of_mul (by norm_num) hRX (hall _))
      (mem_filtration_three_of_mul (by norm_num) (hall _) hRY)) (add_mem (add_mem ?_ ?_) ?_)
    · exact Submodule.smul_mem _ _ (mem_filtration_three_of_mul (by norm_num) hX hY2)
    · exact Submodule.smul_mem _ _ (mem_filtration_three_of_mul (by norm_num) hX2 hY)
    · exact Submodule.smul_mem _ _ (mem_filtration_three_of_mul (by norm_num) hX2 hY2)
  -- `Z² ≡ (X + Y)²`
  have hT : Z - (X' + Y') ∈ filtration k H 2 := by
    have : Z - (X' + Y') = (Z - S) + (X' * Y' + h • X' ^ 2 + h • Y' ^ 2) := by
      simp only [S]; abel
    rw [this]
    exact add_mem (filtration_antitone (by norm_num) hZS)
      (add_mem (add_mem (mul_mem_filtration hX hY) (Submodule.smul_mem _ _ hX2))
        (Submodule.smul_mem _ _ hY2))
  have hXY1 : X' + Y' ∈ filtration k H 1 := add_mem hX hY
  have hsq : Z ^ 2 - (X' + Y') ^ 2 ∈ filtration k H 3 := by
    have : Z ^ 2 - (X' + Y') ^ 2 =
        (X' + Y') * (Z - (X' + Y')) + (Z - (X' + Y')) * (X' + Y') +
          (Z - (X' + Y')) * (Z - (X' + Y')) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (mem_filtration_three_of_mul (by norm_num) hXY1 hT)
      (mem_filtration_three_of_mul (by norm_num) hT hXY1))
      (mem_filtration_three_of_mul (by norm_num) hT hT)
  have hlog := clog_sub_mem_filtration_three (k := k) (show g - 1 ∈ filtration k H 1 from hZ)
  have key : bch (k := k) X' Y' - (X' + Y' + h • (X' * Y' - Y' * X')) =
      (clog k g - ((g - 1) - h • (g - 1) ^ 2)) + (Z - S) - h • (Z ^ 2 - (X' + Y') ^ 2) +
        (S - h • (X' + Y') ^ 2 - (X' + Y' + h • (X' * Y' - Y' * X'))) := by
    simp only [bch, Z, g]; module
  have hzero : S - h • (X' + Y') ^ 2 - (X' + Y' + h • (X' * Y' - Y' * X')) = 0 := by
    simp only [S, sq, add_mul, mul_add, smul_add, smul_sub]
    simp only [h]
    module
  rw [key, hzero, add_zero]
  exact sub_mem (add_mem hlog hZS) (Submodule.smul_mem _ _ hsq)

end CompleteGradedAlgebra

end GaloisForLFunctions.HTGeometry
