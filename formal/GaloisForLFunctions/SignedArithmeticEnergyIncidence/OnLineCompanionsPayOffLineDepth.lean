import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic

/-!
# On-line companions pay off-line depth: a local signed sampling law

Near a height `t`, a source of bounded aperture is locally a function with finitely many degrees
of freedom; the **local model** takes it to be a polynomial `p` of degree `< n`.  In this model the
zero-side form of a configuration near `t` is

`Q(p) = Σ_{i ∈ s} p(γ_i)² − w · p'(t)²`:

on-line zeros (companions) at heights `γ_i` contribute the squares `p(γ_i)²`, and an off-line
cluster at height `t` of squared-depth mass `w` contributes `−w p'(t)²` (the depth-squared law of
an off-line quartet: its deviation from an on-line pair is `−δ² |Φ'(t)|²` to leading order).
Unsigned sampling bounds the negative term by the local depth mass alone; the signed form can also
spend the companions.

* **Lagrange identity** (`derivative_eval_eq_sum`): with at least as many companions as degrees of
  freedom, `p'(t) = Σ_i p(γ_i) ℓ_i'(t)` for the Lagrange basis `ℓ_i` of the companions.
* **Companions pay** (`companions_pay`): then `Q ≥ 0` whenever `w · Λ(t) ≤ 1`,
  `Λ(t) = Σ_i ℓ_i'(t)²` — the off-line depth is paid by the on-line companions at the explicit
  Lagrange price, whatever the local depth mass is per companion.
* **Too few companions never pay** (`few_companions_never_pay`): if the source has two more degrees
  of freedom than there are companions, `p = (X − t) · Π_i (X − γ_i)` vanishes at every companion
  with `p'(t) ≠ 0`, and `Q(p) < 0` for every positive depth mass.

* **Beyond the local model** (`companions_pay_up_to_error`): for an arbitrary source `f`, any
  polynomial `p` of degree `< #s` transfers the law at half the price: if `2 w Λ(t) ≤ 1` then
  `Σ f(γ_i)² − w f'(t)² ≥ −(2 Σ (f − p)(γ_i)² + 4 w (f'(t) − p'(t))²)`.  The loss is the local
  approximation error at the companions and at `t`, e.g. a Taylor remainder.

So in the local model the signed floor is governed by a **companion count against the source's
local degrees of freedom**, not by the unsigned local depth mass: this is the signed replacement
mechanism of open question O5, in the stated model.  Transferring it to Paley–Wiener sources of
aperture `A` and the actual zeros of `ζ` (with `≍ A` local degrees of freedom per unit height and
`≍ log T` companions) is open.
-/

open Polynomial Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}

/-- The local signed sampling form: companions `v i`, off-line depth mass `w` at height `t`. -/
def companionForm (s : Finset ι) (v : ι → ℝ) (w t : ℝ) (p : ℝ[X]) : ℝ :=
  ∑ i ∈ s, (p.eval (v i)) ^ 2 - w * ((derivative p).eval t) ^ 2

/-- The Lagrange price `Λ(t) = Σ_i ℓ_i'(t)²` of the companions. -/
def lagrangePrice (s : Finset ι) (v : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, ((derivative (Lagrange.basis s v i)).eval t) ^ 2

theorem lagrangePrice_nonneg (t : ℝ) : 0 ≤ lagrangePrice s v t :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- **Lagrange identity for the derivative.** -/
theorem derivative_eval_eq_sum (hvs : Set.InjOn v s) {p : ℝ[X]} (hp : p.degree < #s) (t : ℝ) :
    (derivative p).eval t =
      ∑ i ∈ s, p.eval (v i) * (derivative (Lagrange.basis s v i)).eval t := by
  conv_lhs => rw [Lagrange.eq_interpolate hvs hp]
  rw [Lagrange.interpolate_apply, derivative_sum, eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul, eval_mul, eval_C]

/-- The derivative at `t` is controlled by the companion values at the Lagrange price. -/
theorem derivative_eval_sq_le (hvs : Set.InjOn v s) {p : ℝ[X]} (hp : p.degree < #s) (t : ℝ) :
    ((derivative p).eval t) ^ 2 ≤ lagrangePrice s v t * ∑ i ∈ s, (p.eval (v i)) ^ 2 := by
  rw [derivative_eval_eq_sum hvs hp, mul_comm]
  exact sum_mul_sq_le_sq_mul_sq s _ _

/-- **On-line companions pay off-line depth** at the Lagrange price. -/
theorem companions_pay (hvs : Set.InjOn v s) {p : ℝ[X]} (hp : p.degree < #s) {w t : ℝ}
    (hw : 0 ≤ w) (hΛ : w * lagrangePrice s v t ≤ 1) : 0 ≤ companionForm s v w t p := by
  unfold companionForm
  have h := derivative_eval_sq_le hvs hp t
  have hS : 0 ≤ ∑ i ∈ s, (p.eval (v i)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h2 : w * ((derivative p).eval t) ^ 2 ≤ w * lagrangePrice s v t * ∑ i ∈ s, (p.eval (v i)) ^ 2 := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hw
  have h3 : w * lagrangePrice s v t * ∑ i ∈ s, (p.eval (v i)) ^ 2 ≤ ∑ i ∈ s, (p.eval (v i)) ^ 2 := by
    calc _ ≤ 1 * ∑ i ∈ s, (p.eval (v i)) ^ 2 := mul_le_mul_of_nonneg_right hΛ hS
      _ = _ := one_mul _
  linarith

omit [DecidableEq ι] in
/-- **Too few companions never pay**: a source with two more degrees of freedom than there are
companions defeats every positive depth mass. -/
theorem few_companions_never_pay {t : ℝ} (ht : ∀ i ∈ s, v i ≠ t) {w : ℝ} (hw : 0 < w) :
    ∃ p : ℝ[X], p.natDegree = #s + 1 ∧ companionForm s v w t p < 0 := by
  set N := Lagrange.nodal s v with hN
  refine ⟨(X - C t) * N, ?_, ?_⟩
  · rw [natDegree_mul (X_sub_C_ne_zero t) Lagrange.nodal_ne_zero, natDegree_X_sub_C,
      Lagrange.natDegree_nodal, add_comm]
  · unfold companionForm
    have hzero : ∀ i ∈ s, ((X - C t) * N).eval (v i) = 0 := by
      intro i hi
      rw [eval_mul, hN, Lagrange.eval_nodal_at_node hi, mul_zero]
    rw [sum_eq_zero fun i hi => by rw [hzero i hi]; norm_num, zero_sub]
    have hd : (derivative ((X - C t) * N)).eval t = N.eval t := by
      rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
    have hNt : N.eval t ≠ 0 := by
      rw [hN, Lagrange.eval_nodal, prod_ne_zero_iff]
      exact fun i hi => sub_ne_zero.mpr (ht i hi).symm
    rw [hd]
    have : 0 < (N.eval t) ^ 2 := by positivity
    nlinarith

/-! ### Beyond the local model -/

/-- The signed sampling form of an arbitrary source `f` with derivative value `f't` at `t`. -/
def sampleForm (s : Finset ι) (v : ι → ℝ) (w : ℝ) (f : ℝ → ℝ) (f't : ℝ) : ℝ :=
  ∑ i ∈ s, f (v i) ^ 2 - w * f't ^ 2

/-- **Companions pay up to the local approximation error.**  If a polynomial `p` of degree
`< #s` approximates the source at the companions with errors `e_i = f(γ_i) − p(γ_i)` and its
derivative at `t` with error `e₀ = f'(t) − p'(t)`, then at half the Lagrange price
(`2 w Λ(t) ≤ 1`) the signed form loses at most `2 Σ e_i² + 4 w e₀²`. -/
theorem companions_pay_up_to_error (hvs : Set.InjOn v s) {p : ℝ[X]} (hp : p.degree < #s)
    {w t : ℝ} (hw : 0 ≤ w) (hΛ : 2 * w * lagrangePrice s v t ≤ 1) (f : ℝ → ℝ) (f't : ℝ) :
    -(2 * ∑ i ∈ s, (f (v i) - p.eval (v i)) ^ 2 + 4 * w * (f't - (derivative p).eval t) ^ 2) ≤
      sampleForm s v w f f't := by
  set Λ := lagrangePrice s v t
  set e₀ := f't - (derivative p).eval t
  set S := ∑ i ∈ s, f (v i) ^ 2
  set E := ∑ i ∈ s, (f (v i) - p.eval (v i)) ^ 2
  have hΛ0 : 0 ≤ Λ := lagrangePrice_nonneg t
  -- `f'(t) = Σ f(γ_i) ℓ_i'(t) − Σ e_i ℓ_i'(t) + e₀`
  have hder := derivative_eval_eq_sum hvs hp t
  have hsplit : f't = ∑ i ∈ s, f (v i) * (derivative (Lagrange.basis s v i)).eval t -
      ∑ i ∈ s, (f (v i) - p.eval (v i)) * (derivative (Lagrange.basis s v i)).eval t + e₀ := by
    rw [← sum_sub_distrib]
    have : ∑ i ∈ s, (f (v i) * (derivative (Lagrange.basis s v i)).eval t -
        (f (v i) - p.eval (v i)) * (derivative (Lagrange.basis s v i)).eval t) =
        (derivative p).eval t := by
      rw [hder]; exact sum_congr rfl fun i _ => by ring
    rw [this]; simp only [e₀]; ring
  have h1 : (∑ i ∈ s, f (v i) * (derivative (Lagrange.basis s v i)).eval t) ^ 2 ≤ Λ * S := by
    rw [mul_comm]; exact sum_mul_sq_le_sq_mul_sq s _ _
  have h2 : (∑ i ∈ s, (f (v i) - p.eval (v i)) * (derivative (Lagrange.basis s v i)).eval t) ^ 2 ≤
      Λ * E := by
    rw [mul_comm]; exact sum_mul_sq_le_sq_mul_sq s _ _
  set a := ∑ i ∈ s, f (v i) * (derivative (Lagrange.basis s v i)).eval t
  set b := ∑ i ∈ s, (f (v i) - p.eval (v i)) * (derivative (Lagrange.basis s v i)).eval t
  -- `(a − b + e₀)² ≤ 2a² + 4b² + 4e₀²`
  have hsq : f't ^ 2 ≤ 2 * a ^ 2 + 4 * b ^ 2 + 4 * e₀ ^ 2 := by
    rw [hsplit]; nlinarith [sq_nonneg (a + b - e₀), sq_nonneg (b + e₀)]
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  unfold sampleForm
  have hwa : w * (2 * a ^ 2) ≤ S := by
    calc w * (2 * a ^ 2) ≤ w * (2 * (Λ * S)) := by nlinarith
      _ = (2 * w * Λ) * S := by ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right hΛ hS
      _ = S := one_mul _
  have hwb : w * (4 * b ^ 2) ≤ 2 * E := by
    calc w * (4 * b ^ 2) ≤ w * (4 * (Λ * E)) := by nlinarith
      _ = 2 * ((2 * w * Λ) * E) := by ring
      _ ≤ 2 * (1 * E) := by nlinarith
      _ = 2 * E := by ring
  nlinarith [mul_le_mul_of_nonneg_left hsq hw]

/-- In the local model the approximation errors vanish and the signed form is nonnegative. -/
theorem sampleForm_eval_nonneg (hvs : Set.InjOn v s) {p : ℝ[X]} (hp : p.degree < #s) {w t : ℝ}
    (hw : 0 ≤ w) (hΛ : 2 * w * lagrangePrice s v t ≤ 1) :
    0 ≤ sampleForm s v w (fun x => p.eval x) ((derivative p).eval t) := by
  have h := companions_pay_up_to_error hvs hp hw hΛ (fun x => p.eval x) ((derivative p).eval t)
  simp only [sub_self, zero_pow two_ne_zero, sum_const_zero, mul_zero, add_zero, neg_zero] at h
  exact h

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
