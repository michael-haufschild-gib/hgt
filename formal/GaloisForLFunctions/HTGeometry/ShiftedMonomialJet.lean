import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Jets of a shifted monomial and of a germ with a flat factor

Two elementary jet computations, both centred at an arbitrary point `ρ` of the complex plane.

The first is the closed form of every iterate of the derivative of `c·(s − ρ)^n`: the falling
factorial appears as the coefficient, so evaluating at `ρ` selects the single index `k = n` and
returns `n!` there and `0` at every other index.

The second says that a germ carrying an explicit flat factor `(s − ρ)^m` has vanishing jets below
order `m`.  The proof differentiates the product once and reuses the statement with `m` lowered by
one, the analytic cofactor absorbing the extra terms.

## Main results

* `iterate_deriv_const_mul_sub_pow`
* `iteratedDeriv_sub_const_pow`
* `iteratedDeriv_eq_zero_of_eventuallyEq_sub_pow_mul`
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Every iterate of the derivative of a shifted monomial, in closed form: the falling factorial
`n.descFactorial k` is the coefficient produced by `k` differentiations. -/
theorem iterate_deriv_const_mul_sub_pow (ρ : ℂ) :
    ∀ (k : ℕ) (c : ℂ) (n : ℕ),
      deriv^[k] (fun s : ℂ => c * (s - ρ) ^ n)
        = fun s : ℂ => c * (n.descFactorial k : ℂ) * (s - ρ) ^ (n - k) := by
  intro k
  induction k with
  | zero => intro c n; funext s; simp
  | succ k ih =>
      intro c n
      rw [Function.iterate_succ_apply]
      have hd : deriv (fun s : ℂ => c * (s - ρ) ^ n)
          = fun s : ℂ => (c * (n : ℂ)) * (s - ρ) ^ (n - 1) := by
        funext s
        have hb : HasDerivAt (fun s : ℂ => s - ρ) 1 s := (hasDerivAt_id s).sub_const ρ
        have h1 : HasDerivAt (fun s : ℂ => c * (s - ρ) ^ n)
            (c * ((n : ℂ) * (s - ρ) ^ (n - 1) * 1)) s := (hb.pow n).const_mul c
        rw [h1.deriv]
        ring
      rw [hd, ih (c * (n : ℂ)) (n - 1)]
      funext s
      cases n with
      | zero => simp
      | succ p =>
          rw [Nat.succ_descFactorial_succ]
          push_cast
          ring

/-- The jets of `(s − ρ)^n` at `ρ`: all vanish except the `n`-th, which is `n!`. -/
theorem iteratedDeriv_sub_const_pow (ρ : ℂ) (k n : ℕ) :
    iteratedDeriv k (fun s : ℂ => (s - ρ) ^ n) ρ = if k = n then ((Nat.factorial n : ℕ) : ℂ) else 0 := by
  have h := iterate_deriv_const_mul_sub_pow ρ k 1 n
  simp only [one_mul] at h
  rw [iteratedDeriv_eq_iterate, h]
  rcases lt_trichotomy k n with hlt | heq | hgt
  · have hne : n - k ≠ 0 := by omega
    have hk : k ≠ n := by omega
    simp [hk, zero_pow hne]
  · subst heq
    simp [Nat.descFactorial_self]
  · have hzero : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hgt
    have hk : k ≠ n := by omega
    simp [hk, hzero]

/-- A germ with an explicit flat factor of order `m` at `ρ` has vanishing jets below `m`. -/
theorem iteratedDeriv_eq_zero_of_eventuallyEq_sub_pow_mul :
    ∀ {n m : ℕ} {f W : ℂ → ℂ} {ρ : ℂ}, AnalyticAt ℂ W ρ →
      f =ᶠ[𝓝 ρ] (fun s : ℂ => (s - ρ) ^ m * W s) → n < m → iteratedDeriv n f ρ = 0 := by
  intro n
  induction n with
  | zero =>
      intro m f W ρ _ hf hn
      rw [iteratedDeriv_zero, hf.eq_of_nhds]
      have hm : m ≠ 0 := by omega
      simp [zero_pow hm]
  | succ n ih =>
      intro m f W ρ hW hf hn
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hWd : AnalyticAt ℂ (deriv W) ρ := hW.deriv
      have hderiv : deriv f =ᶠ[𝓝 ρ]
          fun s : ℂ => (s - ρ) ^ m * (((m : ℂ) + 1) * W s + (s - ρ) * deriv W s) := by
        have h1 : deriv f =ᶠ[𝓝 ρ] deriv (fun s : ℂ => (s - ρ) ^ (m + 1) * W s) := hf.deriv
        refine h1.trans ?_
        filter_upwards [hW.eventually_analyticAt] with s hs
        have hb : HasDerivAt (fun s : ℂ => s - ρ) 1 s := (hasDerivAt_id s).sub_const ρ
        have hd : HasDerivAt (fun w : ℂ => (w - ρ) ^ (m + 1) * W w)
            (((m + 1 : ℕ) : ℂ) * (s - ρ) ^ (m + 1 - 1) * 1 * W s
              + (s - ρ) ^ (m + 1) * deriv W s) s :=
          (hb.pow (m + 1)).mul hs.differentiableAt.hasDerivAt
        rw [hd.deriv]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      have hWana : AnalyticAt ℂ
          (fun s : ℂ => ((m : ℂ) + 1) * W s + (s - ρ) * deriv W s) ρ :=
        (analyticAt_const.mul hW).add ((analyticAt_id.sub analyticAt_const).mul hWd)
      rw [iteratedDeriv_succ']
      exact ih hWana hderiv (by omega)

end GaloisForLFunctions.HTGeometry
