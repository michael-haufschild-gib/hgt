import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Composition at the first nonzero inner jet

If the derivatives of an inner function vanish through order `m - 1`, the `m`th derivative of a
composition contains only the first derivative of the outer function.  This is the all-order
critical-jet reduction needed by finite-criticality Feigenbaum value laws.
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions

/-- **First-nonzero-inner-jet composition law.**  If all positive derivatives of `g` below `m`
vanish at `x`, then
`(h ∘ g)⁽ᵐ⁾(x) = h'(g(x)) * g⁽ᵐ⁾(x)`.

The proof differentiates the ordinary chain rule `m - 1` more times.  In the Leibniz sum, every
term except the one carrying the full `m`th inner derivative contains a positive inner derivative
of order below `m` and vanishes. -/
theorem iteratedDeriv_comp_of_firstNonzero_innerJet
    {h g : ℂ → ℂ} {x : ℂ} {m : ℕ} (hm : 0 < m)
    (hh : ContDiff ℂ m h) (hg : ContDiff ℂ m g)
    (hvanish : ∀ k : ℕ, 0 < k → k < m → iteratedDeriv k g x = 0) :
    iteratedDeriv m (h ∘ g) x = deriv h (g x) * iteratedDeriv m g x := by
  let n := m - 1
  have hmn : m = n + 1 := by simp [n, Nat.sub_add_cancel hm]
  have hnle : n ≤ m := by omega
  have hdiffh : Differentiable ℂ h := hh.differentiable (by norm_cast; exact hm.ne')
  have hdiffg : Differentiable ℂ g := hg.differentiable (by norm_cast; exact hm.ne')
  have hderiv : deriv (h ∘ g) = fun y => deriv h (g y) * deriv g y := by
    funext y
    exact deriv_comp y hdiffh.differentiableAt hdiffg.differentiableAt
  rw [hmn, iteratedDeriv_succ', hderiv]
  have hdh : ContDiff ℂ n (deriv h) := by
    rw [hmn] at hh
    exact hh.deriv'
  have hdg : ContDiff ℂ n (deriv g) := by
    rw [hmn] at hg
    exact hg.deriv'
  have hgn : ContDiff ℂ n g := hg.of_le (by exact_mod_cast hnle)
  change iteratedDeriv n ((deriv h ∘ g) * deriv g) x = _
  rw [iteratedDeriv_mul (hdh.comp hgn).contDiffAt hdg.contDiffAt]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, iteratedDeriv_zero, Function.comp_apply,
      Nat.sub_zero, Nat.cast_one, one_mul]
    rw [← congrFun (iteratedDeriv_succ' (n := n) (f := g)) x]
  · intro i hi hi0
    rw [Finset.mem_range] at hi
    have hki_pos : 0 < n - i + 1 := Nat.succ_pos _
    have hki_lt : n - i + 1 < m := by omega
    have hz := hvanish (n - i + 1) hki_pos hki_lt
    rw [congrFun (iteratedDeriv_succ' (n := n - i) (f := g)) x] at hz
    rw [hz, mul_zero]
  · simp

end GaloisForLFunctions
