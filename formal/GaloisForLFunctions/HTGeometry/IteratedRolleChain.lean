import Mathlib

/-!
# The iterated Rolle chain

If a smooth function vanishes to order `μ` at the origin and has one further zero at `s > 0`, then
its `μ`-th derivative already has a zero inside `(0, s)`.

This is the multiplicity-carrying half of Rolle's theorem: each order of vanishing at the origin
consumes one derivative, and the extra zero at `s` supplies the Rolle point.  It is the step that
converts a zero of high order at one point plus a single zero elsewhere into a genuine zero of a
high derivative, which is what Descartes-type bounds for exponential sums are applied to.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **Iterated Rolle.**  If `f` is smooth, vanishes together with its first `μ - 1` derivatives at
the origin, and vanishes again at some `s > 0`, then `f^{(μ)}` has a zero in `(0, s)`. -/
theorem exists_iteratedDeriv_eq_zero_of_order {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ μ : ℕ, 1 ≤ μ → (∀ j < μ, iteratedDeriv j f 0 = 0) →
      ∀ {s : ℝ}, 0 < s → f s = 0 → ∃ r ∈ Ioo (0 : ℝ) s, iteratedDeriv μ f r = 0 := by
  intro μ
  induction μ with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hvan s hs hfs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- base case `μ = 1`: plain Rolle on `[0, s]`
      subst hn
      have h0 : f 0 = 0 := by
        have := hvan 0 (by omega)
        simpa [iteratedDeriv_zero] using this
      have hcont : ContinuousOn f (Icc 0 s) :=
        (hf.continuous).continuousOn
      obtain ⟨r, hr, hderiv⟩ := exists_deriv_eq_zero hs hcont (by rw [h0, hfs])
      refine ⟨r, hr, ?_⟩
      rw [iteratedDeriv_one]
      exact hderiv
    · -- inductive step: use the chain for `n`, then one more Rolle at the origin
      obtain ⟨r, hr, hzero⟩ := ih hn (fun j hj => hvan j (by omega)) hs hfs
      have hn0 : iteratedDeriv n f 0 = 0 := hvan n (by omega)
      have hcont : ContinuousOn (iteratedDeriv n f) (Icc 0 r) := by
        have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv^[n] f) := hf.iterate_deriv n
        rw [iteratedDeriv_eq_iterate]
        exact hd.continuous.continuousOn
      obtain ⟨r', hr', hderiv⟩ := exists_deriv_eq_zero hr.1 hcont (by rw [hn0, hzero])
      refine ⟨r', ⟨hr'.1, lt_trans hr'.2 hr.2⟩, ?_⟩
      rw [iteratedDeriv_succ]
      exact hderiv

end GaloisForLFunctions.HTGeometry
