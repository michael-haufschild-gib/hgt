import Mathlib
import GaloisForLFunctions.HTGeometry.AddPolynomialInvariance

/-!
# Jet agreement across an analytic envelope factor

The quartet-passport realization prescribes, at each packet point `w`, the finite Taylor class of a
polynomial `B` by

`B(w + x) ≡ ε_w · x / A(w + x)  (mod x^{N+2})`,

and then reads off the local behaviour of the realized function `F = A · B`.  This module is the
calculus that performs that read-off.

The bridge from the Hermite/CRT interpolation data (`RHTower/FiniteHermiteCRT.lean`, stated with
`Polynomial.derivative^[n]`) to analytic jets is the tree's existing
`GaloisForLFunctions.HTGeometry.iteratedDeriv_polynomial_eval`, which is reused, not restated.
* `iteratedDeriv_mul_congr` is the transfer step: multiplying by a fixed analytic factor preserves
  agreement of jets to any order.  It is Leibniz's rule (`iteratedDeriv_mul`) plus a termwise
  comparison — no order/valuation bookkeeping and no non-degeneracy hypothesis.
* `iteratedDeriv_envelopeProduct_eq_linear` combines the two: if `B` matches the jets of
  `ε (z-w)/A` to order `N`, then `A · B` matches the jets of the **linear germ** `ε (z-w)` to order
  `N`.  The cancellation `A · (ε(z-w)/A) = ε(z-w)` is only valid where `A ≠ 0`, so it is applied as
  an `EventuallyEq` at `w` and transported by `Filter.EventuallyEq.iteratedDeriv_eq`.
* `simpleZero_of_envelopeProduct_jets` extracts the two lowest jets: `F(w) = 0` and `F'(w) = ε ≠ 0`,
  i.e. every prescribed packet point is a **simple** zero.
-/

noncomputable section

open Complex Polynomial Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry (iteratedDeriv_polynomial_eval)


/-- **Jet transfer under multiplication.**  Multiplying by a fixed analytic factor preserves
agreement of jets up to any order. -/
theorem iteratedDeriv_mul_congr {A f g : ℂ → ℂ} {w : ℂ} {N : ℕ}
    (hA : AnalyticAt ℂ A w) (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (h : ∀ n ≤ N, iteratedDeriv n f w = iteratedDeriv n g w) :
    ∀ n ≤ N, iteratedDeriv n (A * f) w = iteratedDeriv n (A * g) w := by
  intro n hn
  rw [iteratedDeriv_mul (hA.contDiffAt.of_le le_top) (hf.contDiffAt.of_le le_top),
    iteratedDeriv_mul (hA.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  rw [h (n - i) (by omega)]

/-- The envelope-weighted jet target: matching the jets of `ε (z-w)/A` makes the product `A · B`
match the jets of the linear germ `ε (z-w)`. -/
theorem iteratedDeriv_envelopeProduct_eq_linear {A : ℂ → ℂ} {B : Polynomial ℂ} {w ε : ℂ} {N : ℕ}
    (hA : AnalyticAt ℂ A w) (hAw : A w ≠ 0)
    (h : ∀ n ≤ N, iteratedDeriv n (fun z => B.eval z) w
      = iteratedDeriv n (fun z => ε * (z - w) / A z) w) :
    ∀ n ≤ N, iteratedDeriv n (fun z => A z * B.eval z) w
      = iteratedDeriv n (fun z => ε * (z - w)) w := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => ε * (z - w)) w :=
    (analyticAt_const.mul ((analyticAt_id).sub analyticAt_const))
  have hg : AnalyticAt ℂ (fun z : ℂ => ε * (z - w) / A z) w := hlin.div hA hAw
  have hB : AnalyticAt ℂ (fun z : ℂ => B.eval z) w :=
    (Polynomial.differentiable B).analyticAt w
  have hstep := iteratedDeriv_mul_congr hA hB hg h
  intro n hn
  have h1 : iteratedDeriv n (A * fun z : ℂ => B.eval z) w
      = iteratedDeriv n (A * fun z : ℂ => ε * (z - w) / A z) w := hstep n hn
  have hev : (A * fun z : ℂ => ε * (z - w) / A z) =ᶠ[𝓝 w] fun z : ℂ => ε * (z - w) := by
    filter_upwards [hA.continuousAt.eventually_ne hAw] with z hz
    simp only [Pi.mul_apply]
    field_simp
  rw [hev.iteratedDeriv_eq] at h1
  exact h1

/-- A jet match with the linear germ makes `w` a simple zero of the product. -/
theorem simpleZero_of_envelopeProduct_jets {A : ℂ → ℂ} {B : Polynomial ℂ} {w ε : ℂ}
    (_hε : ε ≠ 0)
    (h : ∀ n ≤ 1, iteratedDeriv n (fun z => A z * B.eval z) w
      = iteratedDeriv n (fun z => ε * (z - w)) w) :
    A w * B.eval w = 0 ∧ deriv (fun z => A z * B.eval z) w = ε := by
  constructor
  · have h0 := h 0 (by norm_num)
    simpa using h0
  · have h1 := h 1 (by norm_num)
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    rw [h1]
    have : deriv (fun z : ℂ => ε * (z - w)) w = ε := by
      have hd : HasDerivAt (fun z : ℂ => ε * (z - w)) ε w := by
        simpa using ((hasDerivAt_id w).sub_const w).const_mul ε
      exact hd.deriv
    rw [this]


end RHTower

end
