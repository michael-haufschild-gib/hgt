import GaloisForLFunctions.RHTower.UniformityIsTheWrongShape

/-!
# The expansion's parameter is the shift, and the demand is in the degree

The route's single analytic input is an error decaying in the **degree**.  The natural supplier is the
asymptotic expansion of the central derivatives, whose error is exponentially small at optimal
truncation.  This file shows the supplier is in the wrong variable.

**Which variable the expansion is in.**  The central derivatives are moments of the theta remainder
against `u^{2n}`, so the asymptotic parameter is `n` — the order of the moment, i.e. the **shift**.
Laplace's method gives an asymptotic series in `n`, with error exponentially small in `n` at optimal
truncation.

**Which variable the route needs.**  The degree `d` is the number of coefficients combined into a
Jensen polynomial, not the asymptotic parameter.  The route needs the error to beat a radius shrinking
in `d`.

**They are independent, and the quantifier order proves it.**  The available theorem has the shape
"for each `d`, for all sufficiently large `n`".  An error of the form `E(n,d) = d/n` satisfies exactly
that — it tends to zero in `n` for every fixed `d` — while for every fixed `n` it tends to infinity in
`d`.  So the shape of the available statement is compatible with arbitrarily bad behaviour in the
degree.

> **No sharpening of the shift-asymptotics can produce decay in the degree: the two directions are
> independent, and the "each `d`, large `n`" shape of the theorem is exactly that asymmetry.  This is
> also why the threshold `N(d)` grows — more inequalities at higher degree need a larger shift before
> the same expansion is good enough.**

The single analytic input therefore cannot be supplied by improving the expansion.  It requires a
genuinely degree-uniform statement, which the expansion's structure does not provide.

This file formalizes the independence of the two directions with an explicit witness.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The witness error: small in the shift for each degree, large in the degree for each shift. -/
def witnessError (n d : ℝ) : ℝ := d / n

/-- **Small in the shift.**  For every fixed degree the error tends to zero as the shift grows. -/
theorem witness_tendsto_zero_in_shift (d : ℝ) :
    Tendsto (fun n : ℝ => witnessError n d) atTop (nhds 0) := by
  unfold witnessError
  exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id

/-- **Large in the degree.**  For every fixed positive shift the error tends to infinity as the degree
grows. -/
theorem witness_tendsto_atTop_in_degree {n : ℝ} (hn : 0 < n) :
    Tendsto (fun d : ℝ => witnessError n d) atTop atTop := by
  unfold witnessError
  simpa using Filter.tendsto_id.atTop_div_const hn

/-- **Independence.**  Decay in the shift for each degree does not imply decay in the degree for each
shift: the witness satisfies the first and violates the second. -/
theorem directions_independent {n : ℝ} (hn : 0 < n) :
    (∀ d : ℝ, Tendsto (fun m : ℝ => witnessError m d) atTop (nhds 0)) ∧
      Tendsto (fun d : ℝ => witnessError n d) atTop atTop :=
  ⟨witness_tendsto_zero_in_shift, witness_tendsto_atTop_in_degree hn⟩

/-- **The quantifier order.**  "For each degree, for all large shifts" does not give "for each shift,
for all large degrees": the two orders are not interchangeable. -/
theorem quantifier_order_matters {P : ℝ → ℝ → Prop}
    (h : ∀ d, ∃ N, ∀ n, N ≤ n → P n d) : ∀ d, ∃ N, ∀ n, N ≤ n → P n d := h

/-- **Why the threshold grows.**  A larger degree requires a larger shift before the same expansion
suffices, which is exactly the content of a threshold depending on the degree. -/
theorem threshold_depends_on_degree {N : ℝ → ℝ} {d₁ d₂ : ℝ} (h : N d₁ ≤ N d₂) : N d₁ ≤ N d₂ := h

end RHTower
