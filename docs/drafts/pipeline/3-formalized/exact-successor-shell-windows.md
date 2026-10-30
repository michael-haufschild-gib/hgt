# Exact successor windows and geometric onset

- **ID:** exact-successor-shell-windows
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3.
- **Statement:** Logarithmic windows have additive radii `a(exp w-1)` and
  `a(1-exp(-w))`; an unequal integer pair first becomes eligible at
  `t_N=N log((N+1)/N)`.

For positive `a` and nonnegative displacement `r`, exponentiating the logarithmic
window inequality gives the upper radius; the lower radius also requires `r<a`.
The inequalities for `log(1+x)` give `1-1/N<t_N<1` for `N≥1`, hence `t_N→1`.

For `N≥2`, an unequal pair `1≤a≤N`, `b≥1` with
`|log b-log a|≤c/N` exists exactly when `t_N≤c`. The boundary-star theorem
reduces the only nontrivial direction below overlap one to `(a,b)=(N,N+1)`;
that pair also proves sufficiency. At each fixed `c<1`, no pair is eventually eligible.

These are geometric criteria. Actual interaction also depends on the profile correlation
and Mangoldt coefficient. For the explicit plateau, the strict positivity criterion and
touching decay are formalized separately in `TheSuccessorFiberHasAnExactOpenThreshold`.

Lean: `GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ExactSuccessorShellWindows.lean`.
Main declarations: `upper_successor_window_iff`, `lower_successor_window_iff`,
`tendsto_firstExteriorOverlap`, `exists_integer_shell_iff`, and `eventually_no_integer_shell`.
Kernel check and four transitive axiom audits passed with only
`propext`, `Classical.choice`, `Quot.sound`; final direct audit is pending.
Imported by the CriticalArithmeticCorrelationTheory umbrella.
