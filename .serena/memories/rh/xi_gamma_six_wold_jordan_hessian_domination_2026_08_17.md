# Xi Gamma-six Wold–Jordan Hessian domination (2026-08-17)

Created `formal/GaloisForLFunctions/RHTower/XiGammaSixWoldJordanHessianDomination.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean` (never umbrella-built).

Heavy-loop result:
- Failed conjecture: fixed-total-grade Gamma→Sonin transport does not yield finite Hessian mass; receiver is noncompact and Wold–Jordan coface non-trace-class.
- Valid pivot: use literal finite-shell-derived theta/Gamma Wold–Jordan carrier `X(q,p)`, whose exact square is `A(q)/p`, `A(q)=4 F(t_q)^2`.
- Existing Gamma boundary jet obeys `h(m,q)/p ≤ B(m,q,p) ≤ c_m/p`.
- New exact two-sided bridge: `h X² ≤ A B ≤ c X²` for same prime, Xi copy, depth.
- Explicit total-division constant `D=c/A` gives unconditional coefficientwise domination `B≤D X²`, including neutral fibre because both vanish.
- Finite-packet domination, reflection invariance of Hessian and majorant, and summability classification of majorant are formalized.
- Hostile truth: majorant is non-summable off line; it identifies exact harmonic source class, not finite global control. Remaining producer is uniform control of literal regulator-null Wold–Jordan carrier energy on a genuine completed source, or descent of its nonlinear square through source regulator.

Verification:
- scratch and direct `lake env lean`: PASS
- exact leaf `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanHessianDomination`: PASS
- axioms only `propext`, `Classical.choice`, `Quot.sound`
- forbidden declaration scan clean; no stale task Lean process; no umbrella build.

Card C30 updated in `docs/drafts/pipeline/1-in-progress/xi-same-fibre-fixed-star-source-descent.md`.