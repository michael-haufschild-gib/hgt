# Suzuki curvature Jordan abscissa rigidity (2026-08-30)

New module: formal/GaloisForLFunctions/RHTower/SuzukiCurvatureJordanAbscissaRigidity.lean; wired into RHTower umbrella. Card promoted to docs/drafts/pipeline/3-formalized/suzuki-curvature-jordan-abscissa-rigidity.md. Frontier map untouched.

Unconditional Lean closure:
- exact positive upper order c_N^+ ≤ 2 (N+1)^(-1/2)
- exact negative upper order c_N^- ≤ Λ(N+1)/sqrt(N+1)
- exact positive lower half-order on N=6m+5
- exact negative lower half-order on prime endpoints p≥11
- Summable ((N+1)^(-α)c_N^+) iff 1/2<α
- Summable ((N+1)^(-α)c_N^-) iff 1/2<α
- closed no-go: no α≤1/2 makes both Jordan sectors summable.

Route consequence: kills all half-density-compatible/subcritical polynomial singular gauges for shared CCM-FU/SP-E Suzuki curvature source. Any survivor must preserve conditional cancellation before crossing half-order wall or use a distribution space with unbounded inverse.

Verification: direct lake env lean passed; targeted lake build module passed (11647 dependency jobs); #print axioms only propext/Classical.choice/Quot.sound. Global lint has unrelated concurrent unwired-module failures; new module is reachable and absent from errors. No task-owned Lean process remains.