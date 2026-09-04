# ULF-INBSG-001

One fixed pre-divisor operator `T = gammaSewnCriticalPhysicalPluckerSpectralOperator / tau` is positive, injective, compact, Schatten-one, all-prime/depth mixed, `Tr T = ||T||₁ = 1`, and recovered from theta first exit with `-index = 1` (`ULF-POINH-001`).

Correction: POINH's proposed bounded-unital norm-gap landing is invalid. Actual P-G98 completion is singular `E_eps(T)=T(eps I+T)^(-1)`; it converges strongly to `I` but `||E_eps(T)-I||=1`. Preserve norm germ in `Q=C_b((0,1],K(H))/C_0`.

Paper theorem: for any positive compact injective infinite-dimensional `T` and `c,d>0`,
`||[E_eps(cT)]-[E_eps(dT)]||_Q = |sqrt c-sqrt d|/(sqrt c+sqrt d)`.
Proof: scalar difference `(c-d) eps lambda / ((eps+c lambda)(eps+d lambda))`; maximize at `eps/lambda=sqrt(cd)`; eigenvalues `lambda_n->0` realize maximum along `eps_n`.

Exact fusion with literal Poisson history `P(t,u)=4tu/(t+u)^2`:
`||e_T(t^2)-e_T(u^2)||^2 + P(t,u)=1`.
Euler specialization `c=p^(2a)` yields oriented contrast `C=(p^a-1)/(p^a+1)=tanh(a log p/2)`, `G=1-C^2`, Burnol holonomy `4C/G`, Gamma curvature `4C^2/G`, visibility `sqrt G`, rapidity `artanh C`. Reflection flips C only. Finite-rank/gapped carrier has zero boundary-germ contrast; faithful spectrum accumulating at zero is exact source of open-history noncompactness.

Exact RH gate: derive pre-divisor from anomaly-subtracted integer/Poisson self-duality that direct/reflected translations of same boundary-transfer history agree modulo norm-null `C_0`; then germ formula forces `p^(2a)=1`, hence `a=0`. Strong equality is automatic/useless; pointwise norm equality impossible; asserted germ equality on Xi fibres is only classifier.

Files: `docs/drafts/pipeline/2-fully-proven/universal-law-field/poisson-scale-history-completion-mechanics/integral-nuclear-boundary-scale-germ-pythagorean-law.md`; STATUS F569-F572, CANNOT-254, MUST-177. Lean was read-only per active goal.