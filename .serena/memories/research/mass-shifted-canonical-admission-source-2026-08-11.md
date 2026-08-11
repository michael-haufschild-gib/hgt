# Canonical shifted-Xi admission-sensitive arithmetic source

Created exact fixed-degree producer for mass-shifted spectral-face route.

- Generic `HTGeometry.MonicMomentAdmission`: inverse leading Hankel solve gives monic polynomial, exact lower-moment orthogonality under nonsingularity, uniqueness, terminal-normalized next-face null-vector specialization, coefficient continuity under moment convergence.
- `RHTower.XiShiftedCanonicalAdmissionRecession`: arcsine admission equals shifted monic Chebyshev; fixed-degree shifted-Xi coefficients converge; existing normalized Hankel PosDef recession upgrades totalized inverse expression to eventual actual unique admission.
- `RHTower.XiShiftedCanonicalAdmissionSourceRecession`: source-coordinate pullback `P_{n,w}(X)=w^(-2n)Q_{n,w}(w^2X)`; exact adaptive shear covariance; exact source law
  `w^(4n+5)/log w * Source(w,P_{n,w}) = L_{t_w}(Shear(Q_{n,w}))` for `w>1`.
- Exact limits: `11/64` for `n=1`; `monicScale n ^ 2 * (8*n+3)/16` for `n>=2`; hence unique admission and literal arithmetic source positivity eventually in every fixed positive degree.
- Remaining obstruction is exclusively diagonal degree/conditioning escape: control source-functional error below collapsing margin `(2n+3/4)16^(-n)` for actual degree law. Generic fixed-degree convergence cannot do it because inverse-Hankel conditioning is degree dependent.
- Report addendum §9.3 equations (9.3.370)--(9.3.377); pipeline card `docs/drafts/pipeline/3-formalized/mass-shifted-fixed-degree-xi-orthogonal-admission-recession.md`.
- Verification: direct Lean passes, targeted source module build passes, axiom audit only `propext`, `Classical.choice`, `Quot.sound`; repo-wide lint currently fails only unrelated concurrently-created unreachable umbrella modules.