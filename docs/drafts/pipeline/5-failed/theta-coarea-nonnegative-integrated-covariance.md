# RN: favorable integrated coarea covariance — refuted

2026-10-04. Paper and Lean closure complete; route RN remains active.

Retired conjecture: the actual integrated covariance
Cov_mu(A_x,A_y-y*partial_y A_y) is nonnegative for every 0<x<=y.
Already on y=x, it is negative for every sufficiently small positive x.
The original coarea measure is identified by an exact change of variables.
This is a whole-half-line result, stronger than the earlier adverse two-mass
pair. It is not a negative full Schur current and not an RH falsification.

Strongest positive survivor: the exact loss coefficient is the strictly
positive finite variance of
a(t)=(c(t)+p(t)/t-2*c(0))/4 under 2*t*k(t)^2 dt/H(0,0):

  Cov_mu(A_x,A_x-x*partial_x A_x)/x^4 -> -Var_mu(a)<0.

Its whole-half-line domination, exact integral decomposition, strict profile
increase and variance positivity have dependency-closed paper proofs and
completed Lean source/axiom audits. All36 public theorem closures use only
propext, Classical.choice and Quot.sound. Certificate:
../3-formalized/theta/rn-integrated-coarea-covariance-variance.md.

The full RN producer must retain and compensate this loss with potential
variation. Its global finite-pair inequality, general anchors, arbitrary
rank and arithmetic transfer remain open.
