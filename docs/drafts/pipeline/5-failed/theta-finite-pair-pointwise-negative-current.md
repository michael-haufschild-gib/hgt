# RN: global pointwise negative finite-pair current — refuted

2026-10-04. Paper and Lean closure complete. Route RN remains active.

Retired conjecture: for all x>0,y>=x,t>0, the actual canonical current
C_y-lambda*C_t-lambda_t*C is negative, where C is the literal transported
center Schur moment and lambda=(p(t+y)-p(y))/(p(t+x)+p(t+y)).
ThetaFinitePairCurrentGerm.exists_positive_finiteCanonicalCurrent proves,
without premises, that some t>0 and 0<x<y have strictly positive current.
finiteCanonicalCurrent_eq_deriv identifies the exact differential current.

The obstruction retains actual kernel jets and Gram data. With q=c(0),
d=c''(0), alpha=I/J, projective descent and Ward identities prove
alpha<=q/2+d/(6q). Exact iterated node/source-time limits then give the
strictly positive coefficient q^2/2-q*alpha+5d/12>=d/4>0.
Smooth source averages and two kernel jets justify all parameter derivatives;
continuity transfers the diagonal witness into the strict chamber x<y.

## Positive survivor, fully formalized

The new structural moment comparison and exact positive current germ survive.
They force signed source-time compensation in any continuation of this current
representation. The existing negative joint-center Schur Hessian remains valid;
no total integral sign or RH counterexample follows from pointwise positivity.
Certificate and full paper proof:
../3-formalized/theta/rn-finite-pair-current-center-variation.md.

All four leaves passed final actual-source `lake --old env lean` audits;
all25 public theorem axiom closures are exactly propext, Classical.choice,
Quot.sound. Umbrella imports are wired. Final sequence88345 exit0.
Lint has twelve unrelated unreachable modules and no own-leaf error.

Next hard problem: prove the complete weighted finite-pair current integral
negative, retaining its positive interior and negative boundary contribution.
The exact finite-pair integrated sign, general-anchor ports, arbitrary-rank
positivity and arithmetic transfer to RH remain open. Working card:
../1-in-progress/rn-finite-current-integrated-compensation.md.

Further positive survivor, audited later on 2026-10-04: the same actual current
has the exact negative boundary profile Ican(x,x,r*x)->-gamma/(2*(1+r)^2)
for every fixed r>=0, with gamma=I/J-q/2>0. Its matched moment divided by x
tends to gamma. Both new leaves and all9 public standard-axiom audits passed.
This classifies a negative source-time regime without discarding the positive
interior. It does not yet prove a weak negative atom or an integrated sign.
Certificate: ../3-formalized/theta/rn-finite-pair-boundary-layer.md.

Further positive survivor RN-P-7ad is now fully formalized: the actual finite-
prefix limit is integral W0*L-gamma/2, and sufficiently short fixed prefixes
are negative for sufficiently small nodes. All four leaves and53 public
standard-axiom queries passed. This closes the finite-prefix compensation
gap without asserting a global finite-pair sign. Certificate:
../3-formalized/theta/rn-finite-current-prefix-compensation.md.
