# BAG moving physical Mellin lines

Continuation01ap. Route: BAG full signed axes action. The growing labelled
near-pole source law is now production Lean checked, but the existing exact
physical cone pairing uses real parts(2,2). Pointwise source convergence at
1+(u,v)/logN cannot be inserted into that fixed-line integral.

Corpus: PositiveQuadrantLogSchwartz; ChiPrimeGaussianCubicConeMellin;
ChiPrimeGaussianCubicTransverse; ChiRamanujanGrowingLabeledSource.
Search16784 and64336 are nonpartial with65913 indexed files, no errors,
background refresh incomplete, source-only candidates. All20 candidates and
20 source arguments of each inspected. Existing arbitrary-line one-variable
Mellin inversion requires convergence/integrability premises; the two-variable
all-Schwartz pullback is currently only on line2. No ready actual moving-line
physical pairing was found.

Conjecture: every planar Schwartz function admits a Schwartz weighted
logarithmic pullback exp(-a*u-b*v)*f(exp(-u),exp(-v)) for EVERY a,b>0.
Fourier inversion then gives exact two-variable Mellin inversion on those
lines, with full integrable profile. Pair the complete rational cone on
a,b>1 using its already proved absolutely convergent HasSum. In particular
choose a=1+lambda/logN,b=1+mu/logN for positive lambda,mu. This places the
actual physical profile on the new source scale without a contour-shift
assumption. The full profile must remain dependent on N.

Paper mechanism: set delta=min(a,b)>0 and choose integer m>=max(a,b)+delta.
In each coordinate exp(-a*u+delta*abs(u)) <= (1+norm(node u))^m.
Thus the exponential weight times exp(delta*(abs(u)+abs(v))) is absorbed
by Schwartz decay of degree2m. Polynomial log-coordinate growth is bounded
by k!*delta^(-k)*that exponential. The exact derivative replaces f by
(-a*f-x*d_x f,-b*f-y*d_y f), again Schwartz. Induction closes all derivatives.
This is a proof plan, not yet audited Lean.

Remaining hard problems after this identity: compact-uniform source limit,
uniform control of the ACTUAL moving profiles and frequency tails, coupled
pole/near-cone cancellation across all sectors, full axes o(N/log^2N),
growing moments/cofactors and deterministic common-height return.

Progress01ap: arbitrary-positive-line logarithmic Schwartz construction and
full two-variable inversion scratch71545 empty PASS, production86634 empty
PASS in HTGeometry.PositiveQuadrantMellinLines (wired once). Complete physical
cone pairing and actual cutoff-family attachment are now under scratch audit.
No global profile bound or limiting interchange has been assumed.

Final01ap: exact line identity and actual moving family are LEAN AUDITED.
Production86634 PositiveQuadrantMellinLines269lines (5theorems/7defs) and4433
ChiPrimeGaussianCubicMovingMellin164lines (2theorems/3defs) empty PASS.
Axiom62726 all17 standard3. Index87535/API17/imports once. Lint67343 exit1:
27 unrelated unreachable modules,174warnings; no owned finding/global NOT clean.
The initial line-pairing conjecture is solved. Keep this card active for its
remaining uniform-limit/profile/tail obligations. New exact cancellation
conjectures and paper analysis: bag-mixed-frequency-mellin-cancellation.
