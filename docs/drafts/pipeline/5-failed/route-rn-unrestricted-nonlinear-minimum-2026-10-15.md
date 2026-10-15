# RN candidate: unrestricted nonlinear minimum

Status: FALSE. Route RN and its full-divisor orientation problem remain active.

## Exact failed conjecture

For every real compact smooth chi and real a, the complete action

N_chi(a) = sum_n Lambda(n)/sqrt(n) integral_x k(x)k(x+log n)
  (cosh(a(chi(x+log n)-chi(x)))-1)
  - integral_(u>0,x) b(u)k(x)k(x+u)
  (cosh(a(chi(x+u)-chi(x)))-1)

is nonnegative. Here k is the actual theta cusp source and b is the literal
combined Gamma/pole translation coefficient. Every prime power is retained.

## Obstruction

Choose two opposite smooth flat plateaus with sufficiently distant supports
whose difference interval contains no log(n), n>=2. All extremal jumps of
size 2 join opposite plateaus. No prime link realizes such a jump; continuous
links realize it on an open set of positive measure where b is positive.
The complete action tends to minus infinity. The same profile has strictly
positive full quadratic arithmetic energy by the corpus's far-gap coercivity.
The new action's small-amplitude Taylor identity was not separately formalized.

## Positive survivor and exact new insight

For a>=0 and |d|<=2,
0<=exp(-2a)(cosh(ad)-1)<=d^2/8. Its limit is 1/2 when |d|=2,
and zero otherwise. Consequently exponential normalization of the complete
action converges exactly to prime extremal mass minus continuous signed
extremal mass, with each mass carrying factor 1/2. The absolute quadratic
majorant justifies the entire limit, including the Gamma singularity and
infinite prime sum. The unnormalized action is absolutely integrable for
every real amplitude on the bounded profile class.

This classifies the large-amplitude obstruction: global nonlinear positivity
can fail on actual arithmetic sources with positive quadratic energy. It
does not refute RN's special normal-field comparison or RH. The method is
dominated convergence; no external novelty claim is made.

Paper proof: dependency-closed, recorded in the active RN working card.
Lean status: verified, no added axioms or unproved declarations.

- formal/GaloisForLFunctions/RHTower/ThetaNonlinearExtremalJump.lean
  - tendsto_thetaNonlinearAction_scaled
  - integrable_thetaNonlinearAction_terms
- formal/GaloisForLFunctions/RHTower/ThetaNonlinearPlateauEscape.lean
  - exists_positive_quadratic_negative_nonlinear_limit
  - exists_positive_quadratic_nonlinear_escape

Both modules are imported by RHTower.lean. Final `lake --old env lean`
module audits passed; all 26 public declarations passed a separate axiom
audit using only propext, Classical.choice, Quot.sound. Formal lint passed.

Active work: docs/drafts/pipeline/1-in-progress/route-rn-full-divisor-charge-2026-10-15.md.
Next RN target remains the constrained causal remainder's arithmetic sign
or a direct full-divisor renewal-charge identity, retaining multiplicities.
