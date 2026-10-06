# BAG: exact normal height isometry of the retained tube

- **ID:** bag-near-cone-normal-height-isometry-31az
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ChiCubicNearConeHeightTrace; ChiCubicNearConeReduction; WindowTransformSamplingParseval; ChiRamanujanCriticalSourceControl.

## Exact result and scope

For any physical Schwartz f, let near_epsilon f be the ENTIRE retained
test, with Fourier transform chi(D/epsilon)*Fourier(f), D=xi_2+xi_0*xi_1.
For 0<epsilon<=1/4 and fixed real x,y define

    psi(D)=Fourier(near_epsilon f)(x,y,D-x*y).

For EVERY real tau, all integer heights have the exact HasSum identity

    sum_(r in Z) |Fourier(psi)(tau+r)|² = integral |psi(D)|² dD.

No derivative budget is assumed. The original epsilon=N^(-1/8) enters
this range on EVERY sufficiently large original natural scale, for EVERY
physical Schwartz input, hence also the actual moving input.

Both contraction translations are retained pointwise. At shifts u,v,
the translated test is Fourier(near_epsilon f) at
(x+u,y+v,D-x*y-u-v). Its normal slice is exactly the slice at (x+u,y+v)
translated by u*(y-1)+v*(x-1)+u*v. Translation changes the normal Fourier
transform by a unit character, so the same HasSum identity holds. This
covers each term in both literal finite averages and their intersection;
it does not estimate the complete signed sum of those terms.

For the COMPLETE critical multiplier M_P, including uncovered integer
frequencies, set w_P(r)=M_P(|r|)/log(1+|r|). Then 0<=w_P(r)<=1, including
r=0 with Lean's division convention. The ENTIRE weighted square series
is summable and <=integral |psi|², uniformly in every finite P. Every
finite height family and every pair of projector translations has the
corresponding bound without a prime-cutoff constant.

This closes a normal trace input for the actual tube. It does NOT give
signed tangential prime cancellation or an operator bound for the whole
critical action. Original cubic, higher moments/cofactors, deterministic
common-height return and RH remain open.

## Dependency-closed proof

1. Exact cutoff identity makes psi zero for |D|>=2epsilon, hence outside
   [-1/2,1/2]. Continuity follows by affine restriction of the actual
   Schwartz Fourier test.
2. Apply corpus sampling Parseval with interval length one and modulation
   -2*pi*tau. The checked paperFT/Fourier dictionary gives precisely
   tau+r. Zero extension identifies interval and whole-line integrals.
3. Expanding both contraction translations gives the full mixed normal
   shift. Exact Fourier translation preserves every sample norm.
4. The all-integer critical multiplier envelope gives w_P in[0,1].
   Positive comparison proves weighted summability and the trace bound.
5. N^(-1/8)->0 and positivity give the original natural-scale endpoint.

## What the failed attempt taught

The narrow-height-bump test concerns unrestricted profiles. It is not an
obstruction for this actual truncated family: its normal support fits
inside one sampling period. A moving derivative penalty is unnecessary
here. Gallagher's general estimate already existed and was not repackaged
as new frontier progress. No route is retired by this test.

All integer heights are deliberately retained. Near-cone Fourier
truncation need not preserve original physical height support; its
outside-band samples must not be silently omitted.

## Audits

- Scratch44274 and final direct89755 passed without diagnostics. Final
  command: lake --old env lean GaloisForLFunctions/RHTower/ChiCubicNearConeHeightTrace.lean
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ChiCubicNearConeHeightTrace.olean.
- Final axiom44654 passed: all10 public theorem endpoints depend only on
  propext, Classical.choice, Quot.sound.
- One RHTower umbrella import; no umbrella/full build, added axiom,
  computation, heartbeat override, commit or subagent.
- Index35025 passed (4 changed,0 removed). Authoritative lint21018:
  ZERO findings for the new leaf; repository exit1 has27 unrelated
  unreachable modules and367 size warnings.
- Logs/search JSON retained under /tmp with31az suffix. All owned
  processes terminal; owned scratch sources removed after audits.

## Next hard target

Prove cancellation of the ENTIRE signed tangential critical source across
growing denominators, retaining both projectors, integer aliases and
cross-height interactions. This isometry is quadratic control, not that
signed estimate. Do not substitute fixed-denominator estimates,
coefficientwise annihilation, local-axis removal, or another height budget.
