# PW-B unit-ground boundary and complete rapid-tail constraint

- **ID:** PW-B-GAMMA-GROUND-BOUNDARY-2026-09-11
- **Stage:** 3-formalized
- **Statement:** For every complex coefficient parameter, the complete ground-subtracted source and logarithmic current have exponential tails. The unit-corrected skew source has retained boundary value minus the complete reciprocal endpoint. A scalar equation forces that endpoint to vanish and its entire reciprocal current to decay faster than every inverse power.

## Exact signed source and tail

Use the original Q, coefficient-deformed M_z, logarithmic current E_z,
weighted Frullani generator H and source-fixed inverse-gain reflection R.
Set F_z=M_z/Q-1. The exact normalized atom identity at x>0 is

`GlobalAtom(z,n,x)/Q(x) = d_n(z)*exp(-(n-1)*(x-1))`,

where d_n(z)=GlobalAtom(z,n,1)/Q(1). The complete sequence is absolutely
summable. Its n=0 term is zero and its n=1 term is one. Removing these
two terms is an exact infinite-sum identity, not a finite approximation.
For x>=1 and n>=2, the exponential factor is at most exp(-(x-1)).
Thus

`|F_z(x)| <= (sum_(n>=2)|d_n(z)|)*exp(-(x-1))`.

The logarithmic current has both initial terms zero, and the same
argument gives the analogous bound with its actual signed coefficients.
No positivity of the arithmetic coefficients is assumed.

The source and current retain decay after multiplication by every
fixed power x^k. The source retains it after a further log(x) factor.
The proofs use the existing exact polynomial-times-exponential limit
and log(x)<=x on the positive tail. Constants can depend on z and k;
no order growing with x is used.

## Retained boundary and necessary scalar constraint

The literal skew-source expression remains

`K_z=E_z-R(H(R M_z))-2*log(x)*M_z`.

The previous [unique correction theorem](pw-b-gamma-skew-source-endpoint.md)
forces the unit ground coefficient in any scalar equation of this form.
Its next complete normalized limit is

`(K_z(x)+2*log(x)*Q(x))/Q(x) -> -B_z`,

where B_z is the absolutely convergent series in the
[arithmetic reciprocal endpoint theorem](pw-b-gamma-arithmetic-reciprocal-endpoint.md).
Indeed, the quotient equals E_z/Q-R(H(R M_z))/Q-2*log(x)*F_z.
The first and last terms vanish, and the middle term retains B_z.

Consequently, an identity throughout the positive ray

`K_z+2*log(x)*Q = lam*(M_z-Q)`

forces B_z=0. More strongly, solving this identity for the reflected
current and retaining all complete tails gives, for every natural k,

`x^k*R(H(R M_z))(x)/Q(x) -> 0`.

These are necessary conditions. They do not produce a scalar solution,
identify B_z with Xi, construct a common operator domain, establish a
full adjoint or force Ward balance. RH and PW-B remain open.

## Next mathematical test

The [continuing pairing card](../1-in-progress/pw-b-gamma-reversible-pairing.md)
records an explicit all-moment proof candidate. Splitting the original
singular integral at its moving scale and retaining the near-region
cancellation should give a full asymptotic expansion. The preferred
positive survivor now uses the Gamma-normalized high-order moments:
they should recover the nonzero n=2 coefficient with an explicit
inverse-order plus geometric error bound. This avoids the separate
exponential-window density construction, retained as a backup. The
stronger exclusion and moment detector are not yet verified in Lean.

## Verification

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaGroundBoundary.lean`.
All10 public declarations pass scratch Lean with only propext,
Classical.choice and Quot.sound. Promoted bodies exactly match that
scratch, every public name is unique in source and generated LEAN_API,
and one RHTower umbrella import is wired. The targeted leaf build
passed in482s, building only this leaf; dependencies were replayed.
Index passed with zero changed entries and zero removals, and final
repository formal lint passed. Only redundant-tactic style warnings
remain. No full or umbrella build, numerical experiment, added axiom,
subagent, commit or push occurred.
