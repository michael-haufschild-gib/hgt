# PW-B unit-ground-corrected Gamma scalar occurrence: excluded

- **ID:** PW-B-CORRECTED-GAMMA-SCALAR-OCCURRENCE-2026-09-11
- **Status:** Exact obstruction and positive finite-order survivor passed Lean scratch and the targeted leaf build (6.3 seconds). Final index and repository formal lint passed.
- **Scope:** The unchanged complete Gamma/Möbius family in the specific unit-ground-corrected pointwise scalar equation below. PW-B is not retired; RH is not proved.
- **Depends on:** [original finite cutoff expansion](../3-formalized/pw-b-gamma-reciprocal-cutoff-expansion.md), [complete moment detector](../3-formalized/pw-b-gamma-moment-detector.md), [forced current flatness](../3-formalized/pw-b-gamma-ground-boundary.md).

## Exact obstruction

For every complex z, there is no complex scalar lambda such that, at every
positive x,

`K_z(x)+2*log(x)*Q(x)=lambda*(M_z(x)-Q(x))`,

where K_z is the existing complete skew source

`K_z=E_z-R(H(R M_z))-2*log(x)*M_z`.

This is the unique unit-ground correction surviving the earlier leading
logarithmic test. The equation is now excluded at every parameter, including
any parameter one might later try to identify with a Xi zero. This result
excludes the stated pointwise ansatz; it does not exclude other source fields,
other corrections, weak formulations or PW-B as a route.

## Strongest positive survivor: finite endpoint order

Set

`G_z(v)=exp(-v)*SameSourceCurrent_z(v)/Q(v)`

and retain the actual coefficients

`B_j(z)=integral_(t>0) exp(-t)*[M_z(1/t)/Q(1/t)-1]/t^(j+1) dt`.

For every complex z there exists a natural j such that

`B_j(z)!=0`, `B_i(z)=0` for every `i<j`, and

`x^j*G_z(1/x) -> B_j(z)` as x tends to positive infinity.

Thus the complete original current has a finite first nonzero asymptotic
coefficient at each parameter. It cannot be flat to every order. No uniform
bound on j as z varies is asserted; the theorem does not identify j or B_j
with Xi data.

## Dependency-closed proof

The complete signed detector proves B_(k+2)(z) is nonzero for every sufficiently
large k. Choose the least nonzero B_j. The original finite cutoff theorem at
order j+1 gives

`norm(G_z(v)-v^j*B_j(z))<=C*v^(j+1)` for `0<v<=1/2`,

because every earlier coefficient vanishes. Substitute v=1/x and multiply by
x^j. The retained error is at most C/x, which tends to zero. This proves the
nonzero limit above without invoking infinite-series convergence or a separate
moment-determinacy measure.

The existing ground-boundary theorem shows that the displayed corrected scalar
equation would force every power-normalized reflected current to tend to zero.
The exact source reflection identity converts it to the reciprocal current;
multiplication by exp(-1/x), tending to one, preserves the zero limit. At the
least nonzero index this contradicts uniqueness of limits.

The proof keeps the complete signed arithmetic series throughout. The preceding
cutoff module retains the original near response, removed moments, finite far
remainder and source loss. There is no extra occurrence assumption in the
negative theorem or the positive existence theorem.

## Lean declarations and verification

`ThetaCuspHawkingParikhWilczekGammaReciprocalCurrentValuation.lean` contains:

- `pwGammaMobiusReciprocalNormalizedCurrent_exists_valuation`;
- `pwGammaMobiusReciprocalNormalizedCurrent_not_flat`;
- `pwGammaMobiusSkewSource_no_corrected_scalar`.

All three public theorems passed the final foreground scratch check with
exit0 and no diagnostics. The exact source is promoted with one RHTower
umbrella import. The source-bound and finite-expansion dependencies passed
targeted builds in43s and76s; the valuation leaf passed in6.3s. No numerical experiments or axiom-print checks
were used.

## Surviving PW-B task

Return to the complete original-cutoff transposition and retained adjoint
contact in the [pairing card](../1-in-progress/pw-b-gamma-reversible-pairing.md).
The [complete paired-contact passage](../3-formalized/pw-b-gamma-adjoint-paired-contact.md)
now retains the moving layer and empty incoming constant loss. Finite-cutoff
gain transposition and changing-source response limits remain open. The resulting domain must be derived and
then connected to an actual Xi occurrence through a different justified
realization. Positive pairing, all-parameter admission and skew symmetry alone
do not force the missing Ward balance.
