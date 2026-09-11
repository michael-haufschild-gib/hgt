# Route L: actual residual of damped paired prime Green sources

- **ID:** L-C41
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / finite-source paper derivation
- **Depends on:** C38 paired source, C39 fixed Sonin transport, [C40 original-Meyer compact escape](../3-formalized/route-l-cofinal-green-source-limit.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed-reader agreement →
conormal vanishing → RH. C40 excludes a coefficient-preserving limit of
exact cofinal prime-kernel sources in the original Meyer topology. It does
not apply automatically to damped approximate kernels. The next attack
must derive their residual and its full normalization before passing to a
source limit or claiming a physical boundary cancellation.

## Finite algebra to verify in Lean

Use the original log translation `T_c g(t)=g(t-c)` and weighted reflection
`Jg(t)=exp(-t)g(-t)`. For `L=log(p)>0` and real damping `a`, put
`D_(L,a)=Id-exp(-aL)T_(-L)` and `E_(L,a)=D_(L,a) J D_(L,a) J`.
The existing exact J/translation law gives
`J D_(L,a) J=Id-exp(-(a+1)L)T_L`.
Thus its literal Mellin multiplier is
`A_(L,a)(s)=(1-exp(-(a+s)L))(1-exp(-(a+1-s)L))`.
For `a>=0` and an actual Xi coordinate, both factors are nonzero; the
multiplier is reflection invariant. This follows from open-strip placement,
not RH.

At the ORIGINAL prime circle, translation by either sign of L acts as the
identity. Therefore the COMPLETE periodization is
`Per_L(E_(L,a)g)=r_(L,a) Per_L(g)`, where
`r_(L,a)=(1-exp(-aL))(1-exp(-(a+1)L))`.
Its first variation at a=0 is `L(1-exp(-L))`, positive. For a finite
commuting product with one occurrence of p removed, the same identity
holds with the entire remaining source as g. Repeated prime depths retain
the corresponding power of the residual factor.

After normalizing by the actual Xi evaluation, the exact recursion is
`Per_L(g_(P,a))/M(g_(P,a))(rho)`
`= [r_(L,a)/A_(L,a)(rho)] * Per_L(g_(P\p,a))/M(g_(P\p,a))(rho)`.
The prefactor tends to zero, but the remaining normalized source moves with
the cutoff. Its growth is the mathematical obstacle; a fixed finite-source
continuity argument cannot prove the cofinal residual tends to zero.

The infinite Euler expression `1/[zeta(a+s)zeta(a+1-s)]` is only a candidate
chamber representation until its literal product convergence and source
admission are proved. Do not claim that a meromorphic continuation is an
original-Meyer source limit. Do not replace the original physical reader by
a newly normalized limiting diagnostic.

## Prior source checks

- C38 proves the undamped paired defect and the weighted J/translation law.
- `DeningerTomographyNonstrict.lean` has exact periodization of translated
  sources; `deningerPeriodizationSum_periodic` and the linear periodization
  map supply the required fixed-period identities.
- `Sieve/DampedEulerCorrection.lean` defines a relative damped Euler factor;
  its norm estimate is a different normalization, not the needed source law.
- `SoninCofinalMobiusGammaXiIncidence.lean` transports actual Möbius Fisher
  data through singular cofinal Sonin corners at fixed Euler points. Its
  `fixedEulerCofinalDamping` diverges to compensate a collapsing coordinate;
  it is not this vanishing damping parameter.
- Deep/method report `/tmp/route_l_cofinal_c40_abel_residual_deep.json`,
  generation 874835, semantic 2352929/2353624, partial. All 20 candidates and
  20 source arguments inspected; no generated ingredient premise adopted.

No C41 Lean file, module or verified infinite-limit theorem yet.


## New quantitative conjecture, with a closed scalar paper proof

For every `a>0`, `L>0` and actual Xi point `rho`, the normalized residual
is strictly contractive: `|r_(L,a)/A_(L,a)(rho)|<1`. Put
`q=exp(-aL)`, `x=exp(-L Re(rho))`, `y=exp(-L(1-Re(rho)))`.
All three lie in `(0,1)` and `xy=exp(-L)`. The reverse triangle inequality
bounds `|A_(L,a)(rho)|` below by `(1-qx)(1-qy)`, whereas
`r_(L,a)=(1-q)(1-qxy)`. Their difference is exactly
`q(1-x)(1-y)>0`. Thus the contraction is unconditional throughout the
open strip and has an explicit positive margin.

Repeating one original prime factor k times, with no other moving factors,
gives the exact normalized periodization `(r/A)^k` times the original
normalized periodization. This tends to zero in the actual prime-circle
space, while the Xi reading remains one. Formalize that actual family and
its exact physical transport as the positive survivor. In a cofinal
multi-prime family, the remaining operators can amplify other circle
components; the one-prime contraction does not by itself control that
moving remainder. That comparison is the next substantive obstacle.
