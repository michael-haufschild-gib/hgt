# Xi-shift rooted polar normal cone

- **ID:** `xi-shift-rooted-polar-normal-cone`
- **Stage:** 1-in-progress
- **Status:** `[PAPER-PROVED CORE] [LEAN-PROVED CORE] [NOVELTY SEARCH PASSED, NOT CERTIFIED] [NOT RH]`
- **Type:** SOURCE-TO-ARCHIMEDEAN BRIDGE / SHARP NORMAL LAW / RH FRONTIER ROUTING
- **Parents:**
  - `gamma-sewn-xi-shift-tangent-hilbert-kernel`
  - `gamma-jordan-xi-tangent-response-gap`
  - `gamma-julia-endpoint-correction-hilbert-schmidt-dressing`
  - `xi-shift-tangent-stationary-kernel-no-go`
- **RH used:** no
- **Computation used:** no

## Research question

The normalized completed `+2` Xi-shift tangent Gram is built in inverse-prime coordinates, while
the completed polar response is stationary in prime-log differences.  Direct pointwise stationary
sewing is impossible.  Does a source-forced rooted renormalization retain a nonconstant stationary
boundary, and what is its first normal correction?

## Exact source response

For ordinary primes `p,q`, write

```text
a = 1/p,
b = 1/q,
delta = ((a-b)/(1-ab))^2.
```

Then the normalized all-depth tangent correlation is exactly

```text
C(p,q) = sqrt(1-delta) * (1-2 delta).                    (RP1)
```

Moreover `0 <= delta < 1`.

Define

```text
R(delta)
  = 1 / (2(1+sqrt(1-delta))^2)
    - 2 / (1+sqrt(1-delta)).
```

Rationalizing `1-sqrt(1-delta)` gives the exact normal expansion

```text
1-C = (5/2) delta + delta^2 R(delta),    R(0)=-7/8.     (RP2)
```

No Taylor series or unproved differentiability interchange is used.

## Rooted polar variables

Put

```text
u = 1/(pq),
A = (p-q)^2/(pq).
```

Then

```text
delta = A u/(1-u)^2,                                    (RP3)
A = 2 cosh(log p-log q)-2.                              (RP4)
```

Substitution into `(RP2)` gives the exact finite-prime identity

```text
pq(1-C)
 = (5/2) A/(1-u)^2
   + A^2 u/(1-u)^4 R(Au/(1-u)^2).                       (RP5)
```

The right side extends continuously to `u=0`.  Therefore, at fixed logarithmic lag `t`,

```text
pq(1-C(p,q)) -> (5/2)(2 cosh t-2)
              = 10 sinh(t/2)^2.                         (RP6)
```

At doubled log nodes `x=2 log p`, `y=2 log q`, the critical polar kernel is
`2 cosh((x-y)/2)`.  Thus `(RP6)` is exactly `5/2` times its diagonal-subtracted tangent.
The coefficient `5` is the boundary Fisher mass of the normalized depth tangent: its first
inverse-prime variation has depth coordinates `(-1,0,2,0,...)`, whose squared norm is `5`.

## Second rooted normal law

Subtract the polar tangent in `(RP5)` and divide by `u`.  The quotient has a continuous extension
at `u=0` equal to

```text
Q(A) = 5A-(7/8)A^2 = A(40-7A)/8.                        (RP7)
```

For `A>0`,

```text
Q(A)>0  iff  A<40/7,
Q(A)=0  iff  A=40/7.
```

Using `(RP4)`, the unique positive-lag transition is

```text
cosh(t)=27/7.                                            (RP8)
```

This is a one-transition orientation law, not a global one-sided sign.

## Positive survivor

The earlier stationary-kernel no-go is sharp rather than terminal:

1. unscaled pointwise source sewing collapses to the constant kernel;
2. the symmetric root `pq` is the first scale that recovers a nonconstant stationary boundary;
3. that boundary is exactly the critical polar tangent, with source-forced coefficient `5/2`;
4. the next normal coefficient has one explicit sign transition.

Any source-to-completed intertwiner that discards the absolute/root coordinate before taking this
normal quotient loses the polar response.  A viable intertwiner must carry the rooted scale through
the first two normal orders.

## Hostile falsification

This theorem does **not** orient Xi zeros.

- The positive off-line Euler quartet can be equipped with the same local geometric-depth tangent
  packet.  Hence `(RP1)`--`(RP8)` are not, by themselves, a zero-exclusion theorem.
- Positive Euler source, exact inversion, reflection, entire completion, hypertranscendence,
  `8 pi` Ward charge, and positive unsquared Cauchy orientation already coexist with an off-line
  zero in `PositivePrimeDensityMobiusInversion.lean`.
- The law is local/source-geometric.  RH needs an additional continuation-compatible global
  coupling identifying the rooted normal quotient with the actual Xi Cauchy/Weil response.
- The second normal coefficient changes sign for large lag, so no global one-sided Julia theorem
  may be inferred from it.

## Internal collision audit

Searches across `formal/`, stages 2/3/5, and `scripts/formal_tools.py research` found:

- the exact source Gram and Fisher response in
  `GammaSewnXiShiftTangentHilbertKernel.lean` and
  `GammaJordanXiTangentResponseGap.lean`;
- the polar kernel `2 cosh((x-y)/2)` in the CCM/polar modules;
- no theorem identifying the symmetric `pq` defect blow-up with that polar tangent;
- no occurrence of the second normal coefficient `A(40-7A)/8` or transition `cosh(t)=27/7`.

## External collision audit

Targeted searches covered boundary Fisher kernels, normalized Szegő/Hardy kernels, hyperbolic
Fisher geometry, prime-log stationary kernels, Julia operators, and RH.  General Fisher/hyperbolic
geometry is classical, but no source was found containing this Xi-shift inverse-prime Gram,
its rooted prime-pair blow-up, or the second normal transition.  This is a noncollision result,
not a proof of priority.

Nearby general literature:

- S. Costa, S. Santos, J. Strapasson,
  [Fisher information distance: a geometrical reading](https://arxiv.org/abs/1210.2354).
- Generic weighted-Szegő boundary asymptotics exist, but the searches found no arithmetic
  source-to-polar law matching `(RP1)`--`(RP8)`.

## Lean theorem map

Formal module:

`formal/GaloisForLFunctions/RHTower/XiShiftTangentRootedPolarNormalCone.lean`

The module proves unconditionally:

- `gammaSewnXiShiftEndpointUnitTangentKernel_eq_boundaryResponse`;
- `xiShiftTangentBoundaryDelta_lt_one`;
- `one_sub_xiShiftTangentBoundaryResponse_eq`;
- `xiShiftTangentBoundaryNormalRemainder_zero`;
- `xiShiftPolarLag_eq_cosh`;
- `xiShiftTangentBoundaryDelta_eq_polarLag_mul_root`;
- `primeRooted_xiShiftTangentKernel_defect_expansion`;
- `primeRooted_xiShiftTangentKernel_secondNormal_eq`;
- continuity and boundary limits of both normal extensions;
- factorization, positivity range, and zero classification of `Q(A)`.

Direct foreground check:

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftTangentRootedPolarNormalCone.lean
```

passes.

## Open RH core

Construct and prove a source theorem that identifies the rooted two-order normal quotient with the
continued Xi Cauchy/Weil response while using structure absent from the explicit positive off-line
Euler quartet.  Candidate additional structure must be genuinely global and
continuation-compatible; positive source, functional equation, entire completion,
hypertranscendence, Ward charge, and unsquared orientation are already ruled out as sufficient.

## Gates

- [x] exact candidate isolated
- [x] dependency-closed paper proof
- [x] strongest positive survivor extracted
- [x] hostile countermodel boundary recorded
- [x] internal collision audit
- [x] targeted external collision audit
- [x] unconditional Lean formalization of core identities
- [ ] identify global Xi-response coupling
- [ ] prove coupling excludes positive off-line Euler realization
- [ ] derive critical-line zero theorem
