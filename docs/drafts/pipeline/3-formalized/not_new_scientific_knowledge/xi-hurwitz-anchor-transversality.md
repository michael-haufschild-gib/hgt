# Xi--Hurwitz canonical-anchor transversality

- **ID:** `xi-hurwitz-anchor-transversality`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE RELATION / BRIDGE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/Hurwitz/AnchorTransversality.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHurwitzAnchorTransversality.lean`
- **Statement:** Every positive-real Xi zero indexes a frozen-exponent continued Hurwitz function
  with a simple zero at the canonical shift `a=1`, independently of the Xi multiplicity; moreover,
  every positive-order shift jet at that anchor is nonzero.

## Goal

Cross the formal boundary at `a=1` in the concrete Taylor-subtracted Hurwitz continuation and
record the resulting unconditional value relation at every Xi zero.  The theorem supplies a
source-side transverse coordinate for future two-variable incidence arguments; it does not infer
the location or multiplicity of an Xi zero.

## Theorem

For every `s` with `0 < Re s`, the canonical continuation is analytic at `a=1` and

```text
deriv (continuedHzeta s) 1 = -s * riemannZeta (s+1).
```

The entire canonical anchor jet is explicit:

```text
iteratedDeriv r (continuedHzeta s) 1
  = (-1)^r * (s)_r * riemannZeta (s+r).
```

For every `r>0`, this value is nonzero. Positive real part excludes the roots
`0,-1,...,-(r-1)` of `(s)_r`, while `Re(s+r)>1` puts the shifted zeta factor in its Euler-product
zero-free half-plane.

Consequently, if `0 < Re rho`, `rho != 1`, and `xi rho=0`, then

```text
continuedHzeta rho 1 = 0,
deriv (continuedHzeta rho) 1 != 0,
analyticOrderAt (continuedHzeta rho) 1 = 1.
```

The last conclusion holds even when `analyticOrderAt xi rho` is greater than one.

## Proof

For `Re s>0`, the canonical regularization degree is zero.  On the disk
`|a-1|<1/2`, every base `m+a` lies in the slit plane.  The derivative of the zero-degree
Taylor-subtracted summand is

```text
-s * (m+a)^(-(s+1)).
```

Its norm is bounded uniformly on the disk by a constant times

```text
((m+1)/2)^(-(Re s+1)),
```

a summable real `p`-series.  Termwise differentiation therefore proves analyticity on a
neighborhood of `1`.  At the anchor, the derivative series sums to
`-s*zeta(s+1)`.

The existing all-order ladder holds on the open upper half-plane. Local analyticity at `1` makes
both its left side and its shifted-zeta right side continuous at the anchor. Since `1` lies in the
closure of the upper half-plane, uniqueness of limits extends the ladder identity to `a=1` for
every order.

For an Xi zero in `Re rho>0`, the existing Xi--zeta zero correspondence and
`continuedHzeta rho 1=zeta(rho)` give the zero value.  Since `Re(rho+1)>1`, Euler-product
nonvanishing gives `zeta(rho+1)!=0`; also `rho!=0`.  The derivative is nonzero, hence the analytic
order is one.

## Top-down attack verdict

The tempting collision

```text
RHLadder 1
  + a local biholomorphic germ weld from xi at rho to
      a |-> continuedHzeta rho a at a=1
  -> Xi order at rho is one
  -> Xi order at rho is both one and even
  -> RH
```

does not pass the non-redressing gate.  Because the Hurwitz anchor germ is simple, existence of
such a local biholomorphic weld is locally equivalent to simplicity of the Xi zero.  It is the
existing ladder--simplicity collision in a new coordinate, not an independent source theorem.
No RH capstone for that wrapper is added.

The positive retained statement is instead the unconditional two-variable incidence geometry:
all Xi exponents lie on the common value fiber `continuedHzeta(s,1)=0`, while that fiber is
transverse in the shift direction at every such exponent.  Any future RH use must add a genuinely
global value relation or source constraint coupling the exponent direction to this transverse
shift direction.

## Lean certificate

Principal declarations:

- `continuedHzeta_analyticAt_one_and_hasDerivAt`
- `continuedHzeta_analyticAt_one`
- `continuedHzeta_hasDerivAt_one`
- `ascPochhammer_eval_ne_zero_of_pos_re`
- `continuedHzeta_iteratedDeriv_at_one`
- `continuedHzeta_iteratedDeriv_at_one_ne_zero`
- `continuedHzeta_xiZero_at_one`
- `continuedHzeta_xiZero_deriv_at_one_ne_zero`
- `analyticOrderAt_continuedHzeta_xiZero_at_one`

## Gates

- [x] 0 → 1: canonical boundary gap isolated; no zero-location premise
- [x] 1 → 2: normal-convergence and derivative proof complete
- [x] 2 → 3: exact Lean modules build
- [x] all-order extension: the full positive anchor jet is explicit and nonvanishing
- [x] non-redressing audit: local germ-weld RH wrapper rejected
- [ ] 3 → 4: no publication claim; theorem is standard analytic continuation infrastructure

## Log

- 2026-07-13 — proved full-disk analyticity, the exact all-order anchor jet, and nonvanishing of
  every positive-order jet; specialized the zero/order statement to the Xi divisor and rejected
  the simplicity-equivalent germ-weld capstone.
