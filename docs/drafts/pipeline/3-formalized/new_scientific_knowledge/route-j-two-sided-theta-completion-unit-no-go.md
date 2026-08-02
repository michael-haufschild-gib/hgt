# Route J two-sided theta completion unit no-go

- **ID:** `route-j-two-sided-theta-completion-unit-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / LITERAL-SOURCE NO-GO / POSITIVE UNIT LAW
- **Scientific status:** `[CORPUS-NEW ROUTE CLOSURE; NO EXTERNAL PRIORITY CLAIM]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTwoSidedCompletionNoGo.lean`
- **Source identity:** `XiCTaylorThetaTailCompletedDensityReflection.lean`

## Literal survivor

Let

```text
A(z)=integral_(0,infinity) rho(t) exp(i t z) dt
```

be the canonical theta-tail second-density phase value, and retain both decaying and reflected
growing channels:

```text
B(z)=A(z)+A(-z).
```

This is the source-defined two-sided completion, not an arbitrary signed density and not a
target-fitted interpolant. The existing exact crossed source identity is

```text
(z^2+1/4) B(z)=1/2+4z^2 XiC(z).                       (JT1)
```

Both sides are holomorphic in the open theta Fourier--Laplace strip `|Im z|<1`.

## New consequence

If `XiC(z)=0`, `(JT1)` becomes

```text
(z^2+1/4) B(z)=1/2.                                   (JT2)
```

Therefore

```text
z^2+1/4 != 0,
B(z) != 0.                                             (JT3)
```

The positive survivor exposed by the no-go is stronger than mere failure to screen:

```text
the literal two-sided theta completion is an analytic unit at every Xi divisor in its strip.
```

No sign or normal-family estimate is used. The fixed meromorphic order of `B` at the divisor is
exactly zero.

Let `sigma` lie in the critical strip and let

```text
z_0=i(1/2-sigma).
```

Then `|Im z_0|<1`. If `xi(sigma)=0`, the analytic-unit gauge law gives, for every source-selected
superaccurate Xi Taylor schedule,

```text
delta_n [
  Im logDeriv(P_n)(z_n)-Im logDeriv(B)(z_n)
]
  -> ord_sigma(xi).                                    (JT4)
```

Since a zero has positive order, the transferred charge cannot tend to zero. Hence the literal
two-sided theta completion does not screen any nonzero Xi divisor.

## Why this is not the positive-completion theorem again

The one-sided transform `A(z)` is zero-free in the upper half-plane by positivity. The two-sided
object `B(z)` contains the reflected growing channel, so that positivity proof does not apply.
Its unit law instead follows from the exact completed reflection relation `(JT1)`. Thus this
closes a genuinely different canonical signed survivor.

## What this closes

Closed class:

```text
canonical theta-tail second-density pair A(z)+A(-z),
with its literal source derivative and exact crossed completion law.
```

Still open:

1. noncanonical signed theta densities not constrained by `(JT1)`;
2. singular integration-by-parts boundary terms;
3. source laws whose two-sided completion is relation-valued rather than scalar;
4. symmetry-breaking support deformations outside the canonical reflected pair.

All remain Route J.

## Novelty and theatre audit

The crossed identity `(JT1)` already existed unconditionally in Lean. The new contribution is
its previously unrecorded divisor-unit consequence and exact connection to the anisotropic gauge
screening classification. Algebraic difficulty is low; scientific value is class closure of the
literal signed theta survivor. No external novelty or priority claim is made.

This is not representation theatre:

- `B` is fixed before choosing `sigma`;
- no zero location or multiplicity appears in its density;
- nonvanishing is derived from the source identity and the divisor equation;
- Lean concludes the actual finite-Taylor transfer retains full multiplicity.

## Lean audit

The new module proves unconditionally:

- the derivative and analyticity of `B` on `|Im z|<1`;
- `B(z)!=0` whenever `XiC(z)=0` in that strip;
- centered critical-strip points lie in the analytic strip;
- exact preservation of anisotropic Taylor divisor charge;
- impossibility of exact gauge screening at every Xi zero in `0<Re sigma<1`.

Direct command:

```text
cd formal
lake env lean GaloisForLFunctions/RHTower/XiCTaylorThetaTailTwoSidedCompletionNoGo.lean
```

passes with no warnings. Module is wired into
`formal/GaloisForLFunctions/RHTower.lean`. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration occurs.

## Route consequence

`J-SF6` loses its most literal signed reflection escape. A surviving signed theta completion must
alter the canonical density or its support law enough to escape `(JT1)`, carry a singular boundary
term, or cease to be a scalar meromorphic gauge.
