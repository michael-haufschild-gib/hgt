# Fixed Burnol colligation landing cannot be completion

- **ID:** ULF-FBCL-FAILED
- **Stage:** 5-failed
- **Type:** retired source-factorization class
- **Status:** `[LEAN-KILLED] [POSITIVE SURVIVOR EXTRACTED]`

## Candidate

Identify the functional-equation radial channel with one fixed scalar mixture of the three exact
Burnol aperture-colligation channels: transported tail, deleted boundary interval, and positive
cocycle defect. Such a mixture is contractive after normalization and would put the completed
covariance directly in ULF-CRSHC-001.

## Exact killing mechanism

`RoutePPrimitiveBurnolConstantChannelLandingNoGo` proves that no fixed finite scalar mixture of
those three channels, applied to even one primitive source column, can equal one strict-right
completed-Xi conormal.

Reason is structural. Every primitive Burnol column has radial decay at rate

```text
lambda_(p,e)=(e+1)log p>=log 2,
```

and every fixed channel mixture retains that exponential floor. A strict-right completed conormal
has decay rate `Re(rho)-1/2` in `(0,1/2)`, strictly slower than every primitive rate. Their tail
ratio diverges, so equality is impossible.

## Strongest positive survivor

The three-channel map is still an exact matrix-complete isometric colligation on source packets.
Each selected channel is a legitimate contractive radial operation and therefore generates a
sub-unit recurrent completion by ULF-CRSHC-001. What fails is pointwise identification with the
completed conormal.

The actual `V_theta` must therefore be nonlocal or aperture-dependent, or contain an additional
completion-defect channel that changes exponential type. Covariance-level factorization may
survive even though featurewise equality does not.

## New insight

```text
cannot be: fixed finite source-channel mixing preserves enough tail type to become completion;
must be: completion changes exponential type while remaining contractive at covariance level.
```

## Status

Killing theorem is Lean-closed in
`RHTower.RoutePPrimitiveBurnolConstantChannelLandingNoGo`. No Lean changes or builds were made.
Survivor feeds the exact open factorization in ULF-TRDS-001.

