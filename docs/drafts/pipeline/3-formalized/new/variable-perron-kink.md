# Variable-width Perron kink

- **ID:** variable-perron-kink
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED HERE]`
- **Date:** 2026-07-10
- **Paper source:** `../../2-fully-proven/new/quiet-flank-growth-support-radius.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/VariablePerronKink.lean`
- **Statement:** For every integer `n>=1` and real `0<delta<1`, the smoothed Perron second
  difference at the knots `n+delta,n,n-delta` is exactly `delta*a_n`. Its numerator vanishes at
  `s=0,-1`, admits an entire double-difference regularization, and has left-edge frequency scale
  `n-delta`.

## Delivered declarations

- `perronKinkAt`
- `perronKinkAt_oneHalf_eq`
- `perronKinkAt_zero`
- `perronKinkAt_negOne`
- `perronKinkAt_differentiable`
- `perronEAt`
- `perronEAt_oneHalf_eq`
- `perronEAt_differentiable`
- `perronEAt_eq`
- `perronKinkAt_norm_le`
- `perronKinkAt_second_difference`
- `perronSecondDiffAt_integral`

## Mathematical content

For an earlier integer `m<n`, all three values of `max(x-m,0)` lie in the same affine region, so
their second difference vanishes. For `m=n`, the weights are `delta,0,0`; for `m>n`, all weights
vanish because `delta<1`. Thus only `a_n` survives, with coefficient `delta`.

At the complex level,

`K_{n,delta}(s)=(n+delta)^(s+1)+(n-delta)^(s+1)-2n^(s+1)`

vanishes at `s=0` and `s=-1`. Applying `dslope` at both points produces an entire regularization
equal to `K_{n,delta}(s)/(s(s+1))` away from the removed poles. On `Re(s)=-M`, the triangle bound is
controlled by `(n-delta)^(1-M)`, which is the exact scale consumed by the variable-flank support
theorem.

## Scope

- `[PROVED]` The fixed half-width kernel is definitionally the specialization `delta=1/2`.
- `[PROVED]` The coefficient extraction and removable-pole interfaces are fully formalized.
- `[PROVED]` The exact coefficient extraction is identified with the vertical Perron integral.
- `[PROVED]` The norm bound exposes the variable left-edge frequency `n-delta`.
- `[OPEN CORE]` The generic rectangle-contour theorem turning an abstract left-flank envelope into
  `HasVariableQuietFlankCoefficientBound` has not yet been factored from the conductor proof.

## Verification

- Target module source compile: PASS.
- Target module build: PASS (`8478/8478`); no umbrella build was run.
- Scratch `#check`: PASS for the principal kernel and integral theorems.
- Scratch `#print axioms`: each principal theorem uses only
  `{propext, Classical.choice, Quot.sound}`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 -> 1: variable knot width and exact coefficient isolated.
- [x] 1 -> 2: finite identity, entire regularization, and norm bound proved.
- [x] 2 -> 3: formalized, target-built, and axiom-audited.
- [ ] 3 -> 4: requires the generic rectangle producer and paper integration.
