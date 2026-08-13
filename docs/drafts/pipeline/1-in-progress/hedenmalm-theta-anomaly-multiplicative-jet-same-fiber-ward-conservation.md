# Hedenmalm theta anomaly: multiplicative-jet same-fibre Ward conservation

- **Label:** `P-G120`
- **Route:** P/R
- **Parents:** `P-G118`, `P-G119`, Route R same-fibre completed-Xi/theta orientation
- **Status:** theorem proved and formalized; direct, exact module, and axiom audits passed; umbrella
  imported

## Conjecture tested

The positive arithmetic/Cartier current and negative compact-theta boundary current should form an
exact same-fibre signed conservation law, not merely have opposite signs.  For an Xi copy `q`, set

```text
E = two-prime arithmetic frame energy,
J = Hermitian multiplicative-jet numerator,
N² = norm square of the completed first-divided Xi vector,
B = compact theta rank-two boundary flux.
```

The division-free Ward identity should be

```text
E (pi M B) + Im(J) N² = 0.
```

At a right-half Xi divisor, Cartier transfer should give the equivalent physical identity

```text
2 F (pi M B) + N² (transferred head energy - fixed head energy) = 0.
```

Here `F` is the strictly positive oriented Cartier head flux.

## Paper proof plan

Same-fibre theta orientation gives `pi M B = Im(z) N²`.  P-G118 gives
`J=-zE`, hence `Im(J)=-Im(z)E`; substitution proves the first identity without division.  P-G119
gives `head defect=-2 Im(z)F`; substitution proves the Cartier form.  On a hypothetical right-half
zero, `E(pi M B)<0` and `Im(J)N²>0`, so cancellation is between two nonzero channels.

## Result

Conjecture succeeds exactly.  Lean proves the global division-free Ward law on every Xi
multiplicity copy and the physical Cartier form on every hypothetical right-half copy.  It also
proves strict negativity of the theta channel, strict positivity of the arithmetic channel, and
that each channel vanishes exactly on the critical line.  Their total nevertheless vanishes
unconditionally.

This closes generic signed total-current cancellation as a Route P producer.  Strongest positive
survivor is a coefficient-faithful two-channel Krein conservation law joining multiplicative Euler
jets, completed Xi divided energy, compact theta flux, and Cartier head transfer.  Missing theorem
must impose channelwise flatness through a definite boundary/passivity condition; conservation
alone contains no line selector.  No RH conclusion is claimed.

## Scientific decision gate

- **Success:** exact signed Ward cancellation is unconditional and therefore cannot select RH.
  Route P requires channelwise flatness, or a positive/Krein boundary condition excluding nonzero
  conserved pairs—not another total-current Ward identity.
- **Failure:** retain exact partial bridge and test factorization-independent prime-pair connection
  before changing routes.
- No RH claim may follow from total signed cancellation alone.

## Verification log

- 2026-08-13 — Card opened after P-G119 proved arithmetic/Cartier orientation positive and corpus
  audit found existing same-fibre completed-Xi/theta orientation negative.
- 2026-08-13 — Direct `lake env lean` passed.  Exact module build passed at `[12942/12942]`; module
  imported by `RHTower.lean`.
- 2026-08-13 — Axiom audit of six capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
