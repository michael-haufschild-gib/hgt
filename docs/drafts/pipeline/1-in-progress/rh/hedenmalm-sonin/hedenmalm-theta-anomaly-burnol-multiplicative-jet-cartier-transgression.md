# Hedenmalm theta anomaly: multiplicative-jet/Cartier transgression

- **Label:** `P-G119`
- **Route:** P
- **Parents:** `P-G118`, Burnol Cartier head-energy Stokes flux
- **Status:** theorem proved and formalized; direct, exact module, and axiom audits passed; umbrella
  imported

## Conjecture tested

P-G118's arithmetic multiplicative-jet numerator and Burnol's Cartier two-head energy should be
two realizations of one source transgression.  At a right-half Xi divisor `rho`, let `q` be any
multiplicity copy above `rho`, let

```text
E = |A2(z_q)|^2 + |A3(z_q)|^2,
J = du(z_q)/k3 conj(A3(z_q)) + dv(z_q)/k2 conj(A2(z_q)),
F = oriented Cartier divided-shift head flux.
```

The exact division-free bridge should be

```text
E * (transferred head energy - fixed head energy) = 2 F Im(J).
```

Moreover `Im(J)>0` and `F>0` on a hypothetical right-half zero, so both sides are strictly
positive.

## Paper proof plan

P-G118 gives `Re(gauge) E = 2 Im(J)`.  On a copy over `rho`, the source gauge is exactly
`2(Re(rho)-1/2)`.  Burnol's existing exact Stokes transgression gives

```text
head-energy defect = 2(Re(rho)-1/2) F.
```

Multiplication and reassociation yield the bridge without division.  P-G118 also gives
`J=-zE`; because `Im(z)=1/2-Re(rho)<0` and `E>0`, `Im(J)>0`.  Existing Cartier theory gives
`F>0` in the right half of the critical strip.

## Result

Conjecture succeeds exactly.  Lean proves both normalized and division-free forms:

```text
head-energy defect = -2 Im(connection) F,
E * head-energy defect = 2 F Im(J).
```

At every hypothetical right-half Xi divisor, `Im(J)>0`, `F>0`, their pairing is strictly
positive, and hence the frame-energy-weighted Cartier defect is strictly positive.  Arithmetic
Euler dilation jets and Archimedean Cartier head transfer therefore carry the same oriented source
class.

This is a substantive no-go closure for positive completion: Cartier head energy cannot cancel
the Route P anomaly because its transgression has the anomaly's sign.  The strongest positive
survivor is the exact arithmetic/Archimedean source-pairing law.  Remaining producer must introduce
an independently derived opposite-signed term before taking positive energy, or force a completed
signed Ward current to vanish.  No RH conclusion is claimed.

## Scientific decision gate

- **Success:** arithmetic Euler dilation jets and Archimedean Cartier head energy are one
  transgression.  Positive completed receivers amplify the anti-Hermitian connection; they cannot
  supply Ward flatness.  Next producer must provide a genuinely opposite-sign signed term before
  positive energy completion.
- **Failure:** isolate which identification is false, retain strongest dependency-closed survivor,
  and pivot to factorization-independent prime-pair connection or a signed KMS completion.
- No theorem may claim RH unless an independent source law forces the resulting positive quantity
  to vanish or be nonpositive at every Xi divisor.

## Verification log

- 2026-08-13 — Card opened.  Corpus search found exact P-G118 gauge/frame identity and existing
  Burnol Cartier head-current positivity; no existing theorem joins them.
- 2026-08-13 — Direct `lake env lean` passed.  Exact module build passed at `[12941/12941]`; module
  imported by `RHTower.lean`.
- 2026-08-13 — Axiom audit of all five capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-13 — Full `GaloisForLFunctions.RHTower` umbrella build passed at `[19795/19795]`.
