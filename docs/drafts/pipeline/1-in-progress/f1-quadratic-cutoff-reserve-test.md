# The quadratic endpoint cutoff tests the reserved Gamma form

- **ID:** F1-QC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Two-moment payment](f1-primitive-variance-joint-payment.md)
- **Statement:** The odd unit-window profile `F(x)=2x(1−4x²)²` on `|x|≤1/2`, zero outside, has `P(F)+∫F²/64<0`; the inequality persists under support-preserving smoothing.

## Exact candidate data

`E=128/3465`, `m=∫xF=4/105`, and, for `0≤t≤1`,

`C(t)=128/3465−(256/315)t²+(128/21)t⁴−(128/15)t⁵
 +(512/105)t⁷−(128/63)t⁹+(256/693)t¹¹`.

Centering the overlap at `−t/2` reduces the correlation to the integral of
`(z²−t²)[z⁴−2(1+t²)z²+(1−t²)²]²` on `0≤z≤1−t`.
Thus the logarithmic lag and first lag are rational integrals of this polynomial.
The sinh pole is at least `m²/2`, since `xF(x)≥0`.

## Consequence if verified

This would refute both the uniform floor `P≥−E/64` and the sufficient two-moment
sign `D≥0`, because `D≤P+E/64`. It would not refute complete Weil positivity:
the exact local Gamma remainder and the reserve beyond `E/64` remain present.

## Gates

- [ ] Audit the exact correlation and rational sign certificate in Lean.
- [ ] Transfer the strict sign to a real odd C² test with exact unit support.
- [ ] Identify and prove the strongest positive survivor before retiring this target.

The full joint Gamma/prime/pole inequality remains active.
