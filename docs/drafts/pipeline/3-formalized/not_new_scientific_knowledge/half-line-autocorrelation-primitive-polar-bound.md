# A bounded growing half-density primitive controls polar autocorrelation

- **ID:** `half-line-autocorrelation-primitive-polar-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM / ANALYTIC INFRASTRUCTURE
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/HalfLineAutocorrelationPrimitive.lean`

## Statement

For a real half-line source `R`, put

```text
C_R(h)=integral_0^infinity R(s+h)R(s)ds,
A_R(t)=integral_0^t exp(s/2)R(s)ds.
```

Under the natural local-integrability and Fubini hypotheses, for every `H>=0`,

```text
integral_0^H exp(h/2)C_R(h)dh
 =integral_0^infinity exp(-s/2)R(s)
   [A_R(s+H)-A_R(s)]ds.                                      (1)
```

Consequently, if `|A_R(t)|<=M` on the positive half-line, then

```text
|integral_0^H exp(h/2)C_R(h)dh|
 <=2M integral_0^infinity |exp(-s/2)R(s)|ds.                  (2)
```

The cancellation is performed before absolute values are taken.  Thus an oscillatory bounded
primitive controls the exponentially growing branch of the polar kernel even when the growing
weighted source itself is not absolutely integrable.

## Connes-route use

For the constrained radial prolate tail, the exact Bessel/Liouville--Green phases are expected to
give `M=O(sqrt(d_1)/c)`, while the decaying weighted source has `L1` norm `O(sqrt(d_1))` by
Cauchy--Schwarz and the radial norm law.  Equations `(1)`--`(2)` then turn the continuous polar
charge into `O(d_1)`.  The concrete radial primitive remains a separate analytic theorem; this
card does not hide it as an assumption about the actual CCM source.

## Lean declarations

```text
halfLineAutocorrelation
halfLineExpPrimitive
integral_exp_half_mul_halfLineAutocorrelation_eq_primitive
abs_integral_mul_primitive_sub_le
```

The two headline theorems compile in the leaf module and their axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Classification

Equation `(1)` is Fubini plus translation of an interval integral, and `(2)` is the triangle
inequality.  The result is useful infrastructure, not new parent mathematics.

## Gates

- [x] exact half-line Fubini identity formalized
- [x] bounded-primitive estimate formalized
- [x] umbrella import registered
- [x] axiom audit passed
- [ ] discharge the concrete constrained radial primitive estimate

