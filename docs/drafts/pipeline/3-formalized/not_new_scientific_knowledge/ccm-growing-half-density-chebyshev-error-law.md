# The growing half-density reads the unnormalized Chebyshev error

- **ID:** `ccm-growing-half-density-chebyshev-error-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / CRITICAL-MELLIN SOURCE IDENTITY
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCM/CCMCriticalMellinGrowingCumulative.lean`

## Statement

Let

```text
dM(h)=2cosh(h/2)dh
 -sum_(n>=2)Lambda(n)n^(-1/2)delta_(log n)(h)
```

be the polar--prime critical Mellin measure.  At finite aperture `2a`, define

```text
J(a)=integral_(0,2a] exp(h/2)dM(h).
```

Then, unconditionally,

```text
J(a)
 =exp(2a)-1+2a-Psi(exp(2a))
 =2a-1-[Psi(exp(2a))-exp(2a)].                                (1)
```

The identity follows because at every logarithmic atom

```text
n^(-1/2) exp(log(n)/2)=1,                                     (2)
```

while

```text
exp(h/2)*2cosh(h/2)=exp(h)+1.                                 (3)
```

The real cumulative is exactly the existing complex critical-Mellin Stieltjes pairing evaluated
on the growing half-density.

## Positive Connes consequence

The Poisson-center cross autocorrelation contains

```text
exp(h/2) integral_h^infinity exp(-t/2)R_lambda(t)dt.
```

Fubini and `(1)` turn its coupled polar--prime value into the single source integral

```text
integral_0^infinity exp(-t/2)R_lambda(t)
 [t-1-(Psi(exp t)-exp t)]dt.                                  (4)
```

Thus the center correction is not an undefined difference of divergent prime and polar channels.
It is one explicit PNT-error pairing.  Proving the exact radial envelope for `R_lambda` makes `(4)`
lower order at the prolate leakage scale.

## Lean declarations

```text
criticalMellinAtomWeight_mul_exp_log_half
criticalMellinGrowingCumulative
criticalMellinGrowingCumulative_eq
criticalMellinGrowingCumulative_eq_chebyshevError
criticalMellinStieltjesPairing_exp_half_eq
```

The leaf module compiles, is registered in the RHTower umbrella, and all four audited headline
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Classification

This is an exact Abel/Stieltjes evaluation and a change of weight in the Chebyshev cumulative sum.
It is a route-relevant bridge, not new parent mathematics and not an estimate for the PNT error.

## Gates

- [x] atomwise square-root cancellation formalized
- [x] continuous growing polar integral evaluated
- [x] Chebyshev-error identity formalized
- [x] complex Stieltjes carrier identification formalized
- [x] umbrella import registered
- [x] axiom audit passed
- [ ] combine with the concrete summed radial envelope
