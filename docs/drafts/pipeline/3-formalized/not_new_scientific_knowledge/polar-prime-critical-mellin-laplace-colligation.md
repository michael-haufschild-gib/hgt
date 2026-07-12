# Polar--prime critical Mellin Laplace colligation

- **ID:** `polar-prime-critical-mellin-laplace-colligation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[FORMALIZED] [UNCONDITIONAL] [BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PolarPrimeMellinDefect.lean`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`

## Statement

For real `s>0`, Lean defines the continuous polar channel

```text
P(s)=integral_(0,infinity) exp(-(s+1/2)h) 2cosh(h/2) dh,
```

the resolved prime-power channel

```text
E(s)=sum_n Lambda(n)n^(-(s+1))
    =-zeta'(s+1)/zeta(s+1),
```

and the signed critical Mellin-defect channel

```text
M(s)=P(s)-E(s).
```

It proves

```text
P(s)=1/s+1/(s+1),
E(s)>0,
1/s=E(s)-1/(s+1)+M(s).
```

Consequently, for `x,y>0`,

```text
1/(x+y)
 =E(x+y)-1/(x+y+1)+M(x+y).
```

For every finite positive-node packet `x_i`, Lean now also proves that the resolved Euler matrix

```text
E_ij=E(x_i+x_j)
```

is positive semidefinite.  Its quadratic form is the convergent prime-power Gram sum

```text
sum_n [Lambda(n)/n] |sum_i c_i n^(-x_i)|^2 >= 0.
```

Thus the arithmetic coefficient remains unsquared, and all mixed node terms are retained.  The
scalar colligation simultaneously lifts entrywise to the exact finite matrix identity

```text
CauchyGram = EulerGram - ShiftedPolarGram + CriticalMellinDefectGram.
```

This is the real-kernel polar--prime Mellin colligation required by the diagonal Fock source
coordinate.  The signed channel is defined before the identity as the Laplace transform of the
continuous polar density minus the discrete von Mangoldt atoms.  No Xi divisor, zero location,
RH hypothesis, or target Gram factorization enters the construction.

## Lean declarations

```text
continuousPolarLaplaceChannel
vonMangoldtPrimeLaplaceChannel
criticalMellinDefectLaplaceChannel
continuousPolarLaplaceChannel_eq
vonMangoldtPrimeLaplaceChannel_eq_logDeriv
vonMangoldtPrimeLaplaceChannel_pos
vonMangoldtPrimeLaplaceGram
vonMangoldtPrimeLaplaceGram_posSemidef
cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
cauchyKernel_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
cauchyLaplaceGram
shiftedPolarLaplaceGram
criticalMellinDefectLaplaceGram
cauchyLaplaceGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
```

## Route consequence

The source-identification part of the four-channel route is now formal on the real convergence
ray:

```text
continuous polar input + resolved von Mangoldt output + signed critical Mellin defect
  -> exact universal Cauchy coordinate.                              [Lean]
finite positive node packet
  -> actual von Mangoldt prime-power Gram is positive semidefinite   [Lean]
  -> exact finite Cauchy/Euler/polar/Mellin matrix incidence         [Lean]
```

The finite Euler channel is therefore no longer part of the open sign problem.  What remains
RH-bearing is the signed critical Mellin-defect coupling inside the source-selected Gauss/Sonin
graph and its cofinal passivity or four-unit relative-trace bound:

```text
formal real-kernel colligation
  + source-selected relative graph convergence                       [OPEN]
  + cofinal passivity / four-unit boundary density                    [OPEN RH CORE]
  -> real Euler-ray kernel positivity or zero defect index
  -> RH.
```

## Verification

- `lake env lean GaloisForLFunctions/RHTower/PolarPrimeMellinDefect.lean` passed.
- `lake build GaloisForLFunctions.RHTower.PolarPrimeMellinDefect` passed.
- Scratch `#print axioms` for the seven new theorems reports only
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced.

## Classification

The Laplace evaluation, the Euler-region logarithmic derivative, and the channel rearrangement are
classical.  The result is a useful exact source bridge and a Lean formalization, not new scientific
knowledge and not an RH proof.

## Gates

- [x] continuous polar channel defined and evaluated
- [x] resolved von Mangoldt channel identified with the zeta logarithmic derivative
- [x] strict real-ray prime-channel positivity proved
- [x] all finite positive-node resolved Euler matrices proved positive semidefinite
- [x] signed critical Mellin-defect channel defined independently of the target identity
- [x] scalar and two-variable real-kernel colligations formalized
- [x] exact finite Cauchy/Euler/polar/Mellin matrix incidence formalized
- [ ] construct the corresponding source-selected Gauss/Sonin graph
- [ ] prove cofinal passivity or the four-unit boundary relative-trace estimate
- [ ] RH
