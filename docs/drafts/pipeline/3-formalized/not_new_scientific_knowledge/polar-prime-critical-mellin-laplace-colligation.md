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
cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
cauchyKernel_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
```

## Route consequence

The source-identification part of the four-channel route is now formal on the real convergence
ray:

```text
continuous polar input + resolved von Mangoldt output + signed critical Mellin defect
  -> exact universal Cauchy coordinate.                              [Lean]
```

What remains RH-bearing is not this identity.  It is the source-selected Gauss/Sonin graph
realization and its cofinal passivity or four-unit relative-trace bound:

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
- Scratch `#print axioms` for the five new theorems reports only
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
- [x] signed critical Mellin-defect channel defined independently of the target identity
- [x] scalar and two-variable real-kernel colligations formalized
- [ ] construct the corresponding source-selected Gauss/Sonin graph
- [ ] prove cofinal passivity or the four-unit boundary relative-trace estimate
- [ ] RH
