# The first self-dual code direct sum creates a critical-circle Duursma interaction

- **ID:** `double-repetition-duursma-zeta-interaction`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[FINITE BASELINE] [POSITIVE NONMULTIPLICATIVITY] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/DuursmaDoubleRepetition.lean`
- **Consumer:** `../../1-in-progress/prime-syndrome-duursma-code-zeta-limit-rh.md`

## Theorem

The binary repetition code `[2,1,2]` has weight enumerator `x^2+y^2` and Duursma zeta polynomial
`1`.  Its direct sum with itself is the self-dual `[4,2,2]` code with

```text
W(x,y)=x^4+2x^2y^2+y^4=(x^2+y^2)^2.
```

For a candidate degree-two zeta polynomial `a+bT+cT^2`, Lean expands the defining degree-two
Duursma coefficient extraction and proves that it equals `(W-x^4)/(2-1)` for all `x,y` exactly when

```text
(a,b,c)=(1/3,0,2/3).
```

Thus

```text
P(T)=(1+2T^2)/3.
```

The numerator is one third of the reciprocal block `iharaBlock 2 0`.  The existing sharp quadratic
selector therefore gives

```text
P(T)=0 -> |T|^2=1/2,
```

so this first assembled self-dual code satisfies the binary code Riemann hypothesis.

## Positive nonmultiplicativity

Lean also proves

```text
P_(C direct-sum C)(T)=P_C(T)^2+(2/3)(T^2-1),
P_(C direct-sum C) != P_C^2.
```

Therefore direct-sum code assembly is not a disguised product of disconnected local zeta
numerators.  It creates a normalized quadratic interaction at the smallest possible self-dual
example while retaining the critical-circle law.  For the prime-syndrome detour, this is positive:
a source-faithful code construction could retain cross-prime information.  The theorem does not
construct the prime-syndrome code or any cofinal limit to `XiC`.

## Formal certificate

The module proves:

- `binaryDegreeTwoDuursmaCoefficient_expanded`;
- `doubleRepetition_duursma_definingCoefficient`;
- `doubleRepetition_duursma_coefficients_unique`;
- `doubleRepetitionDuursmaZeta_eq_scaled_iharaBlock`;
- `doubleRepetitionDuursmaZeta_directSumInteraction`;
- `doubleRepetitionDuursmaZeta_not_multiplicative`;
- `doubleRepetitionDuursmaZeta_zero_criticalCircle`.

The exact module and the `RHTower` umbrella build.  Axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] defining coefficient extraction expanded
- [x] zeta coefficients proved unique
- [x] direct-sum nonmultiplicativity proved
- [x] binary critical-circle law proved
- [x] exact Lean build
- [x] umbrella build
- [x] accepted-axiom audit
- [ ] source-syndrome realization
- [ ] cofinal microscopic limit
