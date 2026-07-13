# Finite positive prime--archimedean tensor sections have only negative real zeros

- **ID:** `prime-arch-dual-cauchy-finite-tensor-law`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / [POSITIVE FINITE PRODUCER] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeArchDualCauchyTensor.lean`
- **Consumer:** `../../1-in-progress/prime-arch-dual-cauchy-rsk-fredholm-rh.md`

## Theorem

For finite index sets `P,A` and positive real weights `x_p,y_j`, define

```text
F(u)=product_(p in P) product_(j in A) (1+u x_p y_j).
```

Lean proves that every zero of `F` is a negative real number.  More precisely, a vanishing factor
gives

```text
u=-(x_p y_j)^(-1)<0.
```

It also defines the pair-product power sums and proves the exact tensor identity

```text
sum_(p,j)(x_p y_j)^n
  =(sum_p x_p^n)(sum_j y_j^n).
```

This is simultaneously the finite spectral trace law for a tensor product of positive diagonal
operators and the logarithmic power-sum law of the dual-Cauchy product.

## Positive boundary

The finite root geometry is complete.  No additional stability or determinant theorem is needed
once both alphabets are positive.  Therefore a failed RH construction cannot be blamed on the
finite tensor section: the only remaining burdens are to construct the archimedean alphabet from
the completed source, prove the trace identities, and obtain one trace-norm cofinal limit whose
Fredholm determinant is the square-coordinate Xi function.

This theorem does not assert that such an alphabet exists and does not identify the finite product
with Xi.

## Formal declarations

- `finitePrimeArchFermionSection`;
- `finitePrimeArchPairPowerSum`;
- `finitePrimeArchPairPowerSum_eq_mul`;
- `finitePrimeArchFermionSection_zero_is_negativeReal`.

The exact module build is green.  Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] finite pair-product section defined
- [x] exact tensor power-sum factorization formalized
- [x] every finite zero classified as negative real
- [x] accepted-axiom audit
- [ ] source archimedean alphabet constructed
- [ ] trace-norm cofinal Xi comparison
