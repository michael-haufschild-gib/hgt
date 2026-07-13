# Prime-Frobenius ramification on the local Xi jet — retired

- **ID:** `prime-frobenius-local-jet-simplicity-rh`
- **Stage:** 5-failed
- **Type:** `[PROVED NO-GO]`, `[POSITIVE SUCCESSOR EXTRACTED]`
- **Abstract Lean theorem:** `LocalDivisorJetPrimeFrobenius.lean`
- **Source-correct successor:** `LocalDivisorJetAdamsDilation.lean`

## Retired claim

The proposed route asked the Euler/Adams operation at a prime power to act on

```text
A_m = C[X]/(X^m)
```

by ramification `X |-> X^n`.  If that map were an automorphism for `n >= m`, the formal theorem
`localDivisorJet_primePower_equiv_forces_simple` would indeed force `m=1`, and the conditional RH
capstone in the same file is correct.

The source identification is false.  For the actual Euler coordinate

```text
x_p(s) = p^(-s),
x_p(rho + X)^n = p^(-n rho) exp(-n log(p) X).
```

Thus the analytic local coordinate undergoes the dilation `X |-> n X`, not the ramification
`X |-> X^n`.  The theorem `primeDerivativeJet_primePower_coeff` proves this on every coefficient of
the corpus's actual finite prime derivative jet.  A nonzero dilation is reversible for every jet
depth, so reversibility supplies no reducedness information.

## Why no alternative source interpretation rescues the route

`AdamsOperations.lean` raises Satake parameters and sends the Euler base to a prime power.  Neither
operation ramifies the spectral parameter `s-rho`.  Transporting `X |-> X^n` through an arbitrary
finite-prime Vandermonde isomorphism would define a target-fed operation, not identify the Adams
operation.  Ordinary Euler multiplication is separately divisor-jet blind by `SigmaDivisorJet.lean`.

The abstract ramification theorem remains reusable if a genuinely ramified, globally source-defined
operation is ever found, but it is not an Euler/Frobenius/Adams consequence.

## Positive successor

The correct dilation has spectrum

```text
1, n, ..., n^(m-1)
```

and diagonal determinant

```text
n^(m(m-1)/2).
```

It therefore remembers multiplicity without destroying the cotangent direction.  Two valid
successors are:

1. a single-pure-weight realization of the local Adams spectrum, which forces `m=1` because the
   eigenvalues cannot have one common norm when `m>1` and `n>=2`;
2. a Lefschetz comparison whose trace defect is
   `sum_(j<m) (n^j-1)`, positive exactly for `m>1`.

The first successor and its RH consumer are formalized in
`LocalDivisorJetAdamsDilation.lean`; the missing theorem is the source-derived local purity
comparison.

## Status

- `[PROVED LEAN]` the abstract ramification-plus-invertibility implication;
- `[PROVED NO-GO LEAN]` the actual prime-power derivative jets transform by dilation instead;
- `[RETIRED]` Euler/Adams descent to `X |-> X^n`;
- `[POSITIVE]` dilation determinant, pure-weight obstruction, and corrected Lefschetz defect.
