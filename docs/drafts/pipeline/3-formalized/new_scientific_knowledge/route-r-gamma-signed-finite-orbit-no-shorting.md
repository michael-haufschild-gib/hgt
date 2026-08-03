# Route R signed finite Gamma-orbit no-shorting

- **ID:** `route-r-gamma-signed-finite-orbit-no-shorting`
- **Stage:** 3-formalized
- **Type:** THEOREM + CLASS-COMPLETE NO-GO
- **RH used:** no
- **Xi zero used:** no
- **Computation used:** no
- **Parent:** `singular-infinite-source-pointed-common-test-factorization.md`

## Frontier statement

The positive-cone theorem forces any Gamma shorting mechanism to use signed
cross-pair incidence.  That condition is not sufficient.  Every finitely
supported signed chain whose coefficients are fixed across modular
displacement is now excluded exactly.

Let a canonical cross-prime depth edge be

```text
E=(p,e;q,f),  p<q,
```

and put

```text
N_E=p^(e+1) q^(f+1),
lambda_E=log N_E.
```

If `E=(p,e;q,f)` and `E'=(r,g;s,h)` have the same `N`, unique factorization
first identifies the ordered prime supports `{p,q}={r,s}`.  The inequalities
`p<q` and `r<s` exclude the swapped orientation.  Valuation at `p` and `q`
then gives `e=g` and `f=h`.  Therefore

```text
E |-> N_E
E |-> lambda_E
```

are injective, and every `lambda_E` is strictly positive.

The actual cooriented Gamma exterior has the exact form

```text
C_E(a)=A_E sinh(lambda_E a),
A_E=b_E,left b_E,right (height_left-height_right)^2 > 0.
```

Its entire modular orbit is

```text
C_E^hol(z)=A_E sinh(lambda_E z),
```

whose restriction to real `z=a` is exactly the actual source exterior, not a
replacement model.

## Theorem

For every finite packet of distinct canonical cross-prime depth edges,

```text
{ z |-> C_E^hol(z) }_E
```

is linearly independent over `C`.  Equivalently, for every finitely supported
coefficient field `c`,

```text
forall z : C, sum_E c_E C_E^hol(z)=0
  ->
forall E, c_E=0.
```

Thus no nonzero locally finite signed source chain with
displacement-independent coefficients can be a universal modular
null-homotopy.  If every finite aperture of a compatible source chain is
already an exact orbit identity, every aperture is zero coefficientwise.

## Proof

For distinct positive frequencies `lambda_k`, consider the doubled frequency
packet

```text
beta(inl k)= lambda_k,
beta(inr k)=-lambda_k.
```

Positivity prevents a positive frequency from colliding with a negative one;
injectivity of `lambda` handles both equal-sign sectors.  Hence `beta` is
injective.  Vandermonde independence of the entire exponentials

```text
z |-> exp(beta_j z)
```

implies independence of

```text
sinh(lambda_k z)
  =(exp(lambda_k z)-exp(-lambda_k z))/2.
```

Indeed a relation among the sinh functions gives a relation on the doubled
exponential packet with coefficients `(c_k/2,-c_k/2)`, so every `c_k=0`.
Multiplication by `A_E>0` preserves independence.  The unique-factorization
argument above supplies the required distinct actual Gamma frequencies.

## Anti-theatre audit

This is not another critical-line detector and does not restate
`C_E(a)=0 iff a=0`.  It classifies a previously open producer category:
arbitrary signs are allowed, all canonical cross-prime/depth cells are
allowed, and conclusion is coefficientwise triviality of universal finite
shorting.

Generic exponential independence and prime factorization existed separately
in corpus.  New frontier content is identification of actual cooriented Gamma
cell orbit with simple semiprime-power frequency spectrum and resulting exact
kernel classification for signed Route-R source chains.

The theorem does not prove RH.  It forces next source object into a much
narrower category:

1. cancellation only after genuinely infinite completion; or
2. coefficients coupled nonseparably to divisor provenance/spectral
   parameter.

A fixed finite signed prime cycle, finite cross-pair boundary, or stagewise
exact finite aperture is now dead.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  GammaSignedFiniteOrbitNoShorting.lean
```

Key declarations:

- `xiGammaEulerCanonicalCrossPrimePairNat_injective`;
- `xiGammaEulerCanonicalCrossPrimeFrequency_injective`;
- `xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_ofReal`;
- `complexSinh_realFrequency_linearIndependent`;
- `xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_global_linearIndependent`;
- `xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_finsupp_noShorting`.

## Exact surviving producer

Construct a signed all-prime source differential whose finite apertures need
not vanish, whose cofinal limit cancels in the conservative Gamma graph, and
whose coefficients retain divisor provenance before completion.  Any claimed
producer lacking one of these three properties is excluded by this theorem or
the preceding positive-cone theorem.

## Countable strengthening: absolute-summability wall

The finite classification extends to every enumerated canonical cross-prime
depth chain whose physical orbit amplitudes are absolutely summable.  Let
`E_n` be pairwise distinct canonical edges and suppose

```text
sum_n |c_n A_(E_n)| < infinity.
```

If

```text
forall y : R,
  sum_n c_n C_(E_n)^hol(i y)=0,
```

then `c_n=0` for every `n`.

Proof uses Bohr--Cesaro extraction, not a finite truncation argument.  Write

```text
sinh(i lambda_n y)
  =(exp(i lambda_n y)-exp(-i lambda_n y))/2.
```

Absolute summability permits interchange of countable sum and Cesaro window
integral.  Multiply by `exp(-i lambda_m y)` and average.  Injectivity keeps
exactly the `+lambda_m` diagonal; positivity excludes every collision with
the `-lambda_n` sector.  Limit is `c_m A_(E_m)/2`.  Vanishing of the original
series makes same average zero, and `A_(E_m)>0` gives `c_m=0`.

This closes more than finite support.  An infinite signed chain with normal
or absolutely summable physical orbit convergence still cannot be the
universal null-homotopy.  Surviving completion must be genuinely singular
beyond `ell1` orbit amplitude, or its coefficients must depend
nonseparably on divisor provenance.

Additional Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  GammaSignedSummableOrbitNoShorting.lean
```

Capstones:

- `complexSinh_tsum_coeff_zero`;
- `xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_summable_noShorting`.
