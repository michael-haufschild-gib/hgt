# Finite-time high-moment sinc-energy law

- **ID:** `finite-time-high-moment-sinc-energy-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / DIRICHLET-POLYNOMIAL ENERGY REDUCTION / `[BRIDGE]`
- **Statement:** Every symmetric finite-time even moment of a finite Dirichlet polynomial is its
  independent Steinhaus moment plus an exact sinc-weighted multiplicative collision spectrum.
  The absolute deterministic-independence error is bounded by one explicit local
  multiplicative-energy functional of the iterated Dirichlet-convolution coefficients.

## The theorem

Let

```text
P(t)=sum_(n in S) a_n n^(-it),
P(t)^k=sum_m b_k(m)m^(-it),
```

where `S` is a finite set of positive integers and `a_n` is real.  For `T>0`, put

```text
K_T(m,n)=sinc(T log(n/m)),

E_k(T)=sum_(m!=n)|b_k(m)b_k(n)|
         min(1,1/(T|log(n/m)|)).
```

Then, on the symmetric window,

```text
(1/(2T)) integral_(-T)^T |P(t)|^(2k)dt
 =sum_m b_k(m)^2+sum_(m!=n)b_k(m)b_k(n)K_T(m,n),          (1)
```

and hence

```text
|(1/(2T)) integral_(-T)^T |P(t)|^(2k)dt
  -E_Steinhaus |sum_(n in S)a_n X_n|^(2k)|
 <=E_k(T).                                                  (2)
```

The pointwise kernel bound used in `(2)` is sharp in scale:

```text
|sinc(TL)|<=min(1,1/(T|L|)),   L!=0.                       (3)
```

More generally, for every shifted window `[A,A+U]` with `U>0`,

```text
(1/U) integral_A^(A+U) |P(t)|^(2k)dt
 =sum_m b_k(m)^2
  +sum_(m!=n)b_k(m)b_k(n)
    cosInt(log(n/m),A,U)/U,                                (4)
```

where

```text
|cosInt(L,A,U)/U|<=min(1,2/(U|L|)).                        (5)
```

Consequently the shifted-window deterministic--Steinhaus discrepancy is bounded by

```text
E_k^[U]
 =sum_(m!=n)|b_k(m)b_k(n)|min(1,2/(U|log(n/m)|)).           (6)
```

The position `A` changes the exact phases but disappears from the universal energy envelope.
Taking `A=U=T` gives the dyadic observation window `[T,2T]` used by the prime-log frontier
conjecture without introducing the trivially coherent time `t=0`.

## Role in the prime-log frontier

For the normalized critical prime polynomial, `b_k` is exactly the weighted `k`-fold prime-product
convolution.  Therefore every discrepancy between deterministic prime phases and the independent
phase model is concentrated in the cofinal local energy `E_k(T)`.  At the conjectural critical
regime

```text
k asymp pi(X),       log T asymp pi(X),
```

proving the required exponential bound for `(2)` is precisely the nonclassical gate in
`prime-log-kronecker-coherence-capacity-conjecture.md`.  Fixed-order moment convergence, ordinary
Kronecker recurrence, and the crude least-spacing bound do not control this regime.

## Novelty status

The algebraic power reduction, character orthogonality, sinc kernel, and triangle bound are
classical mechanisms.  This card is deliberately classified as a bridge, not new scientific
knowledge.  Its purpose is to make the genuinely new arithmetic obligation exact and
machine-checked.

## Formalization

Module:

```text
GaloisForLFunctions.RHTower.DirichletPolynomialSincEnergy
```

Principal declarations:

- `cosInt_symmetric_div_eq_sinc`
- `abs_sinc_mul_le_min`
- `abs_cosInt_le_window`
- `abs_cosInt_div_le_min`
- `secondMoment_window_kernel`
- `secondMoment_window_independence_error_le`
- `secondMoment_symmetric_sinc`
- `secondMoment_symmetric_sinc_error_le`
- `evenMoment_symmetric_sinc`
- `evenMoment_symmetric_independence_error_le`
- `evenMoment_window_kernel`
- `evenMoment_window_independence_error_le`

The source file passes a narrow `lake env lean` check.  No new axiom, placeholder, or numerical
certificate is introduced.
