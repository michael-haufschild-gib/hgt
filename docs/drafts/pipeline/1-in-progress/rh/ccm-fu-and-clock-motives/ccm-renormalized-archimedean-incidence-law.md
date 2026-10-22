# CCM scalar-renormalized archimedean incidence law

- **ID:** `ccm-renormalized-archimedean-incidence-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE] [NOT AN RH PROOF]`
- **Source:** the candidate scalar-renormalized archimedean radial diagonal law and the exact radial
  prime law
- **Statement:** The full scalar-renormalized archimedean radial form is bounded at the first
  leakage scale. The remaining conjecture is a second-order limit law, including any surviving
  off-diagonal constant.

## Exact renormalization

Let `A_arch` be Suzuki's archimedean multiplier form, `G_lambda(j,k)` the radial Gram matrix, and
`c=2*pi*lambda^2`. Define

```text
B_lambda(j,k)
 =A_arch(H_(lambda,j),H_(lambda,k))
  -log(c)*G_lambda(j,k).                                       (1)
```

The subtraction in `(1)` is a scalar identity shift relative to the Gram metric. The Lean theorem
`rayleighExcessRatio_add_real_smul_id` proves that it leaves the Rayleigh-excess-to-gap ratio
unchanged exactly.

## Conjecture

`[PROVED in ccm-countable-log-chirp-renormalization-law.md]` The complete renormalized form obeys

```text
B_lambda(R_lambda,R_lambda)=O(d_1(lambda)).                      (2)
```

The stronger second-order statement remains conjectural:

```text
B_lambda(R_lambda,R_lambda)/d_1(lambda)
 ->D_arch^ren+D_arch^off,                                       (3)
```

where the candidate diagonal constant is

```text
D_arch^ren
 =8/(11*pi) sum_(k>=1)1/k integral_0^arcsin(1/k)
    log(1/(pi*sin(2*u)))du.                                    (4)
```

Adding the proved raw prime constant gives

```text
K_exterior^ren
 =D_arch^ren+D_arch^off
  -16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k).                    (5)
```

Numerical evaluation after deriving the diagonal part gives `D_arch^ren` approximately `-0.071`.
Setting the unproved `D_arch^off` to zero would give `K_exterior^ren` approximately `-0.511`;
this is calibration only and is not evidence that the off-diagonal constant vanishes.

## Attack

On the exterior half-line, the radial family has the exact translation relation

```text
H_(lambda,k)(s)=k^(-1/2)H_(lambda,1)(s+log k),  s>=0.            (6)
```

The half-line boundary must not be discarded. After zero extension, `(6)` gives

```text
hat H_k(xi)
 =k^(-1/2)exp(i*xi*log k)
   Fourier(1_[log k,infinity)*H_1)(xi).                          (7)
```

Thus the matrix is a truncated-translation, not a pure Toeplitz, correlation; replacing the
truncated transform in `(7)` by `hat H_1` would erase the Bessel endpoint and is invalid. Prove
the limit `(3)` from `(7)`, or equivalently by second-order half-line semiclassical multiplier
calculus, using the differentiated Dunster spectral density. The countable log-chirp theorem has
already proved the required `O(d_1)` bound. To identify `D_arch^off`, the
`j,k>=2` sector should inherit the exact nonstationary `1/(c*j*k*|j-k|)` bound with one additional
`1+log(j+k)` factor. The first row should inherit the proved Weber bound with an additional
`1+log k`; both remain summable. This is a bilinear multiplier estimate, not cancellation of the
universal `d_1*log c` scalar mass.

## Downstream chain

```text
renormalized archimedean incidence law
  + exact radial prime constant
  + parity/even-gap lower bound
  -> source Rayleigh-excess ratio
  -> projective ground-vector convergence
  -> locally uniform Hermitian determinants
  -> RH.
```

## Failure conditions

1. A scalar-renormalized off-diagonal family survives at order `d_1`; it must be computed as
   `D_arch^off`, not discarded.
2. The central Poisson correction contributes at order `d_1` after scalar renormalization.
3. The true low eigenspace is not contained in the radial carrier on which `(1)` is the correct
   scalar shift.
4. Even if `(5)` is proved, failure of a true even-gap lower bound leaves the determinant chain
   open.

## Gates

- [x] scalar shift isolated and formalized in Lean
- [x] full scalar-renormalized radial form bounded by `O(d_1)`
- [x] renormalized diagonal candidate constant derived and numerically calibrated
- [ ] prove the second-order diagonal localization theorem
- [x] prime constant available
- [ ] compute the second-order off-diagonal constant
- [ ] audit the central term after scalar renormalization
- [ ] compare with the true even gap
