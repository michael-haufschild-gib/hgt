# Xi Taylor theta-tail core symmetric correlation

- **ID:** `xi-taylor-theta-tail-core-symmetric-correlation`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../5-failed/xi-taylor-theta-tail-core-density-current.md`

## Statement

For the canonical density `rho=4T''`, the shifted section `S_d`, and the core atom

```text
H_d(z,x)=1-(z^2+1/4)S_d(z,x),
```

define

```text
D_d(z,x)=partial_z H_d(z,x)
        =-2zS_d(z,x)-(z^2+1/4)partial_z S_d(z,x).
```

Then

```text
U_d(z)  = (1/2) integral_0^infinity rho(x)H_d(z,x)dx,
U_d'(z) = (1/2) integral_0^infinity rho(x)D_d(z,x)dx.        (1)
```

If

```text
K_d(z;x,y)
 = (1/2) Im(D_d(z,x)conjugate(H_d(z,y))
              +D_d(z,y)conjugate(H_d(z,x))),
```

then the finite core current is exactly

```text
J_(U_d)(z)
 = (1/4) integral_(0,infinity)^2 rho(x)rho(y)K_d(z;x,y) dxdy. (2)
```

No divisor, root, limiting measure, or logarithmic derivative is used.

## Proof

Differentiate the finite section term by term.  The coefficient identity

```text
c_k=(1/2) integral rho(x)x^(2k+2)/(2k+2)! dx
```

allows the finite derivative sum to pass through the integral, proving the second identity in
`(1)`.  Multiply the two identities in `(1)`, conjugate the value identity, and use the product
measure formula.  Taking imaginary parts gives the unsymmetrized kernel.  Invariance of
`rho(x)rho(y)dxdy` under `(x,y) -> (y,x)` replaces it by the symmetric kernel and proves `(2)`.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCoreCorrelation.lean
```

Principal declarations:

```text
thetaCuspTailSecondSectionDerivative
thetaCuspTailSecondCoreAtomDerivative
xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral
xiCTaylorThetaTailCoreCorrelationKernel
xiCTaylorThetaTailCorePairCurrent
xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul
xiCTaylorThetaTailCore_current_eq_symmetricCorrelationIntegral
```

## Boundary

This theorem localizes the missing source statement but does not sign the pair current.  A single
core atom can have positive current, so `(2)` must be used through a cancellation identity of the
full canonical density.

## Gates

- [x] finite section derivative identity proved
- [x] derivative integrability proved
- [x] derivative source integral proved
- [x] product-measure current identity proved
- [x] symmetric pair-current identity proved
- [x] formalized in Lean
- [ ] full-density cancellation estimate proved
