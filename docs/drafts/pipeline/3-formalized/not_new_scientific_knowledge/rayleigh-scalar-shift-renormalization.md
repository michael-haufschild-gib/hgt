# Rayleigh scalar-shift renormalization

- **ID:** `rayleigh-scalar-shift-renormalization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** Adding a real scalar multiple of the identity shifts all Rayleigh values and
  spectral energies equally, leaving the spectral gap, Rayleigh excess, and Rayleigh-excess ratio
  unchanged.

## Route use

The CCM exterior calculation isolates the candidate leading term

```text
A_arch(R_lambda,R_lambda)
 =log(c)*||R_lambda||^2+O(d_1),
c=2*pi*lambda^2.
```

Whenever that bilinear leading law is established on the relevant carrier, its `d_1*log(c)` value
is the evaluation of a scalar identity term, not a source-specific counterterm. Ground-vector
selection then depends only on the scalar-renormalized form

```text
A_lambda^ren=A_lambda-log(c)*I.
```

The target ratio is exactly invariant:

```text
(Rayleigh_(A+rI)(g)-(epsilon_0+r))
  /((epsilon_1+r)-(epsilon_0+r))
= (Rayleigh_A(g)-epsilon_0)/(epsilon_1-epsilon_0).
```

Thus the next analytic gate is an order-`d_1` bilinear bound for the renormalized archimedean
symbol, combined with the already explicit prime term. No cancellation of the universal
`d_1*log(c)` scalar mass is required.

## Formal declarations

The module `GaloisForLFunctions.RHTower.RayleighScalarShift` proves:

```text
rayleighQuotient_add_real_smul_id
rayleighExcess_add_real_smul_id
spectralGap_add_cancel
rayleighExcessRatio_add_real_smul_id
```

## Gates

- [x] scalar shift of a nonzero Rayleigh quotient formalized
- [x] Rayleigh excess invariance formalized
- [x] spectral gap invariance formalized
- [x] excess-to-gap ratio invariance formalized
- [ ] represent the scalar-renormalized CCM form in Lean
- [ ] prove the source-specific order-`d_1` bilinear remainder estimate
