# Euler square-root amplitudes generate finite ferromagnetic prime blocks

- **ID:** `euler-square-root-ferromagnetic-prime-blocks`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[POSITIVE SUCCESSOR] [FINITE FLOOR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeEulerFerromagneticInteraction.lean`
- **Consumer:** `../../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`

## Theorem

For every prime `p`, put

```text
c_p=exp(-log(p)/2)=p^(-1/2),
u_p(z)=exp(-log(p) I z).
```

The physical amplitude satisfies `0<c_p<=1`, so it is an admissible two-spin ferromagnetic
coefficient `exp(-2J_p)`, with `J_p=log(p)/4`.  Lean defines the source-native block

```text
L_p(z)=1+2c_p u_p(z)+u_p(z)^2
```

and proves

```text
L_p(z)=0 -> Im z=0.
```

For every finite prime aperture `P`, it also proves

```text
product_(p in P) L_p(z)=0 -> Im z=0.
```

Thus the square-root amplitude that displaced the Lee--Yang torus when used as part of the field
becomes a valid critical-line selector when used as an interaction coefficient.

## Boundary of the result

This finite partition is source-native but is not the completed Euler product.  After reciprocal
Euler pairing the linear coefficient is `c_p+c_p^(-1)`; the ferromagnetic block has coefficient
`2c_p`.  Their explicit difference is the remaining local comparison defect.  A complete RH chain
must absorb that defect through further source-defined interactions or a zero-free completed
normalization and then prove locally uniform convergence to a zero-free factor times `XiC`.

## Formal certificate

The module proves:

- `primeEulerFerromagneticCoefficient_pos`;
- `primeEulerFerromagneticCoefficient_le_one`;
- `primeEulerFerromagneticBlock_zero_im`;
- `primeEulerFerromagneticPartition_zero_im`.

## Gates

- [x] physical amplitude converted into an interaction coefficient
- [x] ferromagnetic chamber membership proved
- [x] one-prime critical-line selector proved
- [x] arbitrary finite-aperture selector proved
- [x] exact Lean build
- [ ] completed Euler/Xi comparison and zero-free relative factor
