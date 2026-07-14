# Prime-log Hermitian KMS mirror completion

- **ID:** prime-log-hermitian-kms-mirror-completion
- **Stage:** 3-formalized
- **Type:** PHYSICS VALUE BRIDGE / LEAN
- **Physics source:** KMS detailed balance, thermofield/Wightman half-density, and the finite Lehmann representation
- **Lean consumers:** `PrimeLogKMSRealization`, the universal prime-log HT carrier, and finite passive-response consumers

## Goal

Separate the existing directed prime-log KMS carrier from the response of a genuine Hermitian observable.  Construct the Hermitian completion explicitly and identify its exact response value, rather than adding Hermiticity as an untracked hypothesis.

## Physics value relation

For a finite Hamiltonian with levels `0` and `omega_p=log p`, the existing directed amplitude has only the transition `0 -> p`.  Hermiticity forces the reverse matrix element with the same Wightman half-density intensity.  Therefore the completed finite response is

```text
-R_P^herm(z)
  = sum_(p in P) w_p * ((omega_p-z)^(-1) - (omega_p+z)^(-1))
  = H_P(z) - H_P(-z).
```

Thus the full one-sided carrier `H_P(z)` is a directed response value, while the genuine Hermitian KMS/Wightman carrier is its mirror-odd projection.  The omitted value `H_P(-z)` is the exact Hermitian-completion defect.

## Gates

- [x] existing KMS and prime-log Lean surfaces audited
- [x] primary detailed-balance and half-density mechanism identified
- [x] exact finite source specialization derived
- [x] Hermitian amplitude and intensity formalized
- [x] exact Gibbs detailed-balance and fluctuation--dissipation values formalized
- [x] exact mirror-completion response formalized
- [x] non-Hermitian obstruction for the directed carrier formalized
- [x] thermodynamic limit and universal-carrier consumer formalized
- [x] targeted Lean build and axiom audit
- [x] formal lint and index refresh
- [ ] RH

## Verification boundary

The literature supplies KMS detailed balance and the necessity of reverse transitions for a self-adjoint observable.  Lean must prove the explicit Hermitian amplitude, both transition intensities, the finite mirror identity, positivity/passivity, and the infinite prime-log limit.  No numerical evidence is used.

Primary sources: L. Accardi and K. Imafuku, *Dynamical detailed balance and local KMS condition for non-equilibrium states*, arXiv:quant-ph/0209088; S. R. Jain and P. Gaspard, *Dynamical response and time correlation functions in random quantum systems*, arXiv:2408.09419.

## Formalized result

`FiniteKMSDetailedBalance.lean` proves finite Gibbs detailed balance and the exact `sinh`, `cosh`, and `tanh` fluctuation--dissipation values.  `PrimeLogKMSHermitianCompletion.lean` constructs the Hermitian observable, proves its exact prime-log spectral values, identifies the finite and infinite mirror-odd response, proves the thermodynamic and universal-gauge limits, and proves that no Hermitian observable can realize the existing nonempty directed intensity.

## Open core

The one-sided carrier remains the source of the existing orientation selector, but it is necessarily directed rather than a self-adjoint-observable response.  The reflected value `H(-z)` is now the exact orientation-bearing residue between that selector and the physical Hermitian KMS carrier.  A further RH route must use this residue in a named continuation, cancellation, or critical-line consumer; KMS/FDT alone does not determine it.
