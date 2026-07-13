# Finite response-theory Liouvillian sum rule for the prime--archimedean moment tower

- **ID:** `finite-response-liouvillian-sum-rule-prime-arch`
- **Stage:** 1-in-progress
- **Type:** PHYSICS VALUE BRIDGE / LEAN
- **Physics source:** spectral moment sum rules and equal-time nested commutators in quantum
  response theory
- **Lean consumers:** self-adjoint-observable Hankel producers, thermal Krylov moments,
  prime--archimedean source positivity, strict Krylov residual determinants, and RH capstones

## Physics value relation

In an energy eigenbasis, the Liouvillian commutator with a Hamiltonian is diagonal on transition
matrix elements:

```text
(L A)_(a,b) = (E_a-E_b) A_(a,b).
```

For the transition vector `omega_(a,b)=sqrt(I_ab)`, where `I_ab >= 0`, its response moments are

```text
inner omega (L^k omega)
  = sum_(a,b) I_ab (E_a-E_b)^k.
```

Thus spectral response moments are exact self-adjoint-observable orbit values.  The squared
Liouvillian `L^2` has the even moments as its ordinary orbit:

```text
inner omega ((L^2)^n omega) = thermalEvenGapMoment I E n.
```

This converts the finite transition sum into the operator-value interface already consumed by the
reflection-positive and prime--archimedean Hankel theorems.  It also makes odd-moment cancellation
under transition symmetry a selection rule for the unsquared Liouvillian.

Primary reference: Bradlyn--Abbamonte,
[`Spectral Density and Sum Rules for Second-Order Response
Functions`](https://arxiv.org/abs/2404.16144), where frequency moments of the response spectral
density are identified with equal-time commutator values.  The finite diagonal Liouvillian here is
the exact finite spectral algebra behind that relation.

## Verification boundary

- The finite eigenbasis value identity is unconditional algebra once `I_ab >= 0` is supplied.
- No source moment is claimed to equal a response moment without an explicit all-order comparison.
- Numerical pre-certification on a random eight-level transition system verified the orbit/moment
  identity through order eight.

## Gates

- [x] physics value relation isolated
- [x] numerical pre-certification completed
- [ ] finite self-adjoint Liouvillian and orbit sum rule formalized
- [ ] squared-Liouvillian thermal moment specialization formalized
- [ ] existing self-adjoint/Hankel consumers connected
- [ ] source-defined all-order response comparison constructed
- [ ] RH
