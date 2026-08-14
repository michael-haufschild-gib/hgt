# Route P full Hardy-half-plane polarization

- **ID:** `route-p-full-hardy-half-plane-polarization`
- **Label:** P-G169
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / SOURCE-DOMAIN EXTENSION
- **RH status:** open
- **Computation used:** no
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePFullHardyHalfPlanePolarization.lean`

## Conjecture

P-G167 uses the sufficient chart `Re u >= 0`. Its literal Euler column has squared exponent

```text
sigma + 2 Re(u) (sigma-1),
```

so its sharp Hilbert-domain wall is instead `Re u > -1/2`. P-G168's projective node
`u_R(a)=R a-1/2` therefore lies strictly inside the actual source domain for every `R>0`, `a>0`.
The earlier no-fixed-`R` obstruction is a chart obstruction, not a source obstruction.

For nodes in the full Hardy half-plane, prove the actual complex Euler columns are square summable,
their exact overlap remains

```text
<h_sigma(u),h_sigma(v)>
  = zeta(sigma+(v+conj u)(sigma-1))/zeta(sigma),
```

and the transverse Fisher reporter, graph normalization, completed-Xi correction, augmented Gram,
and four-unit source diagonal remain valid. At projective nodes prove the finite-`sigma` identity

```text
<h_sigma(u_R(a)),h_sigma(u_R(b))>
  = zeta(1+R(a+b)(sigma-1))/zeta(sigma),
```

and the pole-cancelled critical limit

```text
R <h_sigma(u_R(a)),h_sigma(u_R(b))> -> 1/(a+b).
```

This would identify P-G168's universal Hardy kernel as the literal critical limit of P-G167's
full-Euler source for every fixed positive projective scale, without zero-fitted scale selection.

## Hostile checks

1. L2 convergence must use the doubled real damping exponent; checking only the linear zeta
   exponent is insufficient.
2. Pair overlap needs `Re u + Re v > -1`, exactly forced by the two half-plane hypotheses.
3. The projective limit must cancel both zeta poles through the existing analytic residue unit;
   no asymptotic axiom or numerical certificate is allowed.
4. The old theorem that `Re u_R(a)<0` for some `a` at fixed `R` remains true. P-G169 must explain
   why negativity is harmless while staying strictly above `-1/2`.
5. This closes source-domain and finite-sigma provenance, not the Euler--Gamma trace budget.

## Conjecture loop

- **C1:** require `Re u>=0` and let `R` diverge with depth. **Failed as global source law:** fitted,
  nonuniform scale.
- **C2:** truncate the cubic integral to projectively admissible scales. **Rejected:** cutoff depends
  on divisor depth.
- **C3:** use fixed source translations instead of the Hardy chart. **Valid parallel realization,**
  but it does not explain finite-`sigma` P-G167 provenance.
- **C4:** enlarge P-G167 to its sharp L2 half-plane `Re u>-1/2`. **Selected:** literal source weights
  already have this domain and every positive projective node is automatically admitted.

## Gates

- [x] corpus noncollision and exact convergence-threshold audit
- [ ] Lean sharp half-plane square summability
- [ ] Lean exact full-half-plane non-diagonal overlap
- [ ] Lean transverse reporter and augmented Gram on full half-plane
- [ ] Lean projective finite-`sigma` overlap
- [ ] Lean pole-cancelled projective Hardy limit
- [ ] scratch compile, forbidden-token scan, and axiom audit
- [ ] source-faithful dyadic height trace budget
