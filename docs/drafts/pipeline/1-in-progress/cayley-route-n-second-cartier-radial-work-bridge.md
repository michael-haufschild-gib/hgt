# Cayley--Route-N bilateral capacity bridge to second-Cartier radial work

- **ID:** cayley-route-n-second-cartier-radial-work-bridge
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** cross-corpus Frankenstein seam (centered-flow capacity, Route N, theta translation, Route P)
- **Statement:** The critical Route-N weight times the two opposite prime-time centered-flow capacities has an exact nonnegative excess equal to analytic multiplicity times theta prime-translation excess; at prime two its completed energy is uniformly comparable to literal completed radial source work and vanishes exactly on the critical line.

## Goal

Replace an unspecified Route-P order premise by one explicit positive completed-source defect which
simultaneously retains prime label, both time orientations, analytic divisor multiplicity, and the
literal completed Xi response.  A source law forcing this excess below its critical baseline would
give equality, radial-work extinction, endpoint moderation, and RH through existing consumers.

This card does **not** assert that missing upper source law.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure finite-time carrier and exact attack
- [ ] 1 → 2 fully-proven: bridge proof is complete; independent source upper law remains open
- [ ] 2 → 3 formalized: target module and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and novelty audit

## Heavy-conjecture loop

### C1 — ordinary completed-source continuity forces endpoint order — **FALSIFIED**

Reflection-paired complete source points collapse cofinally while their exact endpoint characters
remain separated off line.  `CompleteResolutionReflectionPairEquicontinuityFirewall` rules out every
exact extractor with a common continuity modulus.  This cannot be repaired by nonlinear regularity.

### C2 — adaptive Green contraction supplies the order — **FALSIFIED**

Adaptive Möbius--theta countertransport is bounded only after divisor-dependent depth selection and
does not preserve the literal coefficient `p^(1/2-rho)`.  It is not a coefficient-faithful landing.

### C3 — finite Weyl/anti-Herglotz admission supplies the order — **FALSIFIED**

The finite Jacobi moment variable is independent of the Xi prime-normal endpoint.  No theorem lands
its finite positive functional on the literal second-Cartier character.  Post-selected
Toeplitz/Bochner admission is already excluded on every occupied strict-right fibre.

### C4 — covariant/determinant conservation bounds both physical legs — **FALSIFIED**

For opposite prime times, centered-flow capacities have fixed product but a hyperbolic trace.
Conservation therefore fixes the determinant, not the trace.  Arithmetic--geometric mean gives the
wrong direction: the critical trace is the strict minimum.  This matches the semilocal literature:
local/finite-place normalization does not provide global Weil positivity or the missing trace sign.

### C5 — bilateral prime-time capacity is the exact positive defect — **PROVED HERE**

For an actual Xi copy `q`, prime `p`, multiplicity mass `M(q)`, critical Route-N weight
`w_p = p^-1`, centered rate `t(q)=2 Re(q)-1`, and raw centered-flow capacity `C_q(tau)`, define

```text
B_p(q) = w_p (C_q(log p) + C_q(-log p)),
E_p(q) = B_p(q) - 2 M(q) w_p.
```

Exact centered-flow and theta-translation identities give

```text
E_p(q) = M(q) w_p (p^t(q) + p^-t(q) - 2)
       = 2 M(q) w_p (cosh(t(q) log p) - 1).
```

Hence `E_p(q) >= 0`, and because `M(q)>0`, `p>1`,

```text
E_p(q)=0  <->  Re(q)=1/2.
```

Multiplying by the exact completed first-divided Xi norm gives `E_p^completed`.  Existing
prime-translation/radial-work comparison at `p=2` yields

```text
2 M(q) (log 2)^2 W(q)
  <= E_2^completed(q)
  <= 4 M(q) (log 2)^2 W(q),
```

where `W(q)` is literal completed radial source work.  This is coefficient- and
multiplicity-faithful and uses neither finite measures nor scalar shorting.

## Exact remaining producer

Construct before divisor specialization a global completed Euler--Gamma/Poisson order law whose
descent gives

```text
B_p(q) <= 2 M(q) w_p
```

at one prime, or an equivalent singular all-positive-aperture law.  Combined with proved
`B_p(q) >= 2 M(q) w_p`, this forces equality.  Determinant conservation, a contractible
countercharacter, fixed-prime Sonin positivity, and any common reflection-pair continuity modulus
cannot provide this inequality.  The law must use global Poisson normalization before finite
prime-cell compression and retain the marked two-orientation carrier.

## Literature / novelty audit

- Connes--Consani's archimedean Sonin compression supplies a positive single-place framework, not
  global finite-place Weil positivity.
- Connes--Consani's scaling-Hamiltonian analysis explicitly identifies global Poisson
  normalization as indispensable; a semilocal Hardy multiplier is not bounded.
- Recent numerical truncated-Weil work reports exponential residual blow-up under injected
  off-line zeros and explicitly does not prove the required positivity/order law.
- No checked primary source states the exact Cayley-capacity/Route-N/theta-translation/radial-work
  identity above.  **Novelty remains unverified**, but this is a corpus-derived exact bridge rather
  than an external theorem claim.

## Log

- 2026-08-19 — C1--C4 failed; C5 paper proof completed in scratch Lean.
