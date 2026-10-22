# Route P primitive collision trace budget

- **ID:** `route-p-primitive-collision-trace-budget`
- **Label:** P-G174
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / THEOREM (Lean) / SOURCE TRACE-CLASS ENVELOPE
- **RH status:** open
- **Computation used:** no
- **Parent:** `route-p-critical-collision-schur-trace.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveCollisionTraceBudget.lean`

## Conjecture

P-G173 proves that every finite critical-collision matrix is positive and has diagonal

```text
C_R(a,a;0)=115/(864a^3).                                (174.1)
```

The corpus already places this scalar kernel on a primitive Euler cell `pe=(p,e)` at radial
frequency

```text
a_pe=log(p^(e+1))
```

and multiplies it by resolved von Mangoldt mass `Lambda(p^(e+1))/p^(e+1)`. Conjecture: this is not
only a diagonal coincidence. Congruencing the full arbitrary-frequency P-G173 kernel by the
positive square root of that literal mass gives a positive primitive Euler collision matrix whose
trace is exactly the existing summable cubic Euler weight. Hence all finite source clusters share
one global frequency-independent trace budget.

## Proof

For a finite list of distinct primitive cells `pe_i`, arbitrary scaled collision frequencies
`kappa_i`, and `R>0`, define

```text
a_i = log(p_i^(e_i+1)),
q_i = sqrt(Lambda(p_i^(e_i+1))/p_i^(e_i+1)),
K_ij = C_R(a_i,a_j;kappa_j-kappa_i),
M = diag(q) K diag(q)^*.
```

P-G173 gives `K>=0`, so congruence gives `M>=0`. The exact diagonal calculation is

```text
M_ii
 = [115/(864 a_i^3)] Lambda(p_i^(e_i+1))/p_i^(e_i+1)
 = 115/[864 (e_i+1)^3 p_i^(e_i+1) (log p_i)^2],        (174.2)
```

which is definitionally the cubic primitive Euler weight already proved summable in
`XiWardCubicLogMomentEulerSource.lean`. Therefore

```text
trace M = sum_i cubicEulerWeight(pe_i)
        <= sum_(pe) cubicEulerWeight(pe) < infinity.    (174.3)
```

Neither side of `(174.2)--(174.3)` depends on `kappa`; the bound is also independent of packet
cardinality. Injectivity of `i -> pe_i` is the only condition needed for the global bound and merely
prevents counting the same Euler cell repeatedly.

## Higher principle

Critical clustering is a correlation phenomenon, not a new mass phenomenon. The same cubic
homogeneity simultaneously makes zero-side collision blocks Schur-positive and makes the complete
primitive Euler diagonal summable. Collision frequencies rearrange a fixed trace-class source
budget but cannot increase it.

## Novelty and anti-theatre audit

The scalar cubic self-charge, its primitive Euler coefficient, and its summability predate this
card and are not claimed as new. P-G174 contributes their exact non-diagonal synthesis: arbitrary
collision frequencies survive on the literal prime-depth carrier while positivity and the complete
summable trace remain intact. Corpus searches found no prior theorem joining the P-G172 collision
kernel to the primitive Euler source by this exact congruence.

This still is not the completed source-to-zero theorem. The source index `pe` and zero index `rho`
are different carriers. A matching scalar constant does not identify them, and `(174.3)` cannot be
spent on zeros until a coefficient-faithful completed incidence/contraction is constructed before
divisor expansion. Claiming RH, `75%`, or even a zero-energy upper bound from `(174.3)` alone would
be theatre.

## Lean certificate

`RoutePPrimitiveCollisionTraceBudget.lean` proves:

- `routePPrimitiveCollisionCubicKernelMatrix_posSemidef`
- `routePPrimitiveCollisionCubicKernelMatrix_apply`
- `routePPrimitiveCollisionCubicKernelMatrix_diagonal`
- `trace_routePPrimitiveCollisionCubicKernelMatrix`
- `routePPrimitiveCollisionCubicTraceBudget_nonneg`
- `re_trace_routePPrimitiveCollisionCubicKernelMatrix_le_budget`

Targeted compilation produced
`/tmp/routep-snapshot/GaloisForLFunctions/RHTower/RoutePPrimitiveCollisionTraceBudget.olean`.
Audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; targeted
forbidden-token scan is clean. Umbrella import is wired and umbrella is intentionally not built.

## Gates

- [x] literal primitive Euler congruence
- [x] arbitrary-frequency source collision positivity
- [x] exact diagonal identification with cubic Euler weight
- [x] exact finite trace
- [x] uniform global summable trace budget for distinct cells
- [x] targeted compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] completed coefficient-faithful source-to-zero incidence/contraction
- [ ] unconditional RH closure

## Log

- 2026-08-14 — P-G173 trace constant collided with existing cubic Euler weight. Proved the full
  non-diagonal primitive collision congruence, positivity, exact trace, and global summable trace
  budget in Lean; isolated completed carrier transport as the sole remaining seam.
