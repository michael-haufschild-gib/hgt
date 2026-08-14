# Route P critical collision Schur trace

- **ID:** `route-p-critical-collision-schur-trace`
- **Label:** P-G173
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / THEOREM (Lean) / POSITIVE SURVIVOR
- **RH status:** open
- **Computation used:** no
- **Parent:** `route-p-critical-collision-scale-kernel.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePCriticalCollisionSchurTrace.lean`

## Conjecture

P-G172 leaves a four-term complex kernel at critical ordinate-collision scale:

```text
C_R(a,b;k)
 = 2R^3/[R(a+b)+ik]^3
 - 2R^3/[R(a+2b)+ik]^3
 - 2R^3/[R(2a+b)+ik]^3
 + 2R^3/[R(2a+2b)+ik]^3.                     (173.1)
```

Individual entries can be complex and their real parts need not admit the diagonal-discarding
argument used by the earlier positive tensor kernel. Conjecture: `(173.1)` is nevertheless a
positive kernel for arbitrary collision frequencies because it is a compression of a higher
Hardy Gram, and its trace is independent of all collision gaps.

## Higher principle

Fixed-gap diagonalization was the far-field shadow of a stronger statement. The zeta pole resolves
nearby ordinates by a complex Cauchy Gram. Cubic differentiation takes its third Schur power;
Hellinger aperture subtraction is a signed first-difference compression. Positivity is therefore
stable through arbitrary clustering. What can grow is only diagonal trace mass, not a hidden
negative cluster interaction.

## Conjecture loop

- **C1:** Use the pointed completed-response/prime-ratio Dirichlet energy as the missing
  source-oriented producer. **Failed and pivoted:** the combined pairing-plus-half-Dirichlet budget
  is a pure row-marginal gauge
  (`HedenmalmThetaCompletedResponseMarginalGaugeNoGo.lean`). A genuine zero-marginal response
  cancels from it, while two-prime cofinal gauges have strict negative quadratic and strict positive
  Dirichlet directions (`HedenmalmThetaCompletedResponseCofinalGaugeNegativity.lean`). This object
  cannot retain the required off-diagonal source orientation without a separate sign theorem.
- **C2:** Bound `(173.1)` entrywise by a diagonal envelope. **Rejected:** that discards its Gram
  structure and would reintroduce cluster-size losses.
- **C3:** Double every Hardy node to apertures `a` and `2a`, take the third Hadamard power of the
  doubled Cauchy Gram, then compress by the signed aperture difference. **Proved:** the compression
  is exactly `(173.1)` and is positive semidefinite with no spacing or distinctness assumption.

## Closed result

For a finite packet with `R>0`, `a_i>0`, and arbitrary scaled frequencies `kappa_i`, set

```text
w_i^L = R a_i - i kappa_i,
w_i^R = 2R a_i - i kappa_i,
G_xy  = 1/(w_x + conjugate(w_y)),
H     = 2R^3 (G Hadamard G Hadamard G),
D_i   = e_(i,L) - e_(i,R).
```

Lean proves `G` positive semidefinite as the Gram of literal half-line Laplace features, `H`
positive semidefinite by the Schur product theorem, and

```text
[C_R(a_i,a_j;kappa_j-kappa_i)]_(i,j) = D H D^* >= 0.    (173.2)
```

The diagonal and trace are exact:

```text
C_R(a,a;0) = 115/(864 a^3),
trace C = sum_i 115/(864 a_i^3).                         (173.3)
```

Both `R` and all `kappa_i` disappear from `(173.3)`. Consequently the exact finite collision
limit proved in P-G172 is nonnegative for every coefficient packet. Mesoscopic zero clustering is
not the missing positivity theorem and needs no zero-spacing hypothesis.

## Novelty and corpus audit

Corpus search found the diagonal constant and horizontal law already formalized in
`XiWardCubicLogMomentHellingerCauchySeparator.lean`, and the same `115/864` source weight in
`XiWardCubicLogMomentEulerSource.lean`. Therefore `(173.3)` at frequency zero is not claimed as a
new scalar identity. New content is the exact all-frequency Schur-cube compression `(173.2)`, its
unconditional positive semidefiniteness through arbitrary critical clusters, and the conclusion
that the full collision trace equals the old horizontal diagonal mass without spacing loss.

The source-side occurrence

```text
115/[864 (e+1)^3 p^(e+1) (log p)^2]
```

is summable, but it is not yet a source-to-zero trace identity. Treating equal constants as such an
identity would be theatre. Remaining theorem is a completed, source-faithful contraction or trace
comparison carrying this summable Euler mass to the zero packet.

## Lean certificate

Module `RoutePCriticalCollisionSchurTrace.lean` proves:

- `routePCollisionDoubledCauchyGram_posSemidef`
- `routePCollisionDoubledCubicGram_posSemidef`
- `routePCollisionCubicKernelMatrix_eq_compression`
- `routePCollisionCubicKernelMatrix_posSemidef`
- `routePCollisionCubicKernel_diagonal`
- `trace_routePCollisionCubicKernelMatrix`
- `routePFiniteCollisionCubicLimit_nonneg`

Targeted compilation produced
`/tmp/routep-snapshot/GaloisForLFunctions/RHTower/RoutePCriticalCollisionSchurTrace.olean`.
Audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; targeted
forbidden-token scan is clean. Umbrella import is wired and umbrella is intentionally not built.

## Gates

- [x] exact Schur-cube representation
- [x] arbitrary-cluster positive semidefiniteness
- [x] exact spacing-free diagonal and trace
- [x] finite P-G172 collision-limit nonnegativity
- [x] completed-response producer conjecture killed against existing no-go corpus
- [x] internal novelty collision audit
- [x] targeted compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] completed source-to-zero contraction/trace comparison
- [ ] unconditional RH closure

## Log

- 2026-08-14 — C1 failed against exact marginal-gauge no-go; pivoted to C3. Proved Schur-cube
  compression, arbitrary-cluster positivity, exact trace, and finite collision-limit positivity in
  Lean. Corpus audit isolated source-to-zero trace transport as remaining hard core.
