# Complete-resolution reflected-shell second-Cartier descent

Status: in progress; descent theorem formalized unconditionally in Lean. Independent completed-source
budget producer remains open.

## Problem

Route P needs a pre-divisor completed-source law controlling the literal bilateral
second-Cartier endpoint. Post-selected finite measures, scalar shorting, and positive
Toeplitz/Bochner admission are closed by formal no-gos. The missing source input must retain the
prime coefficient, both reflection orientations, and Xi multiplicity before the endpoint is
scalarized.

## Heavy-conjecture loop

1. **Pontryagin completion.** Conjecture that the rank-two theta boundary defect completes the
   compact source inverse to an index-one Krein-self-adjoint operator. **Fail.** The theta metric
   is singular, the boundary form has signature `(1,1)` with a nontrivial radical on quartet
   spans, and a nonreal quartet can hide in that radical. Rank counting does not force reality.
2. **Compact source clock.** Tensor the literal hyperbolic endpoint orbit with powers of the
   compact theta inverse. **Fail.** Its eigenvalue decay moderates a weighted endpoint by erasing
   the physical gain. Dividing the clock back out recreates the singular normal reader.
3. **Positive higher trace moments.** Identify reciprocal-Xi trace moments with the unconditional
   positive theta-likelihood moment tower. **Fail.** Only the first compact trace calibration is
   present; all-order identification is precisely an RH-strength source-Hankel sign, not a
   consequence of likelihood positivity.
4. **Frozen reflected-shell powers.** Raise one shell ratio at base `K` to orbit depth `n`.
   **Fail as source producer.** Although its limit is the correct endpoint, it repeats a frozen
   transfer by an external clock. It is an algebraic normal model, not completed-source evolution.
5. **Consecutive reflected-shell descent.** Multiply the actual transfers at
   `K,K+1,...,K+n-1` in both orientations. **Survives.** This is literal source evolution, and its
   non-scalar polarized jet converges coefficient-faithfully to the second-Cartier orbit.
6. **Compact reporter on normalized translated heads.** Use weak escape of prime-normal source
   heads and a fixed compact theta reporter to force both endpoint gains to be contractive.
   **Fails at coefficient-faithful factorization.** Off-line Fourier--Laplace evaluation is not a
   bounded functional on unweighted physical `L²`; passing through a compact bounded reporter
   erases exactly the exponential conormal gain. A weighted repair makes the translated source
   orbit unbounded and restores the same order problem.
7. **Cross-prime Bessel admission.** Put both reflected prime-normal endpoint legs into one
   prime-labelled Hilbert source and use Bessel. **Fail.**
   `XiSafeHalfPlaneJacobiGammaRecovery.lean` proves the recovered prime-power stream is square
   summable exactly for aperture `x > 1/2`; its reflected aperture is on the nonsummable side.
   Simultaneous coefficient-faithful Hilbert admission is therefore the desired order theorem,
   not an unconditional input.
8. **Uniform moving source metric.** Seek positive metrics `H_K` with exact consecutive-shell
   conservation and shell-uniform coercivity. **Fail as an independent producer.** The conserved
   Krein product is available, but uniform condition number is equivalent to zero horizontal
   Lyapunov rate. Off line, corpus conditioning theorems and the finite-shell two-stage escape
   force the condition number to diverge.
9. **Small thermal energy plus integral Ward quantum.** Combine the unconditional bound
   `xiSourceEntropyOrientationEnergy < 1/150000` with the Ward--Green off-line quantum `> 16`.
   **Fail at height normalization.** Thermal entropy suppresses an atom by reciprocal powers of
   its ordinate; Ward--Green inversion removes that suppression. Cauchy localization restores the
   atom only by developing the corresponding pole, so no height-uniform bound follows.
10. **Coefficient-faithful exterior source contour.** Use the exact contour landing from
    `HedenmalmCoefficientFaithfulExteriorSourceContour.lean` to bound the Ward--Green packet.
    **Fail the pre-divisor test.** Its polynomial is `Lagrange.interpolate` on
    `xiCClosedRectangleZeros`; arbitrary target coefficients are fitted after the finite divisor
    is known. Replacing it by a genuine holomorphic prime clock retains the reciprocal hyperbolic
    magnitude and hence the same endpoint escape.

## Construction

For a prime `p`, shell base `K`, orbit depth `n`, spectral point `s`, and physical coefficient
`c`, put

```text
A_{K,n}(s) = product_{0 <= j < n}
  normalizedPrimePeeledShellAdjacentTransfer p (K+j) s,
B_{K,n}(s) = product_{0 <= j < n}
  normalizedPrimePeeledShellAdjacentTransfer p (K+j) (1-star s),
J_{K,n}(s,c) = (A_{K,n}(s), c B_{K,n}(s), c B_{K,n}(s)).
```

This is a genuine three-coordinate Krein jet, not a scalar energy, fitted post-divisor measure, or
repeated frozen multiplier. Both source orientations remain independent at every finite stage.
When traversed residuals are nonzero, the forward product telescopes exactly:

```text
A_{K,n}(s) = p^(n/2) * R_{K+n}(s) / R_K(s),
```

where `R_K` is the prime-peeled shell residual. Thus orbit depth is literal completed-source
composition.

The existing prime-peeled shell theorem gives

```text
A_{K,n}(s) -> lambda^n,
B_{K,n}(s) -> ((star lambda)^(-1))^n,
lambda := p^(1/2-s).
```

Hence, for every fixed orbit depth,

```text
J_{K,n}(s,c) ->
  sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lambda c n.
```

Continuity of the positive radial energy then gives

```text
E(J_{K,n}(s,c)) -> ‖lambda‖^(2n) + 4 ‖c‖^2 ‖lambda‖^(-2n),
```

which is exactly the literal two-sided endpoint radial energy already identified in Route P.
Specializing `p=2` and `s` to an actual strict-right Xi copy preserves the existing conormal
coefficient and the support-fibre multiplicity sum.

## What this proves and what remains

This closes the representation gap between genuine consecutive completed-source evolution and the
literal endpoint. It also records two false producers precisely: raw-shell damping changes the
endpoint, while powers of one frozen shell transfer are not source natural. Only the consecutive
reflected non-scalar jet retains endpoint, coefficient, and both orientations.

Remaining hard producer is now one precise upstream estimate: a completed Euler--Gamma law must
bound the radial energy of these finite reflected-shell jets uniformly in orbit depth after the
cofinal shell limit, without replacing either orientation or coefficient. Such a bound is not
proved here; after the descent theorem it immediately implies literal endpoint moderation and RH.
The additional failed pivots above rule out importing this bound from ordinary cross-prime
Hilbert admission, uniformly coercive moving metrics, height-damped thermal energy, or
divisor-interpolated contour reporters.

## Novelty audit

Bounded literature search found standard Möbius/reciprocal-zeta Dirichlet-series work and
prime-power asymptotics, but no source-reflected prime-peeled shell construction identified with a
second-Cartier/Krein endpoint orbit. Novelty remains unverified until broader expert review.

## Formalization target

Formalized in
`formal/GaloisForLFunctions/RHTower/CompleteResolutionReflectedShellSecondCartierDescent.lean`:

- exact telescoping consecutive source transfer;
- reciprocal-star reflected consecutive orientation;
- consecutive jet and radial-energy convergence;
- consecutive cofinal finite-shell budget iff literal endpoint moderation;
- strict-right consecutive finite-shell two-stage escape;
- universal actual-Xi consecutive budget iff RH;
- actual Xi prime-two coefficient/multiplicity capstone.
