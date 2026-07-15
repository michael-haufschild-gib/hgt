# Quantum replica Hausdorff convexity

- **ID:** `quantum-replica-hausdorff-convexity`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE]` exact quantum-information value relation / general corpus strengthening
- **Scientific status:** standard unit-interval density-spectrum constraint transferred to the
  rectangular Hilbert--Schmidt constraint API; novelty is not claimed
- **Verification status:** source-only by explicit instruction; no Lean process or build run

## Claim

For a Hilbert--Schmidt constraint channel `C`, put

```text
T = C† C,
m = Tr(T) = ||C||_HS^2,
M_k = Re Tr(T^(k+1)),
P_k = M_k / m^(k+1).
```

The normalized positive effect `rho = T/m` is a density operator when `m > 0`.  Its spectral
values lie in `[0,1]`, so its replica values `P_k = Tr(rho^(k+1))` form a Hausdorff moment
sequence.  The source formalization establishes the first new complementary condition beyond
the already available monotonicity:

```text
0 <= P_k - 2 P_(k+1) + P_(k+2).
```

Before division this is

```text
D_k = m^2 M_k - 2 m M_(k+1) + M_(k+2) >= 0.
```

No spectral theorem is needed for this order.  If `k = 2n`, then

```text
D_(2n) = ||m C T^n - C T^(n+1)||_HS^2.
```

If `k = 2n+1`, then

```text
D_(2n+1) = ||m T^(n+1) - T^(n+2)||_HS^2.
```

Thus the difference is a static constraint square, not a propagated flow.

## General HTGeometry value

`formal/GaloisForLFunctions/HTGeometry/QuantumReplicaHausdorff.lean` adds a rectangular,
zeta-independent API:

- the exact real-scalar Hilbert--Schmidt quadratic expansion;
- master-effect power columns and their Hankel trace pairing;
- real trace moments, mass, and normalized replica moments;
- even/odd trace-moment representations as Hilbert--Schmidt norm squares;
- exact even/odd representations of the complementary second difference;
- nonnegativity of both the unnormalized and normalized differences.

The file is imported by the `HTGeometry` umbrella.  Every future hypertranscendental constraint
channel of the form `C` can use the theorem without importing any zeta or Sonin declaration.

The mathematical all-order statement is stronger:

```text
(-Delta)^r P_k >= 0  for every k,r.
```

Only `r = 1` (the earlier replica contraction) and `r = 2` (this card) have source
formalizations.  Promoting the complete Hausdorff sequence should reuse the existing
`StieltjesMomentProblem` / Hausdorff machinery through a spectral representing measure for the
normalized compact master effect.  That spectral-measure bridge remains open and is not claimed
as Lean-proved.

## Direct RHTower consumer

For the coupled all-prime Sonin column `C_a`, let

```text
S_k(a) = Tr((C_a† C_a)^(k+1)),
P_k(a) = Re S_k(a) / Re S_0(a)^(k+1).
```

`SoninCoupledPrimeArchGramTransfer.lean` now identifies `P_k(a)` with the general quantum replica
moment and exposes

```text
0 <= P_k(a) - 2 P_(k+1)(a) + P_(k+2)(a),

0 <= Re S_0(a)^2 Re S_k(a)
       - 2 Re S_0(a) Re S_(k+1)(a)
       + Re S_(k+2)(a).
```

The quotient-free form remains available without assuming the coupled source is nonzero.  It is
strictly stronger than isolated moment nonnegativity and one-step replica monotonicity, and it
cuts the simultaneous source moment locus by a closed quadratic family.

## Direct route audit

This strengthens the coupled source corpus but does **not** discharge the current per-test
source-norm comparison.  The canonical/projective coupled route permits an external positive
rescaling, while the new constraint contains the unscaled source mass `Re S_0(a)`.  Unless that
mass is also controlled, the second-difference inequality cannot be promoted to an unconditional
target Hausdorff inequality: a diverging source mass makes the leading positive term dominate.

The useful conditional diagnostic is exact.  If a normalized moment-ratio schedule converges and
its source masses converge to a finite radius `R`, then its target ratio sequence must satisfy the
`R`-scaled second Hausdorff difference.  This provides a route-killing compatibility test for any
future proposed aperture schedule and identifies source-mass control as the missing hypothesis
needed to feed the new physics relation into the existing scaled-Hausdorff RH surface.

No RH implication is claimed from the new inequality alone.

## Adjacent quantum-Fisher audit

`[ROUTE RETIRED]` Replacing the existing pure-state projective Fisher value by mixed-state quantum
Fisher or Wigner--Yanase skew information does not improve the live variance comparison.  The
relevant density is a function of the coupled effect `T`, and the moment observables are
polynomials in that same `T`; they commute.  The mixed-state unitary Fisher/skew-information
channel therefore vanishes, while the pure-state projective Fisher value already present in the
corpus is exactly four times the required normalized variance.  The mixed-state substitution
would discard the classical spectral variance rather than bound it.

## Physics provenance

- A. Elben, S. T. Flammia, H.-Y. Huang, R. Kueng, J. Preskill, B. Vermersch, and P. Zoller,
  *The randomized measurement toolbox*, Nature Reviews Physics 5 (2023), 9--24,
  [arXiv:2203.11374](https://arxiv.org/abs/2203.11374).  The review treats higher density-matrix
  moments as measurable multi-copy observables and records positivity inequalities among them.
- A. Neven, J. Carrasco, V. Vitale, C. Kokail, A. Elben, M. Dalmonte, P. Calabrese, P. Zoller,
  B. Vermersch, R. Kueng, and B. Kraus, *Symmetry-resolved entanglement detection using partial
  transpose moments*, npj Quantum Information 7 (2021), 152,
  [arXiv:2103.07443](https://arxiv.org/abs/2103.07443).  The paper uses ordered moment inequalities
  and the Stieltjes moment problem to test operator positivity.
- G. Toth and F. Frowis, *Uncertainty relations with the variance and the quantum Fisher
  information based on convex decompositions of density matrices*, Physical Review Research 4
  (2022), 013075,
  [DOI 10.1103/PhysRevResearch.4.013075](https://doi.org/10.1103/PhysRevResearch.4.013075).
  This supplies the mixed-state QFI/variance comparison used in the adjacent no-go audit.

## Verification status

Source inspection only.  Under the active user constraint, no Lean invocation, scratch
compilation, lint, numerical check, targeted build, or full build was run.  The declarations stay
in stage 1 until a narrow validation pass is authorized.

