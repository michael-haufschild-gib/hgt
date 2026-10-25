# Canonical horizon kernels and prime-power transitions

- **ID:** biarithmetic-prime-power-transition-groups
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), corrected B1 and B2 calibration.
- **Statement:** Reduction between divisor-incidence period groups is functorial and surjective. Its successive cyclic kernels have order `p` at powers of `p` and order one elsewhere. The torsion group in the arithmetic Euler formula is isomorphic to the canonical kernel of reduction from period to horizon.

## Paper proof

Write `L_N=lcm(1,...,N)`, with `L_0=1`. For `M≤N`, every integer contributing to `L_M`
divides `L_N`; hence `L_M|L_N`. Reduction modulo `L_M` defines a surjection
`r_(M,N):Z/L_NZ→Z/L_MZ`. Integer representatives prove surjectivity, and successive
reductions compose exactly.

Put `J_N=L_(N+1)/L_N`. The kernel of `r_(N,N+1)` consists precisely of the multiples of
`L_N`, so it is cyclic of order `J_N`. The classical identity `log L_N=ψ(N)` gives

`log J_N=ψ(N+1)-ψ(N)=Λ(N+1)`.

Since `J_N` is a positive integer, `J_N=1` iff the Mangoldt atom is zero, namely iff
`N+1` is not a prime power. At `N+1=p^r`, `r≥1`, its logarithm is `log p`, so `J_N=p`.
This classifies every transition, including the trivial first step.

For a fixed positive horizon `H`, `H|L_H`. Reduction to `Z/HZ` therefore gives a canonical
exact sequence

`0 → ker(Z/L_HZ→Z/HZ) → Z/L_HZ → Z/HZ → 0`.

Its kernel is cyclic of order `L_H/H=Q_H`, hence isomorphic to `Z/Q_HZ`. Thus the earlier
formula becomes

`E(log H)=(H-1)-log #ker(Z/L_HZ→Z/HZ)`.

At every nonnegative aperture the same kernel at `H=floor(exp s)` occurs, with the exact
continuous remainder `(exp s-H)+(s-log H)` from the all-aperture formula.

The kernel itself and both maps are canonical. The Lean equivalence from `Z/Q_HZ` chooses a
cyclic generator; no particular generator is required for the cardinality or Euler formula.

## Contribution and limits

The correction of B1 now has a genuine kernel and exact restriction maps, with a completely
classified prime-power transition law. This gives the arithmetic charge a functorial finite-group
interpretation; it does not define payment cohomology or its Mayer–Vietoris sequence.
The fixed-horizon orders `Q_H` need not divide one another, so their transition maps cannot be
inferred from the period filtration.

These period groups may have more than polynomially many elements. The argument uses their
symbolic cyclic presentations and orders; it is not a horizon-complete signed observation
construction, nor a licence to enumerate a full period. The source weights are the actual
integer prime powers, but no orientation or source-cancellation estimate follows.
The group arithmetic and least-common-multiple identity are classical; no general novelty
claim is made for them.

## Verification

- [x] Dependency-closed paper proof, including kernels and all prime-power transitions.
- [x] Scratch proof of the period filtration, jump laws, kernel orders, and cyclic equivalences.
- [x] Direct leaf check including the arithmetic box comparison.
- [x] Main-declaration transitive axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Module: `GaloisForLFunctions/BiarithmeticGeometry/PrimePowerTransitionGroups.lean`.
