# Route K exact quartic incidence and all-order factorization

- **Stage:** 3-formalized
- **Status:** dependency-closed unconditional Lean
- **Source card:** `../../5-failed/route-k-prime-cycle-trace-class-relocation.md`
- **Scientific status:** `[PROVED HERE] [LEAN]`; source-specific synthesis appears new relative to
  checked primary literature, but no external priority claim is made
- **Not claimed:** existence of a complete all-order carrier, centered-Xi determinant identity, or RH

## Exact positive survivor

Write

```text
A = M_0^src / 2,   B = M_1^src / 2.
```

The strict source inequality `0 < B < A²` leaves a nonzero control margin.  An arbitrarily late
prime cut `N` is selected so that the reciprocal smooth Riemann--von Mangoldt tail has small
Hilbert--Schmidt energy.  A positive multiple of a cofinal sum of disjoint source-defined triangle
blocks is added on the same tail.  This cycle carrier is self-adjoint, Schatten-1, exactly
zero-diagonal, supported after `N`, and has nonzero holonomy on every selected triangle.

For the resulting reserve `R_N`,

```text
e = ||R_N||_HS²,   f = ||R_N²||_HS²
```

obey `e < A` and `f ≤ e²`.  The residual pair

```text
E = A - e,   F = B - f
```

is forced into the strict finite atomic cone

```text
E > 0,   E²/N < F < E².
```

One large and `N-1` equal nonnegative atoms therefore give a finite diagonal head `H_N` with

```text
||H_N||_HS² = E,   ||H_N²||_HS² = F.
```

Head and reserve have disjoint invariant supports.  Thus the self-adjoint Hilbert--Schmidt operator
`T = H_N + R_N` satisfies, exactly,

```text
2 Tr(T²) = M_0^src,
2 Tr(T⁴) = M_1^src.
```

Outside the first `N` marked primes its diagonal is the reciprocal smooth RVM skeleton, while its
selected cofinal source triangles retain nonzero holonomy.  This is an unconditional simultaneous
solution of the first two reflected source moment equations with the arithmetic tail and
determinant-visible cycle data both preserved.  It is stronger than a scalar feasibility check.

## All-order ownership theorem

For any self-adjoint Hilbert--Schmidt operator `T`, define

```text
m_n(T) = ||T^(n+1)||_HS².
```

For every real polynomial `p(X)=Σ_i c_i X^i`, the odd-power probe

```text
P_p(T) = Σ_i c_i T^(2i+1)
```

obeys

```text
⟨T^(2i+1), T^(2j+1)⟩_HS = ||T^(i+j+1)||_HS²
```

and hence

```text
Σ_i,j c_i c_j m_(i+j)(T) = ||P_p(T)||_HS² ≥ 0.
```

Consequently, complete reflected incidence

```text
2 ||T^(n+1)||_HS² = M_n^src   for every n
```

forces every normalized prime--archimedean source Hankel test to be nonnegative.  Existing
source-Hankel equivalence then gives RH and the compact positive Markov germ representation before
any Fredholm determinant is formed.  Complete incidence is therefore exactly Route P's carrier
problem, not an unmatched Route K pivot.

This theorem does **not** construct the all-order `T`.  It proves ownership: finite-order
marked-prime incidence remains Route K's positive survivor; its only complete extension lands in
Route P.

## Novelty audit

Nearby primary literature covers the ingredients separately:

- Berg--Szwarc, [*Self-adjoint operators associated with Hankel moment
  matrices*](https://arxiv.org/abs/2105.07252), studies closed Hankel forms and associated
  self-adjoint operators.  It supports treating Hankel positivity as established moment-operator
  theory, not as a novelty claim here.
- Mädler--Schmüdgen, [*On the Truncated Matricial Moment Problem.
  I*](https://arxiv.org/abs/2310.00957), proves finite atomic representation in a much more general
  truncated moment setting.  The two-level finite-head realization is therefore an elementary
  component, not the claimed contribution.
- Bownik--Jasper, [*The Schur-Horn theorem for operators with finite
  spectrum*](https://arxiv.org/abs/1302.4757) and [*Diagonals of self-adjoint operators I: compact
  operators*](https://arxiv.org/abs/2212.08182), characterizes possible diagonals in unitary orbits
  of self-adjoint operators.  Those results do not supply this fixed cofinite RVM diagonal together
  with source moments and off-diagonal source holonomy.

No checked source gave the exact combined theorem: preserve a prescribed cofinite reciprocal-RVM
diagonal, retain a cofinal Schatten-1 source-cycle carrier with nonzero holonomy, and match the
first two reflected prime--archimedean source moments exactly by a disjoint finite head.  This is
noncollision evidence, not proof of priority.  The odd-power Gram/Hankel identity is recorded as
structural factorization, not new science by itself.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCofinalTriangleNuclearCarrier.lean
formal/GaloisForLFunctions/RHTower/FiniteTwoLevelMomentCarrier.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedFiniteTwoLevelDiagonalCarrier.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCofiniteRVMQuarticReserve.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence.lean
formal/GaloisForLFunctions/RHTower/XiPrimeMarkedAllOrderIncidenceFactorization.lean
```

Headline theorems:

- `two_mul_opTrace_four_routeKQuarticallyAdmittedOperator`
- `routeKQuarticallyAdmittedOperator_diagonal_of_index_ge`
- `routeKQuarticallyAdmittedOperator_selectedHolonomy_ne_zero`
- `momentFunctional_pow_two_eq_hsNormSq_oddPowerProbe`
- `riemannHypothesis_of_routeKAllOrderReflectedEnergyIncidence`
- `primeArchCompactMarkovGermRepresentation_of_routeKAllOrderIncidence`

Targeted builds pass.  `#print axioms` for the closure theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.
