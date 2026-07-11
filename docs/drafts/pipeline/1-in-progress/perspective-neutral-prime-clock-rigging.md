# Perspective-neutral prime-clock rigging

- **ID:** `perspective-neutral-prime-clock-rigging`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** completed Euler--Gamma constraint viewed in the reflected infinite prime CCR superspace
- **Statement:** `[CONJECTURE]` There is a source-derived operator family `T(s)` whose CCR covariance
  defect factors through the completed constraint `Xi(s)`, and whose on-shell value at every `Xi`
  zero is a nonzero bounded normal intertwiner between the reflected prime coherent sectors.

## Goal

Prove RH without introducing a time-propagating Hamiltonian. The physical state is to be defined by
the completed arithmetic constraint before a prime-clock perspective is chosen. Changing between
the two FE--Schwarz-related clock perspectives need only be covariant **on shell**, at a zero of the
constraint. The already formalized prime-clock Shale diagonal would then force every zero onto
`Re(s)=1/2`.

This card is deliberately separate from the four live routes in
`docs/reports/rhtower_status_1107.md`.

## Gates

- [x] 0 → 1 in-progress: the target implication, required representation category, known selector,
  and immediate countermodel tests are explicit.
- [ ] 1 → 2 fully-proven: construct the on-shell family from the completed Euler--Gamma source,
  prove its covariance-defect factorization, and prove its zero fibers are nonzero, normal, and
  CCR-covariant.
- [ ] 2 → 3 formalized: formalize the source construction and compose it with
  `riemannHypothesis_iff_xiZero_primeClockShale`.
- [ ] 3 → 4 publication-ready: pass exact parent-literature, non-circularity, novelty, and
  significance gates.

## Mathematical arena

Let `P` be the primes and let `W(c00(P))` be the algebraic Weyl algebra of finite-support prime
coordinates. For `s=sigma+it`, the formal displacement functional is

```text
alpha_s(p) = p^(-s).
```

It defines a coherent representation `pi_s` even when `alpha_s` is not in `l2(P)`, because every
algebraic Weyl observable has finite prime support. Put `tau(s)=1-conj(s)`. The proved Shale diagonal
theorem gives

```text
pi_s and pi_tau(s) are normally/unitarily equivalent
  iff
Re(s)=1/2.
```

Thus it is enough to construct an operator family whose value at each `Xi` zero `rho` is a nonzero
bounded normal operator

```text
U_rho : H_rho -> H_tau(rho)
```

that intertwines the Weyl actions. Irreducibility then upgrades a nonzero intertwiner to sector
equivalence, and the Shale diagonal locates `rho`.

## Required source construction `[OPEN CORE]`

The operator `U_rho=T(rho)` must be obtained from the completed Euler--Gamma constraint, not
postulated from the location of `rho`. The continuous-family no-go proves that `T(s)` cannot be an
intertwiner at every parameter: it would vanish on the dense off-line set and hence everywhere.
The viable replacement is an on-shell defect factorization

```text
T(s) pi_s(a) - pi_tau(s)(a) T(s) = Xi(s) R_s(a)
```

for every finite-support Weyl observable `a`. A construction must simultaneously establish:

1. **FE covariance modulo the constraint:** its failure to change between `s` and `tau(s)` clock
   descriptions factors through the completed equation of motion.
2. **On-shell CCR covariance:** at `Xi(rho)=0`, it intertwines every finite-support Weyl observable,
   not merely scalar partition functions.
3. **Normality:** it acts inside the Hilbert/GNS representation category in which the Shale
   obstruction is valid.
4. **Nonvanishing at a zero:** it must survive when the scalar completed amplitude itself vanishes.
5. **Source purity:** no factor `Xi(s)`, zero divisor, or assumption equivalent to square
   summability may be inserted into its definition.

The tension between items 4 and 5 is the present mathematical core. A simple value-level rigging map
dies at a zero; a residue-level map is nonzero at a simple zero but has not been shown to be
CCR-covariant or to cover multiple zeros.

## Countermodel and kill tests

- `[FALSIFIED INTERFACE]` Scalar functional-equation equality cannot imply sector gluing:
  FE--Schwarz-symmetric entire functions can carry off-line zero quartets.
- `[FALSIFIED INTERFACE]` A bare Hilbert-space isomorphism is irrelevant: separable Hilbert spaces
  are abstractly isomorphic even when their Weyl representations are disjoint.
- `[FALSIFIED INTERFACE]` Finite-prime intertwiners carry no information: all finite coherent
  displacements are implementable.
- `[FALSIFIED INTERFACE]` Multiplication by `Xi` is circular and vanishes precisely where a nonzero
  intertwiner is required.
- `[FALSIFIED INTERFACE]` A continuous family that is already a normal intertwiner at every parameter
  vanishes identically; this is proved in `PrimeClockContinuousNoGo.lean`.
- `[OPEN TEST]` A distributional, nonnormal clock change may evade the Shale criterion; normality must
  be derived physically rather than added only to force the conclusion.

## Attack

Start from the completed source as a constraint, not a flow. Seek a perspective-neutral **on-shell**
map on the algebraic prime Weyl space whose two gauge fixings give `pi_s` and `pi_tau(s)`. The first
decisive subproblem is:

```text
Does the Euler--Gamma completion define a non-circular CCR covariance defect
that is divisible by Xi, while its quotient leaves a nonzero normal map at every zero?
```

A positive answer proves RH through the formalized selector. A theorem that every source-pure defect
factorization is scalar, nonnormal, or zero on shell kills this reformulation cleanly.

## Lean connection

The downstream implication is already formalized in
`formal/GaloisForLFunctions/RHTower/PrimeClockShaleDiagonal.lean`. The continuous-interface no-go is
formalized in `formal/GaloisForLFunctions/RHTower/PrimeClockContinuousNoGo.lean`. No Lean declaration
will be added for the conjectural on-shell map until the paper definition is non-circular and the
normality claim is proved.

## Log

- 2026-07-11 — opened after proving the prime-clock Shale diagonal; scalar, finite-cutoff, and bare
  Hilbert-isomorphism interfaces excluded.
- 2026-07-11 — continuous global-intertwiner interface formally killed; target sharpened to an
  on-shell covariance-defect factorization modulo the completed constraint.
