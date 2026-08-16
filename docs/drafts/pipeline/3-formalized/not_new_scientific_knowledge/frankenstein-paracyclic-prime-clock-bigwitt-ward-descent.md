# Frankenstein paracyclic prime-clock Big-Witt Ward descent

- **ID:** FRANKENSTEIN-PRIME-CLOCK-BIGWITT-WARD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Cross-corpus synthesis: paracyclic source anomaly, Big-Witt Frobenius seam,
  Hochschild BV-Green boundary, Calderon-Witt oriented source, and Gamma reflection-odd boundary
- **Statement:** A prime-clocked paracyclic anomaly has a two-prime Big-Witt seam coefficient that
  is zero exactly on the critical line and strictly negative off it; descent of its Gamma physical
  boundary through the exact oriented source boundary is equivalent, fibrewise, to the critical-line
  condition and, globally, to RH.

## Goal

Test whether the Faddeev-Popov/BRST compensation pattern can convert an exact source relation into a
coefficient-faithful obstruction to an off-line Xi divisor without inserting the desired cancellation
by definition.

Physics correction: Taylor expansion of the sine-Gordon interaction does not itself require
Faddeev-Popov ghosts. Ghosts enter after gauge fixing a genuine redundancy. Accordingly, the only
honest corpus translation is a graded/Koszul compensator attached to an existing source quotient,
with a separately proved physical Ward-descent law.

## Gates

- [x] 0 → 1  in-progress: source carrier and hostile tests identified
- [x] 1 → 2  fully-proven: dependency-closed algebraic statements proved
- [x] 2 → 3  formalized: exact leaf builds and axiom audit pass
- [ ] 3 → 4  publication-ready: novelty audit and unconditional selected Ward descent still open

## Heavy-conjecture loop

### Conjecture 1 — contractible ghost kills the off-line anomaly

**Failed.** `ResiduePromotionAnomaly.lean` proves the fitted compensator splits as the original
complex plus a contractible pair, and the residue vanishes on that pair. Contractible ghost sectors
do not alter physical cohomology; this construction cannot kill an occupied off-line class.

**Positive survivor.** Any useful ghost must be non-contractible before the physical quotient, or
must detect failure of a physical observable to descend through an already exact source relation.

### Conjecture 2 — complete Big-Witt off-diagonal fibre supplies the ghost

**Failed.** Existing complete-fibre BV-Green cancellation is fitted: its off-diagonal chain is exactly
the negative of the physical chain. It contains no new Xi constraint.

**Positive survivor.** Retain the two-prime seam itself and derive its coefficient from the Xi source;
do not complete the fibre by adjoining its negative.

### Conjecture 3 — reflection makes forward and reflected ghosts cancel

**Failed, with sharp survivor.** For `n ≥ 2`, the negative product of the forward and reflected
paracyclic anomaly coefficients equals

```text
GammaSixOppositeBoundaryCurvature(log(mateGain n rho))
  * leadingCoefficient(rho) * leadingCoefficient(reflect rho).
```

It vanishes exactly when `Re rho = 1/2`. Reflection therefore exposes nonlinear curvature rather
than an unconditional cancellation.

Lean:

- `frankensteinParacyclicReflectedCurvatureCoefficient_eq`
- `frankensteinParacyclicReflectedCurvatureCoefficient_eq_zero_iff`

### Conjecture 4 — prime-clock the anomaly before taking the Big-Witt seam

**Proved.** Define

```text
A_rho(p) = (mateGain p rho - 1) * leadingCoefficient(rho).
```

The Big-Witt Frobenius seam for primes 2 and 3 is

```text
-2 * primePairWeight(2,3) * ‖A_rho(2) - A_rho(3)‖².
```

The prime weight is positive and the leading source coefficient is nonzero. Since
`mateGain 2 rho = mateGain 3 rho` iff `Re rho = 1/2`, the seam coefficient is zero exactly on the
critical line and has negative real part exactly off it. This is a source-derived discrete Jacobian,
the closest honest analogue of an FP determinant in this corpus.

The same coefficient is the ground readout of the Hochschild boundary of an explicit BV-Green
chain. Thus the result is chain-level, retains the Xi divisor label, and is not an arbitrary scalar
test.

Lean:

- `deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff`
- `deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_re_lt_zero_iff`
- `frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout`
- `frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout_eq_zero_iff`

### Conjecture 5 — physical Gamma boundary obeys the oriented source quotient

**Exact reduction proved; unconditional producer open.** The explicit two-prime incidence source has
zero Calderon-Witt global oriented boundary. Let selected Ward descent at `rho` mean that some linear
reader of that oriented boundary agrees, on this source, with the actual Gamma-polarized
reflection-defect boundary. Then

```text
SelectedWardDescendsAt(rho) ↔ Re rho = 1/2,
∀ rho, SelectedWardDescendsAt(rho) ↔ RH.
```

This is not an RH proof: unconditional selected Ward descent is precisely the remaining producer.
It cannot be replaced by a global continuous quotient factorization; existing singular-corona and
continuous-boundary no-go theorems rule out that stronger move off the neutral line. Required law is
source-selected, coefficient-faithful, and non-equivariant.

Lean:

- `deningerCalderonWittGlobalOrientedBoundary_primeClockParacyclicTwoThreeIncidence_zero`
- `frankensteinPrimeClockParacyclicSelectedWardDescendsAt_iff`
- `everyFrankensteinPrimeClockParacyclicSelectedWardDescends_iff_riemannHypothesis`

## Interpretation

The corpus can use the ghost concept, but not as “add an unphysical negative copy.” Correct
Frankenstein mechanism is:

1. genuine source quotient supplies gauge redundancy;
2. Xi-dependent prime clock supplies a nonconstant gauge response;
3. Big-Witt two-prime seam supplies a sign-definite discrete Jacobian;
4. Hochschild BV-Green chain realizes it before scalarization;
5. Gamma boundary is the physical observable whose selected Ward descent would force the Jacobian
   to vanish.

This combines paracyclic, Big-Witt, BV/Hochschild, Calderon-Witt, Gamma-six curvature, and RH endpoint
routes. It also isolates exact open core without claiming a fitted compensator as new mathematics.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/FrankensteinParacyclicGhostTwoSheetAnomaly.lean`
- `formal/GaloisForLFunctions/RHTower/FrankensteinParacyclicPrimeClockBigWittGhost.lean`
- `formal/GaloisForLFunctions/RHTower/FrankensteinParacyclicReflectedCurvature.lean`
- all three modules wired into `formal/GaloisForLFunctions/RHTower.lean`
- direct `lake env lean` checks pass
- exact leaf builds pass; no umbrella build was run
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- targeted forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `native_decide`

## Novelty and status

- **Internal mathematical content:** `[PROVED HERE]`
- **Cross-route interpretation:** `[BRIDGE]`
- **External novelty:** `[NOVELTY UNVERIFIED]`
- **RH status:** not proved; unconditional selected Ward descent remains `[OPEN CORE]`

## Log

- 2026-08-16 — conjecture/failure/pivot loop completed; three Lean modules checked and exact leaf
  builds passed; selected Ward descent isolated as irreducible producer.
