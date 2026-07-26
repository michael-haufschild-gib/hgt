# Sonin finite-rank Burnol-Lüders energy-partition universality law

- **ID:** `sonin-finite-rank-burnol-luders-energy-partition-universality-law`
- **Law:** LAW511
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninFiniteRankBurnolLudersEnergyPartitionUniversalityLaw.lean`

## Theorem

For every complex finite-rank packet on the even Sonin space, total physical two-corner
Hilbert--Schmidt boundary energy equals:

```text
Burnol-conductor Ward trace of the Lüders-pinned Fourier-reflected packet
+ Fourier-edge Ward trace of its two discarded boundary blocks.
```

This is an exact conservation law with no self-adjointness, reality, compactness, or
nondegeneracy premise on the packet.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed two independent evaluations:

- `finiteRankCutoffWardForm_evenFourier_reflected_self_eq_physicalBoundaryEnergySum`;
- `finiteRankCutoffWardTrace_evenFourierPosition_ludersBoundarySplit`;
- the definition of `finiteRankCutoffWardForm` as
  `finiteRankCutoffWardTrace` against a second finite-rank probe.

The boundary-energy file evaluates the reflected diagonal Ward form as the sum of lower and upper
physical Hilbert--Schmidt energies.  The Burnol file decomposes any reflected finite-packet Ward
trace into a conductor trace of the cutoff-commuting Lüders block plus the exact discarded
two-corner trace.  Corpus never specializes the latter to the packet's own probe and equates the
two evaluations.

## Dependency-closed paper proof

Given coefficients `c` and physical source vectors `x,y`, set

```text
M = finiteRankProbe c x y,
M_F = finiteRankProbe c (F x) (F y).
```

By definition, the Fourier-reflected diagonal Ward form of `(c,x,y)` is the finite-rank Ward
trace with channel `M_F` and reflected test packet `(c,Fx,Fy)`.  The physical boundary-energy
theorem identifies this scalar with

```text
||crossBoundary M||²_HS + ||upperBoundary M||²_HS.
```

The Burnol--Lüders split identifies the same scalar with the physical-cutoff conductor trace of
`ludersPinching M_F` plus the Fourier-cutoff trace of
`crossBoundary M_F + upperBoundary M_F`.  Transitivity yields the claimed exact partition.  No
numerical computation is used.

## Strict corpus delta

Existing theorems separately give an energy representation and a conductor/Lüders representation
of the same Ward quantity.  New law identifies total physical boundary energy with the exact
conductor-plus-residual split of its Fourier-reflected packet for every finite complex packet.

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninFiniteRankBurnolLudersEnergyPartitionUniversalityLaw.lean`
proves:

- `soninFiniteRank_burnolLudersBoundaryEnergyPartition`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninFiniteRankBurnolLudersEnergyPartitionUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Targeted searches found Burnol's local
conductor operator, general Lüders pinching/instrument theorems, Hilbert--Schmidt commutator
estimates, and operator-energy decompositions.  They did not recover this exact finite Sonin
packet identity equating physical two-corner Hilbert--Schmidt energy with a
Fourier-reflected-packet Burnol-conductor trace plus its discarded Lüders boundary trace.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
Burnol--Lüders--Sonin finite-packet partition, not for generic block pinching or commutator
identities.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
