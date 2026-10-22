# Multi-scale Gamma superselection for unequal-temperature BTZ clocks

- **ID:** `multiscale-gamma-superselection-for-btz-clocks`
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** D. Birmingham, I. Sachs, S. N. Solodukhin, *Conformal Field Theory Interpretation of Black Hole Quasi-normal Modes*, arXiv:hep-th/0112055, equations (2), (7), and (8)
- **Statement:** `[CONJECTURE]` A finite signed product of affine Gamma clocks with several nonzero slopes is DA exactly when every affine pole-lattice charge cancels after partitioning slopes into rational commensurability classes.

## Goal

Extend the proved common-scale Gamma charge classifier to observables whose clock coordinates have
different scales.  The first exact target is the rotating BTZ commutator,

`Gamma(hL+i*p+/(2*pi*TL)) Gamma(hL-i*p+/(2*pi*TL))`

times

`Gamma(hR+i*p-/(2*pi*TR)) Gamma(hR-i*p-/(2*pi*TR))`,

where `TL` and `TR` are generally unequal and `p+`, `p-` are affine functions of the same observed
frequency.  Its poles are exactly the BTZ quasinormal frequencies in the cited source.

## Gates

- [x] 0 → 1 prerequisite: exact source formula, existing one-scale theorem, and missing interface identified
- [ ] 0 → 1 in-progress: state a correct multi-scale charge object and prove the two-scale reduction
- [ ] 1 → 2 fully-proven: prove both commensurable and incommensurable slope cases
- [ ] 2 → 3 formalized: instantiate the rotating BTZ response and its quasinormal pole lattice
- [ ] 3 → 4 publication-ready: standalone multi-clock Gamma classification

## Existing positive residue

Each individual left/right reflected-Gamma sector is already DA exactly on its half-integral
weight lattice and HT otherwise.  Its elementary thermal orientation factor is DA and satisfies
exact KMS detailed balance.  The missing theorem concerns only cancellation between distinct clock
scales in the product observed through one common frequency.

`MeromorphicGammaNatScale.lean` now proves the positive-integer scale-reduction block
unconditionally.  More strongly, every finite signed family containing both `Gamma(n_i*z+a_i)`
and `Gamma(-n_i*z+b_i)` factors is a nonzero DA gauge times its unit-scale refined oriented Gamma
product, and DA/HT is equivalent on the two sides.  Thus the rotating BTZ `+omega/T` and
`-omega/T` pair is covered whenever the temperature scales become integers after one common
normalization.  The remaining commensurable work is cross-sector orbit consolidation and charge
evaluation after refinement, not Gauss reduction, orientation control, or gauge control.

## Required mathematical split

1. **Commensurable slopes.** Use Gamma multiplication to refine all factors to one common scale,
   then apply the existing oriented-orbit charge kernel.
2. **Incommensurable slopes.** Prove that an uncancelled affine pole lattice cannot be hidden by
   factors from another commensurability class and forces hypertranscendence.
3. **Affine offsets.** Track the momentum shifts in `p+` and `p-`; equality of slopes alone is not
   enough for orbit cancellation.

## Corpus impact

- Classifies the complete rotating BTZ black-hole response rather than only each chiral sector.
- Extends `HTGeometry` from one translation clock to finite multi-rate clocks.
- Applies to unequal-temperature CFT sectors, de Sitter static-patch channels, and multi-species
  scattering amplitudes with distinct affine Gamma scales.
- For `RHTower`, supplies a reusable test for whether products of archimedean factors at different
  scales can cancel.  It does not itself constrain zeta zeros or provide prime-source positivity.

## Open core

The incommensurable-slope implication is not currently proved in Lean or on paper in this card.
No BTZ full-product HT claim should be promoted before that implication is established.
