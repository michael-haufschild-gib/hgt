# HB phase-sensitive chiral Ward amplitude

## Status

Paper proof and Lean formalization complete 2026-08-28. Ready for stage-3 promotion. Frontier map is read-only and was not modified.

## Route

HB, with exact transmutation to Deninger, FZZ-P, PW-B, and RBH.

## Corpus basis

- `d4BMMixedHorizonOpticalSourceProjection_eq` gives the actual nonlinear BM horizon projection as orthogonal-helicity mixing times nonzero Green transfer and nonlinear Einstein carrier.
- `d4BMGaugeFixedSecondHarmonicGreen_ne_zero` and `d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero` make the radial/source multiplier faithful for nonzero seed amplitude.
- `d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq` exposes the phase-sensitive complex amplitude whose squared modulus produced the HC42 Ward-energy square.
- `fzzCigarParityDeningerReflectGaugeWardCharge_eq` identifies the common signed coordinate as `1 - 2 Re(rho)`.

## HC43 conjecture

For every Xi-divisor copy `q`,

`d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q = I * q.im * D(q)`,

where `D(q)` is the Deninger reflect-gauge Ward charge. Consequently, for every nonzero nonlinear seed, the actual BM mixed-horizon optical projection is a nonzero complex multiplier times `D(q)`. After calibration by that multiplier, the projection is exactly `D(q)`, not merely its square.

## Positive survivor

Actual BM chiral source projection is a faithful linear carrier of the common signed Ward coordinate. Its multiplier is nonzero for every nonzero Einstein seed. Calibration reconstructs `1 - 2 Re(rho)` exactly, including left/right orientation. Exact complex-ratio identities connect the same amplitude to FZZ information force, every PW-B recoil grade, and actual RBH multiplicity-leading imbalance.

## Open core

This theorem closes phase/orientation loss in passive HB power but does not force common Ward charge to vanish. Universal cancellation of one fixed nonzero physical seed is formally equivalent to RH. Remaining proof burden is therefore a source-native conservation/solvability theorem making actual chiral projection zero unconditionally.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude`

Main results:

- exact helicity coefficient `i Im(rho) D(rho)`;
- nonzero phase-sensitive physical multiplier;
- exact actual-source factorization and calibrated reconstruction;
- strict left/right orientation;
- exact FZZ-P, PW-B, and RBH complex-amplitude transmutations;
- pointwise zero-locus and universal RH equivalence.

All declarations are unconditional. No new axioms, premises, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered exact topological-black-hole quasinormal modes and stability (Birmingham--Mokhtari, arXiv:hep-th/0609028 and 0709.2388), black-hole realizations of Riemann zeros (Giri, arXiv:0905.4939), scaling-Hamiltonian spectral RH work (Connes--Consani, arXiv:1910.14368), nonlinear black-hole mode excitation (arXiv:2112.11168), and complex-bilinear Teukolsky currents/excitation coefficients (arXiv:2210.15935). These sources supply neighboring ingredients but no exact identity between an actual nonlinear BM chiral source amplitude and a Deninger divisor Ward charge, no calibrated signed reconstruction, and no cross-route FZZ/PW/RBH amplitude transmutation. This supports a bounded no-match finding, not an exhaustive literature-wide novelty claim.

## Conjecture loop

- HC43-A: exact helicity coefficient factorization — proved in Lean.
- HC43-B: actual source projection factorization with faithful multiplier — proved in Lean.
- HC43-C: calibrated amplitude recovers signed common Ward charge — proved in Lean.
- HC43-D: universal vanishing is equivalent to RH — proved in Lean.

## Verification audit

- Direct source check: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude.lean` — pass.
- Target-only final build: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude` — pass, 12,003 jobs; no umbrella/full build.
- `#print axioms` on all 16 public theorems — only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint reports no HC43 defect. Global lint remains nonzero only because of pre-existing unreachable modules outside this card's scope.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.
