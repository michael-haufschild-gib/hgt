# FZZ cigar parity-delay source continuation

## Status

Formalized in Lean. FZZ-P continuation/divisor-landing burden closed; dynamical orientation remains
open.

## New source law

Let `B(t)` be the exact FZZ long-string reflection-delay deficit derived from the cigar continuum
spectral asymmetry and positive charge tower. Define

`P(t) = B(t) - 2 B(2t)`.

For every positive delay,

`P(t) = 1/(exp(t)+1)`.

More strongly, `P` is the alternating supertrace of literal FZZ charge-delay sectors:

`P(t) = Σ_{n≥0} (-1)^n exp(-(n+1)t)`.

Thus parity of the FZZ charge tower produces the Fermi kernel without importing a new analytic
source.

## Main theorem

Define the complex source transform without zeta, Xi, or a zero enumeration:

`M_FZZ(s) = Mellin(P)(s)`.

Lean proves:

- `M_FZZ` is holomorphic on `Re s>0`, hence across the whole critical strip;
- on `0<Re s<1`, `M_FZZ(s)=0` iff `ζ(s)=0` iff `ξ(s)=0`;
- at `s=1/2+iE`, the new source mode agrees exactly with the earlier real-energy FZZ horizon mode;
- completeness of source modes by real horizon energies is equivalent to RH.

This repairs the circularity of the earlier endpoint
`fzzCigarContinuumMellinDivisor := riemannZeta`: complex continuation and divisor comparison are now
theorems about a literal FZZ-derived source integral rather than definitions.

## Significance

Closed FZZ-P's independent complex continuation/divisor landing obligation. Source definition is
nonpolynomial and infinite (an alternating charge-tower supertrace), so it survives all formalized
finite affine/polynomial pencil no-go results.

It does not prove RH. Remaining open theorem is physical/dynamical orientation:

`every open-strip zero of M_FZZ has real part 1/2`.

Lean proves that statement is exactly RH-strength. Future work must derive it from literal
interacting FZZ/GFZZ structure, not assume self-adjointness or relabel zeros.

## Lean artifact

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityDelaySourceContinuation.lean`.

Key declarations:

- `fzzCigarParityDelay_eq_fermi`
- `hasSum_fzzCigarParityChargeDelay`
- `analyticOnNhd_fzzCigarParityMellin`
- `fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero`
- `fzzCigarParityMellin_eq_zero_iff_xi_eq_zero`
- `fzzPunctureHorizonDilationMode_iff_parityMellinMode`
- `fzzCigarParityMellinComplete_iff_riemannHypothesis`

## Corpus basis and novelty audit

- `FZZCigarScatteringSpectralAsymmetry` supplies exact cigar reflection deficit, Fourier delay,
  charge-tower sum, and positive-real Bose Mellin identity, but no complex source continuation.
- `SalemFermiModeIntegral` supplies Fermi Mellin holomorphy and continued closed form, but no FZZ
  provenance.
- Corpus search found no prior theorem identifying FZZ parity charge supertrace with the Salem
  source or using that identity to repair FZZ continuation.

Novel contribution is the exact cross-source identification and resulting source-native FZZ
endpoint. Bose/Fermi dyadic algebra and Fermi Mellin formula are classical individually.

## Literature audit (27 August 2026)

- Ashok–Troost, *A Twisted Non-compact Elliptic Genus*, arXiv:1101.1059, derives cigar continuum
  spectral asymmetry from exact reflection amplitudes, but does not connect its charge tower to the
  Salem RH kernel: https://arxiv.org/abs/1101.1059
- González–Negrín, *A new equivalence to the Riemann Hypothesis by means of the Salem integral
  equation*, arXiv:2604.15396, uses the Fermi Mellin integral and pure Mellin modes, but does not
  derive the Fermi source from FZZ cigar reflection data:
  https://arxiv.org/abs/2604.15396
- Creutzig–Hikida–Rønne, *The FZZ duality with boundary*, arXiv:1012.4731, supplies FZZ/sine-Liouville
  boundary and Chan–Paton context but no zeta/Salem Mellin connection:
  https://arxiv.org/abs/1012.4731
- Targeted arXiv searches found no primary source joining these two constructions. Absence claim is
  bounded by searched sources.

## Verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityDelaySourceContinuation.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint reports no error in this module; failures are unrelated concurrently owned
  unreachable modules.
