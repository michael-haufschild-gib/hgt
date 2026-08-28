# FZZ parity source-metric reflection tilt

## Status

Route F9 retired. Bare source-metric antiunitarity provably selects a vertical line strictly right
of the critical line. Exact tilted-axis survivor and unique correcting factor are formalized in Lean.

## Attempted conjecture F9

Use the literal all-scale FZZ parity source pairing to construct its canonical antiunitary
coordinate reflection. Test whether this source-native symmetry implements the centered Mellin
functional-equation reflection and therefore supplies the missing F8 reflected-crossing match.

## Proof outcome

For every physical scale `beta>0`, write

`p=P(beta)`, `q=P(2 beta)`, `r=P(4 beta)`, `a=sqrt(r/p)`.

Lean proves `p>r>0` and constructs

`J_beta(u₁,u₂)=(a conjugate(u₂), a⁻¹ conjugate(u₁))`.

This map is involutive and exactly antiunitary for the literal source Hermitian pairing:

`B_beta(J_beta u,J_beta v)=conjugate(B_beta(u,v))`.

For the centered dyadic Mellin carrier `(1,chi(rho))`, however, its affine projective ratio is

`ratio(J_beta(1,chi(rho)))=(p/r) chi(1-conjugate(rho))`.

Thus source-metric reflection differs from functional-equation reflection by the strict factor
`p/r>1` at every positive scale.

## Why route fails

The source diagonal is intrinsically asymmetric because the Fermi source is strictly decreasing.
Metric preservation therefore forces unequal swap weights. Their square ratio survives projective
normalization and cannot equal one. Bare source-metric antiunitarity does not produce the F8
critical-line reflection law; indeed it fails on every centered Mellin carrier, independently of
whether that carrier is a divisor zero.

## Positive survivor

The projective fixed locus is classified exactly:

`ratio(J_beta(1,chi(rho)))=chi(rho)`

if and only if

`Re rho = 1/2 + log(P(beta)/P(4 beta))/(2 log 2)`.

This axis lies strictly to the right of `Re rho=1/2` for every `beta>0`. Hence no critical-line
carrier is projectively fixed by the bare source reflection.

The obstruction also determines its unique scalar repair. Multiplying the reflected projective
ratio by

`P(4 beta)/P(beta)`

recovers functional-equation reflection exactly, and no other complex scalar does so even on one
Mellin carrier. Any viable interacting FZZ/GFZZ mechanism extending this two-scale source model
must therefore generate precisely this inverse diagonal ratio, or an equivalent nonlocal
renormalization. Merely postulating antiunitarity or source-metric preservation is terminal.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParitySourceMetricReflectionTilt.lean`.

Key declarations:

- `fzzKreinPAt_gt_fzzKreinRAt`
- `fzzCigarParitySourceMetricReflection_involutive`
- `fzzCigarParitySourceMetricReflection_pairing`
- `fzzCigarParitySourceMetricReflection_mellin_ratio`
- `fzzCigarParitySourceMetricReflection_mellin_ratio_ne_reflection`
- `fzzCigarParitySourceMetricReflection_mellin_fixed_iff`
- `fzzCigarParitySourceMetricReflection_criticalLine_not_fixed`
- `fzzCigarParitySourceMetricReflection_counterterm_unique`

## Corpus audit

- `FZZCigarParityAllScaleKreinCrossing` supplies the literal scale-dependent source matrix and its
  strict indefinite Hankel law.
- `FZZCigarParityMellinCharacterCrossingReflection` proves centered dyadic character reflection,
  invariant normalized phase, and the exact F8 critical-line crossing criterion.
- Targeted corpus searches for weighted antiunitary swaps, source-metric reflection, and
  projective Mellin fixed axes found no existing theorem deriving this FZZ coefficient ratio,
  shifted line, or unique counterterm.

## Literature audit (27 August 2026)

- Jafferis–Schneider, *Semi-Classical Analysis of the String Theory Cigar*, arXiv:2004.05223,
  analyzes the exact cigar reflection coefficient through complex saddles and bound-state poles.
  It does not construct the parity-Fermi two-scale Hermitian form or its weighted antiunitary:
  https://arxiv.org/abs/2004.05223
- Halder–Jafferis, *Stretched horizon, replica trick and off-shell winding condensate, and all
  that*, arXiv:2402.00932v3, derives exact-in-alpha-prime cigar thermodynamics and off-shell winding
  dynamics. It contains no source-metric Mellin projective fixed-axis classification:
  https://arxiv.org/abs/2402.00932
- Burnol, *Entrelacement de co-Poisson*, arXiv:math/0407443, develops Mellin/zeta intertwining and
  reflection structures. It does not couple them to the FZZ parity source or derive the diagonal
  tilt: https://arxiv.org/abs/math/0407443
- Takook, *Krein Space Quantization and a Spectral Interpretation of the Riemann ξ-Function*,
  arXiv:2606.13932, uses an indefinite spectral framework for a critical-line ξ representation but
  does not derive this weighted FZZ involution, shifted fixed axis, or correction law:
  https://arxiv.org/abs/2606.13932
- Targeted primary-source searches found no exact synthesis. Absence claim remains bounded by the
  searched arXiv corpus.

Novelty verdict: the coefficient-faithful FZZ source antiunitary, exact projective tilt, fixed-axis
classification, and unique inverse-ratio correction appear corpus-new and literature-unlocated.
They close a concrete FZZ-P orientation mechanism and sharpen the remaining interacting-dynamics
burden, but do not prove RH.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParitySourceMetricReflectionTilt.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParitySourceMetricReflectionTilt`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint has no error in this module; any current failures are unrelated concurrently owned
  unreachable-module entries.

## Surviving open core

Derive from interacting FZZ/GFZZ dynamics the exact scalar response `P(4 beta)/P(beta)` (or an
equivalent operator-valued correction) before invoking the F8 reflected-crossing endpoint. Without
that independently sourced correction, source-metric reflection lands on the wrong vertical axis.
