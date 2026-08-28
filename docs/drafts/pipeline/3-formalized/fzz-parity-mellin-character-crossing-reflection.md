# FZZ parity Mellin-character crossing reflection

## Status

Formalized in Lean. Conjecture loop F8 succeeded. Source-native divisor carrier and exact
transverse detector built; interacting reflected-crossing matching remains open.

## New crossing law

For a complex spectral parameter `rho`, take the corpus's centered Mellin character at the first
dyadic dilation,

`chi(rho)=exp(log(2)*(rho-1/2))`,

and land it in the two-coordinate FZZ parity source block as `u(rho)=(1,chi(rho))`. For each
positive source dilation `beta`, divide the natural grade crossing by `|chi(rho)|` to remove the
projective gauge.

Lean proves the exact decomposition

`C_beta(rho) = q_beta * chi(rho)/|chi(rho)| + r_beta * |chi(rho)|`,

where `q_beta=P(2 beta)` and `r_beta=P(4 beta)` are literal parity-FZZ delay coefficients.

Critical-line reflection `rho#=1-conj(rho)` sends `chi` to its conjugate inverse. After norm
normalization, its unit phase is unchanged exactly. Hence the reflected crossing difference is
purely real:

`C_beta(rho)-C_beta(rho#)
  = r_beta * (|chi(rho)|-|chi(rho#)|)`.

Using reciprocal reflected norms gives the closed formula

`Re(C_beta(rho)-C_beta(rho#))
  = r_beta * (exp(log(2)*(Re rho-1/2))
              - exp(-log(2)*(Re rho-1/2)))`,

and `Im(C_beta(rho)-C_beta(rho#))=0`.

For every `beta>0`, Lean proves:

- the real defect is positive iff `Re rho>1/2`;
- the real defect is negative iff `Re rho<1/2`;
- the two normalized crossings are equal iff `Re rho=1/2`.

This is an unsquared signed transverse detector: vertical Mellin phase cancels, while side of the
critical line survives with no aliasing and no divisor enumeration.

## RH endpoint and remaining producer

Define reflected-crossing matching either at one fixed positive FZZ scale or at every positive
scale, quantified only over open-strip zeros of the source-defined parity FZZ Mellin transform.
Lean proves both predicates equivalent to RH:

- `FZZCigarParityMellinReflectionCrossingMatchedAt beta <-> RH` for every `beta>0`;
- `FZZCigarParityMellinUniversalReflectionCrossingMatched <-> RH`.

These are exact source-native endpoints, not an RH proof. Functional equation supplies the
reflected zero and conjugate-inverse character, but does not force equality of the two physical
crossings. Remaining FZZ-P producer is now one concrete dynamical statement: interacting FZZ/GFZZ
pairing must identify the normalized reflected responses of actual parity-Mellin divisor modes.

## Lean artifact

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityMellinCharacterCrossingReflection.lean`.

Key declarations:

- `fzzCigarParityDyadicMellinCharacter`
- `fzzCigarParityMellinCharacterCarrier`
- `fzzCigarParityMellinCharacterNormalizedCrossing_eq`
- `fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection`
- `fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re`
- `fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re_pos_iff`
- `fzzCigarParityMellinCharacterNormalizedCrossing_sub_reflection_re_neg_iff`
- `fzzCigarParityMellinCharacterNormalizedCrossing_eq_reflection_iff`
- `fzzCigarParityMellinUniversalReflectionCrossingMatched_iff_riemannHypothesis`

## Corpus basis and novelty audit

- `RiemannComplexModularCharacterLaw` supplies the centered Mellin character, its real-ray norm,
  critical-line reflection, and reciprocal reflected norms.
- `FZZCigarParityAllScaleKreinCrossing` supplies the all-positive-scale literal FZZ pairing and
  grade crossing.
- `FZZCigarParityDelaySourceContinuation` supplies the source-defined parity-Mellin divisor and its
  proved comparison with Xi in the open strip.
- Corpus searches found many abstract reflection-fixed-point detectors, but no theorem landing the
  centered Mellin character in the literal FZZ parity crossing, canceling its normalized phase, or
  extracting this exact signed radial defect.

Novel contribution is the coefficient-faithful synthesis and pure-real sign classification. The
Mellin dilation character and functional-equation reflection are classical individually.

## Literature audit (27 August 2026)

- Burnol, *Entrelacement de co-Poisson*, arXiv:math/0407443, develops multiplicative convolution,
  Mellin transformation, zeta, and co-Poisson intertwining, but no FZZ parity crossing:
  https://arxiv.org/abs/math/0407443
- Hikida--Schomerus, *The FZZ-Duality Conjecture—A Proof*, arXiv:0805.3931, proves cigar/
  sine-Liouville correlation equivalence, but contains no Mellin-character RH crossing law:
  https://arxiv.org/abs/0805.3931
- Halder--Jafferis, *Stretched horizon, replica trick and off-shell winding condensate, and all
  that*, arXiv:2402.00932, supplies finite-level replica dynamics but not the normalized reflected
  crossing identity: https://arxiv.org/abs/2402.00932
- Targeted searches found no primary source containing this exact FZZ/Mellin/Krein synthesis.
  Absence claim is bounded by searched sources.

## Verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityMellinCharacterCrossingReflection.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityMellinCharacterCrossingReflection`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint reports no error in this module; failures are unrelated concurrently owned
  unreachable modules.
