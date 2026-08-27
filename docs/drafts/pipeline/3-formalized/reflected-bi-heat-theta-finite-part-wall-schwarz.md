# Reflected bi-heat theta finite-part wall Schwarz law

- **ID:** RBH-TFPW
- **Stage:** 3-formalized
- **Type:** SOURCE ORIENTATION DECOMPOSITION
- **Parent:** RBH-TFPR
- **Frontier-map policy:** read only

## Theorem

Let critical-wall reflection preserve height and heat scale:

`P.wallReflect.z = 1 - conj(P.z)`, `P.wallReflect.x = P.x`.

Then:

1. wall reflection is an involution with fixed locus exactly `Re(P.z)=1/2`;
2. every real-regulator pair sum at wall reflection is complex conjugate of
   original pair sum;
3. canonical theta-pole finite part obeys same exact Schwarz covariance;
4. real channel is wall-even, imaginary channel is wall-odd, and exact defect is
   `2 i Im(finitePart)`;
5. canonical finite part is real on critical wall.

This separates two reflections erased by prior formulations: complementary
factor reflection `z↦1-z` is completely blind, while wall reflection
`z↦1-conj z` retains one canonical odd source channel.

## Corpus basis

- RBH-TFPR proves factor-reflection invariance at regulated and finite-part
  levels.
- `XiHeatCassiniReflectedPhaseSourceJet` shows literal mixed grade--phase source
  jet is odd under grade reflection alone and even when grade and phase flip
  together.
- `Reflection.natCast_cpow_conj` and `Complex.conj_tsum` provide exact termwise
  conjugation and infinite-sum transport.
- Mandatory corpus search found no wall-Schwarz theorem for canonical RBH finite
  part.

## Paper proof

Conjugating datum conjugates both complementary orders at every real regulator.
Positive real Dirichlet bases obey complex-power conjugation, and additive heat
weights are real, so each pair term conjugates.  `Complex.conj_tsum` transports
identity through complete double sum.  Conjugation is continuous; applying it
to canonical pole-subtracted limit, observing real theta-pole coefficient, and
using Hausdorff uniqueness gives finite-part conjugation.

Critical-wall reflection is conjugation followed by complementary factor
reflection.  Prior factor-reflection invariance therefore converts conjugation
law into exact Schwarz law.  Complex extensionality identifies fixed locus,
even/odd channels, and pure-imaginary defect.

## Formal theorem package

- `ReflectedBiHeatDatum.conjugate_conjugate`
- `asymmetricHeatPairTerm_conjugate`
- `reflectedBiHeatPairSum_conjugate_real`
- `reflectedBiHeatFinitePart_conjugate`
- `ReflectedBiHeatDatum.wallReflect_wallReflect`
- `ReflectedBiHeatDatum.wallReflect_eq_iff_re_eq_half`
- `reflectedBiHeatPairSum_wallReflect_real`
- `reflectedBiHeatFinitePart_wallReflect`
- `reflectedBiHeatFinitePart_wallReflect_re`
- `reflectedBiHeatFinitePart_wallReflect_im`
- `reflectedBiHeatFinitePart_sub_wallReflect`
- `reflectedBiHeatFinitePart_im_eq_zero_of_re_eq_half`

## Provisional literature audit

Search checked primary/general sources on zeta regularization, reflection
formulas, and Schwarz reflection.  They support generic symmetry mechanisms but
no result found for this complementary-order additive-heat double sum, its
canonical theta subtraction, or exact wall-odd finite-part defect.  Priority
remains provisional pending expert review.

## New exact insight

Canonical theta finite part is simultaneously factor-reflection even and
critical-wall Schwarz covariant.  Hence it is not wholly orientation-blind:
its real part is blind, but imaginary part is canonical wall-odd source.
Entire critical-wall defect is concentrated in that one scalar channel.

Remaining producer burden is sharpened from “construct an odd source” to
“prove canonical imaginary finite part cannot vanish off wall at actual Xi
divisors,” or identify precise failure locus and replacement augmentation.

## Audit

- Module:
  `GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartWallSchwarz`
- Direct `lake env lean` check passed.
- Targeted `lake build` passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import wired; full umbrella build intentionally not run.

## Log

- 2026-08-27 — conjecture frozen after corpus-derived distinction between
  factor reflection and height-preserving critical-wall reflection.
- 2026-08-27 — exact wall Schwarz law and canonical odd-source decomposition
  formalized; moved to stage 3.
