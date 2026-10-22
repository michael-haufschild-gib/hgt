# Complete-resolution second-Cartier normal order

- **ID:** P-CR-NORMAL-ORDER
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean 4) / OPEN RH-BEARING PRODUCER
- **Source:** `rh-current-frontier-map.md` · Route P plus complete-resolution and Meyer/Deninger source modules
- **Statement:** The complete source normal reader is exactly the literal prime-two second-Cartier endpoint, with coefficient, energy, and multiplicity intact; any exact reflected extractor has sensitivity diverging off-line. Universal pre-divisor order remains exactly RH.

## Goal

Construct endpoint moderation from completed source before Xi selection.  Finite measures,
Toeplitz/Bochner admission, scalar shorting, ordinary Loewner order, and bounded cofinal readers are
already dead.  The source observable must retain the literal endpoint rather than a scalar proxy.

## Gates

- [x] 0 → 1 in-progress: source-pure observable and falsifiable completion target
- [ ] 1 → 2 fully-proven: unconditional global source order still open
- [ ] 2 → 3 formalized: the RH-bearing producer is not formalized because it is not proved
- [ ] 3 → 4 publication-ready: external novelty audit and standalone proof

Formalized positive survivor:
`GaloisForLFunctions.RHTower.CompleteResolutionSecondCartierNormalOrder`.

## Heavy-conjecture loop

### C1 — annular/Hurwitz monodromy forces source descent

**Conjecture.** The completed theta source is globally single-valued in logarithmic scale, so the
centered Xi character has integral monodromy and the open critical strip forces grade zero.

**Failure.** The corpus proves the source atom's spin period and the exact centered monodromy, but
not descent of the Xi evaluation through the log cover.  That descent is already equivalent to
neutral grade.  Treating fibrewise evaluation as a global function of the scale variable inserts
the conclusion. `[FAILED / CIRCULAR]`

### C2 — normal-cone renormalization supplies order

**Conjecture.** Cofinal complete-resolution ratios recover the endpoint while a Gamma normalizer
cancels source collapse and leaves a bounded ordered residue.

**Failure.** The normalizer does recover the exact two-prime spectrum.  Off the line, however,
source reflection displacement tends to zero while endpoint separation stays positive.  Therefore
the required normalizer has inverse conditioning tending to infinity.  Recovery supplies no order
budget. `[FAILED AS PRODUCER]`

### C3 — completed-source Riesz/unitary admission

**Conjecture.** Place the literal conormal in a two-sided isometric completed-source flow.  A
bounded nonzero eigenfunctional then has unit-modulus character.

**Failure.** The unitary/Riesz implication is already proved.  What is missing is precisely
bounded admission of the Xi conormal.  Meyer/Deninger modules classify even a pointwise invariant
finite gauge as RH-strength. `[FAILED / EQUIVALENT PREMISE]`

### C4 — exact normal endpoint plus quantitative singularity

**Result.** `[PROVED HERE]` For every finite complete-resolution base `K`, the first source-normal
reader at an actual Xi support equals

\[
  2^{1/2-\rho},
\]

the literal prime-two second-Cartier endpoint character.  The associated positive orbit energy is
exactly the existing coefficient-faithful Hardy endpoint energy, and the support-fibre sum is
exactly analytic multiplicity times one copy.

If `rho` is off line and an arbitrary nonlinear family `T_K` extracts both reflected endpoint
characters with Lipschitz constants `L_K`, then

\[
  L_K \ge
  \frac{|2^{1/2-\rho}-2^{1/2-(1-\bar\rho)}|}
       {\|E_K(\rho)-E_K(1-\bar\rho)\|_1},
\]

so `L_K → +∞`.  No linearity, positivity, equivariance, or label blindness is used.

## Exact classification

Define the pre-divisor order at a completed source image by boundedness of the literal
second-Cartier orbit of its first normal-reader coordinate.  Lean proves

\[
  \operatorname{Order}_K(s)
  \Longleftrightarrow
  \left|2^{1/2-s}\right|=1
  \Longleftrightarrow
  \operatorname{Re}s=\tfrac12.
\]

Consequently universal Xi admission into this source order is equivalent to RH.  This theorem is
an exact consumer/classification; it is not the requested unconditional producer.

## Remaining producer

Let

\[
 d_K(s)=E_K(s)-E_K(1-\bar s),\qquad
 \Delta(s)=2^{1/2-s}-2^{1/2-(1-\bar s)}.
\]

The remaining viable theorem must construct, before divisor selection, a completed Gamma/source
normal gauge `G_K` and exact physical extractor `T_K` such that:

1. `T_K` retains the literal endpoint coefficient and the multiplicity-resolved conormal;
2. `|Delta(s)| ≤ G_K(s) * ||d_K(s)||_1` on the completed source graph;
3. source/Gamma conservation proves
   `G_K(s) * ||d_K(s)||_1 → 0` whenever `xi(s)=0`;
4. neither `G_K` nor its proof uses `s`, a zero, or an endpoint character as hidden construction
   data.

Then `Delta(s)=0` for every Xi zero, hence the endpoint character is unitary and the literal
second-Cartier endpoint is moderate.  Condition 3 is the hard arithmetic statement.  Ordinary
bounded readers force it trivially but are already ruled out; a viable proof must pair the forced
singular normal gain with independent completed-source arithmetic decay. `[OPEN CORE]`

## Lean declarations

- `shellTransferCharacter_eq_bilateralHalfDensityCharacter_two`
- `completeResolution_sourceNormalPrimeTwo_eq_actualXiEndpointCharacter`
- `CompleteResolutionPreDivisorSecondCartierOrderAt`
- `completeResolutionPreDivisorSecondCartierOrderAt_iff`
- `CompleteResolutionXiPreDivisorSecondCartierOrderLaw`
- `completeResolutionXiPreDivisorSecondCartierOrderLaw_iff_riemannHypothesis`
- `completeResolutionPreDivisorOrder_forces_actualXiEndpointModeration`
- `completeResolutionSourceNormal_actualXiLiteralEndpoint_coefficientMultiplicity`
- `tendsto_completeResolutionReflectionEndpointSensitivity_atTop`
- `tendsto_exactCompleteResolutionEndpointExtractor_lipschitz_atTop`

Exact leaf build passes.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import is wired; umbrella was not built.

## External frontier audit

- Meyer constructs the zeta-zero spectrum on a nuclear Fréchet quotient, not a positive Hilbert
  completion making every zero evaluation bounded:
  <https://arxiv.org/abs/math/0412277>.
- Paugam constructs the unconditional symplectic pairing implementing spectral reflection; this
  supplies cross-fibre duality, not the same-fibre positive order needed here:
  <https://arxiv.org/abs/0803.0199>.
- Deninger's obstruction to a functorial real Weil cohomology for arithmetic curves rules out
  treating a global real positive completion as automatic:
  <https://arxiv.org/abs/2204.02714>.

No checked source supplies the quantitative Gamma/source decay in the remaining producer.  This
is a bounded audit, not a priority claim. `[NOVELTY UNVERIFIED]`

## No-go closure

- **Exact killing mechanism:** complete-source cofinal collapse plus fixed off-line endpoint
  separation forces divergent inverse conditioning.  Normal reconstruction alone cannot yield
  order.
- **Strongest positive survivor:** exact source-normal/literal-endpoint identification, exact
  energy and multiplicity preservation, and quantitative divergence of every faithful extractor's
  Lipschitz sensitivity.
- **New insight:** singularity is not optional.  Remaining producer is a cancellation theorem
  between forced normal-reader singular gain and independent arithmetic source decay, not another
  compact completion or scalar short.
- **Status:** survivor dependency-closed and formalized.  Global moderation law remains open and
  RH-equivalent. `[NOVELTY UNVERIFIED]`

## Log

- 2026-08-18 — four heavy-conjecture pivots audited; exact source-normal endpoint bridge and
  sensitivity blow-up formalized; leaf build and axiom audit pass.
