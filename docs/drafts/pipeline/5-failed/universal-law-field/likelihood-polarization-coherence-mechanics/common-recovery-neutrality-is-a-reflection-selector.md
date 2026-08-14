# Common-recovery neutrality is a reflection selector

- **ID:** ULF-LPCM-F1
- **Stage:** 5 — failed/retired
- **Type:** FALSIFIED FIELD CONJECTURE WITH POSITIVE SURVIVOR
- **Claim:** A functional-equation involution whose lift through a common recovery kernel preserves
  all relative information must identify the reflected endpoint laws.
- **Status:** `[FALSIFIED] [EXACT TWO-POINT COUNTERMODEL]`
  `[POSITIVE SURVIVOR PAPER-PROVED] [LEAN NOT YET WRITTEN] [NOT RH]`

## Conjecture

Let `P,Q` be reflected observer laws and let `K` be a common recovery kernel.  The packet theorem
gives

\[
 D(PK\Vert QK)=D(P\Vert Q).
 \tag{CRS.1}
\]

The conjecture attempted to interpret exact information neutrality as zero reflected information,
hence `P=Q`.

## Exact killing theorem

Equality `(CRS.1)` holds for every common Markov kernel and every pair `P,Q`, including distinct
pairs.  It is a sufficient-statistic identity, not a zero-work identity.

### Two-point countermodel

Take `X={-1,+1}`, let reflection exchange the two points, and set

\[
 P(+1)=3/4,
 \quad P(-1)=1/4,
 \qquad
 Q=R_*P.
\]

Let `K` be any probability law independent of `x`, or any strictly positive `x`-dependent common
kernel.  Then `P ne Q`, Jeffreys information is strictly positive, and appending `K` preserves it
exactly.  The reflected packet action is involutive and information-neutral off center.

## Why stronger common divergences do not help

Relative to the balanced mixture, this pair has nonzero posterior contrast.  ULF-LPCM-1 proves
that common recovery preserves not only KL and Jeffreys information but also Hellinger distance,
triangular discrimination, the full `tanh/sech` likelihood polarization, and the lift-coherence
energy.  Replacing KL by another common-channel `f`-divergence therefore does not repair the
conjecture.

## No-go closure

- **Exact killing theorem/mechanism:** a common kernel is split by first-coordinate projection, so
  it preserves every likelihood ratio.  Information neutrality is isometry, not annihilation.
- **Strongest positive survivor:** a reflected pair canonically generates two distinct lift
  doctrines.  Their exact disagreement is `4||D f||^2`, where `D` is posterior contrast.  On a
  faithful state the lifts agree exactly when `P=Q`.  See ULF-LPCM-1.
- **New insight:** selection requires a source coherence law between different polarizations, not
  stronger conservation inside one polarization.
- **Status:** survivor is dependency-closed on paper in
  `pipeline/2-fully-proven/universal-law-field/likelihood-polarization-coherence-mechanics/`.
  Lean corpus was audited read-only; no Lean file was written or built.

## Hostile boundaries

1. A lossy non-common kernel can contract divergence, but zero after observation proves only
   observer indistinguishability unless the observer is sufficient.
2. An expansive inverse can reconstruct arbitrary information; passivity is a separate law.
3. Product replication amplifies positive information but still does not make neutrality mean
   zero.
4. The survivor does not prove a physical arithmetic source identifies the two lifts.

## Log

- 2026-08-14 — conjecture killed by common-kernel likelihood preservation.
- 2026-08-14 — exact lift-coherence current retained as positive survivor.

