# WP04 — Produce half-integer spectral interval counts

Status: open detection route. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Produce the exact half-integer counting property for the canonical measure `μλ = boundaryMeasure hW`:

\[
\exists Y\subseteq\mathbb R,\quad |\mathbb R\setminus Y|=0,
\qquad \forall a,b\in Y,\ a<b:\quad 2\mu_\lambda((a,b])\in\mathbb N.
\]

The full target derives this from `hW : WeilPositiveFull λ`. It is a strong rigidity target: the existing receiver then yields both `λ = Λ` for `n ≥ 2` and RH. It is not assumed to follow from positivity merely because the receiver exists.

## Starting evidence

- [Half-integer receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilHalfIntegerMassRigidity.lean:297): `vonMangoldt_and_riemannHypothesis_of_half_integer_counting`, including the full-Lebesgue-measure endpoint set.
- [Canonical polarized spectral representation](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConePolarizedRepresentation.lean:143): this fixes which measure must be quantized.
- [Smoothed spectral count](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSpectralCounting.lean:317): a Poisson-kernel count with explicit normalization, not unsmoothed integer counts.
- [Degree-k correspondence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilZetaPowerForward.lean:155): rational interval masses and completed Dirichlet data are equivalent under the theorem's full hypotheses. WP07 owns higher-denominator classification.

## First research milestone

Identify one arithmetic invariant, index or monodromy mechanism that could force **exact** discrete interval mass for this measure. Prove the precise link between that invariant and `μλ` on a nontrivial class of intervals. If it comes from an auxiliary operator or determinant, prove that it represents the same canonical measure and retain every normalization constant.

Separate atomicity, mass quantization and extension to the receiver's common full-measure endpoint set. A local quantization theorem may be a useful intermediate result, but its coverage and unresolved extension must be explicit.

## Exclusions and traps

- Positive measures can have diffuse and fractional components. Representation and positivity alone are not a supplied quantization argument.
- A `T log T` asymptotic, even with small smoothed error, does not give half-integer interval masses. An approximation argument needs a proved separation threshold and a valid limit for the same interval quantity.
- Do not assume the measure is already supported on zeta ordinates, or write it as the zeta zero measure before establishing identification.
- Do not impose an integer-dimensional state space or a single-valued determinant as an extra hypothesis and then call integrality produced. Its construction and identification are the central work.
- Quantization with an arbitrary denominator does not meet the half-integer receiver. Hand denominator-three results to WP07 with exact interval and endpoint conventions.

## Search entry points

```sh
scripts/formal_tools.py research 'half integer counting boundaryMeasure' --module Weil
scripts/formal_tools.py research 'canonical Weil spectral measure quantization monodromy integer mass' --mode deep --budget-seconds 300
scripts/formal_tools.py research 'spectral counting' --module WeilConeSpectralCounting
```

## Completion and handoff

`CLOSED` requires the common full-measure endpoint set and exact counting law derived from arbitrary `hW`, with a compiled application of the existing rigidity theorem. This detects a supplied producer; it does not establish existence. A quantization mechanism requiring an additional structural premise is `CONDITIONAL ADVANCE`, and that premise must be offered to WP01 as an unpaid producer obligation.

If the proposed index mechanism cannot represent the actual measure, state precisely what it does represent and prove the surviving identification or obstruction. Do not record failure of one representation as impossibility of all quantization routes.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/04-quantization/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-04-quantization.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkQuantization*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
