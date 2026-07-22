# Suzuki terminal frontier ledger

- **ID:** `suzuki-terminal-frontier-ledger`
- **Status:** active research control file; read before any Suzuki work
- **Terminal objective:** prove RH, disprove RH, or prove a source-complete no-go for Suzuki's
  operator mechanism.
- **Current terminal result:** none.

## Rule

No new Suzuki card or Lean module is allowed unless it advances the single live edge below or
falsifies it. Coordinate changes, equivalent RH criteria, generic Grams, scalar capacity laws,
and finite-support coefficient reconstructions do not count as progress.

## Already closed — do not reopen

1. **Finite source identification.** The semilocal place connection is exactly the finite
   von-Mangoldt source, coefficient by coefficient (`semilocal-dual-pair-euler-connection-source-law`).
2. **Logarithmic commutator carrier.** The prime shift is the exact logarithmic-position
   commutator and its orthogonal compression splits into internal trace defect plus polarized
   leakage cross (`critical-euler-position-commutator-carrier-law`).
3. **Compact-support cyclic descent.** Physical logarithmic phase and dilation give the exact Weyl
   character; every finite prime-power test descends through the canonical Sonin cyclic probe
   (`SoninSemilocalCyclicWeylDescent.lean`).
4. **Fixed-probe all-prime assembly is impossible.** Critical prime tangent coefficients are not
   absolutely summable, and any fixed nonzero Hilbert--Schmidt central cyclic probe preserves that
   failure in trace norm (`not_summable_traceNorm_soninSemilocalCyclicPrimeTangentCarrier`).
5. **Scalar transport/capacity lane is dead.** Common-displacement splicing pays exactly its own
   seam, and atomless width-two capacity plus untouched decreasing-flank surplus still permits a
   completed-lag violation (`SuzukiBicausalNoFreeSplice.lean`,
   `SuzukiCriticalApexVacuumCapacityNoGo.lean`).
6. **Endpoint weakening is exhausted.** A finite lower floor for the completed prime--Gamma flux
   on Gaussian-rational left-half-strip points is already Lean-equivalent to RH
   (`PrimeArchSourceUpperBoundGate.lean`). Producing more equivalent endpoints is forbidden.
7. **Gamma Schur covariance exists.** The actual valuation tower supplies coherent cross-prime
   covariance, and Gamma Schur elimination is exact valuation translation
   (`XiTransverseGammaValuationCoherence.lean`). Do not search for another abstract covariance.
8. **Coherent causal field exists but bounded recovery fails.** All-prime causal rays fuse before
   squaring (`SuzukiCoherentCausalDepthFusion.lean`), but their gain relative to exact moving-wall
   source is at most `C_h/(p+1)`. No finite uniform inverse exists
   (`SuzukiCoherentResponseGainNoGo.lean`).

## Single live edge

`SUZUKI-COFINAL-COMPLETED-LEAKAGE-FLOOR`

Construct from the actual aperture-dependent Sonin principal/residual graph, before reading any Xi
zero or assuming any Weil sign, a *joint* prime--archimedean cutoff carrier whose finite part is the
canonical Connes--CCM source and prove one cutoff-uniform finite lower bound for its real trace.
Equivalently, prove the completed lower floor consumed by
`CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow`.

The archimedean term must depend on the same cutoff as the prime shell. A fixed trace-class Gamma
operator cannot repair the already-proved non-summability of the positive critical prime tangent
family. Cancellation must occur inside each completed cutoff carrier, before any trace-norm limit.

## Current falsifiable conjecture — only surviving form

`SUZUKI-COHERENT-FUSION-GAMMA-WELD`, **closed unbounded graph form only**:

Construct closed cutoff-dependent relative observation `T_A` from genuine restricted-Weil/Robin
resolvent and Burnol conductor such that:

```text
T_A (coherent causal response) = exact gated sharp wall source,
```

on a common source core, despite forced cofinal gain at least linear in `p`; prove the completed
finite-part trace descends through this graph and satisfies

```text
Re FP Tr(completed prime--Burnol carrier at A) >= -C
```

with one finite `C` independent of `A`. Bounded/frame-preserving `T_A` is formally impossible.
Conjecture is false if forced inverse weights prevent closability, destroy finite-part cyclicity,
or make negative trace defect unbounded below.

## Immediate experiment — symbolic, not numerical

Build graph on explicit prime-wall basis using minimal inverse weights forced by
`SuzukiCoherentResponseGainNoGo.lean`. Determine:

```text
domain(T_A) = {response vectors whose p-weighted sharp reconstruction is square/trace summable}.
```

Then compare this exact graph domain with existing Burnol conductor graph and Connes finite-part
domain. Outcomes:

- common dense closed domain plus finite-part identity: advance live edge;
- graph non-closable or finite-part domain intersection trivial: source-complete no-go for current
  coherent weld;
- generic abstract closed operator without exact source/finite-part identity: no progress; do not
  formalize it.

## Anti-loop checkpoint

Before each new action, answer in this file's log:

1. Which exact unresolved arrow above changes?
2. Which prior theorem prevents this from being a rediscovery?
3. What observation would falsify the conjecture?
4. Does the result prove a source bound, or merely restate RH?

## Log

- **2026-07-22 reset.** `SUZUKI-SOURCE-COMMUTATOR-GRAM` retired as an invalid frontier label:
  corpus already proves the source commutator/Gram and compact-support cyclic descent. Sole live
  edge narrowed to joint cutoff-dependent prime--Burnol completion and a uniform lower floor.
- **2026-07-22 gain hostile test.** Corpus already contained Gamma coherent covariance and exact
  valuation Schur translation, so another square was rejected as rediscovery. Exact causal
  formulas instead prove response/sharp-source gain `<=C_h/(p+1)` and no uniform inverse. This is a
  source theorem, not RH restatement. Live edge is now forced unbounded graph closability plus
  completed finite-part lower floor.
