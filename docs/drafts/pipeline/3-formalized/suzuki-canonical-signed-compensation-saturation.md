# Suzuki canonical signed-compensation saturation

- **ID:** SWA-RELATIVE-COMPENSATION-SATURATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Statement:** The coefficient-faithful atomic-before-continuous signed correction absorbs asymptotically all positive Suzuki transition-core energy, and on apertures `8n` eventually supplies the exact linear mass forced by transition-core Ward semiboundedness.

## Goal

Close the scaling-admission premise left by the transition-core linear-compensation no-go.  Write

`A_N = unitRieszCoherentPrimeOutgoingCharge N`,

`G_N = suzukiNaturalApertureCompletedLowerHardyAmplitude N`,

`C_N = suzukiNaturalApertureTransitionCoreCauchyEnergy N`, and

`E_N = suzukiTransitionCoreAlignedGammaCompletedEnergy N`.

Define the canonical signed correction `K_N = C_N - E_N`.  Prove unconditionally

1. `G_N / A_N -> 0`;
2. `K_N / C_N -> 1`;
3. eventually `n / 576 <= K_(8n)`.

Exact RH chain:

`K_N` has the mandatory signed linear admission scale → the corrected core is exactly `E_N` →
boundedness of `E_N` is equivalent to RH → the shared completed Suzuki source feeds the
HB/FZZ-P/RBH/PW-B endpoints.

This does not claim boundedness of `E_N`.  It removes the prior ambiguity over whether the actual
coefficient-faithful signed source has enough mass to survive the linear-compensation obstruction.

## Gates

- [x] 0 → 1 in-progress: source-pure, exact source chain and attack fixed
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external review

## Corpus basis and novelty audit

Internal search found these exact inputs but no relative-compensation theorem:

- the de la Vallée Poussin limit
  `exp(-h/2) * criticalMellinNormalizedChebyshevError h -> 0`;
- the unit-rate causal resolvent definition of
  `criticalMellinChebyshevResolventSource`;
- `unitRieszCoherentCompletedOutgoingCharge = resolvent / 2` and
  `unitRieszCoherentPolarOutgoingCharge N = sqrt N / 3`;
- bounded polar and archimedean Suzuki corrections;
- `A_N^2 <= C_N` and eventual `C_N <= kappa A_N^2`;
- the exact identity `E_N = C_N (G_N/A_N)^2` when `A_N != 0`;
- eventual `n/288 <= C_(8n)`;
- `E_N` eventually bounded iff RH.

Primary-source audit through 2026-08-31 covered Suzuki's 2022 prime/Lerch screw paper and the
2024--2026 M-function/screw-function paper.  They contain the PNT-scale inputs, but neither the
transition core nor its canonical signed correction, saturation law, exact `8n` admission, or the
four-route descent.  Novelty claimed here is the transition-core classification and premise
discharge, not the classical PNT remainder estimate.

Hostile checks:

- No RH input occurs: the error limit is the unconditional PNT/de la Vallée Poussin theorem.
- No positivity is assigned to the completed amplitude; it is squared only after atomic-continuous
  subtraction.
- Division occurs only eventually, after `A_N != 0` and `C_N >= A_N^2 > 0`.
- Saturation is relative, not boundedness: `E_N/C_N -> 0` does not imply `E_N = O(1)`.
- The exact `1/576` threshold comes from `K_(8n) >= C_(8n)/2` and the corpus lower bound
  `C_(8n) >= n/288`; no optimized constant is the research content.

## Paper proof

### Lemma 1: normalized causal resolvent is negligible at polar scale

Let `e(h)` be the normalized Chebyshev error and `q(h) = exp(-h/2)e(h)`.  Corpus PNT gives
`q(h) -> 0` as `h -> +infinity`.  Also `q` is globally bounded: beyond one threshold this follows
from convergence; on `0 <= h <= H` it follows from the corpus bound
`|e(h)| <= (2h+1)exp(h/2)`; for `h <= 0`, `psi(exp h)=0`, hence `q(h)=-1`.

For the unit causal resolvent `R(h) = integral_(t>0) exp(-t)e(h-t) dt`,

`exp(-h/2) R(h) = integral_(t>0) exp(-3t/2) q(h-t) dt`.

For every fixed `t`, `q(h-t) -> 0`.  The integrand is dominated by
`M exp(-3t/2)`, which is integrable on `(0,infinity)`.  Dominated convergence therefore gives
`exp(-h/2)R(h) -> 0`.

### Lemma 2: atomic and completed amplitudes separate by scale

At `h = log N`, corpus identities give

`unitRieszCoherentCompletedOutgoingCharge N = R(log N)/2`

and

`A_N = sqrt N / 3 + unitRieszCoherentCompletedOutgoingCharge N`.

Since `sqrt N = exp(log N/2)`, Lemma 1 gives
`A_N/sqrt N -> 1/3`.  The completed outgoing charge differs from Suzuki Green by the polar and
archimedean corrections, both uniformly bounded.  Division by `sqrt N -> infinity` therefore
gives `G_N/sqrt N -> 0`.  Quotient continuity at the nonzero denominator `1/3` yields
`G_N/A_N -> 0`.

### Lemma 3: canonical correction saturates the transition core

Eventually `A_N != 0`.  The exact aligned-energy identity gives

`E_N/C_N = (G_N/A_N)^2`,

because `C_N >= A_N^2 > 0`.  Lemma 2 implies `E_N/C_N -> 0`.  Therefore

`K_N/C_N = 1 - E_N/C_N -> 1`.

### Capstone: exact linear admission

Eventually `K_N/C_N >= 1/2`.  Applying this along the cofinal map `n |-> 8n` and combining it with
the unconditional lower bound `C_(8n) >= n/288` gives

`K_(8n) >= C_(8n)/2 >= n/576`.

Thus the actual coefficient-faithful signed correction meets the exact scale forced on every
semibounded transition-core Ward producer.  `[PROVED HERE]`

## Remaining open core

The sole surviving source burden is now a strict scale upgrade:

`E_N = o(C_N)` (proved here) → `E_N = O(1)` (equivalent to RH).

Future conjectures on this branch must act on the aligned residual `E_N`; further changes to the
linear correction scale cannot close RH.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.SuzukiCanonicalSignedCompensationSaturation`

Principal closed theorems:

- `tendsto_exp_neg_half_mul_criticalMellinChebyshevResolventSource_atTop_zero`;
- `tendsto_suzukiCompletedAmplitude_div_primeOutgoingCharge_atTop_zero`;
- `tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero`;
- `tendsto_suzukiTransitionCoreCanonicalSignedCorrection_div_core_atTop_one`;
- `eventually_linear_le_suzukiTransitionCoreCanonicalSignedCorrection_eight_mul`;
- `suzukiTransitionCore_sub_canonicalSignedCorrection_eq_alignedEnergy`;
- `riemannHypothesis_iff_suzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded`.

Audit:

- direct check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiCanonicalSignedCompensationSaturation.lean`;
- targeted final build:
  `lake build GaloisForLFunctions.RHTower.SuzukiCanonicalSignedCompensationSaturation`,
  `13732/13732` jobs completed;
- the five audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- module imported by `GaloisForLFunctions.RHTower`;
- repository lint sees this module as reachable and reports no forbidden declaration in it.  Global
  lint remains red solely because shared-tree modules
  `HedenmalmCriticalFeatureFirstOrderWindingReduction` and
  `HedenmalmCriticalFeaturePoleGammaVerticalFTC` are presently unwired; neither file belongs to this
  result.

## Log

- 2026-08-31 — corpus and literature audit; conjecture frozen; hostile checks passed; complete paper proof recorded.
- 2026-08-31 — Lean formalization, targeted build, axiom audit, and umbrella wiring completed.
