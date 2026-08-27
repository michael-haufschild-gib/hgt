# Reflected bi-heat theta finite-part global selectivity no-go

- **ID:** RBH-TFPGN
- **Stage:** 5-failed
- **Type:** FALSIFIED / THEOREM (Lean)
- **Parent:** RBH-TFPN
- **Frontier-map policy:** read only
- **Statement:** The canonical off-wall imaginary finite-part channel cannot be globally zero-free or one-signed on positive height; its nonzero odd almost-periodic phase has zeros above every threshold.

## Goal

Test the global continuation conjecture left by neutral-height transversality:
whether local off-wall orientation can propagate through every positive height.
Close the no-go with the strongest exact survivor and identify the remaining
RBH burden without weakening it to missing infrastructure.

## Gates

- [x] 0 → 1 in-progress: corpus-led conjecture, exact obstruction, proof plan
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean theorem package, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external expert novelty audit

## Corpus basis

- `ReflectedBiHeatThetaFinitePartNeutralHeightTransversality` gives the exact
  sine expansion and nonzero derivative at neutral height off wall.
- `BohrExponentialSeriesCoefficient` proves Bohr almost periodicity for any
  exponential series with absolutely summable amplitudes.
- `ExponentialDividedDifference.abs_exp_sub_exp_le_of_nonpos` gives the sharp
  exponent-direction estimate needed for amplitude summability.
- `WaveTraceOddPeriodicEscape.exists_neg_of_odd` isolates the odd-sign
  mechanism; here Bohr recurrence replaces exact periodicity.
- Mandatory corpus searches found no existing theorem connecting this
  canonical RBH phase to cofinal sign recurrence or cofinal positive zeros.

## Conjecture loop

1. **Conjecture G1:** local sign `sign(sigma-1/2)` persists for all positive
   heights. **Failed.** The channel is a nonzero odd Bohr almost-periodic
   function, so every nonzero value recurs cofinally while oddness supplies
   its opposite sign.
2. **Survivor G2:** both strict signs occur above every threshold, and
   continuity forces a zero above every threshold. **Proved in Lean.**

## Paper proof

For `r=(N+d)/N>1` and `0<sigma<1`, write each phase amplitude as

`h_x(d) N^-1 (r^(sigma-1)-r^(-sigma))`.

Both exponential arguments `(sigma-1) log r` and `-sigma log r` are
nonpositive.  The exponential divided-difference estimate therefore gives

`|r^(sigma-1)-r^(-sigma)|
  <= |(2 sigma-1) log r| <= log r <= d/N`.

Thus the absolute amplitude is bounded by `d h_x(d)/N^2`, hence by the already
summable slope majorant.  The phase is the imaginary part of the corresponding
absolutely convergent exponential carrier, so it is continuous and Bohr
almost periodic.  It is odd termwise.

Neutral-height transversality gives nonzero derivative off wall, so the phase
is not identically zero.  Choose one nonzero value; oddness produces values of
both signs.  Given any threshold, a sufficiently accurate relatively dense
almost period transports either chosen value beyond that threshold without
changing its strict sign.  Recur one sign first and the opposite sign after it.
Continuity and the intermediate value theorem then give a zero between them,
above the original threshold.

## No-go closure

- **Exact killing theorem/mechanism:** nonzero odd Bohr almost-periodic
  functions have cofinal occurrences of both strict signs, hence no global
  positive-height sign or nonvanishing law is possible for this channel.
- **Strongest positive survivor:** every off-wall canonical RBH imaginary
  finite-part channel has strict positive values, strict negative values, and
  exact zeros above every real threshold.
- **New insight:** canonical odd channel cannot globally select critical wall.
  Actual Xi-height exclusion must separate a discrete arithmetic height set
  from a cofinal recurrent zero set; analytic global sign propagation is
  structurally impossible.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Formal theorem package

- `abs_reflectedBiHeatFinitePartMixedPhaseAmplitude_le`
- `summable_abs_reflectedBiHeatFinitePartMixedPhaseAmplitude`
- `reflectedBiHeatFinitePartMixedPhaseCarrier_im`
- `isBohrAlmostPeriodic_reflectedBiHeatFinitePartMixedPhase`
- `continuous_reflectedBiHeatFinitePartMixedPhase`
- `reflectedBiHeatFinitePartMixedPhase_neg`
- `cofinal_both_signs_of_odd_isBohrAlmostPeriodic`
- `cofinal_zero_of_continuous_odd_isBohrAlmostPeriodic`
- `exists_ne_zero_reflectedBiHeatFinitePartMixedPhase`
- `cofinal_both_signs_reflectedBiHeatFinitePart_vertical_im`
- `cofinal_zero_reflectedBiHeatFinitePart_vertical_im`
- `not_global_nonvanishing_reflectedBiHeatFinitePart_vertical_im`

## Provisional literature audit

Current searches through August 2026 found classical and modern almost-periodic
zero-set theory, plus an especially close proof pattern in Diamond--Pintz,
*Oscillation of Mertens' product formula* (2009): a finite odd trigonometric
polynomial is almost periodic, so near-origin signs recur at arbitrarily large
arguments.  Thus the abstract odd-almost-periodic recurrence mechanism is not
claimed as new.  Favorov's work on zero sets of holomorphic almost-periodic
functions studies periodicity and zero-difference structure, not this channel.
Recent Gaussian-field double Dirichlet series work concerns subconvexity and
moments, not the canonical complementary-order additive-heat finite part.

No source found the RBH amplitude estimate, exact Bohr carrier identification,
or resulting cofinal-zero obstruction for this canonical theta-pole finite
part.  Novelty claim is specific to that synthesis and remains provisional
pending expert review.

## Audit

- Module:
  `GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartGlobalSelectivityNoGo`
- Direct `lake env lean` check passed.
- Targeted `lake build` passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.
- Banned-token and scoped diff checks passed.
- Umbrella import wired; full umbrella build intentionally not run.

## Log

- 2026-08-27 — G1 killed by corpus Bohr recurrence; G2 extracted and paper proof closed.
- 2026-08-27 — sharp amplitude summability, carrier almost periodicity,
  cofinal two-sign recurrence, cofinal zeros, and global nonvanishing no-go
  formalized and audited.
