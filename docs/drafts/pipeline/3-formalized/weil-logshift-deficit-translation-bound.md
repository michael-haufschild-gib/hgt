# Deficit translation bounds from logarithmic shift tests

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web searches or external papers.

## Statement

Write `a = WeilExcess.weilDeviation lam`, `e = deviationExcess lam`,
`v = deviationDeficit lam`, `K = riemannAutocorr`, and
`psi = deviationPotential lam`. Assume only
`WeilLogShiftAsymptoticPositive lam` and `Summable e`.

Then:

1. A nonnegative constant bounds `sum (n in F), v n` for every natural `j`
   and every finite set `F` contained in `floor(log n) = j`.
2. A nonnegative constant bounds `kernelPotential v y` for every real `y`.
3. A nonnegative `D` satisfies `CauchyBounded v D`.

The original `WeilLogShiftTestsPositive lam` predicate and summability of
`max (lam n - vonMangoldt n) 0 / sqrt n` imply the same Cauchy bound.

## Dependency-closed paper proof

The previous one-sided excess-control result gives `|a(n)| <= 100 E`,
where `E = sum e`, convergence of the deficit potential at every real
shift, and the sampled bound

`kernelPotential v (log m) <= S := 2 K(0) E - psi(0)` for every `m >= 2`.

The nonnegative potential at `log 2` shows `S >= 0`. Also `v(0)=0`,
`v >= 0`, and `|v(n)| <= 2 log n + 100 E`, so the existing finite-sum
potential comparison applies.

For each natural `j`, choose `m = floor(exp j) + 1`. Then `m >= 2` and
`j <= log m <= j+1`: use `exp j >= 1`, `exp 1 >= 2`, and
`m <= exp j + 1 <= 2 exp j <= exp(j+1)`.
If `floor(log n)=j`, then `j <= log n < j+1`, hence
`|log m - log n| <= 1`.

The corpus supplies `kappa > 0` with `K(z) >= kappa` on `[-1,1]`.
For every finite subset `F` of this logarithmic block, positivity of the
other kernel terms gives

`kappa * sum (n in F), v(n) <= kernelPotential v (log m) <= S`.

Thus every block has mass at most `S/kappa`. The existing theorem
`WeilAbscissa.nullPotential_le_of_block`, together with
`K(y) <= C exp(-2 |y|)`, bounds the potential at every real shift by
`6 C exp(2) S/kappa`.

Finally, integrate this uniform potential bound against each nonnegative
Cauchy profile. The corpus's `tsum_mul_kernelSmooth_le` controls the
smoothed weighted series. Its `cauchyProfile_le_kernelSmooth` bounds
each original profile by `3/(2 kappa)` times its smoothing; the Cauchy
profile integral is `pi`. Nonnegative domination proves both summability
and the uniform bound required by `CauchyBounded`.

## Corpus audit and exact new insight

Used only these existing Lean mechanisms:

- `WeilLogShiftExcessControl`: coefficient and sampled potential bounds
  from asymptotic log-shift positivity plus summable excess.
- `WeilNullPotentialSignPartRigidity`: finite local mass comparison and
  global potential control from logarithmic blocks.
- `WeilDeviationTranslationBound`: positive smoothing and Cauchy profiles.

The local lexical query `logShift CauchyBounded` found no indexed match.
The broad local search exposed the existing full-Weil-positive receiver.
This establishes the exact dependency reduction above; it is not an
external literature novelty claim or a claim of exhaustive semantic search.

The new bridge is the integer-log probe inside every unit logarithmic
block. It removes full Weil positivity from the deficit translation bound
when excess is summable. It does not prove summable deficit, positive
definiteness of the signed potential, mixed-sign rigidity, or RH.

## Lean artifact and validation

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftDeficitTranslation.lean`.
Public declarations:

- `exists_deficit_logBlock_bound_of_logShiftAsymptoticPositive`
- `exists_deficit_kernelPotential_bound_of_logShiftAsymptoticPositive`
- `exists_deficit_cauchyBounded_of_logShiftAsymptoticPositive`
- `exists_deficit_cauchyBounded_of_logShiftTests`

Final leaf compile passed with default heartbeats and no diagnostics.
Scratch signature and axiom audit passed for all four declarations;
each uses exactly `[propext, Classical.choice, Quot.sound]`.
Module wired in `RHTower.lean`; index refresh passed and all four API rows
were verified. Scoped whitespace checks passed.

The authoritative lint run exited 1 with 13 unrelated unreachable modules:
RHTower's `CanonicalProductE1RealLineBounds`, `PaperCircleFrequencyGeometry`,
`SincSeparatorContour`, `SincSeparatorMellin`, `StretchedBoseDefect`,
`StretchedBoseSeparator`; HTGeometry's `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
`BoundaryCoronaCStarAlgebra`, `ComplexRateGammaIntegral`, and
`PaperFourierThermalMetric`. No lint error concerns this leaf.

## Next frontier

Investigate whether the new Cauchy control upgrades fixed-shift convergence
to a uniform whole-panel approximation under summable excess alone.
Mixed-sign summable-excess rigidity remains open.
