# Log-square prime observation windows decide RH

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B130 scale locality; strengthening the square-root-window criterion.

## Theorem

There is a fixed `C>0` such that a uniform lower bound for the zeta spline
trace on all primes in arbitrarily late windows

`|log p-T|≤C (log(T+2))²`

is equivalent to RH. Centers may be arbitrarily sparse. No attained-top premise.
Equivalently, failure of RH forces prime traces below every fixed `-K` in
every sufficiently late such window.

## Proof

The positive deletion multiplier has the sharper one-factor estimate

`Q_(a,h)(s)≤exp(min(s²h²/2, |sh|))`.

For `h=π/γ`, split factors at `|γ|=H`. Their logarithmic moment cost is at
most

`|s| Σ_(|γ|≤H) |h| + (s²/2) Σ_(|γ|>H) h²`.

Existing zeta bounds give head cost `O((log H)²)` and tail square cost
`O(log H/H)`. With `H=T` and Chernoff parameter `q=T`, the total moment
cost is `O(T(log T)²)`. A sufficiently large fixed log-square radius
dominates this cost and the trace envelope `exp(DT)`.

If a zero lies deeper than `α≥0`, a sufficiently late deletion tail preserves
that exponent and kills all but finitely many spline modes. The surviving
conjugate-symmetric finite sum has negative excursions of size
`η exp(βt)`, with `β>α`, at bounded gaps. Apply the positive average to
the normalized trace `exp(-αt)f(t)`. The local floor loses only `O(exp(-T))`,
contradicting the surviving growing negative excursion.

Prime gaps of size `x^(2/3)` transfer a constant prime floor to an interior
continuous floor of size `-M exp(αu)` whenever the configuration width is
at most `a` and `a-1/3≤α`. Applying continuous detection twice reduces
width `1/2→1/6→0`. RH supplies the converse through the global prime floor.
Negating the forward implication gives the every-late-window negative witness.

## Explicit constants

Put `A=xiLineTwoLogDerivConstant`, `E=log(T+2)`, and
`C₀=80π(A+2)+32π²`. The corpus head and tail estimates give

`head(T)≤40π(A+2)E²`, `tailSquare(T)≤16π²E/T`.

For `D≥0`, `T≥max(3,exp(12),D)`, `E≥1`, and `s=D+T≤2T`, the mixed moment is at most
`C₀TE²`. Set `r₀=2(C₀+1)` and local radius `r₀E²/2`.
If `E²≥D+1` and `|t|≤T+B`, then

`D|t|-T(r₀E²/2)+C₀TE²≤DB-T`.

Thus radius `r₀E²` suffices continuously, uniformly in the chosen
depth exponent. Prime windows of radius `2r₀E²` leave this radius after
the prime-gap transfer. These inequalities pass Lean in
`LogSquareWindowLeakage.lean`, with only the standard three axioms.

## Corpus inputs

- `RHTower.sum_xiCopiesBelow_inv_abs_le` in `VonKochChebyshevBound.lean`.
- `SquareRootThreshold.sum_inv_norm_sq_le` in
  `EffectiveHorizons/TheEGCContourIsExplicit.lean`.
- `RHTower.summable_inv_sq_xiCopyOrdinate` and its ordinate/norm comparison.
- `ScaleLocality` positive deletion, infinite trace passage, and finite-spectrum oscillation.

## Lean audit

All modules lie in `SurfaceOfSpecZ/ScaleLocality/` and are wired into its umbrella.

- `MixedPositiveMoments.infinite_tail_translated_mixed_floor`: infinite positive
  averaging with a uniform mixed moment bound.
- `ZetaMixedMomentBounds.zeta_mixedMomentCost_le`: actual zeta tail prefixes.
- `LogSquareWindowLeakage.infinite_zeta_logSquare_floor`: exponential leakage.
- `ZetaTailDeletion.exists_zeta_deletion_tail`: cofinite isolation preserving a chosen mode.
- `ZetaLogSquareWindows.zeta_re_le_of_logSquare_windows`: continuous depth detection.
- `PrimeWindowTransfer.prime_windows_transfer`: prime transfer for growing radii.
- `PrimeLogSquareWindows.riemannHypothesis_iff_prime_logSquare_windows` and
  `eventually_prime_logSquare_window_negative`: final equivalence and local witnesses.

These are filenames followed by declaration names; every declaration is in namespace
`GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`. Final direct audit:
`lake --old env lean GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogSquareWindows.lean`.
All four capstone axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

## Limits

The arithmetic lower bound itself and arbitrarily slowly growing windows remain
open. This theorem is for actual zeta; the generic tempered-configuration theorem
proved here uses square-root windows. No external novelty claim.
