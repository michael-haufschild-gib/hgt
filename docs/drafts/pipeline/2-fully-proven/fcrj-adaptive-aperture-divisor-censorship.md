# FCRJ adaptive-aperture divisor censorship

- **ID:** `fcrj-adaptive-aperture-divisor-censorship`
- **Stage:** `2-fully-proven`
- **Route:** `CCM-FU / FCRJ`
- **Type:** `THEOREM (paper) [LEAN-PROVED] [NO-GO] [POSITIVE SURVIVOR]`
- **Date:** 2026-08-27
- **Source:** conjecture loops 58--66 in
  `docs/drafts/pipeline/1-in-progress/critical-multiplicative-compensated-cancellation-rh.md`

## Question

Loop 66 proves shrinking physical aperture width suppresses full carrier energy. Can an adaptive
schedule `c_n -> 0` retain coefficient-faithful detection of each fixed divisor mode even though
normalized carrier energy collapses?

## Answer

For the exact physical log-window multiplier

```text
M_c(z) = exp(cz) - 1,
```

the global Taylor estimate is

```text
||M_c(z)|| <= |c| ||z|| exp(|c| ||z||).                 (DC1)
```

Hence every schedule `c_n -> 0` satisfies `M_{c_n}(z) -> 0` for each fixed mode. This collapse is
sharp along positive widths:

```text
M_c(z)/c -> z,
||M_c(z)||/c -> ||z||.                                 (DC2)
```

For every nonzero `z`, sufficiently small positive `c` therefore obeys the explicit two-sided law

```text
(||z||/2)c <= ||M_c(z)|| <= 2||z||c.                   (DC3)
```

On the divisor half-plane `Re z<0`, the corpus fixed-width theorem still gives

```text
c>0  ==>  M_c(z) != 0.                                 (DC4)
```

Thus a positive shrinking schedule has a nonzero multiplier at every finite stage but response
tending to zero, and no positive uniform norm floor can survive.

## Verdict

`[PROVED — SHRINKING APERTURES ARE POINTWISE NONCENSORING BUT UNIFORMLY DIVISOR-CENSORING;
ATTENUATION IS EXACTLY FIRST ORDER IN WIDTH]`.

This closes a false escape from loop 66. Shrinking `c` can meet full-carrier energy budgets only
while destroying uniform observability of every fixed divisor mode. The positive survivor is exact
jet law `(DC2)--(DC3)`: renormalization by `1/c` restores mode `z`, revealing an unavoidable
first-order inverse-conditioning cost. Fixed positive width remains source-faithful and therefore
retains the genuine RH-strength centered prime-log discrepancy burden.

## Novelty audit

Complex exponential Taylor expansion and differentiation are classical and are not claimed new.
Prime short-interval explicit-formula and variance literature is adjacent; primary references
include [Montgomery--Soundararajan](https://arxiv.org/abs/math/0409258) and
[Gafni--Tao](https://arxiv.org/abs/2505.24017).

Mandatory corpus searches and targeted current-literature searches found no statement combining
the exact FCRJ physical moving-window multiplier, open-left-half-plane finite-width
noncensorship, adaptive-width vanishing, exact normalized jet, and full-carrier source-retention
wall. Candidate-new content is restricted to this coefficient-faithful provider obstruction and
its formal connection to FCRJ. No broad priority claim is made without expert review.

## Lean

Module:

```text
GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureAdaptiveDivisorCensorship
```

Capstones:

- `norm_xiPhysicalLogWindowModeMultiplier_le`
- `tendsto_xiPhysicalLogWindowModeMultiplier_zero_of_width`
- `tendsto_xiPhysicalLogWindowModeMultiplier_div_width`
- `tendsto_xiPhysicalLogWindowModeMultiplier_div_width_of_width`
- `tendsto_norm_xiPhysicalLogWindowModeMultiplier_div_width`
- `eventually_norm_xiPhysicalLogWindowModeMultiplier_two_sided`
- `xiPhysicalLogWindowModeMultiplier_adaptive_censorship`
- `not_exists_uniform_positive_norm_xiPhysicalLogWindowModeMultiplier_of_width`

Audit:

- direct `lake env lean` check: pass;
- targeted `lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureAdaptiveDivisorCensorship`:
  pass;
- capstone `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- theorem-area umbrella: wired;
- global lint: both loop 67 modules are reachable and clean; repository gate remains blocked by
  unrelated concurrently owned unwired `RHTower.Sieve`, theta-cusp, and `HTGeometry` modules.

## Remaining burden

Do not use adaptive shrinking as a source-preserving FCRJ regularizer. Work at fixed physical
ratio, or exhibit an independently justified `1/c` renormalization whose amplified arithmetic and
ultraviolet errors remain within the RH endpoint budget. The next live problem is a fixed-width
off-diagonal centered prime-log energy estimate; `(DC2)` shows width decay cannot supply it for
free.
