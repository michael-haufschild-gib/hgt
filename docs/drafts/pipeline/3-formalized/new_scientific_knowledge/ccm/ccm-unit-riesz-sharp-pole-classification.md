# Sharp unit-Riesz CCM-HG pole classification

- **ID:** `ccm-unit-riesz-sharp-pole-classification`
- **Stage:** 3-formalized
- **Type:** SHARP CROSS-ROUTE RH EQUIVALENCE / QUANTITATIVE SUZUKI--CCM CLASSIFICATION
- **Scientific status:** `[LEAN FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `ccm-unit-riesz-suzuki-green-producer-classification`
- **Lean:** `GaloisForLFunctions/RHTower/CCM/CCMUnitRieszSharpPoleClassification.lean`

## Theorem

Let

```text
q_N = unitRieszCoherentCompletedOutgoingCharge N = R_1(log N)/2,
ell_N(u)=q_N exp(-u/2).
```

Corpus now proves unconditionally in Lean

```text
RH -> for every N>=2, |q_N|<2,

RH iff for every N>=2 and u>0,
  boundaryRelativeTrace(ell_N,u)
    <= boundaryRelativeTrace(polePacketProfile,u).
```

Since traces equal respectively `q_N^2(1-exp(-u))` and `4(1-exp(-u))`, sharp CCM-HG pole
domination is exactly RH, not an auxiliary estimate.

## Quantitative chain

Under RH, multiplicity-exact reciprocal-square weights satisfy

```text
sum_q xiCriticalScrewWeight(q) = normalizedPrimeArchMoment 0 < 29/625.
```

Therefore full Suzuki relation hull is `<58/625`, and `|Psi(h)|<58/625` for every real `h`.
At forced Green base `b=1/2`, first prime mass vanishes. Exact corrected first-gap derivative,
first Lerch atom, and symbolic bounds for `exp`, `log`, `arctan`, Euler constant, and `pi` give

```text
|ccmGuinandWeilXiScrewRightSlope(1/2)| < 1.
```

For reporter `F_H(h)=exp((h-H)/2)-exp(h-H)`, Lean proves universal sharp caps

```text
|F_H(h)| <= 1/4,
|F'_H(h)| <= 1/2                 (h<=H).
```

Together with second-derivative mass `<=3/2`, exact Suzuki Green contribution is

```text
|G_H| < 241/500.
```

Exact polar formula is bounded by a discriminant-negative exponential minorant plus three
analytic height regimes:

```text
|P_H| < 7/10 for H>=log 2.
```

Reporter cap and exact Gamma density integral give

```text
|A_H| < 7/10.
```

Thus

```text
|q_N| <= |G_H|+|P_H|+|A_H| < 241/500+7/10+7/10 < 2.
```

Existing exact profile law yields RH-to-pole-domination. Existing resolvent continuation gives
reverse implication.

## Novelty and theatre audit

This is not literature restatement or receiver repackaging. New content is quantitative fusion of:

- exact prime--Gamma zeroth moment with multiplicity-exact Suzuki relation hull;
- corrected first-gap derivative with first Lerch atom to beat base-slope constant one;
- forced unit-Riesz reporter extremum `1/4`;
- symbolic polar discriminant and global archimedean integral;
- literal CCM-HG pole constant four.

Result changes frontier: sharp scalar HG/O/GS/EP/FU/UR contractivity is proved to be precisely
RH-strength. Any non-circular advance must derive it upstream from independent source/ground or
operator-valued provenance. Sharpening scalar receiver constants cannot be intermediate progress.

## Formal audit status

- [x] scratch proof with `lake env lean`
- [x] dedicated module checks with `lake env lean`
- [x] wired into `GaloisForLFunctions/RHTower.lean`
- [x] exact leaf `lake build` final audit
- [x] `#print axioms` final theorem audit: only `propext`, `Classical.choice`, `Quot.sound`
- [ ] independent mathematical audit
- [ ] external priority audit

## Log

- 2026-08-16 -- Proved Xi screw hull `<58/625` under RH from exact prime--Gamma moment.
- 2026-08-16 -- Proved base right-slope absolute bound `<1` using first Lerch atom.
- 2026-08-16 -- Proved Green `<241/500`, polar `<7/10`, arch `<7/10`.
- 2026-08-16 -- Closed `RH iff uniform literal outgoing CCM-HG pole domination` in Lean.
