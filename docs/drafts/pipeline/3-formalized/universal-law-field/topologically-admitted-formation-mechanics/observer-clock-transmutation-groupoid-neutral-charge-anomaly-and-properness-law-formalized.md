# Observer-clock transmutation groupoid, neutral-charge anomaly, and properness — Lean formalization

- **ID:** ULF-TAFM-19
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CLOCK GROUPOID / GLOBAL PROPERNESS CLASSIFICATION
- **Paper source:** `observer-clock-transmutation-groupoid-neutral-charge-anomaly-and-properness-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.FormationClockTransmutation`;
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiHarmonicRieszClockTransmutation`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified generic mechanism

The generic module proves:

1. Target-clock charge is reference-clock charge times relative edge rate.
2. Relative rates compose multiplicatively across three nondegenerate clocks.
3. Every finite target response is reconstructed by transmutation of one reference charge.
4. Transmuted response is exactly boundary storage plus prefix/clock-acceleration work.
5. Neutral unit dipoles have total charge zero and fixed `l1` mass two.
6. Relative rate is uniformly bounded iff all neutral unit-dipole responses are uniformly bounded.
7. Every unbounded rate produces arbitrarily large response from neutral fixed-mass charges.

The last two results are a sharp global properness classification: noncompactness is created by
observer-clock acceleration, not by failure of source recovery.

## Certified literal landing

The Suzuki module constructs literal harmonic and square-root clocks and proves:

1. Harmonic edge is `1/(k+1)-1/(k+2)`.
2. Square-root edge is `sqrt(k+2)-sqrt(k+1)`.
3. Generic harmonic charge is the existing completed prime--polar--Gamma harmonic charge.
4. Generic square-root response is the literal completed Möbius--divisor Riesz moment.
5. Harmonic formation charge is summable with total charge exactly zero.
6. Generic relative rate is the existing `completedRieszHarmonicClockRatio`.
7. This ratio dominates `k+1` for every `k>=3`, hence is not uniformly bounded.
8. Neutral harmonic charges of `l1` mass two have arbitrarily large Riesz-clock response.

## Verification

- Batched scratch elaboration passed.
- Direct foreground elaboration passed for both final modules.
- Imports in generic module were reduced from broad `Mathlib` to six narrow modules; its cached
  leaf build dropped from `8655` to `938` jobs.
- Targeted leaf builds only:
  - `GaloisForLFunctions.HTGeometry.FormationClockTransmutation`: `938/938`
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiHarmonicRieszClockTransmutation`: `12876/12876`
    (large inherited dependency replay after cache changes)
- Both modules imported by `HTGeometry.UniversalLawField`; literal module also imported by
  `RHTower`; neither umbrella built.
- Twenty audited declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

This proves universal harmonic-to-Riesz operator boundedness is false. RH must instead be
exceptional-domain regularity of the one arithmetic source under an unbounded clock transmutation.
Remaining producer must control signed boundary storage and acceleration work jointly; separate
absolute estimates erase harmonic zero-charge conservation.
