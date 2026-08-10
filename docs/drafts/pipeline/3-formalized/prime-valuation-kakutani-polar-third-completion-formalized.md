# Prime-valuation Kakutani polar third completion — formalized closure

- **ID:** `prime-valuation-kakutani-polar-third-completion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./prime-valuation-kakutani-polar-third-completion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.DivergentSeriesThinning` — the thinning engine.
- `GaloisForLFunctions.HTGeometry.PrimeValuationKakutaniSector` — the twisted sectors, the
  radial dichotomy, and the Hellinger identities.

Pre-existing and reused:

- `HTGeometry.PrimeValuationSector` — the critical sector `μ₀` as a Kolmogorov product of the
  geometric laws `(1 - p⁻¹) p^{-k}`, its cylinder masses `∏_{p∈P}(1 - p⁻¹)`, and conditional
  cylinder estimates;
- `HTGeometry.ProductOccupancyDichotomy` — the two Borel–Cantelli directions for an arbitrary
  family of local hitting targets in a Kolmogorov product;
- `HTGeometry.PrimeValuationInfiniteSupport` — divergence of the critical occupancy masses;
- `RHTower.PrimeValuationKakutaniRadialPurity` — the scalar selector `(13a)`, `(13b)`.

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. **The twisted local laws** `(8)`.  `primeTwistRatio c p = p^{-(1-2c)}`,
   `primeTwistedParam`, `primeTwistedLaw` (geometric with that ratio) and the product sector
   `primeTwistedMeasure hc` are defined for every `c < 1/2`; `primeTwistedLaw_compl_zero` computes
   the local occupancy mass as exactly the ratio.
2. **The critical ray is the untwisted sector.**  `primeTwistedMeasure_zero` — at `c = 0` the
   twisted sector *is* `primeValuationMeasure`.
3. **Thinning a divergent series below a fractional power** — `exists_thin_subset`: a positive
   family with divergent sum and vanishing terms has a subfamily whose sum converges while the sum
   of its `s`-th powers diverges, for every `0 < s < 1`.  The construction is the greedy two-scale
   block: block `j` collects mass about `2^{-j}` out of terms already smaller than
   `(2^{-j})^{1/(1-s)}`, so it contributes at least one unit of `s`-power mass
   (`thinBlock_sum_le`, `thinBlock_rpow_sum_ge`, `thinBlock_disjoint`).
4. **The separating prime set** — `exists_thin_primeSet`: for `0 < c < 1/2` there is a set of
   primes whose reciprocals are summable while their `(1-2c)`-th powers are not.  This is the
   thinning lemma applied to `p ↦ 1/p` along an enumeration of the primes.
5. **Kakutani radial purity** `(10)`.
   - `mutuallySingular_primeTwistedMeasure_of_neg` — for `c < 0` the twisted occupancy masses
     `p^{-(1-2c)}` are summable while the critical masses `p⁻¹` are not, so infinite occupancy is
     null for one sector and full for the other.
   - `mutuallySingular_primeTwistedMeasure_of_pos` — for `0 < c < 1/2` both families diverge and
     the same argument is run on the thinned prime set (`thinTarget`).
   - `mutuallySingular_primeTwistedMeasure` — every `c ≠ 0` gives mutual singularity.
   - `primeTwistedMeasure_absolutelyContinuous_iff` and
     `primeTwistedMeasure_equivalent_iff` — the boxed statement `(10)`: the twisted sector lies in
     the measure class of the critical sector exactly when `c = 0`.
6. **The Hellinger computations** `(11)`–`(13)`.  `hasSum_geometricHellinger` — the affinity of two
   geometric laws is `√((1-a)(1-b))/(1-√(ab))`; `one_sub_geometricHellingerAffinity` — the exact
   rationalized defect `(√a-√b)²/((1-√(ab))((1-√(ab))+√((1-a)(1-b))))`;
   `geometricHellinger_defect_ge` — the bound `1 - H ≥ (√a-√b)²/2`.

## Proof-route note

The paper proof deduces `(10)` from Kakutani's product-measure theorem applied to the affinity
`(11)`.  Mathlib has no Kakutani dichotomy, and the Lean proof here reaches the same statement by a
tail-event route that needs no likelihood-ratio martingale: the separating events are occupancy
events, read on all primes when the twist is negative and on a thinned prime set when it is
positive.  The card's own Hellinger identities `(11)`–`(13)` are formalized alongside, so every
scalar computation of §4 is covered as well.

## Verification

- `lake env lean` clean, with no warnings, on both new modules.
- `lake build GaloisForLFunctions.HTGeometry` — green (17699 jobs) with both modules wired into the
  umbrella.
- `#print axioms` on the eleven capstones: `propext`, `Classical.choice`, `Quot.sound` only.  No
  hypothesis interface, no added axiom; the twist bound `c < 1/2` is the condition under which the
  local law `(8)` is a probability law at all.

## Scope boundary

This closes the card's Lean gate.  It does not touch the three research gates: the independent
specialist novelty audit, the conjectured Xi conormal critical-sector normality of §6, and RH.  As
the card's own terminal audit records, the sector and its Kakutani wall do not by themselves
transport analytic zeros; the descent was proved RH-equivalent in the retired prime-aperture route.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
