# Quantitative rapidity and cutoff bound for the Möbius fold

- **ID:** CHMD-FOLD-TAIL-1810
- **Stage:** 3-formalized
- **Parent:** [all-scale folded Möbius control](../1-in-progress/chmd-all-scale-folded-mobius-control-2026-10-18.md)
- **Source:** `formal/GaloisForLFunctions/RHTower/CHMDLightConeFoldTailBound.lean`

## Exact results

Put `P(y)=(1+|y|)(1+y²) exp(π|y|)`. Independently of `y`, spatial shift, and cutoff, there are nonnegative constants such that

`|conjugatedLaplacian y s| ≤ C P(y) exp(-(π-1/2)s)` for `s≥0`,

`|mobiusFold y v| ≤ C P(y) exp(-(π-1/2)v)` for `v≥0`,

`Σ' j |mobiusFold y (log(j+N+1))| ≤ C P(y) N^(-(π-3/2))` for `N≥1`.

The constants in these three statements need not be equal. The leaf also proves `|lightConeBesselReal w|≤1` for `w≥0` and nonnegativity of `P`.

## Paper proof and corpus reuse

The existing integral Bessel function `besselJ0` agrees with `HTGeometry.besselJ 0` by their integral representations. Uniqueness of derivatives identifies their order-one functions. Reuse `BesselJOneRecurrence.abs_besselJ1_le` and `besselJ_one_eq` to bound the normalized light-cone kernel by one, including its value at zero.

For a spatial kernel bounded by `C(1+|s|) exp(-π|s|)`, existing `shift_decay_le` bounds either light-cone shift by `C(1+|y|) exp(π|y|) exp(-(π-1)|s|)`. The interval has length two, so the pair-minus-Bessel-tail costs at most `2C P(y) exp(-(π-1)|s|)`. Apply this single estimate to the existing d'Alembert kernel and its first two spatial derivatives. Conjugation gives the first result.

The actual dilation-source bound is `sourceBound exp(u)`. Integrating its product with the conjugated-Laplacian majorant gives the second result. Summability and the existing exact `Sieve.tsum_tail_rpow_neg_le` give the third. No Möbius cancellation, zero-location premise, or new axiom enters these estimates.

The local research audit recovered the existing growth law, plateau taper, Bessel bounds, and exact power-series tail bound. The first twelve retrievals and their coverage are recorded in `logs/chmd-lightcone-tail-1810d-search-manifest.json`; one deep query was partial. Retrieved ingredient sets were not accepted as proofs. External novelty is not established.

## Verification

- Direct source audit passed: `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CHMDLightConeFoldTailBound.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/CHMDLightConeFoldTailBound.ilean GaloisForLFunctions/RHTower/CHMDLightConeFoldTailBound.lean`.
- A separate `/tmp` import audit passed. All five public theorem closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella import occurs once. `scripts/formal_tools.py index` passed; exact lexical search finds the absolute-tail theorem.
- `scripts/formal_tools.py lint` returned 1 for unrelated missing BVI imports `BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge` and `BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge`, and root-level `TransHorizonIncidenceMechanics.lean`. No finding names this leaf. No global lint pass is claimed.
- Source check, axiom output, index output, lint output, and source hash are retained under `logs/chmd-lightcone-tail-1810d-*`.

## Remaining arithmetic gap

The bound has an explicit rapidity cost; it is not uniform boundedness of the complete folded wave. On paper, `N=ceil(2 exp(3y))` makes the tail bounded, and the already defined plateau taper would transfer subpower finite-row growth to the existing CHMD growth receiver. That finite-row estimate remains unproved. This leaf completes an analytic ingredient; the parent all-scale research task remains open.
