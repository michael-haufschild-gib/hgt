# Exact overlap, length, and height coordinates

- **ID:** overlap-length-height-coordinates
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3.
- **Statement:** For positive length `X` and overlap `c`, height is `T=X/c`;
  bandwidth is `log X/log T`, and every fixed positive overlap has limiting bandwidth one.

For `T>1`, the exact bandwidth identity is
`log X/log T = 1 + log(X/T)/log T`. Thus bandwidth at most one is equivalent
to overlap at most one. Length `T^α` instead has overlap `T^(α-1)`.
The renormalized height logarithm satisfies `log(X/c)-log X=-log c`.
At fixed `c`, `log c/log X→0`, and the formula
`bandwidth(X,X/c)=1/(1-log c/log X)` gives the limiting bandwidth.

The nominal aperture `log X/2` has prime cutoff `X`. The actual support enclosure
also includes the profile width, as formalized in `TheAtomicApertureRetainsTheProfileWidth`.
These are coordinate identities, without a positivity or common-threshold claim.

Lean: `GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean`.
Main declarations: `LengthHeight.bandwidth_eq_one_add_log_overlap`, `overlap_rpow`,
`log_height_sub_log_length`, and `tendsto_bandwidth_fixed_overlap`.
Kernel checked; final direct audit including the three transitive axiom prints is pending.
Imported by the SpacingScaleHarmonicAnalysis umbrella.
