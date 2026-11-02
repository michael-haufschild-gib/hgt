# Low-conductor spans through weighted residuals

- **ID:** low-conductor-spans-through-weighted-residuals
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Σ1d in `docs/reports/review-0111/walls-ledger.md`.
- **Statement:** For every nonzero real `C²` profile supported on `[0,1]` and every bounded overlap interval `1≤c≤K`, the complete Weil form is eventually uniformly coercive on `conductorSubspace ⌊N^θ⌋ N` for `0<θ<1/1080`. This would include every fixed polylogarithmic conductor span.

## Open core

Single-conductor coercivity does not control cross terms in a growing span.
The tilted-spline polylogarithmic theorem currently imposes `α+2q<1`;
collective mid-band coercivity excludes the low-conductor subspace.
The target is a whole-span estimate, then its maximal growing-overlap range
determined by the profile's completed conductor floor.

## Proof

Split at a fixed large conductor `Q`. For a unit packet above `V_Q`, write
`E=primeAdjunctionMass R a` and `G=Σ(1+log m)a_m²`. The lower frame gives
`G≤2+E`. The weighted center and merged overlap/downward bounds give squared
pairings at most `B(2+E)`, with `B` depending only on the profile and `K`,
provided `1080(1+log R)≤log N` and `(1+log R)R²log N/N≤1`.
Each pairing costs at most `E/32+8B+1/16`. Prime coercivity retains `E/8`
and `(log Q)/4`; separated and upward terms have bounded norm. Thus the
high block retains `(log Q)/4-C` uniformly.

Choose fixed `Q` making the high-block lower bound at least one. Normalize
the uniform profile floor to `0<e≤1`. On `V_Q`, put
`M=|completeWeilSelfFinitePart(φ,1)|+2log Q+3K⁴` and
`η_N=9(1+log Q)/log N`. Uniform finite-conductor quasimodes eventually give
`Σ_(m≤Q)‖r_m‖²≤e²/128`, and `η_N M≤e/4` eventually.

For `p=Σa_m v_m`, the lower frame gives `Σa_m²≤2‖p‖²`; hence
`‖Σa_m r_m‖≤(e/8)‖p‖`. Polarized Gram discrepancy bounds the diagonal
energy below by `(e−η_N M)Σa_m²≥(e/2)‖p‖²`. Thus
`W(p)≥(3e/8)‖p‖²`. If `z⊥V_Q`, the diagonal packet pairs to zero and
`2|⟨Wp,z⟩|≤(e/8)(‖p‖²+‖z‖²)`. Splitting a vector of `V_R` into its
orthogonal projection onto `V_Q` and its complement yields
`W(p+z)≥(e/4)(‖p‖²+‖z‖²)`.

For `R=⌊N^θ⌋`, `0<θ<1/1080`, all high-block horizon conditions eventually
hold: `R⁶≤N`, `1080(1+log R)≤log N`, and
`(1+log R)R²log N/N→0`. This completes the mathematical assembly; the
finite-frame estimates and horizon passage still require Lean verification.

For profiles with real Fourier zeros, separately establish strict positivity
of the integrated shell tail from compact support and nontriviality. A
pointwise Fourier lower bound is not part of the conjecture.

## Corpus boundary

- `BilinearConductorResidualsAndOneEighthPackets.lean`:
  `eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge`
  controls the spectral-floor matrix for `α<1/8`, `α+2q<1`.
- `CollectivePacketCoercivityAndLogarithmicConfinement.lean`:
  `eventually_tiltedUnitSpline_collective_packet_coercive_with_defect_below_one_quarter`
  controls the orthogonal mid-band for `α<1/4`, `q>3α`.
- `Conductor/CoprimeFourierOrder.lean`:
  `log_conductor_sub_log_overlap_le_completedEnergy` holds for every such profile.

No whole-span Lean theorem is claimed.
