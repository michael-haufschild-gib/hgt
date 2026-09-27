# Ordered cross-prime curvature has unbounded exterior rank — Lean certificate

- **Paper card:** `stc-ordered-curvature-unbounded-rank.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCOrderedCurvatureRank`,
  `GaloisForLFunctions.RHTower.STCPrimeWindowPackets` (PNT packets),
  `GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesFourChannelObstruction` (identity (1))
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| (1) four-channel identity | `stokes_odd_four_channel` |
| `c_pq` symmetric; `R_qp = R_pq⁻¹` | `routeRCrossPrimeStokesOddCurvature_comm`, `routeRCrossPrimeStokesRatio_swap` |
| symmetric packet matrix has rank ≤ 4 (and vanishes at `g = 0`) | `rank_symmetricStokesMatrix_le` |
| `n` primes in `[P,(1+ε)P)` above any threshold (PNT) | `exists_prime_packet` |
| `sinh(t+δ)/sinh t → 1` | `tendsto_sinh_add_div_sinh` |
| (2) normalized entries `c/(-4 sinh(g log P)) → 1` | `tendsto_stokesOdd_log_normalized` |
| `S_n` invertible for even `n` | `det_orderSignMatrix_ne_zero`, `det_orderSignMatrix_real_ne_zero` |
| **Theorem**: rank `n` ordered packets for every `g ≠ 0`, even `n` | `exists_prime_packet_orderedStokesMatrix_rank` |
| no fixed finite alternating one-prime channel form | `no_finite_alternating_stokes_channels` |
