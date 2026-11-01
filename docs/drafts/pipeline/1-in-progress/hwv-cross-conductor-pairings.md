# Cross-conductor pairings of the complete Weil form against the conductor margin

- **ID:** hwv-cross-conductor
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** HWV README §8 topic 1 (top coprime stratum); `totient_mul_conductorEnergy_eq`
- **Statement:** Bound the cross-conductor pairings `⟨W_{c,N} r_e, r_{e'}⟩`, `e ≠ e'`, and the
  quasimode residuals below the conductor margin `E_m(c) ≍ E(c/m)`, uniformly in `N`.

## Goal
Positivity of the top coprime stratum against the strata below with `N`-independent constants.

## Approach
1. Möbius over the divisor lattice: only pairs with `lcm(e, e') = m` enter the `m`-th Möbius
   difference of the star pole energies (lcm law).
2. Cross pairing = energy × Gram channel + residual channel; Gram channel explicit `O(1/log N)`
   (corpus harmonic Gram remainder).
3. Uniform range: every diagonal conductor margin, all `m ≤ N`, in the universal regime (corpus
   all-conductor floor).
4. Boundary: star poles and conductors are bases of the horizon, so the whole cross-pairing matrix
   over all conductors is the complete form in another basis; its positivity on the pole
   hyperplane at logarithmic overlap is RH (RIT).

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** entrywise (Gershgorin) control over all conductors cannot
  hold at the top band: there the conductor vectors are local and overlap-`c` neighbours couple at
  diagonal size. Quadratic control over all conductors is RH.
- **Strongest positive survivor:** lcm law; uniform diagonal margins for all conductors in the
  universal regime; explicit Gram channel.
- **New insight:** the generic threshold comes from the boundary layer `N/n ≤ T` (Mertens remainder
  `R(N/n) = O(1)` there), not from the PNT error in the bulk.
- **Status:** see Log.

## Log
- 2026-11-01 — created.
