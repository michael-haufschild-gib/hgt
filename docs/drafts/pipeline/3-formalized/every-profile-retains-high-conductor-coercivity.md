# Every compact profile retains high-conductor coercivity

- **ID:** every-profile-retains-high-conductor-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; the high block of the growing-span conjecture.

For every real nonzero `C²` profile supported on `[0,1]` and every `K≥1`,
there is `C>0` such that a unit packet `u=Σ_(m≤R)a_m v_m` orthogonal to
`V_Q` satisfies

`W_(φ,c,N)(u) ≥ E(a)/16 + (log Q)/4 − C`,

uniformly for `1≤c≤K`, under the following finite-horizon conditions:

- `2≤Q≤R`, `R⁶≤N`, `1080(1+log R)≤log N`;
- `c/N≤1/3`;
- `(R²+1)(linearNearRowRadius(c)+1)≤N` and `(R²+1)(c exp(1)+1)≤N`;
- `(1+log R)R²log N/N≤1`.

Here `E(a)=Σ(log m+tameDifferent(m))a_m²`.

## Proof

The lower harmonic frame gives `Σa_m²≤2`, so the weighted coefficient mass
`G=Σ(1+log m)a_m²` is at most `2+E`. The weighted center estimate and the
merged overlap/downward estimate bound the squares of their respective
quadratic pairings by `B₁(2+E)` and `B₂(2+E)`, with positive constants
depending only on `φ,K`. Indeed `(1+log R)/log N≤1`, and the last horizon
condition bounds the remaining near contribution.

If `z²≤B(2+E)` and `B>0`, then
`|z|≤E/32+8B+1/16`, by expanding `(|z|−16B)²≥0` and dividing by `32B`.
Thus both terms together cost at most `E/16+8(B₁+B₂)+1/8`.
The separated and upward operator norms are bounded on `1≤c≤K`.
The self finite part equals its value at one minus `log c`; its remainder
is bounded by `exp(1/2)/2`. The two-pole pairing vanishes on `V_1^⊥`.

`primePacket_energy_ge_adjunction_and_log_of_orthogonal` supplies
`E/8+(log Q)/4−(log 4+4)`. Substituting the preceding bounds into the exact
complete-Weil decomposition proves the claim.

The analytic inputs are `WeightedConductorCrossBounds`,
`ConductorBandOverlapAndNonRatioBounds`, `ConductorBandPrimeAndCenterBounds`,
and `TheCompleteWeilMatrixDecomposesAtEveryOverlap`.

## Lean

`CriticalArithmeticCorrelationTheory/EveryProfileRetainsHighConductorCoercivity.lean`:
`exists_profile_highConductor_coercivity`.

Direct Lean check passed. The dependency audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.
