# Geometric-skeleton Brown ramp transfer law — formalized closure

- **ID:** `geometric-skeleton-brown-ramp-transfer-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./geometric-skeleton-brown-ramp-transfer-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean module

`GaloisForLFunctions.HTGeometry.GeometricSkeletonBrownRamp` (new), on top of the
approximate-complexity layer of `HTGeometry/ExactPenaltyCircuitBellman`
(umbrella `GaloisForLFunctions.HTGeometry`).

## Formal theorem chain

1. `uniformSimComplexity` — definition `(1)`: least word length of a circuit simulating the flow
   at elapsed time `u` uniformly on the whole space to accuracy `γ`.
2. `wordAct_append` — concatenated words compose the gate actions.
3. `approxComplexity_le_add_of_witnesses` — the composition transfer `(9)`:
   `C_{ε₋+γ}(ψ_{u+t}) ≤ C_{ε₋}(ψ_t) + S(u, γ)`, proved from the isometry of the flow, the group
   law and the triangle inequality.  No monotonicity or continuity of complexity is used.
4. `lt_approxComplexity_of_skeleton` — **Theorem A**, the boxed `(7)`: endpoint hardness
   `c v T − K < C_{ε₊}(ψ_T)` at a skeleton time `T ≤ q t` forces
   `(1 − q(1−c)) v t − (K + A + 1) < C_{ε₋}(ψ_t)` at every earlier time of the cell.  The additive
   `+1` is the integer ceiling of the simulator cost `v u + A`.
5. `approxComplexity_le_of_easy_seed` — **Theorem B**, the boxed `(12)`:
   `C_{η+δ}(ψ_t) ≤ b + S(t, δ)`, so a `v t + A₊` simulator gives the matching upper ramp.
6. `skeleton_card_le` — **Theorem C** `(13)`: a geometric progression of ratio `q > 1` from `T₀`
   truncated at `Tmax` has at most `2 + log(Tmax/T₀)/log q` terms.
7. `skeleton_union_bound` — `(15)`: `N + 1` events each of failure probability at most
   `B e^{-κ r}` have total failure at most `(N+1) B e^{-κ r}`.
8. `skeleton_replica_order` — `(16)`: taking `r ≥ log(B(N+1)/δ)/κ` bounds that total by `δ`.
   With `Tmax/T₀ = exp(O(n))` this is `(17)`: `r = O(log n + log(1/δ))`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/GeometricSkeletonBrownRamp.lean` — clean, no
  warnings.
- `lake build GaloisForLFunctions.HTGeometry.GeometricSkeletonBrownRamp` — green.
- `#print axioms` on statements 3–8: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

The card's exact surviving open core — simultaneous robust hardness at `O(n)` prescribed geometric
times for one ordinary fixed-strength local Hamiltonian ensemble, with an aligned plateau onset —
is a dynamical research target on the parent cards, not formalization debt for Theorems A–C.
