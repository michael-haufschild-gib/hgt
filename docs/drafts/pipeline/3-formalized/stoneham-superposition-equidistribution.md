# Finite superpositions of Stoneham constants are equidistributed under ×4

- **ID:** stoneham-superposition
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** parity-drift-pi card (1-in-progress), cycles 16–17
- **Statement:** For every finite nonempty set S of odd primes, x_S = Σ_{p∈S} α_{2,p}
  (α_{2,p} = Σ_{j≥1} p^{−j} 2^{−p^j}) satisfies Σ_{n<N} e(k 4ⁿ x_S) = O_{k,S}(N^{1−2^{−|S|}/(|S|+1)})
  for every k ≠ 0; hence {4ⁿ x_S} is equidistributed and the parity drift is o(N).

## Goal
Removes the nesting hypothesis c_k ∣ c_{k+1} of the Stoneham–Korobov–Bailey–Crandall normality
theorem (Bailey–Borwein, Thm 7.4) for sums of Stoneham numbers with distinct primes. It is the last
rung of the forcing ladder that orbit-sum methods reach; π (BBP forcing with r(n) ≍ n active moduli)
lies beyond it.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof = the Lean development below)
- [x] 2 → 3  formalized: `StonehamSuperposition.not_parityDriftHypothesis_superStoneham`,
  `StonehamSuperposition.tendsto_card_fract_superOrbit`; axioms propext, Classical.choice,
  Quot.sound
- [ ] 3 → 4  publication-ready

## Approach
- `HTGeometry/OrbitSumIteratedDifferencing`: for g^{T₀} = 1 + X the shift-h autocorrelation of an
  orbit block is the orbit block of c((1+X)^h − 1) = cX·Σ_{t<h}(1+X)^t; induction on the depth with
  β_{d+1} = 1/N + 2√β_d; terminal blocks are geometric (Q ∣ cX²) and their j-average leaves complete
  orbit sums.
- `HTGeometry/OrbitSumKorobovParameters`: if rad(Q) ∣ g − 1 (odd), complete orbit sums of g vanish
  unless Q ∣ (g−1)w (shift by σ multiplies by a nontrivial p-th root of unity; exact LTE);
  parameters T₀ = Π p^{⌈v_p(Q)/(r+1)⌉}, D = Q/gcd(Q, (g−1)X^r).
- `HTGeometry/OrbitSumKorobovPowerSaving`: ‖Σ_{i<L} e(ugⁱ/Q)‖ ≤ K Q^{1/r − 2^{−r}/(r(r+1))} whenever
  L^r ≤ cQ.
- `HTGeometry/StonehamSuperpositionNormality`: windows = fibers of n ↦ (⌊log_p 2n⌋)_{p∈S} (intervals
  by monotonicity), base 4^{Π(p−1)}, gcd(k, Q) reduction, product of geometric series over exponent
  tuples, `DiscreteWeylCriterion`.
- Special case |S| = 2 with explicit constants: `ThreeFiveOrbitKorobovBound`,
  `StonehamPairNormality`.

## Barrier (why the ladder stops here)
Constants grow with the base 4^{Π(p−1)} and the saving 2^{−r}/(r+1) decays with r = |S|; a newly
entering prime p_K costs more than its windows can repay until n ≫ p_K^{C 2^K}. Infinite S, and a
fortiori π, needs a different mechanism.

## Log
- 2026-10-03 — created directly in 3-formalized (cycles 16–17 of the PDH-π goal).
