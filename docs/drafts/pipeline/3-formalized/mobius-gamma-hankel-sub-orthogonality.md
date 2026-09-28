# Möbius sub-orthogonality: a smoothed Mertens conjecture that implies RH and simple zeros

- **ID:** `MC-SUBORTHO-001`
- **Stage:** 3-formalized (implications); conjecture open
- **Type:** THEOREM (Lean) + CONJECTURE
- **Route:** MC / Route E carrier (Gamma–Hankel Möbius covariance)
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusGammaHankelSubOrthogonality.lean`
  (wired in `RHTower.lean`; leaf build `lake build --old` green; axioms `propext, Classical.choice, Quot.sound`).
- **RH used:** no. **Computation used:** no.

## Objects
Atoms `v_n(x) = x^{(r-1)/2} e^{-nx}` in `L²(0,∞)`, `⟨v_m,v_n⟩ = Γ(r)/(m+n)^r > 0`.
Finite energy `E_r(N) = ‖Σ_{n≤N} μ(n) v_n‖²` (`finiteMobiusGammaHankelEnergy`),
diagonal `D_r(N) = Γ(r)Σ_{n≤N} μ(n)²(2n)^{-r}`, off-diagonal `O_r(N) = E_r(N) − D_r(N)`.

## Conjecture (sub-orthogonality, SO)
There is `σ₀ > 1/2` such that for every `1 < r < 2σ₀` and every `N ≥ 1`:

`O_r(N) ≤ 0`, i.e. `‖Σ_{n≤N} μ(n)v_n‖² ≤ Σ_{n≤N} μ(n)²‖v_n‖²`.

The Möbius sign pattern is conjectured to be *sub-orthogonal* for the positive Gamma–Hankel Gram
matrix: the signs never add constructively in aggregate.

**Contrast with Mertens.** For the rank-one kernel (all atoms equal) SO is `M(N)² ≤ Q(N)`
(`Q` = squarefree count), i.e. `|M(N)| ≤ 0.78√N`, the Mertens conjecture (false: Odlyzko–te Riele).
The rank-one kernel weights a zero by `1/|ρ ζ'(ρ)|`, which is not absolutely summable. The
Gamma–Hankel kernel weights it by `|Γ(ρ)|²/|ζ'(ρ)|²` and damps height `γ` like `e^{-π|γ|}`.

**Heuristic under RH + simple zeros (not a theorem).** By Plancherel,
`E_r(∞) = (1/2π)∫|Γ(r/2+it)/ζ(r/2+it)|² dt`. As `r ↓ 1` each zero contributes
`|Γ(ρ)|²/((r−1)|ζ'(ρ)|²)`, so `E_r(∞) = (r−1)^{-1} Σ_ρ |Γ(ρ)|²/|ζ'(ρ)|² + O(1)`.
The first pair `ρ = ½ ± 14.13…i` dominates the sum, giving a coefficient of order `10^{-18}`,
against the diagonal `D_r(∞) ~ (3/π²)/(r−1)`. The off-diagonal cancels the diagonal to about 17
orders of magnitude at leading order.
For finite `N` the excess over `E_r(∞)` is about `M(N)² N^{-r}/r`. `D_r(N)` grows like
`(3/π²)log N` for `N ≪ e^{1/(r−1)}`, so SO needs only `M(N)²/N ≪ log N`, far weaker than Mertens.

## Proved in Lean (unconditional implications)
1. `exists_order_vertical_window_floor_of_canonical_identity`: a boundary zero of order `n`
   forces a Mellin floor `c/rⁿ` on the window of radius `r` at abscissa `σ + r`.
2. `memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le`: a
   cutoff-uniform ceiling `B` on `E_{2σ}(N)` passes, by Fatou, to the infinite source with the
   same `L²` ceiling.
3. **Multiplicity law** `two_mul_analyticOrderAt_toNat_le_of_powerApertureCeiling`: if
   `E_{2σ}(N) ≤ C/(2σ−1)^k` for all `N` and all `1/2 < σ < σ₀`, then RH holds and every zero of
   order `n` in the strip satisfies `2n ≤ k+1`. The blow-up exponent of the Gamma–Hankel energy
   bounds zero multiplicity: exponent `2m−1` is exactly what an order-`m` zero forces.
4. `reciprocalApertureCeiling_of_subOrthogonal`: `D_r(N) ≤ 2/(r−1)` for `1<r≤2` (from
   `Γ ≤ 1` on `[1,2]` by convexity and the `p`-series tail), so SO gives exponent `k=1`.
5. **Main:** `riemannHypothesis_and_simple_zeros_of_subOrthogonal`:
   `SO ⇒ RiemannHypothesis ∧ ∀ρ in the strip, analyticOrderAt ζ ρ = 1 ∧ ζ'(ρ) ≠ 0`.

## Relation to the corpus
- Strengthens the Route E receiver (`MobiusGammaHankelOffDiagonalUpperBounded`, any constant
  `C(r)`) to the sharp constant `0`. The sharp constant forces simplicity as well as RH.
- The corpus's `MobiusLaplaceSimpleZeroResidueCap` obtains simplicity from *pointwise*
  half-power decay of Φ. Here an `L²` reciprocal-aperture ceiling suffices, and the general
  multiplicity law (item 3) is new.
- Analogue of Titchmarsh §14.29 (weak Mertens ⇒ RH + simple zeros), in a sign-law form with the
  exact diagonal as the ceiling.

## What remains open
SO itself. It is RH-strength: SO ⇒ RH (+ simplicity). Its value as a producer target is that it
is a *pointwise-in-N sign law* on a positive Gram form, with a very large conjectured margin, of
the same shape as the corpus's proved partial edge sections (`RouteEAllQuotientPowerEdgeDominance`:
selected edge sections `≤ 0` for all `N`, `r ≥ 1`). SO is the full-section version of those
laws.

## Log
- 2026-09-28: conjecture formulated, Plancherel heuristic computed, implications formalized.
