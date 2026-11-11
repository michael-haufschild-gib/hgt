# Worlds of the Zero Configuration (WZC) programme

- **ID:** wzc-programme
- **Stage:** 1-in-progress
- **Type:** PROGRAMME
- **Source:** docs/reports/review-1111/obstacles-summary.md §2.17 (questions 1–6; items B145, B170,
  B183, B141, B13, B138, B157, A120, B59)
- **Statement:** theory of the two failure worlds of RH (world I: a finite isolated top layer;
  world II: a tail), of the three atoms ZAL, B13, Landing, and of their models; search for the one
  inequality for a finite layer that uses the exact count or the functional equation.

## Goal
Folder `formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/`, umbrella
`WorldsOfTheZeroConfiguration.lean`, foundational README. Answer the questions of §2.17 or reduce
each to a named residual; a producer for AAL or ZAL is the success criterion.

## Corpus facts the programme starts from (do not redo)
- Worlds and atoms: `ExceptionalLayerTheory.riemannHypothesis_iff_three_atoms`,
  `asymptoticAbscissaLaw_orthogonal_factorization_tfae`,
  `ZeroConfigurationGeometry` `quasiRH_iff_zetaAsymptoticAbscissa_lt_one`.
- World-I receivers: FloorFreeArithmetic (non-attainment, unit gap, moments, quadrichotomy, quantum,
  tangent data of `μ`, `λ`).
- World-I models: tempered symmetric configurations with any top layer; natural-norm Euler products
  with any divisor; rational primes with repetition (`ArithmeticPositiveDuality.RationalPrimeOneOff`,
  count in the mean only); the firewall `ζ(s)/(ζ(s+1−ρ₀)ζ(s+1−ρ̄₀))`; prime-deletion fakes
  (`SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt`, real zero on top:
  `exists_real_fake_zero_of_keptPrimeSystem`); add-only systems vanish at the real abscissa.
- Tools: `HeckeLFunctions.growthCont` (Dirichlet series with partial sums `O(x^θ)`),
  `HTGeometry.isExactOn_rightHalfPlane`, `RHTower.exists_theta_window_lower_seventeenThirtieths`
  (`θ(y+L) − θ(y) ≥ (L − (y+L)^α)/2`, `α > 17/30`), `sumSystem`, `keptPrimeSystem`,
  `keptPrimeSystem_count_sub_le_of_summable`.

## Questions and state
| # | Question | State |
|---|---|---|
| Q2 | B183: integer norms, a count rate, one non-real pair of fake zeros and no real fake zero | Theorem A below: paper proof done; Lean in progress |
| Q1 | B145 / B170: AAL | open |
| Q3 | B141: `¬AAL ⇒ ZAL` | open |
| Q4 | B13, Landing; B157, A120 | open |
| Q5 | B59: cluster wall of the cameras | a peer session works on box cameras in MZF; not started here |
| Q6 | half-planes of world II | the questions of §2.18; not started here |

## Theorem A (two-sided prime edits with a non-real pair alone)
**Statement.** Let `½ < β₀ < 14/15`, `γ₀ ≠ 0`, `ρ₀ = β₀ + iγ₀`, `ζ(ρ₀) ≠ 0`, and `β > β₀`. There are
disjoint sets `S₋`, `S₊` of rational primes such that the system `B` with the primes of `S₋` deleted
and the primes of `S₊` doubled has: integer norms; `N_B(x) = Ax + O(x^β)`, `A > 0`; and
`(s−1)ζ_B(s) = (s−1)ζ(s)·C·(s−ρ₀)(s−ρ̄₀)·exp(H(s))` with `C ≠ 0` and `H` holomorphic on `Re s > ½`.
So the fake zeros of `B` in `Re s > ½` are exactly `ρ₀`, `ρ̄₀`, both simple; `B` has no real fake
zero.

**Proof.**
1. *Target.* `η = 1 − β₀`, `m(k) = −(k^{ρ₀−1} + k^{ρ̄₀−1}) = −2k^{−η}cos(γ₀ log k)` for `k ≥ n₀`,
   `m(k) = 0` below. For `Re s > β₀`: `Σ m(k)k^{−s} = −ζ(s+1−ρ₀) − ζ(s+1−ρ̄₀) + P(s)`, `P` a
   Dirichlet polynomial.
2. *Greedy rounding.* `δ(0) = 0`; at `k`: `d = δ(k−1) + m(k)`; if `k` is prime and `d ≥ log k`,
   put `k` in `S₊`-side (`ε(k) = 1`), if `k` is prime and `d ≤ −log k`, `ε(k) = −1`; otherwise
   `ε(k) = 0`; `δ(k) = d − ε(k) log k`. So `δ(n) = Σ_{k≤n}(m(k) − ε(k) log k)`.
3. *Thinness.* A step with `ε ≠ 0` lowers `|δ|` by `log k`, a step without raises it by at most
   `|m(k)|`: `|δ(n)| + Σ_{k≤n}|ε(k)| log k ≤ Σ_{k≤n}|m(k)| ≤ (2/β₀)n^{β₀}`.
4. *Discrepancy.* Let `α > 17/30` with the window bound `θ(y+L) − θ(y) ≥ (L − (y+L)^α)/2` for
   `y ≥ X`, and `n₀ ≥ max(X+1, 8^{1/η}, 4^{1/(1−α)})`. Call `k` low if `δ(k) ≤ log(k+1)`. A prime
   `k` without `ε(k) = 1` has `δ(k) < log k`, so it is low. Let `a ≤ n` be the last low index. On
   `(a, n]` every prime has `ε = 1`, so `δ(n) = δ(a) + Σ_{a<k≤n}m(k) − (θ(n) − θ(a))`. With
   `a' = max(a, n₀−1)`, `ℓ = n − a'`: if `ℓ ≤ 2n^α` the drift is `≤ 2n^α·2(a'+1)^{−η} ≤ 8n^{α−η}`;
   if `ℓ > 2n^α` then `θ(n) − θ(a') ≥ ℓ/4 ≥` drift. So `δ(n) ≤ log(n+1) + 8n^{α−η}`, and
   symmetrically below.
5. *Continuation.* `c(k) = ε(k) log k − m(k)` has partial sums `O(x^{c₀})`, `c₀ = α − η + ε'`; by
   summation by parts `Σ c(k)k^{−s}` is holomorphic on `Re s > c₀`. With `E(s) = Σ ε(p)p^{−s}`:
   `E′(s) = −Σ ε(k) log k·k^{−s} = ζ(s+1−ρ₀) + ζ(s+1−ρ̄₀) − P(s) − Σ c(k)k^{−s}`
   `= 1/(s−ρ₀) + 1/(s−ρ̄₀) + Φ(s)`, `Φ` holomorphic on `Re s > c₀` (`ζ(w) − 1/(w−1)` is entire).
   Let `K` be a primitive of `Φ` on the half-plane. Then `exp(E − K)/((s−ρ₀)(s−ρ̄₀))` has zero
   derivative on `Re s > 1`: `exp(E(s)) = C(s−ρ₀)(s−ρ̄₀)exp(K(s))`.
6. *Euler product.* `ζ_B(s) = ζ(s)·∏_{S₋}(1−p^{−s})·∏_{S₊}(1−p^{−s})^{−1} = ζ(s)exp(E(s) + Q(s))`,
   `Q(s) = Σ ε(p)(−log(1−p^{−s}) − p^{−s})`, absolutely convergent on `Re s > β₀/2` by step 3.
7. *Count.* `N_B(x) = Σ_{b ∈ ⟨S₊⟩} N_{ℙ∖S₋}(x/b)`; Rankin for `ℙ∖S₋` and `Σ_{b∈⟨S₊⟩} b^{−β} < ∞`.
With `α = 3/5`: `c₀ < ½` for `β₀ < 9/10`.

**Reading.** A count rate at every exponent above `½`, integer norms, multiplicities `0, 1, 2`
over the rational primes do not force a real zero on top of a finite layer: the Landau mechanism of
the deletion fakes is a property of one-sided edits. Below `√x` the count needs discrepancy at
every frequency (random selection) and a zero-free half-plane of `ζ`: Theorem B, not started.

## Log
- 2026-11-11 — created; Theorem A proved on paper.
