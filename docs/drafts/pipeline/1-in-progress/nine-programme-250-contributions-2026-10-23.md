# Nine-programme research ledger (2026-10-23)

- **ID:** nine-programme-250-20261023
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** user `/goal` of 2026-10-23 (nine programme READMEs, read-only)
- **Statement:** 250 significant contributions: a discharged significant hypothesis, a significant
  reduction of the RH proof burden, or a significant new tool solving a previously inaccessible
  problem. Numerical improvements, no-gos, identities alone and renamings count zero.

## Counting rule

A contribution counts only when (i) the corpus search shows the question open, (ii) the paper proof
is complete, (iii) the exact theorem compiles with `lake --old env lean`, axioms
`[propext, Classical.choice, Quot.sound]`, (iv) the leaf is wired into its umbrella, and (v) the
significance survives an honest audit against the user's exclusions.

Theorems whose hypotheses are unproven analytic premises (a density bound on the flipped primes, a
lower bound for a series) are criteria, not contributions, unless a concrete weight discharges them.

**Accepted: 9 / 250.**

1. THIM §5 open item "the pole law for kernels outside the critical Wiener algebra": for
   `0 < ε < 1/2`, `q ≥ 0` in `𝒞(K, ε)` with `Σ q(d)d^{-(1−ε)} = ∞`, and `Σ|k(j)|j^{-(1−ε)} < ∞` with
   `K(1−ε) ≠ 0`, the receiver of `k ⋆ q` is unbounded
   (`not_receiverBounded_dirichletConv_of_not_summable`,
   `TransHorizonIncidenceMechanics/APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa.lean`), via the
   general pole law of `TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint.lean`.
2. THIM §5 open item "the `1/4` law", mean-field model: `z^{Ω(d)} d^{-1/2}` is paid iff `z < 1/2`
   for every `z ∈ [−1, 1]`, the boundary `z = 1/2` unpaid (`receiverBounded_constantSign_iff_full`,
   `TheQuarterLawOfTheConstantSignPattern.lean`, `…OnTheFullRange.lean`; the negative range uses
   `1/ζ ≪ |t|^{1/4}` right of `Re w = 1`), through the boundary-energy identity of
   `TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries.lean` (the identity itself is a
   Nyman–Beurling-type Plancherel formula and is not counted). Extended to the full `(z, ε)` phase
   diagram (`receiverBounded_constantSign_damped_iff`, `ThePhaseDiagramOfTheConstantSignPattern.lean`):
   paid ⟺ `ε > 1/2`, or `ε = 1/2 ∧ z < 1/2`, or `z = 0`, or `z = −1` and `μ(d)d^{-ε}` paid.
3. THIM §5 (density premise of the prime-density laws discharged): for every `q ≥ 1`, `S ⊆ ZMod q`,
   the completely multiplicative `±1` pattern flipping the primes with residue in `S` has
   `|Σ_{p mod q ∈ S} p^{-w} − ρ log(1/(w−1))| ≤ B`, `ρ = #(S ∩ (ZMod q)ˣ)/φ(q)`
   (`exists_abs_tsum_residueFlip_sub_le`, from Mathlib's Dirichlet-theorem residue-class L-series by
   dominated convergence). Unconditional consequences: `4#(S∩units) < φ(q)` ⇒ unpaid at half
   damping (`not_receiverBounded_residueFlip_half`); for `0 < ε < 1/2`, `ρ ∉ {1/2, 1}` ⇒ unpaid
   (`not_receiverBounded_residueFlip`, through `not_receiverBounded_of_flippedDensity` of
   `APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa`).
   `TransHorizonIncidenceMechanics/ResidueClassFlipsAndThePrimeDensityLaws.lean`. Boundary included:
   `4#(S∩units) ≤ φ(q)` ⇒ unpaid at half damping (`not_receiverBounded_residueFlip_half_of_le`,
   `TheQuarterBoundaryOfResidueClassFlips.lean`: complex class density
   `Re Σ_{p≡a}p^{-s} = φ(q)^{-1}log(1/|s−1|) + O(1)` near `s = 1` by the mean value theorem on
   Mathlib's residue-class L-function, Euler lower bound for `±1` patterns, and the generic criterion
   `not_receiverBounded_of_sq_norm_dirichletSeries_ge`). So a paid residue-class flip has `ρ > 1/4`.
4. THIM §5 "the `1/4` law", sufficiency for genuine non-character `±1` patterns: for a subgroup
   `H ≤ (ZMod q)ˣ` with `2|H| ≤ φ(q)`, the pattern `f_H` flipping every prime `p ∤ q` with
   `p mod q ∉ H` gives a paid `f_H(d)d^{-1/2}` (`receiverBounded_subgroupFlip_half`); for index
   `≥ 3` the receiver of `f_H(d)d^{-ε}` is paid **iff** `ε ≥ 1/2` (`receiverBounded_subgroupFlip_iff`).
   Mechanism: orthogonality `[b ∈ H] = φ^{-1}Σ_χ c_χ χ(b)` with `c_χ ∈ {0, |H|}` puts `ζ` at exponent
   `2/k − 1 ∈ [−1, 0]` and every `L(·, χ)` at a nonnegative exponent, so only `1/|ζ|` and upper
   bounds for `|L|` are needed — no zero-free region for `L`.
   `TransHorizonIncidenceMechanics/SubgroupFlipsArePaidAtHalfDamping.lean`.
5. THIM §5 "prime-density heuristics at half damping", the quarter law is height-local: for
   `f(p) = a cos(t₀ log p)` (completely multiplicative, `a ∈ [−1, 1]`) the half-damped weight is paid
   iff `t₀ = 0 ∧ a < 1/2`, or `t₀ ≠ 0 ∧ (a < 1 ∨ ζ(1/2 + it₀) = 0)` (`receiverBounded_oscWeight_iff`).
   The prime mean on the real axis is `0` for `t₀ ≠ 0`, yet `a = 1` is unpaid unless `1/2 + it₀` is a
   zero: the receiver reads `ζ` at the heights `±t₀` with exponent `a/2` each, and on the threshold it
   detects exactly the critical zeros (`receiverBounded_oscWeight_one_iff`).
   `TransHorizonIncidenceMechanics/OscillatingPrimePatternsReadTheCriticalZeros.lean`,
   `…/OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros.lean`.
   Same prime signs and same (zero) prime mean, opposite receivers
   (`exists_paid_unpaid_with_same_prime_signs_and_mean`,
   `PrimeSignsAndPrimeMeansDoNotDecideTheHalfDampedReceiver.lean`).
6. THIM §3.17 quantization of the prime mean, made height-local: below half damping a paid receiver
   forces an integral order of `C` at every point `1 − ε + it₀` of the abscissa line (complex pairing
   identity off the real axis, `complexMellinPairing_eq_zeta_mul_of_summable`; ray orders,
   `exists_ray_bounds_of_order`). For `0 < ε < 1/2`, `t₀ ≠ 0`: `f_{a,t₀}(d)d^{-ε}` is paid iff `a = 0`
   (`receiverBounded_oscPattern_damped_iff`), although its real-axis prime mean is `0` for every `a`.
   `TransHorizonIncidenceMechanics/ThePrimeMeanIsQuantizedHeightByHeight.lean`.
7. THIM §5 "the `1/4` law", sufficiency for every inversion-symmetric residue pattern: for
   `S ⊆ ZMod q` closed under inversion on the units, `f_{q,S}(d)d^{-1/2}` is paid iff
   `φ(q) < 4#(S ∩ units)` (`receiverBounded_residueFlip_half_iff`). The nonprincipal characters enter
   with exponents of both signs; the new tool is the reciprocal bound `1/|L(σ+it, χ)| ≤ C log⁷|t|`
   on `1 ≤ σ ≤ 2` (3-4-1 beyond the corpus strip, `RHTower.exists_norm_inv_LFunction_le_log_pow`).
   `TransHorizonIncidenceMechanics/TheEulerExponentsOfSymmetricResidueFlips.lean`,
   `…/TheQuarterLawOfSymmetricResidueFlips.lean`, `RHTower/DirichletLReciprocalRightOfTheOneLine.lean`.
8. THIM §5 "the `1/4` law" on the whole residue family: for every `q ≥ 1` and `S ⊆ ZMod q`,
   `f_{q,S}(d)d^{-1/2}` is paid iff `φ(q) < 4#(S ∩ units)` (`receiverBounded_residueFlip_half_iff_general`).
   New tool: the Euler logarithm `ℓ_χ` of `L(·, χ)` with `ℓ_χ' = L'/L` and
   `|ℓ_χ(σ + it)| ≤ 9 log log|t| + C` on `1 < σ ≤ 2` (`RHTower.exists_norm_eulerLog_le_large`), bounded
   on boxes for `χ ≠ 1`; complex character exponents cost only a power of `log|t|`.
   `TransHorizonIncidenceMechanics/TheQuarterLawOfResidueFlips.lean`,
   `RHTower/DirichletLEulerLogarithmRightOfTheOneLine.lean`.
9. THIM §5, the phase law: for `f(p) = a cos(t₀ log p + φ)`, `|a| ≤ 1`, `t₀ ≠ 0`, the half-damped
   weight is paid iff `a cos φ < 1` or `ζ(1/2 + it₀) = 0` (`receiverBounded_phaseWeight_iff`). Only
   `Re(a e^{iφ})` is read; the conjugate part couples to `arg ζ`, which is bounded at the pole
   (`RHTower.exists_abs_im_zetaEulerLog_le`, new). Generic strip-bound payment criterion for
   patterns: `receiverBounded_pattern_half_of_bounds`.
   `TransHorizonIncidenceMechanics/ThePhaseLawOfOscillatingPrimePatterns.lean`,
   `RHTower/ZetaEulerLogarithmOnBoxes.lean`.

## Active conjecture

See `half-damped-receiver-pole-law-and-quarter-threshold.md`.

## Log
- 2026-10-23 — phase law: two leaves compiled, axioms clean, wired; contribution 9.
- 2026-10-23 — general residue flips: two leaves compiled, axioms clean, wired; contribution 8.
- 2026-10-23 — symmetric residue flips: three leaves compiled, axioms clean, wired; contribution 7.
- 2026-10-23 — `ThePrimeMeanIsQuantizedHeightByHeight` compiled, axioms clean, wired; contribution 6.
- 2026-10-23 — oscillating prime patterns: two THIM leaves compiled, axioms clean, wired; contribution 5.
- 2026-10-23 — `SubgroupFlipsArePaidAtHalfDamping` compiled, axioms clean, wired; contribution 4.
- 2026-10-23 — `TheQuarterBoundaryOfResidueClassFlips` compiled, clean, wired (extends 3).
- 2026-10-23 — `ThePhaseDiagramOfTheConstantSignPattern` compiled, clean, wired (extends 2).
- 2026-10-23 — `ResidueClassFlipsAndThePrimeDensityLaws` compiled, axioms clean, wired; contribution 3.
- 2026-10-23 — four THIM leaves compiled (axioms `propext`, `Classical.choice`, `Quot.sound`) and
  wired; contributions 1–2 accepted. Not counted: the general δ < 1/4 criterion (premise on the
  flipped primes, no concrete pattern discharges it).
- 2026-10-23 — all nine READMEs read (shared-target section byte-identical across all nine);
  STATUS and frontier map consulted. Lead rejected: BVI balanced regime `Q ≍ P` is limited by the
  cubic tail of the cross-scale expansion, not by block equidistribution, so PNT error terms do not
  close it.
