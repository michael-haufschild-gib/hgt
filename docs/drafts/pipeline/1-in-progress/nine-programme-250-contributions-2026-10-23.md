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

**Accepted: 3 / 250.**

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

## Active conjecture

See `half-damped-receiver-pole-law-and-quarter-threshold.md`.

## Log
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
