# Uniform finite-fold approximation of the completed Möbius wave

- **ID:** CHMD-FOLD-UNIFORM-APPROXIMATION-1810
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Statement:** Finite real linear combinations of folds at nonnegative shifts cannot approximate the completed folded Möbius wave uniformly on the rapidity half-line.
- **Parent:** `../1-in-progress/chmd-all-scale-folded-mobius-control-2026-10-18.md`

## Goal and exact scope

Test whether uniform approximation by finite folds can justify passing a rapidity-uniform estimate to the completed wave. Only this approximation shortcut is retired. Uniform boundedness of finite approximants, followed by pointwise convergence, remains a possible argument. The all-scale arithmetic bound remains open.

Write `F(y) = foldedMobiusWave y` and `Φ(y,v) = mobiusFold y v`. The killing theorem is

`∃ δ > 0, ∀ finite s ⊂ [0,∞), ∀ a : ℝ → ℝ, ∃ y ≥ 0, δ ≤ |F(y) - Σ_{v∈s} a(v) Φ(y,v)|`.

This is `exists_uniform_separation_finite_mobiusFold`. The separate theorem `exists_uniform_separation_mobiusFold_truncations` specializes the same separation to every literal Möbius truncation. Neither theorem assumes RH.

## Strongest positive survivor

For `λ > 0`, define the temporal cosine observation

`A_T(f,λ) = ∫_{t∈(0,1]} f(Tt) cos(λTt) dt`.

For every `v ≥ 0`, its exact limiting value on a single fold is

`lim_{T→∞} A_T(Φ(·,v),λ) = if λ = sqrt(7/4) then (γ+1) exp(-v) / cos(1/4)^2 else 0`.

Thus the only positive-frequency temporal atom of a finite fold combination is the explicit pole atom, with coefficient `(γ+1) / cos(1/4)^2 * Σ a(v) exp(-v)`. This is an exact classification, stronger than the negative approximation statement. The corresponding formal theorem is `mobiusFold_hasTemporalCoefficient`; `finite_mobiusFold_hasTemporalCoefficient_zero` handles every other positive frequency.

The completed wave satisfies the exact identity

`F = K(·,0) - poleShadow - chmdArchWave/(2π) + chmdWave`.

Its explicit pole mode cancels. Under RH its temporal coefficients instead recover `shadowTemporalMass λ`, the sum of positive `kgAtomWeight` values at all actual zero frequencies equal to `λ`. Frequency collisions are retained.

## Dependency-closed paper proof

1. Integrating products of two cosines gives limiting observation `1/2` at matching positive frequencies and zero at distinct positive frequencies. A uniform bound `|f(y)| ≤ C` for `y ≥ 0` bounds `|A_T(f,λ)|` by `C` for `T ≥ 0`.
2. The Klein–Gordon frequency map `r ↦ sqrt(r²+2)` has at most two points in each fibre. Every fibre therefore has Lebesgue measure zero. Dominated convergence, using the source-proved integrable spectral densities, makes every positive-frequency coefficient of the continuous spectral integral vanish. The same argument covers the first two spatial derivatives and their conjugated combination.
3. Existing uniform kernel bounds admit the bounded spatial integrals and exponentially dominated remainder integral. They therefore have zero positive-frequency coefficients. The exact pole-tail decomposition leaves precisely the single-fold coefficient displayed above.
4. Finite sums preserve these coefficients. The source identity for `F` cancels the explicit pole. Under RH, absolute summability of the actual zero series permits extraction of its colliding frequency masses; each actual zero contributes strictly positive weight. Its frequency lies strictly above `sqrt(7/4)`.
5. Fix one actual zero `ρ` and put `δ = kgAtomWeight ρ / 2 > 0`. If a finite fold combination had error everywhere strictly below `δ`, its existing uniform bound would imply a bound for `F`. The already-proved CHMD receiver would then imply RH. Extracting the temporal coefficient at `kgAtom ρ` would give a difference at least `kgAtomWeight ρ`, while the uniform error bound forces that difference to be at most `δ`. Contradiction. Negating this strict error bound gives the asserted separation point.

## Prior-work and novelty audit

The corpus already contains generic Bohr coefficient extraction for summable discrete spectra and a residue-based obstruction for raw Báez–Duarte Möbius approximants. No general spectral-extraction or nonconvergence novelty is claimed. This result identifies the exact atom of the actual CHMD fold and applies it to arbitrary finite fold combinations. The proof reuses `sqrt_seven_fourths_lt_re_kgFreq` and `integrable_sechSqHalf_mul_gammaBracket` from existing CHMD modules. External priority is not assessed in this corpus-only task.

## Formalization and gates

- Paper proof: complete for the exact statements above.
- Lean: seven leaves, from `CHMDTemporalCosineExtraction` through `CHMDUniformFoldApproximationObstruction`, compiled successfully by a targeted `lake --old build`; all seven are imported once by the `RHTower` umbrella.
- Direct final checks: `lake --old env lean` passed for `CHMDFoldedPoleMode.lean` and `CHMDUniformFoldApproximationObstruction.lean`, with no diagnostics. A separate scratch-file audit of `mobiusFold_hasTemporalCoefficient`, `finite_mobiusFold_hasTemporalCoefficient_zero`, `foldedMobiusWave_eq`, `exists_uniform_separation_finite_mobiusFold`, and `exists_uniform_separation_mobiusFold_truncations` passed; each uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Generated indexes refreshed. The original `scripts/formal_tools.py lint --check-generated` reported two unrelated concurrent-tree errors: unreachable `BezoutValuationIncidence.NaturalCutoffMultiDepthCofactorAndConditionalTailBridge`, and root research leaf `GaloisForLFunctions/TransHorizonIncidenceMechanics.lean`. No forbidden declaration or error in these CHMD leaves was reported. No global lint pass is claimed.
- At the requested pause, all seven compiled artifacts are newer than their sources and every umbrella import occurs once. Generated indexes were refreshed again. `logs/chmd-closeout-1810f-verification.json` records the final closeout checks for these seven leaves and the separate quantitative-tail leaf.
- Final `lint --check-generated` reports only the unrelated package-root `TransHorizonIncidenceMechanics.lean`; no stale generated file or owned-leaf finding remains.
- No full build, new axioms, numerical experiments, or heartbeat increases.

## New insight and surviving obligation

Finite-fold temporal atoms and the completed arithmetic spectrum differ even when the latter is bounded. A valid boundedness proof must tolerate this nonuniform emergence of modes at zeta-zero frequencies. The missing arithmetic estimate is still a rapidity-uniform one-sided bound on the completed wave; this obstruction does not provide it.
