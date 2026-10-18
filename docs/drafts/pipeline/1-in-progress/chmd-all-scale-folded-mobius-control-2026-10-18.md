# All-scale control of the folded Möbius wave

- **ID:** CHMD-FOLD-ALL-SCALE-1810
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Derive an unconditional, rapidity-uniform one-sided bound on the complete folded Möbius transport from the actual arithmetic source.

## Exact target

In `RHTower.CHMDChebyshevTransport`, set

`F(y) = mobiusWaveConstant * mobiusWave y + (γ + 1) * mobiusTailPairing y + remainderFoldSeries y`.

Prove `∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → F(y) ≤ C` (or its lower-bound counterpart), with no unproved arithmetic premise. The existing `riemannHypothesis_iff_mobius_pieces_bddAbove` and `_bddBelow` identify this target with RH; neither proves it.

## Plan and gates

1. [in progress] Audit exact source, kernel, prior conjectures, and all-scale receivers using the local research search and actual Lean declarations.
2. [pending] State competing precise cancellation conjectures; attack their quantifiers, source fidelity, and prior-corpus overlap.
3. [pending] Complete a dependency-closed paper proof of each surviving mathematical claim before formalization.
4. [pending] Formalize unconditional results, wire leaves into their area umbrella, audit each leaf using `lake env lean`, inspect axioms, run formal lint.
5. [pending] Reassess whether the actual target is proved; continue conjecturing if it remains open.

## Constraints

- No numerical experiments, new axioms, assumed cancellation, full builds, or heartbeat increases.
- One foreground build at a time; reuse unchanged objects with Lake's `--old` option.
- Preserve concurrent work and the existing frontier map.
- Knowledge ledger: `logs/chmd-all-scale-folded-mobius-1810.md`; facts and failures only.
- `update_plan` is unavailable in this session; this checklist tracks the multi-step task.
- Serena's symbol operation rejects the ignored Lean path; use source reads and direct Lean checks for this subtree.

## Current mathematical boundary

For each fixed rapidity, the folded series converges absolutely with shift decay `exp(-(π-1/2)v)` and a rapidity-dependent constant. The available rapidity-uniform remainder bound is only `7 * laplacianBound * exp(-v/2)`. Neither estimate justifies a uniform sum over all Möbius scales. All three pieces and their cross-cancellation must remain visible.

## Proof status

**OPEN CORE:** independent all-scale arithmetic cancellation. No proof claimed.

## Conjecture: uniform truncation versus atomic completion

**Candidate shortcut:** the finite sums converge uniformly for all nonnegative rapidities. This is stronger than boundedness of the completed sum.

**Proposed obstruction and positive survivor:** every finite linear combination of folds has zero temporal cosine coefficient at every positive frequency other than the explicit pole frequency `sqrt(7/4)`. If the completed wave is bounded, the existing receiver implies RH; its temporal cosine coefficients then recover positive masses at actual zeta-zero frequencies. Therefore finite folded sums cannot approximate the completed wave uniformly on the entire rapidity half-line. The positive result is the exact temporal spectral classification, not merely nonconvergence.

### Paper proof

Use `A_T(f,λ) = ∫₀¹ f(Tt) cos(λTt) dt`. Its operator norm on bounded functions on the forward half-line is at most one for `T≥0`. Product-to-sum and the sine primitive give `A_T(cos(a·),λ) → 1/2` for `a=λ>0`, and zero for distinct positive frequencies. For an integrable spectral density, dominated convergence permits integration of this limit.

The Klein–Gordon frequency is `sqrt(r²+2)`. Each frequency fibre contains at most two real points, hence has Lebesgue measure zero. The explicit Fourier formulas therefore give zero temporal coefficient for `K_y(v)`, its first two spatial derivatives, and their conjugated combination. Their existing uniform bounds permit the same conclusion for every fixed bounded spatial integral and for the exponentially dominated remainder fold.

The pole law rewrites the tail exactly as
`exp(-v) * [P(y) - poleShadow(y) - ∫₀ᵛ K_y(s) exp(s/2) ds]`.
Consequently the only temporal atom of one fold is the pole mode, with coefficient `(γ+1) exp(-v)` times the pole mode's coefficient. In particular every finite fold combination has zero coefficient at every positive `λ ≠ sqrt(7/4)`.

The complete fold has the exact source identity
`F(y) = K_y(0) - poleShadow(y) - chmdArchWave(y)/(2π) + chmdWave(y)`.
The first three terms have zero temporal cosine coefficients. Under RH the last is the absolutely summable cosine series over actual zero frequencies, with strictly positive weights. At any actual zero frequency its coefficient is half the total matching weight, hence positive. Its frequency is at least `sqrt(2)`, distinct from the pole frequency.

If the complete fold has no uniform bound, no uniformly bounded finite fold can uniformly approximate it. If it is bounded, RH follows and the preceding positive coefficient separates it from every finite fold combination by a fixed positive sup-norm distance. This proves the proposed obstruction, provided the stated source identifications and analytic exchanges are checked in Lean.

**Current verdict:** SURVIVES PRELIMINARY ATTACK; paper mechanism fixed, Lean verification pending. This does not refute uniform boundedness of partial sums or of the completed wave. A valid all-scale argument may allow spectral atoms to emerge in a nonuniform limit.
