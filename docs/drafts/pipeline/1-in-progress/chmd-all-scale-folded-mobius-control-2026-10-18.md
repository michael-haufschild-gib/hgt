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

1. [done for current candidates] Audit exact source, kernel, prior conjectures, and all-scale receivers using the local research search and actual Lean declarations.
2. [in progress] State competing precise cancellation conjectures; attack their quantifiers, source fidelity, and prior-corpus overlap.
3. [done for finite-fold spectral classification] Complete a dependency-closed paper proof before formalization; the all-scale arithmetic bound remains open.
4. [done for spectral classification and separation] Seven leaves compile; both final leaves pass direct `lake --old env lean` checks; five theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella wiring and generated indexes updated. Global lint retains two unrelated tree errors, recorded on the failed-route card.
5. [in progress] Reassess whether the actual target is proved; continue conjecturing if it remains open. The requested all-scale bound remains unproved.

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

## Corrected corpus baseline

Local research search and direct source inspection recover stronger existing producers than the first pass recorded:

- `MobiusDivisorPaidPrimeExhaustion`: unconditional exhaustive insertion with every prefix paid at its own proportional clock.
- `MobiusDivisorExhaustiveClockCheckpoints`: nested exhaustive cores, universal full logarithmic energy bound at geometric checkpoints, and fourth-root cutoff collars.
- `MobiusDivisorTerminalClockOrder`: complete terminal insertion orders bounded by the larger actual endpoint; the completed source square remains explicit.
- `MobiusDivisorGrowingDepthCurrentPayment`: unconditional logarithmic-size omitted-prime payment over the initial core.
- `MobiusDivisorWeightedCutoffDiagonal`: exact signed correlation and self-square in cutoff evolution.

Do not rebuild these producers or infer an all-scale bound from their incompatible cutoff/core quantifiers. The unresolved scheduling obligation is signed drift and earlier completed action across changing cutoffs. Generic summable-spectrum Bohr extraction is also already available in `HTGeometry/ExponentialSeriesFiberwise` and `SummableSpectrumScrewBohrCoefficients`; the finite-fold work below only applies that spectral distinction to this specific transport.

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

If the complete fold has no uniform bound, no uniformly bounded finite fold can uniformly approximate it. If it is bounded, RH follows and the preceding positive coefficient separates it from every finite fold combination by a fixed positive sup-norm distance. The source identifications and analytic exchanges are now checked in Lean.

**Current verdict:** UNIFORM APPROXIMATION SHORTCUT RETIRED; exact positive-frequency atom classification and unconditional uniform separation formalized. See [failed-route card](../5-failed/chmd-uniform-fold-approximation-2026-10-18.md) for the exact theorem, positive survivor, paper proof, prior-work audit, and verification limits. This does not refute uniform boundedness of partial sums or of the completed wave. A valid all-scale argument may allow spectral atoms to emerge in a nonuniform limit.

## Next arithmetic candidate: bounded supported Möbius rows

The existing `selbergMobiusCoeff N m` is supported on `1 ≤ m ≤ N`, has absolute value at most one, and tends to `μ(m)` at every fixed index. Test the precise claim

`∃ C : ℝ, ∀ N ≥ 2, ∀ y ≥ 0, |Σ_{m=1}^N selbergMobiusCoeff N m * mobiusFold y (log m)| ≤ C`.

Fixed-rapidity absolute summability makes pointwise passage to the complete fold available. The missing work is the bound itself. Uniform approximation is neither needed nor compatible with the proposed atom classification. Existing Selberg total-energy estimates retain a growing diagonal/remainder; bounded coefficients alone do not pay them. Do not formalize the easy pointwise-limit receiver as an arithmetic advance. First attack the actual signed spectral density or source pairing of these already-defined rows, with pole and all-scale tail retained.

## Existing one-sided source target recovered across routes

The corpus already contains a sharper sufficient signed comparison than an absolute bound on the neutral quadratic work. `ChebyshevDeficitPrimitiveOneSidedRH.lean` proves RH from either envelope `±D(T) ≤ B(1+T) exp(T/2)` for every `T ≥ 0`. The TG audit in `tg-native-covariance-transfer-2026-10-15.md` already checked its application to the short work and the neutral decomposition in Lean. This is recovered existing work, not a new receiver to formalize.

For the literal neutral coefficient vector, retain the exact `D(T) = L(T) - Q(T)`. The sufficient arithmetic comparison is

`∃ B : ℝ, ∀ T ≥ 0, Q(T) ≥ L(T) - B(1+T) exp(T/2)`

(or `Q(T) ≤ L(T) + B(1+T) exp(T/2)`). It includes every unequal-label term and retains the actual linear work. Its existing quadratic-polynomial envelope cannot be silently replaced by a linear envelope. The comparison remains unproved.

The same prior audit records why coefficient-tail redesign and an assumed variational minimum do not pay this comparison. The head-extension action is stationary, but its complete Hessian is signed. Paid linear and diagonal channels do not control the complete quadratic form. Preserve those prior failures when attacking this specific source estimate.

## Applicability attack: terminal cancellation versus all-scale transfer

Candidate mechanism: use the exact child-cofactor cancellations from the Euler-deletion route to control the complete wave. The corpus already proves terminal composite-level vanishing and a high-clock leakage bound `N²/(clock(l)+1)` for arbitrary coefficients of absolute value at most one. Neither fact alone estimates the earlier simultaneous signed tails.

A stronger indexing check is required before using any terminal child theorem: `historyLayer_predictableDrift_eq_reverse_tail` sums only over `l < i < N`. At `N=l+1`, this is empty, so the entire terminal drift layer vanishes at every level, including prime levels. Paper proof: apply the existing reverse-tail identity and use the empty index condition. A scratch Lean applicability audit is running; this is a consequence of existing work, not a new arithmetic cancellation theorem.

The nonempty target must retain `N > l+1`. For the separate geometric-checkpoint attempt, clock energy only samples cofactors disjoint from the processed core. The existing terminal classification `mobiusDivisorFiniteClockEnergy_terminal` leaves the current head square and omitted-prime singleton squares. Old processed cofactors are absent, so those coordinates cannot directly recover earlier completed cutoffs.
