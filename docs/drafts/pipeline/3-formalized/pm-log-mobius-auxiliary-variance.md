# Logarithmic Möbius auxiliary variance and the canonical norm

- **ID:** pm-log-mobius-auxiliary-variance
- **Stage:** 3-formalized
- **Type:** PROVED EXACT CANONICAL SOURCE CONSTRAINT
- **Source:** Route PM; finite logarithmic floor inversion; half-line Fermi coercivity
- **Target:** Expose the literal arithmetic variance forced to vanish by canonical
  logarithmic Fermi convergence, without assuming a rate for a Möbius sum.
- **Status:** Refined whole-tail identity, canonical variance bound and mean/variance split formalized. RH remains open.

## Corpus evidence and missing step

The weighted endpoint now has a build-verified unconditional rate in `L²(t dt)`.
It does not remove the extra `t`. Existing `FermiNymanRawMobiusTailFloor` supplies
full-half-line coercivity `∫|E|² ≤ 6∫|E−2E(2·)|²`. Existing finite logarithmic floor
inversion supplies the exact head of a corresponding auxiliary Nyman error.
`Sieve.MoebiusLogarithmicNormalization.tendsto_sum_moebius_log_div_one` proves

`B_N := Σ_(d≤N) μ(d)log(N/d)/d → 1`.

That limit has no critical scale rate in its statement. It cannot be substituted
for the required norm estimate. Do not infer a zero-multiplicity obstruction from
the logarithmic-derivative Chebyshev head alone; its analytic pole orders need a
separate audit. No such obstruction is claimed here.

## Literal objects and candidate identities

For `N≥2`, let `L_N=log N`, `c_N=1/(N+1)` and

`E_N(t)=1_(0,1](t)+Σ_(d≤N) [μ(d)log(N/d)/L_N] ρ_d(t)`.

Here `ρ_d` is the existing literal fractional-part Nyman generator. Then:

1. `E_N(t)−2E_N(2t)=h(t)−A_N^log(t)` on `(0,1]`; it vanishes for `t>1`.
2. For `t>c_N`, floor inversion gives
   `E_N(t)=[B_N/t−ψ(1/t)]/L_N`.
3. `E_N` is measurable and square-integrable on `(0,∞)`: bounded on `(0,1]`,
   and exactly `B_N/(t L_N)` for `t>1`.
4. Inversion on `c_N<t≤1` gives the exact auxiliary head energy
   `L_N^(-2)∫_[1,N+1) |B_N−ψ(x)/x|² dx`.
5. The tail on `t>1` has exact energy `(B_N/L_N)²`. Coercivity therefore yields
   `6 E_Fermi(N) ≥ L_N^(-2)[B_N²+∫_[1,N+1)|B_N−ψ(x)/x|² dx]`.

All integrals must be proved integrable before use. Reciprocal endpoint conventions
must be checked explicitly; singletons may then be discarded using atomlessness.
The result is a necessary source condition, not a producer of convergence and not
an RH proof. Next paper audit should ask what actual corpus estimates can control
this variance, rather than replacing it by the scalar statement `B_N→1`.

## Search audit

- Deep dyadic-Chebyshev/multiplicity query: `partial=false`, no errors, complete
  63,545-file inventory. All 20 candidate and 20 source-argument statements read.
  Returned power bounds require an error spectrum or a zero half-plane bound.
- Focused logarithmic-Möbius harmonic/critical-energy query: `partial=false`, no
  errors, complete 63,548-file inventory; compiler metadata mostly pending/stale.
  All 20 candidate and 20 source-argument statements read. It returned exact
  normalization `B_N→1` and a boundedness theorem, but no matching critical rate.
  Suggested ingredient sets are unverified and supply no variance decay.
- Exhaustive source text search for logarithmic auxiliary-error/variance/coercivity
  names found no prior exact bridge. No novelty beyond reviewed source is claimed.

## Gates

- [x] Inspect exact existing source statements and record candidate before coding.
- [x] Dependency-closed paper proof and endpoint audit.
- [x] Scratch verification and Lean formalization.
- [x] Targeted build, final direct actual-leaf, all-declaration axioms, wiring/index/lint (unrelated global findings recorded below).
- [x] Search independent canonical source estimates and record the next exact candidate.

## Paper audit refinement

Invert the full auxiliary tail `t>c_N` in one step. Its exact energy should be

`L_N^(-2)∫_(0,N+1) (B_N−ψ(x)/x)² dx`.

This includes the `B_N²` term from `0<x≤1` and avoids splitting at `1` twice.
The source integrand is locally bounded even at its open zero endpoint because
`0≤ψ(x)≤(log 4+4)x` for `x>0`; thus its integrability does not depend on any
cancellation estimate. Prove the isometry and source integrability before the
coercivity transfer. This is an exact finite arithmetic variance, not a guessed
Mellin asymptotic. No conclusion about critical-line multiplicities is asserted.

A possible next positive refinement is the exact mean/variance decomposition. With
`R=N+1`, `f(x)=ψ(x)/x`, and `m_R=R⁻¹∫_(0,R)f`,

`∫_(0,R)(B_N−f)² = R(B_N−m_R)² + ∫_(0,R)(f−m_R)²`.

Thus scalar normalization and prime-profile fluctuations are separate nonnegative
budgets. This identity has an elementary dependency-closed paper proof by expanding
the square and using `∫(f−m_R)=0`; its exact specialization and all integrability
hypotheses still need Lean verification. It does not itself bound either budget.

Paper audit complete: finite floor inversion cancels the indicator exactly;
`Chebyshev.psi_eq_zero_of_le_one` gives the literal `1/t` tail. The global bound
on `ψ(x)/x` proves finite source integrability, while boundedness plus the `1/t`
tail proves square integrability of the auxiliary error. The reciprocal image of
`(c_N,∞)` is `(0,N+1)`, with no endpoint term. The dilation difference vanishes
on `(1,∞)`, so full-half-line coercivity transfers to the actual PM norm.
No asymptotic or zero-location assumption is needed for this candidate identity
and lower bound. Lean implementation remains pending.


2026-10-01 implementation log:
- Fresh hybrid search for the Nyman/Chebyshev variance bridge: `partial=false`, no
  errors, full 63,554-file inventory; all 20 candidate and 20 source-argument
  statements inspected. No exact bridge returned. Compiler metadata remains
  largely pending/stale, so source statements were checked directly.
- Scratch proof has accepted the general finite-real-coefficient Nyman error's
  measurability, square integrability, literal Fermi difference and canonical
  coercivity. It also accepted the logarithmic floor-inversion formula and
  `B_N→1` against the actual installed source. Reciprocal energy and mean/variance
  decomposition are in the current scratch check; no convergence is claimed.

- The reciprocal identity has passed scratch checking. It identifies the full
  auxiliary tail exactly with `logMobiusChebyshevVariance/log²N`, including the
  open endpoint and independent source integrability. The two-budget decomposition
  remains in the current complete scratch pass.
- Deep prime-square-error query completed: `partial=false`, no errors, complete
  63,556-file inventory; all 20 candidate and 20 source-argument statements read.
  Taper functions named `psi` are not `Chebyshev.psi`; their squared-integral
  estimates and the proposed ingredient set do not apply to the arithmetic target.
  `CCMPrimeDeficitChronologicalWork` was read in full: its storage identity retains
  unbounded signed chronological work, and its critical energy is built from the
  integrated deficit. It supplies no independent upper estimate for this variance.

- Deep Selberg/prime-correlation search: `partial=false`, no errors, complete
  63,557-file inventory. All 20 candidate and 20 source-argument statements read.
  Actual Selberg symmetry and `abs_psiRemainder_recursion` have an `O(N)` remainder;
  the second inequality retains weighted absolute remainders. Returned sieve
  mean-square estimates require `sigma>1` and do not match this critical source.
  No independent critical variance producer was found in these results. The
  suggested prime-support ingredient set supplies no variance bound.

- Complete scratch proof passed with empty diagnostics. Two new leaves:
  `FermiNymanFiniteCoefficientError` (8 declarations / 130 lines) and
  `FermiNymanLogMobiusAuxiliaryVariance` (23 declarations / 248 lines). The latter
  includes the exact reciprocal identity, canonical lower bound, mean/variance
  decomposition and separate estimates for both nonnegative budgets. All 31 names
  are unique, both imports unique, all API entries present once. Targeted build
  and final direct/axiom audits in progress.
- The next audited paper candidate is `pm-weighted-source-input-power-boundary.md`:
  a sharp power-family classification testing exactly the analytic hypotheses
  used in the weighted endpoint. It does not replace the actual prime profile or
  reject the logarithmic arithmetic sequence. No model Lean code has been written.

- Targeted old-mode build passed: finite-coefficient leaf 66s; auxiliary-variance
  leaf 72s. Final direct actual-leaf and all-declaration axiom checks follow.
  First `lint --check-generated` snapshot flags 12 unrelated unwired modules plus
  concurrent generated API/overview drift; neither new leaf is reported. Indexes
  refreshed again before the final plain lint snapshot.


## Final formalization certificate — 2026-10-01

The exported statement uses the refined full-tail form, combining the original
head and `t>1` contributions into one integral over `(0,N+1)`.

- `FermiNymanFiniteCoefficientError`: 8 declarations, 130 lines. Arbitrary finite
  real coefficient vectors have a literal square-integrable auxiliary error,
  exact Fermi difference, and full-half-line to canonical norm coercivity.
- `FermiNymanLogMobiusAuxiliaryVariance`: 23 declarations, 248 lines. Literal
  logarithmic auxiliary formula, `B_N→1`, source integrability, exact reciprocal
  energy, canonical variance lower bound, and the two-budget decomposition.
- Main identities: `integral_normSq_logMobiusNymanError_tail`,
  `logMobiusChebyshevVariance_le_six_error`,
  `logMobiusChebyshevVariance_decomposition`. Separate nonnegative bounds are
  `logMobiusNormalizationBudget_le_six_error` and
  `chebyshevProfileVarianceBudget_le_six_error`.
- `lake --old build +GaloisForLFunctions.RHTower.FermiNymanLogMobiusAuxiliaryVariance:olean`
  passed, building only the two owned leaves (66s and 72s); dependencies replayed.
- Final `lake env lean` on each actual leaf passed with empty diagnostics.
  All 31 separate `#print axioms` checks passed with only `propext`,
  `Classical.choice`, `Quot.sound`; both main theorem types checked explicitly.
- All 31 names unique, one umbrella import per leaf, all API entries present once;
  scoped whitespace clean. Indexes regenerated. First generated-file lint audit
  detected concurrent API/overview drift and 12 unrelated unwired modules.
  Indexes refreshed again; final plain lint exits 1 solely for those 12 modules.

Unrelated lint findings at the final snapshot: `CCMApertureChainProfile`,
`CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
`CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
`CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
`MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
`WeilFibreBochnerLaw`, `ZetaNotchTwistPolynomialEnvelope`, `ZetaZeroDensityPowerSaving`
(all in `RHTower`). No proof-debt or own-leaf finding was reported.

No upper estimate or canonical convergence has been proved. Four new corpus queries
were complete, with no errors; all 20 candidates and 20 source arguments from each
were inspected. The next paper candidate is
`1-in-progress/pm-weighted-source-input-power-boundary.md`: sharp classification of
what the currently used analytic inputs permit, including its positive optimal-
variance survivor. No model Lean code yet. The actual arithmetic/RH goal remains
active. No full or umbrella build, numerical experiment, added axiom, proof hole,
heartbeat increase, commit or push occurred.

Cleanup: all owned jobs completed. Both final leaf bodies match the verified
scratch source. All 23 owned temporary files removed after results were recorded.
