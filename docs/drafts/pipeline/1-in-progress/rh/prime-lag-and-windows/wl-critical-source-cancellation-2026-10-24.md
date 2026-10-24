# WL — critical cancellation in the actual prime source

- **ID:** wl-critical-source-cancellation-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md`, WL; literal Lean source.
- **Statement:** For every ε > 0, the actual logarithmic Chebyshev deficit
  `D(T) = ∫₀ᵀ (exp(t) − ψ(exp(t))) dt` admits a one-sided bound
  `D(T) ≤ Cε exp((1/2 + ε)T)` for all sufficiently large T.

## Goal

Derive the bound from actual prime arithmetic and discharge the existing WL
receiver. The full task ends only with an unconditional Lean proof of RH.
Another receiver, a numerical improvement, a model obstruction, or an exact
identity with an unpaid remainder does not complete this task.

## Constraints

No web searches, external novelty checks, or numerical experiments. No new
analytic assumptions, axioms, placeholders, or raised Lean resource limits.
Preserve unrelated work. Compile only individual required files with
`lake --old env lean` from `formal/`, one owned foreground process at a time.

## Established inputs inspected

- `RHTower.ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents`
  (`CCMPrimeDeficitPrimeWork.lean`):
  `D(T) = exp(T) − 1 − Σ(n ≤ exp(T)) Λ(n)(T − log(n))`.
- `RHTower.ccmPrimeDeficitCriticalEnergy_prime_work_balance`
  (`CCMPrimeDeficitPrimeWork.lean`):
  the full signed prime-entry work equals half the terminal critical energy
  plus half its accumulated integral. Its nonnegativity gives the opposite
  direction from the upper energy payment still required.
- `RHTower.ccmLogChebyshevDeficitPrimitive_scale_descent`
  (`CCMPrimeDeficitScaleDescent.lean`):
  the higher-power sector is a half-radius copy plus an explicitly bounded
  positive cubic-root remainder. The prime-only same-scale deficit remains.
- `PrimeWindowCeilingVinogradovKorobovRemainder`:
  the unconditional envelope is `C exp(T − κ T^a)`, `0 < a < 3/5`.
  Its leading exponent remains 1.

The five declarations listed in the verification section received a fresh
dependency audit. Other observations here remain source inspections.

## Direct attack

Keep the complete signed arithmetic source together. Investigate the exact
Selberg convolution and the Möbius inversion of factorial/logarithmic tents
before applying absolute values. Seek cancellation of the full same-scale
remainder, including the moving hyperbola boundary. The first unproved step
must remain explicit; it must not become a premise of a claimed solution.

**[OPEN CORE]** Obtain an unconditional critical-scale upper estimate for the
signed remainder of the actual prime source. Existing prime-power descent
does not estimate the prime-only same-scale term.

## Gates

- [x] Exact source and missing estimate identified.
- [ ] Dependency-closed paper proof of the source estimate.
- [ ] Lean formalization, direct final compilation, and transitive axiom audit.
- [ ] Existing WL receiver discharged and unconditional RH conclusion audited.

## Research status

Active. No claimed source estimate or RH proof. External and novelty audits
are deliberately omitted under the user's instruction.

## Direct-attack findings

The existing finite identity `ccmLogChebyshevDeficitPrimitive_dilation_conservation`
already gives, with `x = exp(T)` and `N = floor(x)`,

```
Σ(n ≤ x) D(log(x/n))
  = x H_N − N − Σ(k ≤ x) log(k) log(x/k) =: S(T).
```

`ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation` is its exact inverse.
`abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le` already proves

```
|D(T) − (explicitWork(T) + L M(floor(exp(T))) + transientTail(T))|
  ≤ (T + 14)/4.
```

Thus eliminating the small-divisor transient is not new work. The signed
combination inside the parentheses still needs the critical-scale estimate;
estimating its terms separately has not supplied it.

For clarity, the ordinary Laplace transforms for real `s > 1` can be derived
directly from the absolutely convergent prime series:

```
Laplace(D)(s) = 1/(s(s−1)) + ζ'(s)/(s² ζ(s)),
Laplace(S)(s) = ζ(s)/(s(s−1)) + ζ'(s)/s².
```

Indeed, integration of `exp(T) − 1` gives `1/(s(s−1))`, integration of each
tent `(T−log n)_+` gives `n^(−s)/s²`, and
`Σ Λ(n)n^(−s) = −ζ'(s)/ζ(s)`. Multiplicative delays multiply the transform
by `ζ(s)`. Absolute convergence for `s > 1` justifies these interchanges.
This calculation is an explanatory paper observation, not a new Lean theorem.
It supplies no justification for moving the inverse transform into the
critical half-plane. Such a move needs the unresolved source estimate or an
independently proved continuation, not division by `ζ` across possible zeros.

The inspected Selberg formula has a remainder bounded by `410N`, not by
square-root scale. The Euler half-logarithmic balance retains the deleted-prime
work and the lower-order surviving-prime work with opposite signs. Neither
their nonnegativity nor the half-logarithmic force estimate bounds the complete
signed difference. No term has been dropped from the requested estimate.

**Outcome:** no significant obstacle closed in this pass. These observations
are a record of the exact unfinished argument, not an additional criterion or
a claimed new no-go. The next proof step must estimate the complete long-tail
combination from the actual Möbius/prime arithmetic. Repeating the established
inversion, diagonal bound, or small-divisor estimate would not advance it.

## Verification

From `formal/`, the focused command
`lake --old env lean /tmp/wl-critical-source-audit-2026-10-24.lean`
exited 0. It checked the full types and printed transitive axioms of:

- `RHTower.ccmPrimeDeficitCriticalEnergy_prime_work_balance`
- `RHTower.ccmLogChebyshevDeficitPrimitive_scale_descent`
- `RHTower.abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le`
- `RHTower.ccmLogChebyshevDeficitPrimitive_sub_eulerAction_halfLog_balance`
- `RHTower.selberg_symmetry_formula`

Each reported exactly `{propext, Classical.choice, Quot.sound}`. These certify
the existing identities and bounds only; they do not certify the missing
critical cancellation or RH. No repository Lean source or umbrella was added
or edited by this pass.

Final direct source audit:
`lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPrimeDeficitMobiusTailLocalization.lean`
exited 0 with empty output. The five inspected source files and both route
reports remain unchanged. The owned temporary audit file was removed.

## Continuing conjecture loop: short arithmetic action

The current worktree contains a newer unconditional input:
`BezoutValuationIncidence/TheMoebiusPrimitiveEnergyGrowsLinearly.lean`,
`tendsto_twelve_mul_sievePrimitiveEnergy_moebius_div`. Its full-period canonical
primitive energy is asymptotic to a constant times N. This is a different
observable from WL's deficit; its name alone supplies no transfer.

The corpus also already proves
`abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le`: the complete
deficit differs from a quadratic expression in μ(1), …, μ(floor(exp(T/2))) by
at most `7 exp(T/2)`. The source matrix is the literal divisor source, including
all pole terms. This makes the following source-specific conjecture concrete:

**C1 — critical control of the short arithmetic action.** There are C > 0 and
an integer k ≥ 0 such that, at every T ≥ 0,

```
ccmPrimeDeficitShortQuadraticWork(T)
  ≤ C (1+T)^k (1 + sievePrimitiveEnergy(floor(exp(T/2)), μ)).
```

The bound would discharge the existing WL positive-slack target using the new
linear energy theorem. It is an unproved conjecture about the actual μ row,
not a new conditional Lean result. Neither an identity nor the energy limit
proves this inequality.

**First attack.** `CompletePeriodQuadraticFormsAreOrientationBlind.lean`
shows that complete-period readings preserve squared Selberg coordinates and
lose their signs. This does not refute C1 for actual μ. It does prevent treating
the period energy as a reconstruction of the signed WL action. Likewise
`PronicEnergyTailAtTheQuadraticHorizon.lean` controls the weighted far tail of
the canonical primitive, not the reciprocal reflection at the moving cutoff.
No norm transfer has been assumed.

**C2 — retain the signed reflection rather than its separate norms.**
`CCMPrimeDeficitShortReflection.lean` gives the complete action as
`shortReflectedMainWork + shortReciprocalPairing + shortReciprocalErrorWork`.
The pairing is an integral of two actual Möbius-weighted sawtooth profiles at
s and T−s, one with the logarithmic coefficient `(T/2−1−log n)`. A direct
candidate proof of C1 must bound this complete combination; estimating the
three terms independently has not justified critical-scale control.

**C3 — complete the pole before estimating the reflection.**
`CCMPrimeDeficitCompletePole.lean` already isolates the full rank-two pole:

```
exp(T) ((c T+d) m0² − 2 c m0 m1),   c = γ+1,
m0 = Σ v_i exp(−u_i),   m1 = Σ v_i u_i exp(−u_i).
```

Its remaining matrix bound costs `(1+T)² (Σ|v_i|)²`, which is still of
exponential order 1 for an actual square-root-length μ row. Removing the pole
again is therefore rediscovery. The live question is whether the literal
signed row and its short linear main term permit an upper bound by primitive
energy; arbitrary-row phase erasure cannot be substituted for that proof.

Status: C1 remains open. C2 and C3 specify attempted proof mechanisms and their
first missing steps, not additional claimed results. No premise was inserted
into Lean, and no route has been retired.

## Further source checks and attempted transfers

The following checks used the corpus search and then the actual Lean statements.
They do not constitute new proofs or a closure of WL.

- `CCMPrimeDeficitNeutralWork.lean` already supplies a diffuse harmonic-neutral
  extension of the literal short Möbius row. Its full action is exactly D;
  its linear work and absolute diagonal have critical polynomial budgets.
  The remaining signed quadratic work includes all mixed and negative-time
  terms. Reconstructing this extension would repeat existing work.
- `CCMPrimeDeficitShortSourceMatrix.lean` proves that the actual two-index
  source matrix at `T = 2 log 2` has determinant -1. A generic positive
  semidefinite source-matrix argument cannot be substituted for an estimate
  on the literal arithmetic row. This does not disprove C1.
- `MobiusDivisorMonotoneSignLaw.lean` proves a nonpositive Möbius divisor-pair
  section against nonnegative decreasing weights of `m+n`. The reciprocal
  WL action has a product cutoff and also contains non-comparable pairs.
  No sign-preserving transfer covering those terms was obtained.
- `CCMFUSuzukiCriticalChordMeasure.lean` proves positivity of
  `suzukiCriticalRenormalizedMobiusRieszProducer` by identifying it with the
  positive atomic chord. The polar chord is a separate positive quantity;
  neither positivity statement bounds their signed difference.
- `TheMoebiusEnergyTransfersAtEverySuperlinearHorizon.lean` controls
  `sieveL2PrefixEnergy`, the mean square of the divisor-sieve sequence.
  It is not a theorem about its primitive's pronic energy or WL's reciprocal
  pairing. No integration estimate with the required constants has been
  proved here.
- `AnIndexFormulaForTheActualReceiver.lean` obtains index zero and reverse
  hull inclusion above `zetaZeroAbscissa - 1/2`. Its all-positive-damping
  assertion is an RH equivalence. The title does not discharge the width.

### Attempt to iterate known compensation

`ArithmeticCompensationTheory/ATwoScaleCompensationRate.lean` proves, on the
common head, a power bound for changing the Ramanujan coefficient cutoff:

```
twoScaleCompleteShiftEnergy ε P Q P ≤ Cε P^(1-3ε),   Q ≥ P ≥ 1.
```

The proof cancels the same cutoff-independent divisor remainder from both
approximants. It therefore estimates an approximation difference, not that
remainder. The summable projection changes in
`TheCompensatingProjectionMovesSummablyAcrossScales.lean` likewise concern
relative compensation coordinates. Multiplication by the growing sector
energy is still present in the absolute work. No contraction for the newly
added horizon shell, or for the complete WL action, follows from these
statements alone. The attempted direct iteration has not closed its first
missing estimate; no stronger conclusion is being attributed to these files.

## C4 — complete dyadic increment, including the new prime shell

Put `G(x) = D(log x)` for `x ≥ 1`. A concrete next conjecture is that some
`C > 0` and integer `k ≥ 0` satisfy

```
G(4x) - 2 G(x) ≤ C sqrt(x) (1+log x)^k,   x ≥ 1.
```

This is an unproved source estimate to attack, not a conditional Lean
criterion to add. The existing prime-tent identity gives its complete
arithmetic expression:

```
G(4x) - 2 G(x)
  = 2x + 1
    - Σ(n ≤ x) Λ(n) log(4n/x)
    - Σ(x < n ≤ 4x) Λ(n) log(4x/n).
```

Both sums include every prime power. The first kernel changes sign at x/4,
so a theorem about the new shell alone would not estimate the increment.
The identity is obtained by subtracting the two existing finite prime-tent
formulas; no limit, analytic continuation, or zero-free assumption is used.

Why this particular estimate matters: write `x = 4^j u`, `1 ≤ u < 4`, and
divide the increment by `2 sqrt(x)`. Summing along that orbit would bound
`G(x)/sqrt(x)` by a bounded initial value plus
`(C/2) Σ(i<j) (1+log u+i log 4)^k`, hence by a polynomial of degree k+1 in
`log x`. This explains the target; it does not prove its arithmetic bound.

**First unpaid step:** control the old signed prime-prefix work together
with the newly added shell at square-root scale. The inspected compensation
theorem keeps the evaluation horizon fixed and cancels its common remainder;
C4 changes the evaluation horizon, so that cancellation cannot be invoked.
The corpus's subexponential PNT error still has leading exponent 1 in x.

No new Lean theorem, significant obstacle closure, or unconditional RH
conclusion was obtained in this batch. C1 and C4 remain live conjectures;
their failed proof mechanisms are recorded to prevent repetition.
