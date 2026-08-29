# Arithmetic-progression Li criterion and even square-source reduction

- **ID:** LI-AP-SQUARE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `LiCriterion.lean` · `LiPositivityFails.lean` · `LiPairedPrimeArchShiftedMomentLanding.lean`
- **Statement:** For every fixed `k > 0`, RH is equivalent to nonnegativity of the paired Li coefficients only at degrees `k n`; at `k = 2`, the exact source polynomial at degree `2(n+1)` is `u(4-u) U_n(1-u/2)^2`.

## Goal

Compress Route LI to one fixed arithmetic progression and then to one weighted-square family in the completed prime--Gamma quarter-shift moment functional. This is source-pure: the final open input is nonnegativity of explicit finite combinations of `primeArchShiftedReciprocalMoment (1/4) j`, with no Xi divisor coordinate in the statement.

Full RH chain:

`completed prime--Gamma quarter-shift moments`
`→ source functional on u(4-u) U_n(1-u/2)^2 for every n`
`→ nonnegative paired Li coefficients at every even positive degree`
`→ arithmetic-progression Li criterion`
`→ RH`.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem names, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus origin and hostile audit

`scripts/formal_tools.py research` exposed the exact combination that generated the conjecture:

- `exists_re_tsum_liTerm_neg`: a bounded reciprocal family with square-summable defect and one point outside the unit circle has a negative paired Li sum at some degree;
- `riemannHypothesis_of_forall_re_xiLiPaired_nonneg`: applies that dominance theorem to `xiRootV`;
- `xiLiPaired_eq_liPrimeArchShiftedMomentSource`: lands every paired Li coefficient on a finite quarter-shifted prime--Gamma moment polynomial;
- `liShiftedMomentPolynomial`: identifies that polynomial as `2 - 2 T_d(1-u/2)`.

No corpus declaration returned a fixed-step Li subsequence criterion or the even weighted-square landing. Searches included `paired Li coefficients arithmetic progression fixed step sparse criterion Riemann hypothesis`, `xiLiPaired subsequence multiples every kth coefficient nonnegative`, and `Li criterion cofinal degrees sparse degree family`.

Literature audit through 2026-08-29 checked Li's original all-degree criterion, Bombieri--Lagarias's abstract multiset criterion, later generalized/modified Li criteria, and searches for `even Li coefficients`, `subsequence of Li coefficients`, and `Li criterion arithmetic progression`. These sources state all-degree positivity or different sparse/window criteria; no fixed-step theorem or even Chebyshev-square source identity was found. A July 2026 result proves a bounded-gap/long-block criterion under false RH, but that does not force a negative coefficient in any prescribed residue class.

## Attack

For fixed `k > 0`, replace every reciprocal coordinate `w` in the corpus dominance theorem by `w^k`. The defect remains square-summable by `norm_pow_sub_one_le`, a common norm bound becomes its `k`th power, and an exterior point remains exterior. The algebraic identity

`liTerm (w^k) n = liTerm w (k n)`

forces the negative degree produced by dominance to lie in `kℕ`. Specializing `k = 2` and using

`1 - T_{2m}(x) = 2(1-x^2) U_{m-1}(x)^2`

with `x = 1-u/2` yields

`2 - 2T_{2(n+1)}(1-u/2) = u(4-u) U_n(1-u/2)^2`.

## Open core

Formalization items 1--3 are closed. Remaining hard Route-LI producer is unconditional positivity of the weighted-square source family `liPrimeArchEvenSquareSource`; by the final equivalence, that assertion is exactly RH and cannot be replaced by a generic positive-measure premise without circularity.

## Paper proof

**[PROVED HERE]** Fix `k ≥ 1`. Write the multiplicity-exact paired Li family in the corpus normalization as

`Λ_d = Σ_ρ m_ρ (2 - w_ρ^d - w_ρ^{-d})`,

where the reciprocal representative satisfies `|w_ρ| ≥ 1`, is uniformly bounded, and

`Σ_ρ m_ρ |w_ρ - 1|² < ∞`.

These facts, including absolute convergence of each paired sum, are unconditional corpus theorems. If RH holds, every `|w_ρ| = 1`, so every summand has nonnegative real part and hence `Re Λ_{kn} ≥ 0` for every `n`.

Conversely, suppose RH is false. Then some `ρ₀` has `|w_{ρ₀}| > 1`. Put `v_ρ = w_ρ^k`. We have `|v_ρ| ≥ 1`, a uniform bound `|v_ρ| ≤ M^k`, and `|v_{ρ₀}| > 1` because `k ≥ 1`. Moreover,

`|w^k - 1| ≤ k max(1,|w|)^k |w-1|`,

so the common bound on `|w|` gives

`Σ_ρ m_ρ |v_ρ - 1|² < ∞`.

Apply the corpus abstract dominance theorem `exists_re_tsum_liTerm_neg` to `(v_ρ)`. It gives an `n` with

`Σ_ρ m_ρ Re(2 - v_ρ^n - v_ρ^{-n}) < 0`.

But powers and inverses commute, hence

`2 - v_ρ^n - v_ρ^{-n} = 2 - w_ρ^{kn} - w_ρ^{-kn}`.

Therefore `Re Λ_{kn} < 0`, contradicting nonnegativity on the fixed progression. This proves

`RH ↔ ∀ n, Re Λ_{kn} ≥ 0`.

For the even source identity, set `m=n+1` and `x=1-u/2`. The standard polynomial identities

`T_{2m}(x)=2T_m(x)²-1`,

`T_m(x)²-1=(x²-1)U_{m-1}(x)²`

give

`2-2T_{2(n+1)}(x)=4(1-x²)U_n(x)²`.

Direct expansion gives `4(1-(1-u/2)²)=u(4-u)`. Thus

`liShiftedMomentPolynomial (2(n+1))(u) = u(4-u)U_n(1-u/2)²`.

The corpus theorem `xiLiPaired_eq_liPrimeArchShiftedMomentSource` applies the same finite polynomial coefficient-by-coefficient to the completed prime--Gamma quarter-shift moment tower. Combining it with the `k=2` criterion proves the announced source-only equivalence and the full chain in `Goal`. No dependency remains open in this theorem.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.LiArithmeticProgressionSquareSourceCriterion`

- `exists_re_tsum_liTerm_neg_on_multiples`
- `riemannHypothesis_of_forall_re_xiLiPaired_mul_nonneg`
- `riemannHypothesis_iff_forall_re_xiLiPaired_mul_nonneg`
- `riemannHypothesis_iff_forall_re_xiLiPaired_mul_succ_nonneg`
- `liShiftedMomentPolynomial_two_mul_eq_weighted_chebyshevU_square`
- `xiLiPaired_two_mul_eq_liPrimeArchEvenSquareSource`
- `riemannHypothesis_iff_forall_re_liPrimeArchEvenSquareSource_nonneg`

Audit on 2026-08-29:

- `lake env lean GaloisForLFunctions/RHTower/LiArithmeticProgressionSquareSourceCriterion.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.LiArithmeticProgressionSquareSourceCriterion` — PASS
- `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions.RHTower`
- repository lint scan reports no defect in this module and recognizes it as reachable; global exit remains nonzero because unrelated concurrently present modules are missing from the `RHTower` and `HTGeometry` umbrellas

## Log

- 2026-08-29 — conjecture frozen after corpus-first and literature hostile audit; frontier map left untouched.
- 2026-08-29 — paper proof closed; promoted to Stage 2.
- 2026-08-29 — Lean formalization and targeted build completed; promoted to Stage 3.

## Reflection-quotient no-go and positive survivor

### Corpus origin and RH chain

Follow-up searches with `scripts/formal_tools.py research` found:

- the corpus hard-edge antipodal decomposition and Chebyshev diagonalization in
  `XiShiftedHardEdgePrimeGammaAntipodalPolarization`;
- adaptive first-contact producers and transverse capacity in
  `XiShiftedStrictFrontierNativeSourceContactResidue` and
  `XiShiftedHardEdgeAdaptiveSourceTransversality`;
- generic diagonal-versus-PSD countermodels in `HankelGuardrailCounterexamples` and
  `SuzukiJumpKernelLoewnerGap`.

This generated conjecture LI-RQ1: the fixed even-LI family lives in the reflection-even hard-edge
quotient, so an adaptive full-Hankel first-contact argument cannot transfer to it without an
additional source-specific quotient law.

Exact RH chain preserved by the survivor:

`completed prime--Gamma functional controlled on reflection-even LI coordinates`
`→ Re(liPrimeArchEvenSquareSource n) ≥ 0 for every n`
`→ arithmetic-progression Li criterion`
`→ RH`.

The result kills the tempting larger chain

`generic LI diagonal positivity → full hard-edge square positivity → adaptive Hankel positivity`,

at its first implication. Future work must stay in the reflection-even quotient and use actual
prime--Gamma arithmetic; generic moment-cone or adaptive-contact algebra is insufficient.

Literature audit through 2026-08-29 checked Li/Keiper--Li criteria, Bombieri--Lagarias, generalized
Li coefficients, and Chebyshev representations. Standard sources contain the critical-line
sine-square identity, but the audit found no fixed-even hard-edge reflection-quotient
classification or this signed-moment transfer no-go.

### Paper proof

**[PROVED HERE]** Let

`Q_n(u) = u(4-u) U_n(1-u/2)^2`.

Under `u ↦ 4-u`, the hard-edge weight is unchanged and the Chebyshev argument changes sign.
Since `U_n(-x)=(-1)^n U_n(x)`, squaring removes the sign, hence `Q_n(4-u)=Q_n(u)` for every `n`.

For real `a`, define the signed two-atom moment functional

`L_a(P) = Re(P(a)) - Re(P(4-a))`.

Every reflection-invariant polynomial lies in its kernel, so `L_a(Q_n)=0` for every `n`. Taking
`a=1` and the different hard-edge square `W(u)=u(4-u)u^2` gives

`L_1(W)=W(1)-W(3)=3-27=-24<0`.

Thus one literal signed moment functional is nonnegative on the entire even-LI family but negative
on another hard-edge weighted square. Generic diagonal positivity cannot imply full hard-edge
square positivity. Finally, `deg Q_n=2(n+1)`; distinct degrees prove linear independence of every
finite initial LI family. The quotient removes a genuine blind sector but does not make the
surviving LI coordinates redundant.

### Lean certificate

Module: `GaloisForLFunctions.RHTower.LiEvenSquareReflectionBlindnessNoGo`

- `liHardEdgeReflection_involutive`
- `liHardEdgeReflection_liEvenShiftedSquarePolynomial`
- `liHardEdgeReflectionBlindFunctional_eq_zero_of_invariant`
- `exists_liEvenSquare_nonnegative_blindFunctional_not_hardEdgeSquare_nonnegative`
- `natDegree_liEvenShiftedSquarePolynomial`
- `linearIndependent_liEvenShiftedSquarePolynomial`

Audit on 2026-08-29:

- `lake env lean GaloisForLFunctions/RHTower/LiEvenSquareReflectionBlindnessNoGo.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.LiEvenSquareReflectionBlindnessNoGo` — PASS
- `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions.RHTower`
- formal lint finds no defect in this module and recognizes it as reachable; repository-wide exit
  remains nonzero only because unrelated concurrent modules are absent from the RHTower and
  HTGeometry umbrellas

### Consequence

LI first-contact conjecture through generic adaptive Hankel positivity is retired. Positive
survivor is precise: seek an arithmetic inequality or transport law for the actual completed
prime--Gamma functional after hard-edge reflection symmetrization. Anti-invariant source control
cannot contribute to the even-LI criterion, while the independent invariant coordinates remain
RH-complete by the fixed-step theorem above.

## LI-XP1/LI-XP2: fixed prime--Gamma cross balance and localized heat producer

### Corpus origin and full RH chain

Further conjecturing used only `scripts/formal_tools.py research`. Load-bearing corpus declarations
were:

- `routeUShiftedCompletedPrimeGammaBalance_eq_pi_mul_trace` and
  `exists_routeUShiftedCompletedPrimeGammaCrossBalance_neg_of_crossCapital_neg`;
- `eval_routeUHardEdgeCommonLeftReversedPolynomial`,
  `eval_routeUHardEdgeCommonRightReversedPolynomial`, and
  `eval_routeUHardEdgeDegreePaddedReversedPolynomial`;
- `momentFunctional_sq_ofFn`, `dotProduct_mulVec_momentHankelMatrix`, and the unconditional
  `hasDerivAt_xiGaussianHeatMoment` ladder.

These generated LI-XP1 and LI-XP2. For `Pₙ=Uₙ`, `Qₙ=(1-X)Uₙ`, quarter shift, and the
corpus common-degree reversal, prove

`completed cross balance ≥0 for every n,t`
`→ filtered cross capital ≥0`
`→ reciprocal-Hankel cross bilinear ≥0`
`→ Re(liPrimeArchEvenSquareSource n) ≥0`
`→ fixed-step Li criterion`
`→ RH`.

The reverse chain follows from RH because the two common reversals have nonnegative product at every
real squared spectral coordinate. Thus this fixed source family is exactly RH-complete, not merely a
sufficient source cone.

### Exact new identities

**[PROVED HERE]** At reciprocal-Hankel level,

`Re(liPrimeArchEvenSquareSource n) = 2 · crossBilinear₁/₄(Pₙ,Qₙ)`.

The common reversal degree is exactly `n+1`. If `Bₙ` is the intrinsic degree-`n` reversal of
`Uₙ`, then the two padded reversals factor exactly as

`Lₙ(W) = (W+1/4) Bₙ(W)`,

`Rₙ(W) = 2W Bₙ(W)`.

Consequently their product is the Stieltjes-localized square

`Lₙ Rₙ = 2W(W+1/4)Bₙ²`.

For positive heat time, polynomial trace polarization is exactly the moment functional of the
product. Hence the literal completed prime--Gamma cross balance is

`Crossₙ(t) = 2π Lₜ(W(W+1/4)Bₙ²)`.

Writing `Fₙ(t)=Lₜ(Bₙ²)`, the unconditional Gaussian moment derivative ladder gives

`Fₙ'(t) = -Lₜ(WBₙ²)`,

`Fₙ''(t) = Lₜ(W²Bₙ²)`,

and therefore

`Lₜ(W(W+1/4)Bₙ²) = Fₙ''(t) - (1/4)Fₙ'(t)`.

This closes two exact endpoint theorems:

`RH ↔ ∀ n,t>0, Lₜ(W(W+1/4)Bₙ²) ≥ 0`,

`RH ↔ ∀ n,t>0, Fₙ''(t) - (1/4)Fₙ'(t) ≥ 0`.

The remaining proof burden is now a single source-side differential inequality for the actual
completed prime--Gamma functional. Polynomial identities, heat differentiation, common-degree
padding, and zero-side landing are closed. Corpus hostile audit also found that the tempting global
right-even-factorization producer is already formally false
(`not_completedOddLogDerivPolynomialRightEvenFactorization`), so it cannot discharge this sign.

### Literature hostile audit

Audit through 2026-08-29 checked Li/Bombieri--Lagarias, Lagarias's Weil-functional formulation,
the Chebyshev-`U` integral/sum formulas of He--Jejjala--Minic, and Suzuki's model-space norm
criterion. Existing literature contains Chebyshev representations of Li coefficients and
RH-conditional norm identities. He--Jejjala--Minic explicitly flag the branch/criticality issue in
their derivation. The audit found no unconditional identity expressing each fixed even Li source as
the above positive-time completed prime--Gamma cross balance, no common-reversal factorization
`((W+1/4)Bₙ,2WBₙ)`, and no equivalent differential family
`Fₙ''-(1/4)Fₙ' ≥0`. Novelty remains subject to external expert review.

### Lean certificate

Module: `GaloisForLFunctions.RHTower.LiEvenSquarePrimeGammaCrossBalanceCriterion`

- `re_liPrimeArchEvenSquareSource_eq_two_mul_crossBilinear`
- `riemannHypothesis_iff_liEvenPrimeGammaCrossBalanceNonnegative`
- `liEvenCross_leftReversedPolynomial_factor`
- `liEvenCross_rightReversedPolynomial_factor`
- `xiPolynomialGaussianHeatTraceReal_eq_momentFunctional_sq`
- `xiPolynomialGaussianHeatCrossTraceReal_eq_momentFunctional_mul`
- `liEvenPrimeGammaCrossBalance_eq_two_pi_mul_localizedHeatSource`
- `liEvenStieltjesLocalizedHeatSource_eq_secondDeriv_sub_quarter_deriv`
- `riemannHypothesis_iff_liEvenStieltjesLocalizedHeatSourceNonnegative`
- `riemannHypothesis_iff_liEvenBaseHeatDifferentialNonnegative`

Audit on 2026-08-29:

- `lake env lean GaloisForLFunctions/RHTower/LiEvenSquarePrimeGammaCrossBalanceCriterion.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.LiEvenSquarePrimeGammaCrossBalanceCriterion` — PASS
- key `#print axioms` checks — only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions.RHTower`; no umbrella build run
- formal lint finds no forbidden declaration and recognizes this module as reachable; global lint
  failure is limited to unrelated concurrently present modules missing from umbrellas

### Consequence

LI-XP1 is closed as an exact fixed completed-source criterion. LI-XP2 isolates the genuine hard
producer: prove completed prime--Gamma positivity on `W(W+1/4)Bₙ²`, equivalently the heat
differential inequality above. Generic Hankel positivity, derivative-ladder algebra, or the already
refuted global even-factorization interface cannot supply it; future work must exploit arithmetic
structure of the literal prime and Gamma terms.
