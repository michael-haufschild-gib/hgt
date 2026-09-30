# Finite Euler deletion has a sharp terminal Hilbert scale

- **ID:** `theta-prime-deletion-graded-terminal-admission`
- **Stage:** 3-formalized
- **Type:** THEOREM and graded source-transport boundary
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN 4] [NOT AN RH PROOF]`
- **Dependencies:** the exact finite-prime source expansion in [prime-deletion spectral escape](theta-prime-deletion-spectral-escape.md); the all-order theta first-atom approximation in `ThetaCuspFirstAtomAllOrderApproximation.lean`; the weighted theta history in [zero-Jordan history](../../2-fully-proven/theta/theta-compact-inverse-zero-jordan-history.md), with the exact needed history theorem independently certified below.

## Theorem

Let `k` be the literal positive even completed-theta density.
For a finite set `S` of primes, put `P=∏_{p∈S}p`, with `P=1`
when `S=∅`, and define its exact deletion source

```text
k_S = ∏_{p∈S}(1−p^(−1/2)T_(log p)) k
    = ∑_{d∣P} μ(d)d^(−1/2)k(·+log d).
```

For `q>0`, let `H_q=L²(ℝ,k(x)^(−q)dx)`. Then

```text
k_S∈H_q  ⇔  q<2/P².                                  (1)
```

The underlying statement applies to **any** nonzero finite
arithmetic shift polynomial
`f=∑_{d∈D}c_d k(·+log d)`, where `D` is a finite set of
positive integers, `b=max D`, and `c_b≠0`:

```text
f(−T)/k(T−log b) → c_b,
f∈H_q ⇔ q<2/b².                                    (1a)
```

No sign or Euler-factor assumption is needed for (1a). It
includes prime-square deletion
`(1−p^(−1)T_(2log p))k`, whose threshold is `2/p⁴`.

More sharply, the negative cusp has one terminal squarefree
word:

```text
k_S(−T)/k(T−log P) → μ(P)/√P       (T→+∞).          (2)
```

Thus every nontrivial finite deletion is eventually signed at
the negative cusp by the parity of its full prime word. Its
weighted admission threshold depends on the **product of all
deleted primes**, not on the largest single prime. The positive
cusp remains first-atom dominated:
`k_S(T)/k(T)→1` as `T→+∞`.

For every fixed `q>0`, only finitely many finite prime sets have
`k_S∈H_q`. Along any cofinal deletion sequence `S_j`, every
admitting exponent `q_j` satisfies `q_j<2/P_j²→0`. This proves
that the literal all-prime deletion cannot be carried by any
fixed positive theta-weighted Hilbert space. At each finite
stage that is admitted, `k_S` lies in the closed derivative
history `R_q` of the completed source, by the analytic
translation-orbit theorem of the zero-Jordan card. Thus the
cofinal boundary is simultaneously a carrier escape and a
history-quotient collapse.

## Proof

The exact inclusion-exclusion formula above is proved in the
prime-deletion card. The corpus first-atom theorem and the
explicit seed polynomial give

```text
k(T) ~ 4π² exp(9T/2−πexp(2T)).
```

For `d<P`, the ratio

```text
k(T−log d)/k(T−log P)
  = O(exp(−π(d^(−2)−P^(−2))exp(2T)) · exp(O(1)))
```

tends to zero. Since the sum over divisors is finite, its
`d=P` term proves (2). The denominator is positive for large
`T`, and `μ(P)=±1`, so the leading term cannot cancel.
The identical argument with `b=max D` proves the terminal
ratio in (1a) for arbitrary nonzero finite shift polynomials.

On the negative cusp, (2) and the first-atom asymptotic make
the weighted energy density comparable to a positive constant
times

```text
exp((9/2)(2−q)T)
  · exp(−π(2/P²−q)exp(2T)).                        (3)
```

If `q<2/P²`, (3) is integrable by double-exponential decay.
If `q>2/P²`, it grows double-exponentially. At equality, its
remaining factor grows as
`exp((9/2)(2−2/P²)T)` when `P>1`;
for `P=1` it is asymptotically constant. Both are
nonintegrable. At the positive cusp, the retained `n=1`
Gaussian atom dominates every other positive atom, so
`k_S(T)/k(T)→1`; that tail is integrable whenever `q<2`.
This proves (1), including `S=∅`.
For (1a), replace `P` by `b` in the negative-cusp calculation;
all positive-cusp shifts have `d≥1`, so that tail is integrable
whenever `q<2/b²≤2`.

If `k_S∈H_q`, (1) gives `P<√(2/q)`. There are only finitely
many squarefree positive integers below this bound, hence only
finitely many corresponding prime sets. Finally each shift
`log d` in the deletion sum satisfies
`q<2/P²≤2/d²`, so it is admitted in `H_q` and belongs to
the derivative-history closure by the previous card. Their
finite sum `k_S` belongs there too.

## Consequence and limit

The maximal squarefree word fixes the **exact rate** at which a
source-faithful graded carrier must approach the unweighted
endpoint. This is a concrete obstruction to applying one fixed
Hilbert-space operator through cofinal Euler deletion, and a
constraint on any proposed rigged or inductive-limit action.
The boundary coefficient `μ(P)/√P` in (2) is also the top
squarefree monomial of the finite Euler factor
`∏_{p∈S}(1−p^(−1/2−w))`: Mellin translation supplies its
remaining factor `P^(−w)`. Thus the graded cusp detects exactly
the terminal word of the arithmetic product. Recovering the
phase of the **whole** product requires a boundary mechanism
that retains all smaller words as the scale collapses. The
fixed-`P` limit (2) is not uniform along cofinal prime sets:
at the moving cusp `−log P−u`, the exact
[moving-cusp duality](theta-prime-deletion-moving-cusp-dual-source.md)
retains every squarefree word and has a canonical locally uniform
signed-totient limit.
It does not control the complex phase of the Xi divisor. A
proof of RH still needs a source-specific boundary law that
survives this forced scale loss and orients the nonzero Xi
spectrum. No numerical computation or zero-location premise
was used; external novelty has not been established. The
frontier map was read only.


## Complete Lean certificate — 2026-09-30

Every original literal-source clause is certified in ten new modules under
`formal/GaloisForLFunctions/RHTower/`:

| Paper clause | Exact Lean declaration |
|---|---|
| First-atom envelope coefficient of the complete source | `thetaCuspFullSource_div_envelope_tendsto` |
| Arbitrary finite arithmetic polynomial's negative terminal coefficient | `finiteArithmeticThetaShift_terminal_ratio` |
| Literal real and complex weighted admission iff `q < 2 / b²` | `finiteArithmeticThetaShift_memLp_iff`, `finiteArithmeticThetaShift_ofReal_memLp_iff` |
| Failure at the equality boundary and above | `not_integrable_finiteArithmeticThetaShift_energy` |
| Exact finite-prime admission iff `q < 2 / P²` | `thetaPrimeDeletion_memLp_iff`, `thetaPrimeDeletion_ofReal_memLp_iff` |
| Terminal coefficient `μ(P) / √P`, positive ratio one, eventual terminal parity sign | `thetaPrimeDeletion_terminal_ratio_moebius`, `thetaPrimeDeletion_positive_ratio`, `thetaPrimeDeletion_terminal_sign` |
| Exact prime-square admission iff `q < 2 / p⁴` | `thetaPrimeSquareDeletion_memLp_iff`, `thetaPrimeSquareDeletion_ofReal_memLp_iff` |
| Finitely many admitted prime alphabets at each fixed positive weight | `thetaAdmittedPrimeDeletions_finite` |
| Cofinal terminal products diverge and admission thresholds vanish | `PrimeExhaustion.tendsto_primeProduct`, `PrimeExhaustion.terminalThreshold_tendsto_zero` |
| Positive admitting weight sequences tend to zero; fixed positive carriers eventually exclude deletion | `PrimeExhaustion.admitting_weights_tendsto_zero`, `PrimeExhaustion.eventually_not_memLp` |
| Full Gaussian complex bound and a genuine common weighted L² rectangle majorant | `norm_thetaCuspStripSource_le_gaussian_envelope`, `thetaRectangleGaussianMajorant_memLp`, `thetaCuspStripSource_translation_memLp` |
| Actual real-source derivatives are admitted and represent the Hilbert orbit jets | `thetaWeightedDerivative_memLp`, `thetaWeightedDerivativeVector_coe`, `thetaWeightedTranslationFamily_iteratedDeriv_zero` |
| Every admitted real translate belongs to actual closed derivative history | `thetaWeightedTranslationClass_mem_derivativeHistory` |
| Literal admitted finite arithmetic words and finite Euler deletions belong to that history | `finiteArithmeticThetaShift_admitted_derivativeHistory`, `thetaPrimeDeletion_admitted_derivativeHistory` |

Namespaces: all declarations above are under `RHTower`. Modules:
`ThetaArithmeticTerminalCusp`, `ThetaPowerWeightedSource`,
`ThetaPrimeDeletionTerminalCusp`, `ThetaArithmeticWeightedAdmission`, and
`ThetaPrimeDeletionWeightedAdmission`, `ThetaCuspComplexGaussianEnvelope`,
`ThetaPowerWeightedComplexTranslations`, `AnalyticDominatedL2Derivatives`,
`ThetaPowerWeightedDerivativeHistory`, and `ThetaPrimeDeletionDerivativeHistory`.
The locally dominated family declarations in `AnalyticDominatedL2Derivatives`
use namespace `RHTower.DominatedL2Sections`.
The measure is literally
`volume.withDensity (ENNReal.ofReal ∘ (fun x => k(x)^(-q)))`, and deletion is the
actual finite Euler polynomial with its exact Möbius coefficients.

The generic Cauchy lifting dependency `HTGeometry/L2CauchyHolomorphy.lean`
now exposes its actual derivative representative through
`exists_memLp_deriv_hasDerivAt_l2Family_of_cauchy_dominated` and
`hasDerivAt_l2Family_of_cauchy_dominated`, without weakening its existing theorem.
`DominatedL2Sections.Family.coe_iteratedDeriv_section` identifies every order
with the pointwise derivative, and `Family.section_mem_closed_span_jets` proves
the connected-domain closed-span statement by analytic uniqueness. The theta
specialization identifies those jets with `k⁽ⁿ⁾`, rather than defining history
using abstract orbit jets. Finite sums then retain the exact Euler coefficients.

Validation: needed named `lake --old build +MODULE:olean` leaf builds passed.
Final `lake env lean FILE` checks passed without warnings for all ten final
RHTower sources and the strengthened Cauchy lifting dependency. Scratch-file
axiom audits covered all 105 public declarations in the ten leaves and all five
public declarations in that dependency, with no missing reports and no axioms
beyond `propext`, `Classical.choice`, and `Quot.sound`. All ten leaves are wired
into `GaloisForLFunctions/RHTower.lean`. No heartbeat increase, computational
certificate, numerical experiment, full build, or umbrella build was used.

The broader recursive formalization programme remains active. Its authoritative
lint log records unrelated concurrent reachability failures separately; this
card's exact mathematical certificate is complete. External novelty remains
unaudited, and no zero-location statement follows from this theorem.
