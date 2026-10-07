# WP07 — Denominator-three spectral rigidity

Status: open conditional classification problem. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Resolve the first unresolved higher-denominator rigidity target:

\[
W(\lambda),\quad
\forall a<b,\ 3\mu_\lambda((a,b])\in\mathbb N
\quad\Longrightarrow\quad
\forall n\ge2,\ \lambda(n)=\Lambda(n).
\]

Prove the implication or expose a rigorous obstruction to it under its exact assumptions. Start with denominator three; do not turn the assignment into an unbounded classification of every degree. A successful rigidity theorem plus an independent denominator-three producer would give RH. This package does not construct that producer.

## Starting evidence

- [Degree-k correspondence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilZetaPowerForward.lean:155): `weilPositiveFull_counting_iff_zetaPowerDatum` is already formalized for every positive natural `k`.
- [Exact datum structure](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilZetaPowerConverse.lean:41): entire finite-order completion with the functional equation of ζ to the k-th power. The correspondence additionally requires normalization, nonvanishing at `1`, critical-line zeros, and the logarithmic-derivative relation to λ.
- [Denominator-two rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilHalfIntegerMassRigidity.lean:297): do not present a new denominator-two proof as closing the higher-denominator gap.
- [Producer/twin research notes](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/producer-existence-two-walls.md) and [Bohr route notes](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/bohr-route-detection.md): search their C329 and higher-degree discussions; numerical or paper-only exclusions require their own proof audit.

## Exact reformulation and first milestone

Specialize the proved correspondence to `k = 3`. Record **all** its hypotheses on `(λ,g,E)`, especially

\[
E(s)=\bigl(s(s-1)\Gamma_{\mathbb R}(s)\bigr)^3L_g(s),
\qquad L'_g(s)=-3L_\lambda(s)L_g(s)\quad(\Re s>1),
\]

and the separate assumption that every zero of `E` lies on the critical line. The intended conclusion is the coefficient identity for λ; identification of the normalized Dirichlet series with ζ³ can serve as a proved intermediate step.

First prove one new exclusion or classification lemma for degree-three data satisfying the complete correspondence, beyond known finite-type and regular-deviation classes. If studying a fake ζ³ candidate, determine exactly which hypothesis it satisfies or violates. A candidate sharing a functional equation but lacking the critical-zero or logarithmic-derivative condition does not refute the target.

## Exclusions and traps

- Functional equation and finite order alone are not the full theorem's assumptions. Do not infer the critical-zero condition from the functional equation.
- A positive measure whose masses are multiples of `1/3` need not have half-integer masses. Denominator-two rigidity cannot simply be reused.
- Taking a formal cube root of a completed degree-three function may create monodromy. To apply a degree-one uniqueness theorem, prove the required single-valuedness, analyticity, growth and Dirichlet-series representation.
- Do not assume an Euler product or multiplicative coefficients absent from `ZetaPowerDatum`. If a new theorem needs them, label it conditional and identify their producer gap.
- Ruling out one numerically generated twin is not classification. Conversely, failure of a degree-one proof method is not a counterexample to degree-three rigidity.
- Any genuine counterexample must satisfy full positivity and exact interval quantization, or every hypothesis of the proved correspondence. A relaxed model only refutes the corresponding relaxed claim.

## Search entry points

```sh
scripts/formal_tools.py research 'ZetaPowerDatum' --mode lexical --exact --per-module 0
scripts/formal_tools.py research 'degree three zeta power rational mass rigidity twin monodromy' --mode deep --budget-seconds 300
scripts/formal_tools.py research 'C329' --mode lexical --exact
```

## Completion and handoff

`CLOSED` requires the exact denominator-three implication, checked in Lean, or an exact counterexample refuting it with a checked positive-survivor result. New sufficient hypotheses, exclusions of proper subclasses and monodromy reductions are `CONDITIONAL ADVANCE` or `SCOPED NO-GO`, not full classification.

Report whether the argument genuinely extends to other `k`, but do not leave denominator three unfinished to chase generality. Give WP04 the precise rational-mass input any new rigidity theorem can accept; a producer remains open unless independently supplied.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/07-denominator-three/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-07-denominator-three.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkHigherDenominator*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
