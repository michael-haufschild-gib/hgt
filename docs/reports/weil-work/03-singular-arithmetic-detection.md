# WP03 — Arithmetic detection beyond the regular deviation classes

Status: open detection route. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Supply the **bounded zeta-quotient** condition for a full-positive system, with a genuinely new argument that applies beyond the already rigid summable and finite-type deviations.

The complete target is an implication from `hW : WeilPositiveFull λ` to a holomorphic `G` on `Re s > 1/2` satisfying the repository's exact Dirichlet-exponential identity on `Re s > 1`, and

\[
\forall x>\tfrac12\;\exists M\;\forall s,
\quad \Re s>x,\ s\ne1\Longrightarrow |\zeta(s)G(s)|\le M.
\]

This would make every full-positive system detect RH. A theorem on an independently specified proper subclass is useful but conditional until a producer in that subclass exists. The objective is this detector; general spectral quantization and phase production belong to WP04–WP05.

## Starting evidence

- [Exact quotient receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilProducerZetaQuotientBohrRecurrence.lean:474): `riemannHypothesis_iff_exists_bounded_zetaQuotient`. Preserve holomorphy, the literal exponential identity and half-plane uniformity.
- [Prime deviation consequence](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilProducerZetaQuotientBohrRecurrence.lean:617): a proved consequence of boundedness, not a proof of boundedness.
- [Critical-half-plane Herglotz continuation](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeHerglotzCriticalHalfPlane.lean:395): continuation and nonnegative real part already follow from full positivity.
- [Deviation residue law](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeDeviationResidue.lean:41): `ξ'/ξ − Φλ` carries the ξ-zero multiplicity at an off-line zero in the right critical half-plane. This is the permitted compensation mechanism that an arithmetic argument must exclude.
- [Bohr detection research card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/bohr-route-detection.md): inspect its current proved versus paper-only statements before using a recurrence or averaging proposal.

## First research milestone

Derive one new quantitative restriction on the actual Dirichlet reciprocal or its deviation from ζ that remains meaningful without subcritical absolute summability. State the exact norm, domain, height dependence and exceptional set. Prove how strengthening this estimate to a specified uniform bound would pay the quotient receiver.

Test the inference from any averaged or almost-periodic estimate to the **actual untwisted function**. If that passage fails, isolate a counterexample to that inference under its precise assumptions and extract a valid replacement condition. Such a counterexample is not automatically a counterexample to the full arithmetic cone.

## Already closed classes: do not repackage them

- [One-sided summable deviation rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeOneSidedDeviationRH.lean:430): summability of either sign part at any one real exponent below `1` forces Λ. A distinct producer must have both sign parts divergent at every such exponent.
- [Log-summable rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilLogSummableRigidity.lean:1090): a finite weighted critical-line log moment already forces Λ.
- [Finite-type uniqueness](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFiniteTypeUniqueness.lean:435) and [boundary Möbius rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeBoundaryMobiusRigidity.lean:446) close their exact regular classes.
- [Null-potential sign-block rigidity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilNullPotentialSignPartRigidity.lean:398) already handles its uniform one-sign block bound.

Call a proposed class new only after comparing its hypotheses with these statements. “Dense mixed singular deviation” is an informal description, not a formal replacement for their exact exclusions. Do not add boundedness, coefficient ordering, a zero-free assumption or RH under a different name as the missing premise.

## Search entry points

```sh
scripts/formal_tools.py research 'bounded zetaQuotient' --module Weil
scripts/formal_tools.py research 'mixed singular deviation arithmetic rigidity Bohr untwisted bound' --mode deep --budget-seconds 300
scripts/formal_tools.py research 'summable deviation nullPotential' --any --module Weil
```

## Completion and handoff

`CLOSED` means the exact quotient hypotheses are derived for arbitrary `hW`, followed by the existing receiver. This remains conditional on existence when discussing unconditional RH. A proper-subclass result is `CONDITIONAL ADVANCE`; give WP01 an explicit property it would need to produce. A scoped no-go must include a positive survivor and must not retire the whole PBAP route.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/03-singular-arithmetic/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-03-singular-arithmetic.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkSingularArithmetic*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
