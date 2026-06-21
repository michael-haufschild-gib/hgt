# C3 Proof Attempt: Phase-Sobolev Regularity Controls Long-Run Coherence

Source: `docs/consolidated/08-conjectures-required.md` §1.

Claim status: `[CONJECTURE]`.

## Target Claim

The long-run coherence phenomena in Group B are monotone functionals of one
phase-Sobolev seminorm, schematically

```text
|| partial_t arg(Gamma_infty + P) ||,
```

and the true-vs-finite gap is exactly a gap in that regularity functional.

## Proof Attempt

Let `theta(t)` be a continuous phase on an interval `I`, and let a transport
state be defined by a phase gate

```text
state(t) = 1_{theta(t) in E}
```

for an arc `E` of the circle. If `theta` has bounded variation, then every
transition between `E` and its complement forces `theta` to move at least the
angular separation `eta` between the safe interior of `E` and the outside. Thus

```text
number of robust transitions <= Var_I(theta) / eta.         (1)
```

If `theta` is absolutely continuous, then

```text
Var_I(theta) <= int_I |theta'(t)| dt.
```

By Cauchy-Schwarz,

```text
int_I |theta'| <= |I|^(1/2) ||theta'||_L2.
```

Combining gives a rigorous conditional bound:

```text
robust transition count <= |I|^(1/2) ||theta'||_L2 / eta.   (2)
```

This proves that an `H^1` phase seminorm can control one coarse version of
run-count or edge-softness, provided the gates have a robust angular margin.

## Weakened Theorem Proved Here

**Theorem C3-W.** For an absolutely continuous phase `theta` and a phase gate
with angular margin `eta > 0`, the number of robust phase exits on an interval
`I` is bounded by `(2)`.

This is a genuine regularity-to-persistence theorem, but it is weaker than C3:
it uses `H^1`, not `H^{1/2}`, and controls only robust phase exits, not all
Group-B observables.

## Attack As False

The conjecture says one seminorm predicts all Group B. That is too strong
without amplitude and transversality hypotheses. Two phases can have the same
`H^1` norm but different gate residence times by concentrating derivative near
or away from the gate boundary. Thus a seminorm alone cannot determine the
run-length distribution.

The best possible version must include either:

```text
(phase seminorm) + (gate geometry) + (amplitude nondegeneracy),
```

or replace "predicts all" by "bounds selected robust transition counts."

## Where The Full Proof Fails

No inequality is known from an `H^{1/2}` phase seminorm to the empirical
statistics: lifetime, softness, fragility, dissolution, and survivor spine.
The smooth-surrogate kill criterion remains open: a smooth non-HT analytic fake
may match the same seminorm and the same Group-B behavior.

## Missing Input

1. A formal definition of each Group-B statistic as a functional of phase.
2. A theorem linking those functionals to a chosen Sobolev norm.
3. A proof that the norm separates true `xi` from smooth non-HT controls.
