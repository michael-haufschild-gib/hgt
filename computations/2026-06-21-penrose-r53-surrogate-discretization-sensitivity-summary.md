# R53 - surrogate-ladder discretization sensitivity

Status: dead end / instrumentation requirement.

Random source chain:
- seed RandomNode: selection and assortment can be statistically confounded in inferred drift terms
- broad topic RNG: 7, noise-induced transport in Brownian ratchets
- NODE RNG: 8, sensitivity to discretization of stochastic differential equations
- target-file RNG: 1, `docs/consolidated/08-conjectures-required.md`
- target-topic RNG: 20, source map / surrogate-ladder open action
- scientific-method RNG: 9, test small cases
- perturbation-method RNG: 20, name the missing lemma

## Transfer

The NODE says inferred transport can depend on discretization. The target is
the source-map claim that the §4 surrogate ladder is the most informative open
action. The transfer asks whether a minimal phase-weld classifier has stable
true-vs-finite margins under grid resolution and offset changes.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r53-surrogate-discretization-sensitivity.py
```

NODE validation:

```text
Ito endpoint=0.040345
midpoint/Stratonovich-like endpoint=1.005133
```

Small surrogate-ladder grid cases:

```text
sigma=0.3
  samples=16: +0.6532,+0.2493,+0.4716,+0.3655
  samples=64: +0.4306,+0.4003,+0.3636,+0.4171

sigma=0.5
  samples=16: +0.5141,-0.0468,+0.5054,+0.1577
  samples=32: +0.4682,-0.0726,+0.0818,+0.4580
  samples=64: +0.2133,+0.1617,+0.1202,+0.2754

sigma=0.7
  samples=16: +0.1864,+0.0000,+0.1032,+0.0000
  samples=32: -0.0654,+0.0000,+0.0000,+0.0097
  samples=64: +0.0586,+0.0362,+0.0000,+0.0445
```

The left lane is stable in this battery; transition lanes can flip sign under
grid/offset choices.

## Missing Lemma

The source-map surrogate ladder needs an explicit grid-stability certificate:

```text
for each claimed discriminator, the verdict is invariant under a declared
family of t-grid resolutions, offsets, and finite-prime surrogate cutoffs.
```

## Verdict

Dead end for non-reducing count. This is a target-relevant instrumentation
requirement, but the mechanism is discretization/sampling sensitivity rather
than a new native invariant.
