# Direct polynomial-cutoff transfer of the rough dilation graph

- **ID:** twin-prime-direct-rough-dilation-transfer
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [signed cubic roughness](../1-in-progress/twin-prime-signed-cubic-roughness.md)
- **Statement rejected:** Move the published roughness cutoff to `X^(1/3)`
  while retaining its small-label supply, or move the labels above that
  cutoff while retaining fixed polynomial height and unbounded label depth.

## Exact failure

In [Guo's source, “Labels, bins and vertex cuts” and the proof of Theorem 1.1](https://raw.githubusercontent.com/aster2024/openai-math-followups/main/rough-pairs-fixed-distance/source/main.tex),
the primes used in dilation labels are at most `exp(L)`, where
`L=(log X)^(1/625)`. The dilation identity for `λ·1_rough` requires all
label primes to exceed the roughness cutoff. At `z=X^(1/3)`, these
requirements are incompatible for all sufficiently large `X`.

Moving the labels upward does not preserve the height regime: a product
of `J` primes greater than `X^(1/3)` exceeds `X^(J/3)`. A bound `X^A`
with fixed `A` therefore forces `J<3A`. This rules out that specific
unbounded-depth, polynomial-height repair. It is not a universal barrier
to roughness estimates, graph methods, signed weights, or fixed-depth work.

## Positive survivor and second pass

The second pass removes all details of the published prime groups and
classifies every nontrivial divisible edge on cubic rough support.
The exact result is

`E_z = {(q,p): q,p,p+2 prime; z≤q; z≤p; q(p+2)<z³}`.

See the [complete paper proof and Lean audit](../3-formalized/twin-prime-cubic-dilation-classification.md).
This is a nonempty structural classification, not merely failure of one
choice of labels. Producing sufficiently many such edges still requires
twin-prime information.

- **New insight for this route:** keeping the entire graph in the cubic
  support relocates the twin-prime problem into its edge supply.
- **Novelty:** REDISCOVERED elementary factorization; no new scientific
  knowledge established.
- **Paper status:** dependency-closed.
- **Lean status:** exact classification
  `TwinPrime.cubicDilationPairs_eq_prime_twin_parameters`; leaf and axiom
  audits passed. No new axioms or analytic premises.

## Continuing target

The signed cubic estimate itself remains open. The failed transfer gives
no reason to discard it. A replacement must supply new signed arithmetic
control, permit larger physical scales with justified return estimates,
or use a mechanism not requiring this label supply.
