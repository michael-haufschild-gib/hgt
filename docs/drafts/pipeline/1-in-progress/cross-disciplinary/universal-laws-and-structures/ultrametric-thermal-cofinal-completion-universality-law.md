# Ultrametric thermal cofinal-completion universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- UltrametricThermalTruncation: finite shell sums, exact scale recursion, next-shell increment, and
  residual equal to the omitted shell.
- UltrametricThermalMahler: formal infinite signal, affine Mahler constraint, and uniqueness.
- MahlerColliderSignal: branching signal and its one-step self-similarity.

Whole-corpus search found no theorem identifying finite truncations as canonical prefixes of the
unique infinite Mahler signal or giving their exact cofinal tails.

## Universal law

At every branching ratio `p >= 2` and depth `N`, the finite scalar truncation is evaluation of one
canonical polynomial prefix. The unique infinite thermal signal equals the formal image of this
prefix plus

`((p-1)^2/p) * p^(N+1) * B_p(X^(p^(N+1)))`,

where `B_p` is the original branching signal. Every formal solution of the affine thermal Mahler
constraint has this same prefix--tail decomposition.

## Paper proof

Iterate `B_p(X) = X + p B_p(X^p)`. After `N` steps it is the first `N` weighted shells plus
`p^N B_p(X^(p^N))`. Apply the affine transformation defining the thermal signal. The first term
combines with `-X/p` to give `(p-2)X`; remaining finite terms are exactly the scalar truncation
polynomial, and the last term is displayed tail. Constraint uniqueness transports decomposition to
every solution. No numerical computation is used.

## Lean formalization

Module:
GaloisForLFunctions.HTGeometry.UltrametricThermalCofinalCompletionUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/HTGeometry/UltrametricThermalCofinalCompletionUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
