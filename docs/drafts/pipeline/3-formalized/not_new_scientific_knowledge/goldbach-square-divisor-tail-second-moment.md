# Square-divisor tail: uniform second moment

- **ID:** goldbach-square-divisor-tail-second-moment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE
- **Source:** Section 2 of [squarefree bilinear transfer](../../2-fully-proven/goldbach-squarefree-bilinear-transfer.md).
- **Statement:** For every positive integer R and natural X,
  Σ_{1≤n≤X} #{d>R : d² divides n}² ≤ 8X/R.

## Finite paper proof

For positive n≤X every relevant d is at most X. Expand the square and count
multiples of lcm(a²,b²). Their number is at most X/lcm(a,b)², giving

    Σ D_R(n)² ≤ X Σ_{R<a,b≤X} gcd(a,b)²/(a²b²).

The square of gcd(a,b) is at most the sum of g² over their common divisors
1≤g≤X. Interchanging finite sums bounds the last kernel by

    Σ_{1≤g≤X} g² (Σ_{R<d≤X, g|d} 1/d²)².

For g≤R, substitute d=ga. The elementary tail estimate
Σ_{a>R/g}a⁻² ≤ 2g/R bounds the inner sum by 2/(gR). Each such g contributes
at most 4/R², hence their total is at most 4/R.
For g>R, the full reciprocal-square sum is at most 2, so the inner sum is
at most 2/g². These terms total at most 4Σ_{g>R}g⁻² ≤ 4/R.
Multiplying by X proves the claimed 8X/R. X=0 is the empty sum.

## Lean certificate

- Module: `formal/GaloisForLFunctions/goldbach/SquareDivisorTail.lean`.
- Declaration: `GaloisForLFunctions.Goldbach.sum_squareDivisorTail_sq_le`.
- Positive R is encoded by `R : ℕ+`; no analytic input is assumed.
- `lake --old env lean GaloisForLFunctions/goldbach/SquareDivisorTail.lean`
  exited 0 from `formal/`.
- `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- One non-blocking tactic-style warning occurs at the finite case split.
- Audit: `/tmp/hgt-goldbach-square-tail-audit.log`.
- Temporary audit directive removed; the Goldbach umbrella imports the leaf.

This finishes an earlier helper. The full bilinear comparison remains at paper
stage, and no prime-pair existence or new analytic cancellation is claimed.
