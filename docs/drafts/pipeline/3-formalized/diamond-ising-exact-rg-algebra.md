# Diamond-Ising exact RG algebra

- **ID:** `diamond-ising-exact-rg-algebra`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT PHYSICAL RG CORE
- **Scientific status:** `[LEAN-VERIFIED] [UNCONDITIONAL] [PARENT MATHEMATICS]`
- **Paper parent:**
  `../2-fully-proven/needs-audit/diamond-ising-da-scheme-rg-generation-hypertranscendence.md`
- **Statement:** The exact diamond-Ising rational RG map has numerator `2X^2`, denominator
  `1+X^4`, fixed-point numerator
  `-X(X-1)(X^3+X^2+X-1)`, and quotient-rule derivative numerator
  `-4X(X-1)(X+1)(X^2+1)`.

## Lean surface

Module:

```text
GaloisForLFunctions.HTGeometry.DiamondIsingRG
```

Declarations:

```text
diamondIsingRG
diamondIsingRGNumerator
diamondIsingRGDenominator
diamondIsingRGFixedPointNumerator
diamondIsingRGFixedPointNumerator_factorization
diamondIsingRGDerivativeNumerator
diamondIsingRGDerivativeNumerator_eq
diamondIsingRGDerivativeNumerator_factorization
```

The leaf is registered in the `GaloisForLFunctions.HTGeometry` umbrella.

## Exact content

The rational function is defined directly in `RatFunc ℚ`:

```text
R(X) = 2 X^2 / (1+X^4).
```

The unconditional polynomial identities are

```text
2X^2 - X(1+X^4)
  = -X(X-1)(X^3+X^2+X-1),

(2X^2)'(1+X^4) - (2X^2)(1+X^4)'
  = 4X(1-X^4)
  = -4X(X-1)(X+1)(X^2+1).
```

These are the exact algebraic inputs used to identify the nontrivial physical fixed point and the
finite rational critical set in the paper proof.

## Verification

Targeted verification passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/DiamondIsingRG.lean
lake build +GaloisForLFunctions.HTGeometry.DiamondIsingRG
```

The three theorem declarations have only the standard foundational dependencies
`propext`, `Classical.choice`, and `Quot.sound`.

No broad area build was run: the repository is under concurrent formal development, and the
requested verification discipline is the smallest cached foreground target.

## Formal boundary

This card does not claim that Ritt's differential-transcendence theorem, analytic Poincare
existence, or the resulting beta-field HT theorem has been formalized.  Those inputs are external
paper mathematics.  Introducing them as hypotheses would create a conditional wrapper rather than
an unconditional proof, so the formal boundary stops at the exact reusable rational algebra.

## Gates

- [x] Exact physical rational map represented in HTGeometry.
- [x] Fixed-point and derivative-numerator factorizations proved without hypotheses.
- [x] Targeted leaf build and axiom audit passed.
- [ ] External Ritt/Poincare theory available in Lean from unconditional foundations.
