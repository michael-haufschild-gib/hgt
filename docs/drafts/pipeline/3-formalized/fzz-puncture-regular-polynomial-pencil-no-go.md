# FZZ puncture regular polynomial-pencil no-go

- **ID:** FZZ-RPP
- **Stage:** 3-formalized
- **Type:** POLYNOMIAL ENERGY-DEPENDENCE DICHOTOMY / NO-GO
- **Parent:** FZZ-FDP / FZZ-P
- **Frontier-map policy:** read only

## Frozen conjecture

Let `P(E)` be an arbitrary `N×N` matrix whose entries are complex polynomials in
energy, and let `K : ℂ^N→ℂ^Q` be arbitrary.  A dark mode at real `E` is a
nonzero vector in `ker P(E) ∩ ker K`.

Prove:

1. every dark-mode energy is a root of determinant polynomial `det P`;
2. if `det P ≠ 0`, only finitely many energies can occur;
3. no regular finite polynomial pencil is complete for all positive real `XiC`
   zeros;
4. Xi-completeness forces `det P=0` identically.

Use FZZ-FDP's injective Hardy zero packet of size `natDegree(det P)+1` for the
sharp contradiction.

## Expected consequence

This closes every fixed finite-dimensional regular algebraic energy dependence,
not only affine `A-EI`.  Remaining finite-dimensional escape is precisely a
singular polynomial pencil with identically vanishing determinant; otherwise
FZZ requires infinite-dimensional or non-polynomial/moving-domain dynamics.

## Corpus basis

- FZZ-FDP Hardy packets of arbitrary finite size;
- determinant commutes with polynomial evaluation;
- a nonzero polynomial has at most `natDegree` roots.

## Lean theorem package

Module:
`GaloisForLFunctions.RHTower.FZZCigarPunctureRegularPolynomialPencilNoGo`

- `fzzPunctureFinitePolynomialDarkMode_isRoot_det`
- `finite_fzzPunctureFinitePolynomialDarkMode_of_det_ne_zero`
- `not_fzzPunctureFinitePolynomialPencilXiComplete_of_det_ne_zero`
- `fzzPunctureFinitePolynomialPencil_det_eq_zero_of_XiComplete`

The proof evaluates the polynomial matrix at each real energy, converts a nonzero
kernel vector into vanishing evaluated determinant, and uses functoriality of
determinant under `Polynomial.evalRingHom`.  For a regular pencil, a Hardy packet
of size `natDegree(P.det)+1` injects into the distinct-root finset of `P.det`,
contradicting `card(toFinset roots) ≤ card(roots) ≤ natDegree`.

## Exact no-go and positive survivor

The no-go eliminates every fixed finite-dimensional **regular** polynomial
energy dependence, of arbitrary degree and with arbitrary fixed coupling.  Its
sharp positive survivor is the singular boundary:

> Xi-completeness forces `P.det = 0` as a polynomial identity.

This survivor is stronger than existence of infinitely many singular evaluated
matrices: the full algebraic determinant vanishes identically.  Singular pencils,
infinite-dimensional dynamics, and non-polynomial/moving-domain mechanisms remain.

## Novelty audit (provisional, 2026-08-27)

Primary literature on FZZ duality and higher-dimensional puncture analogues does
not formulate this Hardy-packet obstruction.  Polynomial-eigenvalue literature
distinguishes regular from singular pencils, but does not connect regularity to
completeness for all positive real completed-zeta zeros.  No matching theorem was
found in the internal Lean corpus.  Priority remains provisional pending expert
review.

Primary sources checked:

- arXiv:0805.3931 (FZZ duality and sine-Liouville description)
- arXiv:1012.4731 (FZZ algebraic structure)
- arXiv:2010.14681 (FZZ duality review/development)
- arXiv:2411.16669 (higher-dimensional FZZ/puncture context)
- arXiv:2406.16832 (singular polynomial eigenvalue problems)
- arXiv:1612.07011 (structured polynomial eigenproblems)
- arXiv:2104.10883 (regular quadratic matrix-polynomial embedding)

## Verification

- Direct check: `lake env lean formal/GaloisForLFunctions/RHTower/FZZCigarPunctureRegularPolynomialPencilNoGo.lean`
- Targeted build: `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureRegularPolynomialPencilNoGo`
- Axiom audit: all four principal theorems depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Status

- Mandatory corpus and primary-literature searches complete.
- Paper proof dependency-closed.
- Lean proof complete and targeted build passed.
- Route advanced to exact singular-pencil boundary.
