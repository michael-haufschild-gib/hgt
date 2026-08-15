# Finite squarefree Euler complement rigidity — formalized closure

- **ID:** `finite-squarefree-euler-complement-rigidity-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper theorem:** `./finite-squarefree-euler-complement-rigidity.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NO RH INPUT]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/FiniteSquarefreeEulerFunctionalEquation.lean`

## Exact certified statement

For a finite set `P` of primes, `Q = ∏ p ∈ P, p`, and

```text
F_a(s) = ∏ p ∈ P (1 - a_p p^(-s)),
```

the literal hypothesis

```text
∀ s : ℂ, F_a(s) = ε Q^(1/2-s) F_a(1-s),    ε ≠ 0
```

is formalized as `finiteEulerCardFunctionalEquation`.  The exact capstones are:

1. `finiteEulerCardFunctionalEquation_force_coefficients` — sampling the full complex functional
   equation at every negative integer and applying the finite Vandermonde recovery theorem gives
   every Boolean-complement coefficient identity.
2. `finiteEulerCardFunctionalEquation_force_localSquares` — `a_p^2 = p` for every `p ∈ P`.
3. `finiteEulerCardFunctionalEquation_epsilon_formula` and
   `finiteEulerCardFunctionalEquation_epsilon_sq` —
   `ε = (-1)^|P| (∏ p∈P a_p) / sqrt(Q)` and `ε^2 = 1`.
4. `finiteEulerCardFunctionalEquation_zero_realPart` — every zero `s` of the literal finite
   product has `s.re = 1 / 2`.
5. `finiteEulerCardFunctionalEquation_of_localSquares` — the converse restores the full complex
   functional equation, not only coefficient equality or negative-integer samples.
6. `finiteEulerCardFunctionalEquation_rigidity` — combined forward classification capstone.

The bridge uses existing `Sieve.EulerExpansion` distinct squarefree-product injectivity,
`Hurwitz.MulticolumnPowerOrbit` Vandermonde recovery, and the original
`FiniteSquarefreeEulerComplementRigidity` coefficient core.  It introduces no analytic premise,
axiom, or computational certificate.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/FiniteSquarefreeEulerFunctionalEquation.lean` — pass,
  no warnings.
- `lake build GaloisForLFunctions.RHTower.FiniteSquarefreeEulerFunctionalEquation` — pass.
- `#print axioms` on all six capstones — only `propext`, `Classical.choice`, `Quot.sound`.
- Source scan — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Umbrella import added to `GaloisForLFunctions.RHTower`; deliberately no umbrella build.

## Boundary

This is a finite reciprocal-product classification.  It does not assert a passage from finite
prime inventories to the infinite Euler product and does not prove RH.

## Gates

- [x] dependency-closed paper theorem
- [x] literal unconditional Lean theorem
- [x] direct source check and focused final build
- [x] axiom and forbidden-declaration audits
- [x] umbrella import
- [ ] publication target — standard finite algebra, not new scientific knowledge
