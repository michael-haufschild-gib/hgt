# The arithmetic group is a heat monodromy on finite windows but not on a fibre

- **ID:** gtz-arithmetic-group-versus-heat-monodromy
- **Stage:** 3-formalized
- **Type:** THEOREM (with no-go part)
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problem 4 (review-1411 §2.19).
- **Statement:** `G = Gal(E/B)` acting on the zeros of ξ; `G₊(b)` the forward monodromy group at
  a forward time `b` off the branch times, acting on the zeros of `H_b`.
  (A) if `φ` maps the zeros of ξ injectively to the zeros of `H_b` with `φ(1 − ρ) = −φ(ρ)`,
  then for every `σ ∈ G` and every finite family of zeros in distinct reflection pairs there is
  `g ∈ G₊(b)` with `g(φ s_i) = φ(σ s_i)` for all `i`;
  (B) no injective `φ` from the zeros of `H_b` to the zeros of ξ has, for every `g ∈ G₊(b)`, some
  `σ ∈ G` with `φ ∘ g = σ ∘ φ`;
  (C) no injective `φ` from the zeros of ξ to the zeros of `H_b` and `g ∈ G₊(b)` have
  `φ ∘ σ = g ∘ φ` for an automorphism `σ ∈ G` moving infinitely many zeros; conjugation moves
  every zero.

## Goal

Problem 4 asks for a comparison mechanism and an exact account of what it preserves. (A) is the
positive survivor: at every finite level the heat group realizes the arithmetic group. (B), (C)
say that no comparison carries one group into the other on a whole fibre.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) The points `φ(s_i)` lie in distinct pairs `{z, −z}` (injectivity and `φ r = −φ`), and so do
the points `φ(σ s_i)` (`σ` is injective and commutes with `r`). `G₊(b)` moves finitely many zeros
in distinct pairs to any such zeros.
(B) `G₊(b)` is transitive, so `φ` maps the fibre into one `G`-orbit, which is finite; the fibre is
infinite and `φ` injective.
(C) `g` would move every `φ(ρ)` with `σρ ≠ ρ`, infinitely many points; elements of `G₊(b)` have
finite support. Conjugation fixes no zero (`Im ρ ≠ 0`) and the zeros are infinite. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre` | `exists_mem_forwardMonodromy_eq_on_window` |
| B | same | `not_exists_injective_intertwining_forwardMonodromy` |
| C | same | `not_exists_injective_intertwining_of_infinite`, `setOf_primeTraceConjugation_ne_infinite`, `not_exists_injective_intertwining_conjugation` |

## Open

A specialization from forward times to the time `0` on growing windows (transport is controlled
only for `Re τ > 0`), and whether a window of zeros of ξ can be followed to a forward time so that
the arithmetic conjugation becomes the word of the turns.
