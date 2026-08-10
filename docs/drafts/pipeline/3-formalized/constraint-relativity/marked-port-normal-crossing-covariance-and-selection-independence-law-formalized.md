# Marked-port normal-crossing covariance and selection-independence law — formalized

- **ID:** `marked-port-normal-crossing-covariance-and-selection-independence-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `marked-port-normal-crossing-covariance-and-selection-independence-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.MarkedPortCovariance` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/MarkedPortCovariance.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## New infrastructure

Mathlib has no form of the classical covering lemma, so it is built here:

- `exists_le_of_subset_biUnion` — over an **infinite** field, a subspace contained in a finite
  union of subspaces is contained in one of them.  Proved by strong induction on the index finset:
  either the smaller union already covers (induction), or a vector `x` sits in exactly the removed
  member, and then the infinite affine family `y + c·x` must repeat a member by pigeonhole
  (`Set.Infinite.exists_ne_map_eq_of_mapsTo`), forcing `x` into it — a contradiction.
- `exists_smul_of_ker_le_ker` — two functionals with nested kernels are proportional.

The card offered two routes for Theorem A (polynomial unique factorization, or finite hyperplane
permutation).  The second is the one taken: with the covering lemma there is no need to touch
`MvPolynomial` at all.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `port`, `port_ne_zero` — **card `(MPN.2)`**: the ordered coordinate ports.
2. `exists_monomial_of_mapsTo` — **Theorem A, `(MPN.2a)`**: a linear automorphism preserving the
   normal-crossing discriminant is monomial — each output port is a nonzero scalar multiple of a
   single input port, and the induced index map is a permutation.
3. `subspace_in_union_two`, `block_diagonal_or_swap` — **Theorem A', `(MPN.6b)` boxed**: a linear
   automorphism preserving the two block ports is block-diagonal or a block swap.  This half needs
   no infinite-field hypothesis, exactly as in the card's own two-component argument.
4. `shear`, `shear_destroys_full_support` — **card `(MPN.6)`**: full support is not `GL`-invariant.
5. `diagDefect`, `diag_not_full_support`, `ne_zero_not_full_support`,
   `full_support_of_diag_of_ne_zero` — **Theorem B, `(MPN.7)`–`(MPN.8)` boxed**: diagonality and
   nonerasure are logically independent, and together they give full support.
6. `routeR_two_port` — **card `(MPN.8a)`**: a two-legged family whose legs vanish on opposite open
   half-lines is never zero, has full block-port support only at the centre, and has vanishing
   diagonality defect only at the centre.  Stated from the vanishing pattern itself, so it does not
   import the summability law of the companion card as an unproved premise.
7. `static_obstruction` — **card `(MPN.9)`**: against the zero target the kernel is everything and
   every reporter factoring through it is zero, so the cokernel is the whole reporter space — a
   static factorization obstruction, with no parameter, loop or transport.
8. `exists_section_zero_locus` — **card `(MPN.10)`**: every subset is the zero locus of some
   declared section, so arbitrary sections generate arbitrary topology.
9. `contractible_two_term`, `presentation_size_strictMono` — **card `(MPN.11)`**: the two-term
   complex is contractible while the graded size of the stabilized tower strictly increases, so raw
   presentation nontermination is not invariant.

## Scope

§6 lists necessary conditions for a non-theatrical field and §7 is the novelty boundary; the card
states plainly that these are necessary, not sufficient, and construct no source selector.  The two
open gates (literal Route-R marked constitutive map, cross-route transgression theorem) are
unaffected and remain open.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/MarkedPortCovariance.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.MarkedPortCovariance          # green
```
