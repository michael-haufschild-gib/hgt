# Faithful re-encoding does not promote a law — formalized

- **ID:** `faithful-reencoding-no-law-promotion-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `faithful-reencoding-no-law-promotion.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.CloneReencoding` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CloneReencoding.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `Op.transport` — transport of an `n`-ary operation along a bijection, `i_*f = i ∘ f ∘ (i⁻¹)ⁿ`.
2. `Op.transport_apply_map` — the defining equation `(i_*f)(i x₁,…,i xₙ) = i (f x₁ … xₙ)`, card `(1)`.
3. `Op.transport_proj` — projections go to projections.
4. `Op.transport_comp` — transport respects substitution.
5. `Op.transportEquiv`, `Op.transport_injective`, `Op.transport_inj_iff` — transport of operations
   is a bijection; card `(2)` and consequence 2.
6. `Clone` (structure), `Clone.transport` — the transported clone `i_*C` is a clone.
7. `Clone.transport_mem_iff`, `Clone.transportPartEquiv` — **clone conjugacy**: the `n`-ary parts
   of `C` and `i_*C` correspond bijectively; card `(2)`, consequence 1.
8. `Clone.transport_transport_symm` — transporting back returns the original clone.
8a. `Clone.full`, `Clone.projections`, `Clone.projections_ne_full` — the top and bottom of the clone
    lattice are constructed, and they differ as soon as `X` has two distinct elements (a constant
    unary operation is not a projection).  Every statement quantified over `C : Clone X` above is
    therefore about a nonempty, in fact nontrivial, set of clones.
8b. `Clone.transport_full`, `Clone.transport_projections` — transport carries each extreme clone to
    the corresponding extreme clone on the target.
9. `CloneTerm`, `CloneTerm.eval`, `CloneTerm.transport`, `CloneTerm.eval_transport`,
   `CloneTerm.eval_transport_eq` — term evaluation commutes with the encoding.
10. `CloneTerm.eval_transport_inj_iff` — **term identities are preserved and reflected**;
    consequence 2.
11. `CloneTerm.exists_transport_eval_iff` — **term-definable operations correspond bijectively**;
    consequence 3.
12. `Congruence`, `Congruence.transport`, `Congruence.transportEquiv` — **congruence lattices
    correspond bijectively**; consequence 4.
12a. `Congruence.top`, `Congruence.bot`, `Congruence.bot_ne_top` — the total and identity
     congruences of an arbitrary clone, distinct whenever `X` has two distinct elements; the
     bijection of item 12 is therefore between sets with at least two elements, not empty ones.
12b. `Congruence.transport_top`, `Congruence.transport_bot` — the bijection matches the extremes:
     transport sends the total congruence to the total congruence and the identity congruence to
     the identity congruence.
13. `transport_eq_of_intertwine`, `transport_ofInjective_eq_of_intertwine` — the separating-feature
    corollary: an operation defined by `Φ ∘ T = T̂ ∘ Φ` is on the image exactly the transport of `T`;
    card `(3)`.
14. `crossingProfile`, `crossingProfile_le`, `crossingProfile_zero` — the crossing-time profile
    `τ_p = M − x_p + 1`.
15. `crossingProfile_injective` — **the crossing-time profile is a faithful re-encoding** for
    valuation vectors bounded by their top valuation and attaining `0` (the finitely supported
    valuation vectors of integers).
16. `resetCarry`, `crossingProfile_increment` — **reset-and-carry is conjugate to prime
    multiplication**: profiling the incremented valuation vector equals the reset-and-carry action
    on the profile.

Consequence 5 of the card ("zero genuine law-promotion content") is exactly the conjunction of
items 5, 7, 10, 11, 12: everything obtained by transporting old operations is the image of an old
object under a bijection of clones.

## Scope note

The card writes the prime application for "a bounded valuation vector". Bare boundedness is not
enough — the profile is invariant under a uniform shift of the whole vector — so the Lean statement
carries the extra structural fact that the vector attains the value `0`, which holds for every
valuation vector of an integer (all but finitely many exponents vanish). This strengthens rather
than weakens the corollary: it identifies the exact hypothesis under which the profile map is
injective.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CloneReencoding.lean   # clean
lake build GaloisForLFunctions.HTGeometry                                                # green
```

`#print axioms` on `Clone.transportPartEquiv`, `CloneTerm.eval_transport_inj_iff`,
`Congruence.transportEquiv`, `crossingProfile_injective`, `crossingProfile_increment` returns only
`[propext, Classical.choice, Quot.sound]`, and the same on `Clone.projections_ne_full`,
`Clone.transport_full`, `Clone.transport_projections`, `Congruence.bot_ne_top`,
`Congruence.transport_top`, `Congruence.transport_bot`.
