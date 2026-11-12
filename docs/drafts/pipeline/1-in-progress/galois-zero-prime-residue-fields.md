# Prime residue fields and functional-reflection pairs

- **ID:** galois-zero-prime-residue-fields
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Pointwise arithmetic fields; finite presentations of the full prime spectrum; conjugation and reflection.

## Target

Over the proved prime-source trace field `B`, inside the full normal spectral
extension `E`, define

`F_ρ = B(p^ρ : p prime)`,
`H_ρ = B(p^ρ + p^(1−ρ) : p prime)`.

For every actual zero, any two distinct prime values generate `F_ρ`; any three
distinct symmetrized prime values generate `H_ρ`. Both are finite over `B`.
Their fixing subgroups are respectively the stabilizer of `ρ` and the
stabilizer of its unordered functional-reflection pair. Moreover
`[F_ρ:H_ρ]≤2`, and `F_ρ=H_ρ` exactly when functional reflection sends `ρ`
outside its arithmetic orbit.

The chosen embedding of `H_ρ` is real exactly when `Re ρ=1/2`. All arithmetic
conjugates of `H_ρ` are real exactly when the entire arithmetic orbit of `ρ`
lies on the critical line. This supplies an exact arithmetic place criterion,
not a proof that the criterion holds.

Globally any two prime coordinate families generate all of `E` over `B`.
The base continues to retain every mixed prime-source trace.

## Paper mechanism

The normal extension `E/B` has a faithful zero action transporting every prime
value simultaneously. An automorphism fixing two prime values at `ρ` fixes
`ρ`, by two-prime injectivity, and hence every prime value there. Infinite
Galois fixed-field duality proves the two-generator presentation.

Write `U_p(z)=p^z+p^(1−z)`. Equality of `U_p(z)` and `U_p(w)` implies
`p^z=p^w` or `p^z=p^(1−w)`, since the two summands have product `p`.
Among three primes two choose the same branch; two-prime injectivity then
gives `z=w` or `z=1−w`. Fixed-field duality therefore gives the three-generator
presentation and the pair stabilizer.

At least one of two prime values distinguishes an actual nonreal zero from
its reflection. Adjoining that value to `H_ρ` reduces the pair stabilizer to
the point stabilizer, hence gives all of `F_ρ`. The value satisfies
`X²−U_p(ρ)X+p=0`, so the relative degree is at most two. The stabilizers differ
exactly when an arithmetic symmetry sends `ρ` to its reflection.

Conjugating all symmetrized prime values replaces `ρ` by its conjugate.
Three-prime pair separation and the absence of real zeros show that all these
values are real exactly when `conjugate(ρ)=1−ρ`. Transporting generators by
an arithmetic automorphism gives the orbit-wide reality criterion.

## Boundary

No total-realness theorem for these fields, global lift of functional
reflection, or purity assertion is assumed. Two- and three-prime presentations
are relative to the complete mixed-trace base; they do not discard its other
prime data. The statements concern every actual zero and the entire extension.
