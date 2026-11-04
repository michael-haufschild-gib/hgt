# Fifth even theta atoms beyond scale five

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ6
- **Statement:** Every individual theta atom has a positive definite fifth even reflected-moment matrix whenever its reflection scale is at least five.

For `f_n(x)=thetaCuspSourceTerm x n` and `q=π n² exp(2x) ≥ 5`,

`Hᵢⱼ = (-1)^(i+j) (d/dt)^(2(i+j)) [f_n(x+t)f_n(x-t)]|ₜ₌₀`, `0≤i,j<5`,

is positive definite. No assumption on the sign of a theta mixture is used.

The radial matrix has entries `r_(i+j)(q)=P_(i+j)(q²,2q)`.
Its leading two-by-two block has positive first entry and determinant `d`.
The denominator-cleared three-by-three Schur matrix is `q³ S(q)`.
The first entry, leading two-by-two minor and determinant of `S(5+y)` have
strictly positive coefficients for `y≥0`. Two exact square completions
therefore prove positivity of the entire radial matrix. The literal atom
matrix is its positive multiple `4q² exp(x−2q)`.

**Lean:** `ThetaCuspSections/FifthEvenFirstAtom.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.FifthFirstAtom`:

- `radial_even_five_posDef`
- `atom_even_five_posDef`
- `firstAtom_even_five_posDef`

Canonical source check and transitive axiom audits pass; only `propext`,
`Classical.choice`, and `Quot.sound` occur.

The [complete native source](theta-cusp-fifth-even-native-ray.md) is now
strict whenever its first-atom scale is at least five, including the
compensation zero. The individual-atom theorem supplies its positive pure terms.
