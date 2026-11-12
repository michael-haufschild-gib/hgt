# Algebraic monomial relations at all primes

- **ID:** galois-zero-algebraic-prime-relations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Mixed-prime relations in the actual prime spectral field.

## Statement

For a complex exponent `z`, let `K_z` consist of finitely supported integer
prime vectors `m` for which `exp(z Σ m_p log p)` is algebraic over `ℚ`.
For every actual zero `ρ`, this is a saturated subgroup of rational rank
at most two. If `Re ρ` is irrational, its rank is at most one.
There is a fixed finite set of primes containing the support of every
member of `K_ρ`. It can be chosen as the union of the supports of at most
two members, or one when `Re ρ` is irrational.

The lattice is invariant under compatible all-prime scalar embeddings,
conjugation, and functional reflection. It constrains arithmetic orbits
but cannot by itself separate reflected zeros.

## Paper proof

Write `L(m)=Σ m_p log p`. Unique factorization makes `L` injective.
The exponential at exponent one is a positive rational product of primes,
hence algebraic. Algebraic numbers form a field; taking nonzero integer
roots preserves algebraicity. Thus `K_z` is a saturated subgroup.

If `z` is nonrational, the rows `1,z` are rationally independent. Three
independent members of `K_z` would give three independent columns `L(m)`.
All six corresponding exponentials would be algebraic, contradicting
the six-exponentials theorem. Every actual zero is nonreal, hence nonrational.

If `z` is nonreal and its real part irrational, `1,z,conjugate(z)` are
rationally independent: imaginary parts of an integer relation force the
two nonreal coefficients equal; real parts then force both zero.
Two independent members of `K_z` would yield a second forbidden
six-exponentials matrix, since conjugation preserves algebraicity.

Choose a maximal independent family of at most two members. Every other
member satisfies an integer relation with this family, with nonzero
coefficient on that member. Outside the finite union of the chosen
supports this forces its coefficients to vanish. The rank-one case uses
the same argument with one member.

A compatible scalar embedding carries each prime product at `z` to the
same product at its exponent image and reflects algebraicity. Conjugation
preserves algebraicity. The product at `1-z` is the rational product at
one divided by that at `z`; hence reflection preserves the lattice too.

## Boundary

The lattice records which monomials are algebraic, not their exact
algebraic values or their Galois conjugates. Its actual rank and generators,
non-binomial polynomial relations, and the full arithmetic group remain open.

## Formalization

`GaloisForLFunctions/GaloisTheoryOfZeros/TheAlgebraicPrimeRelationsOfTheZeros.lean`:

- `algebraicPrimeRelations_saturated`: nonzero integer roots preserve membership.
- `algebraicPrimeRelations_three_dependent`: rational rank at most two for nonrational exponents.
- `algebraicPrimeRelations_two_dependent`: rank at most one for nonreal exponents with irrational real part.
- `zero_algebraicPrimeRelations_finite_support`: two relation supports capture all actual-zero monomials.
- `zero_algebraicPrimeRelations_irrational_finite_support`: one support in the irrational case.
- `zero_prime_monomials_transcendental_off_finite`: global transcendence outside the resulting finite prime set.
- `algebraicPrimeRelations_arithmetic`: exact invariance under all-prime compatible scalar embeddings.
- `algebraicPrimeRelations_conjugation`, `algebraicPrimeRelations_reflection`,
  `algebraicPrimeRelations_horizontal_reflection`: symmetry boundary.
- `zero_two_algebraic_prime_values_real_rational`: two algebraic prime values force rational real part.

Final direct source check passed without warnings. All 15 transitive dependency
audits use only `propext`, `Classical.choice`, `Quot.sound`.
