# Wiener zero divisors resist ℓᵖ transport

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Γ215; approximate arithmetic constituents.
- **Statement:** For every finite `p > 0`, zeros of a nonzero Wiener expansion with an interior zero cannot all, outside a finite set, be moved to zeta zeros by displacements with summable `p`th powers of their norms.

## Connection

`InfiniteRankPurityTheory/NoSequenceOfZerosApproachesAClassOfOneFrobenius`
excludes square-summable transport for a vertical progression. The extension
concerns the entire Wiener zero divisor, including arbitrary scale support
and multiplicities, and reaches every finite positive exponent.

## Proof

1. Vanishing displacements force purity. An off-line zero recurs in discs at
   positive density; small displacements put zeta zeros in slightly larger discs,
   contradicting `exists_zetaZeroShiftSet_density_zero`.
2. Compact translates, a uniform window floor and Jensen give uniformly bounded
   total multiplicity in fixed height windows on every smaller strip.
3. Vertical mean squares and the functional equation bound dyadic sums of
   unit-cell square masses `Φ` of `(s−1)ζ(s)` by `O(T^(3+ε/2))` on a sufficiently
   thin strip. Thus `Σ Φ(n)/n^(3+ε)` converges. For `1<q<2`, choose
   `ε=(q−1)/q`; weighted Hölder gives `Σ(√Φ(n)/n²)^q<∞`.
4. Area mean value and disc Lipschitz estimates bound normalized zeta error
   by `C√Φ(n)|η|/n²`. Conjugation handles negative heights; a finite-height
   bound completes a two-sided cell envelope in `ℓᑫ`.
5. Raise the displacement exponent to `P=max(p,3)` and take its conjugate
   `q∈(1,2)`. Bounded local multiplicity transfers the cell envelope to the
   divisor. Hölder makes the multiplicity-weighted zeta residues summable.
6. These summable residues contradict
   `expansion_zero_forces_offLine_or_nonsummable_residues`.

## Lean

`ConstituentTheoryOfTheZeros/WienerZeroDivisorsResistSummableTransport.lean`:
`not_cofinite_zeta_zero_of_summable_displacements`.

The capstone and supporting modules passed direct `lake --old env lean`
checks. Programme umbrellas import the modules.
