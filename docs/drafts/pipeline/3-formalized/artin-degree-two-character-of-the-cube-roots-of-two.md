# The index law for the degree-two Artin character of ℚ(∛2, ω)

- **ID:** A133
- **Stage:** 3-formalized
- **Lean:** `HeckeLFunctions/ResidueCharactersTrivialOnUnitsAreHeckeCharacters.lean`,
  `AbsoluteGeometryOfSpecZ/TheCubicCharacterOfTwoIsARayClassCharacterModuloSix.lean`,
  `AbsoluteGeometryOfSpecZ/TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex.lean`

## Statement

Let `ρ` be the irreducible character of degree two of `Gal(ℚ(∛2,ω)/ℚ) ≅ S₃`. Its contacts are
point counts, uniformly in `p` (the ramified `2`, `3` included):

`Λ_ρ(p^m) = (#{x ∈ 𝔽_{p^m} : x³ = 2} − 1) log p`  (`artinCubeContact`).

Then `Λ_ρ = Λ_χ` for the cubic character `χ` of `2` over `ℚ(ω)`, a primitive ray class character
modulo `6`; `L(s,ρ)` has Weil's explicit formula with these contacts; and Weil's form of `ρ` has `n`
negative squares on some family of `n` tests iff `L(s,ρ)` has at least `n` distinct zeros right of
the critical line. No negative square ⇔ GRH for `L(s,ρ)`.

## Proof

1. Class number one: a residue character of `(𝓞/𝔪)ˣ × signs` trivial on global units is a ray class
   character (`heckeOfResidue`).
2. `χ(𝔞) = (π_𝔞 mod 2)`, `π_𝔞` the primary generator (`≡ 1 mod λ²`), read through the cubic
   residue character of the inert prime `2`. It depends on `α mod 6` on principal ideals (two
   primary normalizations of the same residue mod `λ²` use the same unit). Conductor exactly `6`:
   `χ(1+3ω) ≠ 1` with `1+3ω ≡ 1 (3)`, `χ(1+2λ) ≠ 1` with `1+2λ ≡ 1 (2λ)`; every divisor of `6`
   other than `6` contains `3` or `2λ`.
3. Cubic reciprocity at `2` (corpus): at `𝔭 ∤ 6`, `χ(𝔭) = (2/𝔭)₃`.
4. Euler's criterion for cubes in `𝔽_q`: three roots iff `a^{(q−1)/3} = 1` when `3 ∣ q−1`, one root
   when `3 ∤ q−1`. Inert `p ≡ 2 (3)`: `(p)` is the prime above `p`, `χ((p)) = 1`; one root for odd
   `m`, three for even `m`. Split `p ≡ 1 (3)`: two primes of norm `p`, `χ(𝔭)χ(𝔭̄) = χ((p)) = 1`;
   `2^{(p^m−1)/3} = (2^{(p−1)/3})^m` and reduction mod `𝔭` give "three roots iff `χ(𝔭)^m = 1`";
   `u + u⁻¹ = −1` for a primitive cubic root `u`. `p = 2, 3`: both sides vanish.
5. Apply the Hecke explicit formula and index law to `χ`.

Declarations: `heckeMangoldt_cubicTwoHecke`, `logDeriv_heckeL_cubicTwoHecke`, `W_artinZeros_eq`,
`exists_le_negIndex_artinGram_iff`, `forall_negIndex_artinGram_eq_zero_iff`,
`heckeFiniteConductor_cubicTwoHecke`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
