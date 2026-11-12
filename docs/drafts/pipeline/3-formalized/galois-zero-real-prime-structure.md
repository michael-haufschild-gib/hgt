# The real structure determined by two prime translations

- **ID:** galois-zero-real-prime-structure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Structural location of conjugation on the full zero motive.

## Theorem

For the full zero algebra `A=ℂ[Δ]`, classify all real-algebra endomorphisms
commuting with the prime translations `T_2,T_3`. They are exactly
`T_χ` and `T_χ∘J`, where `χ:Δ→ℂˣ` and

`J(Σ a_z[z])=Σ conjugate(a_z)[conjugate(z)]`.

Among these, the maps preserving the augmentation ideal are exactly
identity and `J`. This reconstructs ordinary conjugation as the unique
nonidentity pointed real-algebra symmetry commuting with both prime clocks.

## Paper argument

The original zero group is closed under conjugation. Consequently `J`
is a real-algebra involution. Since the prime logarithms are real,
`J T_p=T_p J`. The common fixed subspace of `T_2,T_3` is the constant
character line, by distinctness of their joint exponential eigenvalues.

Let `F` be a commuting real-algebra endomorphism. It maps constants to
constants, hence restricts to a real-algebra endomorphism `σ` of `ℂ`.
The equation `σ(i)²=−1` gives `σ(i)=±i`; writing each complex number as
`a+bi` shows that `σ` is identity or conjugation. In the first case `F`
is complex-linear, so the complex centralizer theorem makes it a
translation. In the second case `F∘J` is complex-linear and gives the
second form. Every such map is invertible. The two forms are distinguished
by their action on `i`; within either form the character is unique.

Conjugation preserves the augmentation ideal, since it conjugates the
augmentation value. A translation preserving that ideal has
`χ(z)−1=0` for every basis difference `[z]−1`, hence is identity. This gives
the exact pointed classification.

The action on translating points is
`κ(χ)(z)=conjugate(χ(conjugate(z)))`. It is involutive and satisfies
`J T_χ=T_(κχ) J`, giving the composition law in the classified centralizer.
The distinguished real structure sends every actual zero coordinate `[ρ]`
to `[conjugate(ρ)]`.

## Boundary

The base is all of `ℝ`, not the smaller source field. The result identifies
a real structure on the entire coordinate algebra. It does not identify
conjugation with functional-equation reflection or prove purity. Preserving
the augmentation ideal is essential: requiring the complex-valued
augmentation map itself to be fixed would exclude conjugation.

## Formalization

`GaloisForLFunctions/GaloisTheoryOfZeros/TheRealStructureOfPrimeTranslations.lean`:

- `primeTranslation_real_centralizer_unique`: unique translation and conjugation coordinates.
- `primeTranslation_real_endomorphism_bijective`: automatic invertibility.
- `primeTranslation_real_pointed_centralizer`: exact identity-ideal stabilizer.
- `zeroMotiveRealConjugation_unique`: intrinsic characterization within the real centralizer.
- `zeroMotiveRealConjugation_translation`: conjugation action on translating points.
- `zeroMotiveRealConjugation_zeroCoordinate`: action on every actual zero coordinate.

Final direct source check passed without warnings. All 17 dependency audits
use only `propext`, `Classical.choice`, `Quot.sound`.
