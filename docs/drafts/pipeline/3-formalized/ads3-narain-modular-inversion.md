# Modular invariance of the actual Narain partition

- **ID:** W11-NI
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** The convergent normalized Narain partition obeys
  `Z_(ρ,σ)(γτ)=Z_(ρ,σ)(τ)` for every `γ∈SL₂(ℤ)`, together with
  Poisson triality `Z_(ρ,σ)(τ)=Z_(τ,σ)(ρ)`.

## Proof

Write `J(a,b)=(b,−a)` and `S(B,V)=(-B,V)/(B²+V²)`.
Target inversion in `ρ` is a charge permutation: `(n,w)↦(Jw,Jn)`.
Its inverse is `(n,w)↦(−Jw,−Jn)`; spin is unchanged, and expansion of
`M²` shows `M²_(Sρ,σ)(Jw,Jn)=M²_(ρ,σ)(n,w)`.

Momentum Poisson summation gives triality
`Z_(ρ,σ)(τ)=Z_(τ,σ)(ρ)`. The corpus's
`IntegerLatticePoisson.gaussian_theta_characteristics` supplies the
analytic identity with affine convergence. Use
`Bσ(v)=(σ₂v₁,v₂−σ₁v₁)`, Gaussian parameter `τ₂/(ρ₂σ₂)`,
shift `Bσ(ρ₁Jw)` and modulation `τ₁ Bσ^(−T)w`.
The cross phase vanishes by `Jw·w=0`. The dual phase is
`ρ₁ det(m,w)` and its quadratic is
`M²_(τ,σ)(Jm,−w)`. The determinant prefactor converts `τ₂` to `ρ₂`.
The proved Narain Gaussian bound controls both double sums, permitting
Fubini and integer reindexing. Triality followed by target inversion
then proves worldsheet inversion. Together with the proved translation
law, `SpecialLinearGroup.SL2Z_generators` and subgroup closure induction
give invariance under the full modular group.

## Lean endpoints

Modules in `ArithmeticScatteringHolography/ModularBootstrap`:

- `NarainTargetInversion`: `narainPartition_targetInversion`.
- `NarainPoissonCoordinates`: explicit lattice equivalence, determinant,
  inverse adjoint and integer-lattice reindexing.
- `NarainPoissonTerms`: both exact Gaussian characteristic identities.
- `NarainTriality`: `narainPartition_triality` and
  `narainPartition_worldsheetInversion`.
- `NarainModularity`: `narainPartitionOnUpperHalfPlane_modular`.

All five modules passed direct Lean checks; ten endpoint axiom audits
contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports
are wired. No small-height scalar estimate follows from this theorem.

The [mirror-charge theorem](ads3-narain-three-moduli-symmetry.md) now gives all three pairwise moduli exchanges and independent modularity in each variable.

## Gates

- [x] 0 → 1: exact Poisson characteristics and charge reindexing identified.
- [x] 1 → 2: target inversion, triality and worldsheet inversion proved.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
