# The cubic Eisenstein source series

- **ID:** cubic-eisenstein-source-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** Construct the actual level-three cubic Eisenstein series, prove absolute convergence and holomorphic dependence for `Re s>2`, and prove its character automorphy on hyperbolic three-space.

Quotient level-three matrices by equality of their bottom rows. The cubic
character is constant on these classes because a matrix with zero lower-left
entry has character one. Right multiplication reindexes the classes and
multiplies their character values.

Define `E(g,s)=Σ_x κ(x)⁻¹ ‖row(x)g‖₂^(−2s)`. Integral coordinates embed the
rows into `ℤ⁴`; the inverse matrix bounds coordinate norm by row energy.
The lattice series with exponent `2 Re s>4` dominates absolutely. Two
bounding real exponents dominate each vertical strip, proving holomorphic
dependence. Right unitary invariance descends to hyperbolic space, and right
reindexing gives `E(Mw,s)=κ(M)E(w,s)`.

Source: external OpenAI `Eisenstein/Rows.lean` and `HyperbolicSpace.lean`.
Lean: `MetaplecticMobiusDescent/TheCubicEisensteinSeries.lean`.
Endpoints: `summable_norm_summand`, `eisenstein_differentiableOn`,
`hyperbolicEisenstein_automorphy`, `hyperbolicEisenstein_eq_height_series`,
and `height_series_summable_norm`, all in namespace `CubicEisenstein`.
Direct Lean check passes. All five transitive audits use only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella wired.

Continuation to `s=4/3`, residue nonvanishing, and Gauss coefficient
identification remain separate obligations.
