# Smooth incoming cubic forcing

- **ID:** cubic-smooth-incoming-forcing
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** For `1<a<b`, a smooth cubic-equivariant incoming seed equals `v^s` above height `b`. Its Laplace defect descends to a smooth compactly supported quotient function and defines an entire quotient `L²` family.

Distinct principal cusp cosets cannot both have height above one: their
height product is at most one. Thus the character-weighted high-cusp sum
has at most one nonzero term. Bounded integral rows give local finiteness,
so summing smooth profiles preserves smoothness and character automorphy.

Let `χ` transition from zero below `a` to one above `b`, and put
`H_s(v)=χ(v)v^s`. The axis Laplacian gives
`v²H_s″−vH_s′−s(s−2)H_s=v^s(v²χ″+(2s−1)vχ′)`.
This defect vanishes outside `[a,b]`. In an integral cusp of height
`v>max(b,a⁻¹)`, each row height is either `v` or at most `1/v`; hence
every defect term vanishes. Bianchi reduction therefore makes the
quotient defect support compact. The actual smooth quotient charts
transport its coordinate smoothness.

High-cusp uniqueness bounds the profile sum by its scalar sup norm.
Finite quotient volume gives a continuous linear map
`C([a,b],ℂ) → L²`. The defect is its image of the Banach-algebra family
`exp(s log v)(v²χ″+(2s−1)vχ′)`, which is entire. Its `L²` class agrees
with the compact smooth test defined by the pointwise defect.

Lean targets: `CharacterEquivariantCubicCuspProfiles.lean`,
`CubicIncomingHeightProfiles.lean`, `SmoothCubicCuspSeeds.lean`,
`CubicCompactHeightProfiles.lean`, and `CompactSmoothCubicDefects.lean`
in `MetaplecticMobiusDescent`, namespace `CubicEisenstein`.

The source-resolvent matching and nonzero residue remain on the parent
card. Adapted from OpenAI's cusp-profile, compact-profile, and smooth-test
arguments, using the locally checked height calculus and quotient.
