# Perfect unitary links force flat holonomy

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN PROVED]`

Lean: `formal/GaloisForLFunctions/HTGeometry/PerfectUnitaryLinkFlatness.lean`, declarations
`orthonormal_reconstruct_of_crossInnerMatrix_unitary`,
`PerfectUnitaryLinkKernel.link_cocycle`, and
`PerfectUnitaryLinkKernel.triangle_holonomy`. Closed without added axioms.

Source: *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163), perfect-link
globalization theorem. This card supplies a dependency-closed proof suitable for formalization and
does not claim external novelty.

## Statement

Let `I` and `A` be finite. Let `K` be a positive-semidefinite complex matrix indexed by `I × A`
whose diagonal `A × A` block at every `i : I` is the identity. Define

`Lᵢⱼ(a,b) = K((i,a),(j,b))`.

If every `Lᵢⱼ` is unitary, then

1. `Lᵢⱼ Lⱼₖ = Lᵢₖ` for every `i,j,k`, and
2. `Lᵢⱼ Lⱼₖ Lₖᵢ = 1` for every triangle.

## Dependency-closed proof

Positive semidefiniteness gives vectors `vᵢ,a` in one complex Hilbert space with
`K((i,a),(j,b)) = ⟨vᵢ,a,vⱼ,b⟩`. Identity diagonal blocks make each family `(vᵢ,a)ₐ`
orthonormal.

Fix `i,j,b` and put

`p = Σₐ Lᵢⱼ(a,b) vᵢ,a`.

Orthonormality gives `⟨p,p⟩ = Σₐ |Lᵢⱼ(a,b)|²`. Since `Lᵢⱼ` is unitary, its `b`th
column has squared norm one, so `⟨p,p⟩ = 1`. The Gram identity and conjugate symmetry also give
`⟨vⱼ,b,p⟩ = ⟨p,vⱼ,b⟩ = 1`, while `⟨vⱼ,b,vⱼ,b⟩ = 1`. Therefore

`⟨vⱼ,b - p, vⱼ,b - p⟩ = 0`,

hence `vⱼ,b = p`.

Now, for every `a,c`,

`(Lᵢⱼ Lⱼₖ)(a,c)`
`= Σ_b ⟨vᵢ,a,vⱼ,b⟩ Lⱼₖ(b,c)`
`= ⟨vᵢ,a, Σ_b Lⱼₖ(b,c)vⱼ,b⟩`
`= ⟨vᵢ,a,vₖ,c⟩`
`= Lᵢₖ(a,c)`.

Thus `Lᵢⱼ Lⱼₖ = Lᵢₖ`. Applying this twice around a triangle gives
`Lᵢⱼ Lⱼₖ Lₖᵢ = Lᵢᵢ`, and the normalized diagonal block is `Lᵢᵢ = 1`.

## Boundary

Unitarity is the equality case. Contractive cross-Gram blocks need not reconstruct the target
frame, so arbitrary noisy links require a separate quantitative theorem.
