# Middle quasi-isomorphism in a morphism of short exact chain-complex sequences

- **ID:** irregular-rh-short-exact-qiso-middle
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** internal irregular-RH foundation audit; prerequisite for bounded projective K-flatness
- **Statement:** For a morphism between short exact sequences of nonnegative chain complexes in an abelian category, quasi-isomorphisms on the first and third complexes force a quasi-isomorphism on the middle complex.

## Goal
Supply the exact five-lemma bridge needed to induct over a finite projective-cell filtration of a bounded complex. This is standard homological algebra, not an RH endpoint and not new scientific knowledge.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `ShortExactQuasiIso.quasiIso_middle`, targeted `lake build` green, new-declaration axiom audit PASS
- [ ] 3 → 4  publication-ready: not applicable; internal standard infrastructure

## Corpus audit

`scripts/formal_tools.py research "quasiIso tau2 morphism short exact sequences homological complex five lemma"` found no project theorem with this statement. Existing reusable endpoints include degree-zero projective tensor quasi-isomorphism preservation and exact sheafification. Mathlib supplies the long homology sequence and one outer two-out-of-three lemma (`HomologicalComplex.HomologySequence.quasiIso_τ₃`), but its source marks the other analogous lemmas as missing.

## Approach

Fix degree `i`. Apply the abelian five lemma to the natural map between the exact five-term windows

`H_(i+1)(X₃) → H_i(X₁) → H_i(X₂) → H_i(X₃) → H_(i-1)(X₁)`.

The four outer vertical arrows are isomorphisms by the hypotheses. At degree zero, replace the absent final term by zero; exactness there follows because the homology map induced by the epimorphism `X₂ → X₃` is epimorphic at the boundary. Naturality of connecting morphisms supplies the two end squares.

## Paper proof

**[PROVED HERE]** Fix degree `i`. For monicity of the middle homology map, use the exact
four-term window

`H_(i+1)(X₃) → H_i(X₁) → H_i(X₂) → H_i(X₃)`.

The first, second, and fourth vertical maps are respectively epi, mono, and mono because the
outer chain maps are quasi-isomorphisms. The first abelian four lemma makes the third vertical
map mono. If `i = n + 1`, use

`H_i(X₁) → H_i(X₂) → H_i(X₃) → H_n(X₁)`.

The corresponding epi/epi/mono hypotheses and second abelian four lemma make the middle map
epi. At `i = 0`, the map `H₀(X₂) → H₀(X₃)` is epi: `X₂ → X₃` is degreewise
epi and the downward complex shape has no differential out of degree zero. The boundary
three-lemma applied to `H₀(X₁) → H₀(X₂) → H₀(X₃)` makes the middle vertical
map epi. Mono plus epi in an abelian category gives an isomorphism in every degree, hence the
middle chain map is a quasi-isomorphism.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesShortExactQuasiIso`
- Theorem: `GaloisForLFunctions.IrregularStokes.ShortExactQuasiIso.quasiIso_middle`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesShortExactQuasiIso.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesShortExactQuasiIso`
- Axioms: `[propext, Classical.choice, Quot.sound]`

## Hostile review

- Categorical exactness of total tensor is insufficient; this lemma only transports quasi-isomorphisms through an independently established short exact filtration.
- Boundary degree zero must be proved, not hidden by an invalid predecessor index.
- Result must quantify over actual `ShortComplex.ShortExact` witnesses and use mathlib homology, not a bespoke homology predicate.
- This closes one standard infrastructure gap only; it does not prove bounded K-flatness, irregular Riemann–Hilbert, or RH.

## No-go closure

Not applicable: active positive construction.

## Log

- 2026-08-24 — created directly in 1-in-progress after project-corpus audit; paper proof reduced to long-exact-sequence naturality plus five lemma, with degree-zero boundary isolated.
- 2026-08-24 — `[PROVED HERE]`; direct Lean check, targeted module build, and new-theorem axiom audit passed; promoted to 2-fully-proven standard infrastructure.
