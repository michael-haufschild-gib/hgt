# Nonnegative componentwise-projective total tensor is K-flat

- **ID:** irregular-rh-nonnegative-projective-total-tensor-k-flat
- **Stage:** 3-formalized
- **Type:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
- **Source:** internal irregular-RH derived-tensor foundation audit; Stacks Project, Tag 06YQ; Spaltenstein (1988), §5
- **Statement:** Total left tensor by any nonnegative componentwise-projective complex of module presheaves preserves quasi-isomorphisms of nonnegative complexes.

## Goal
Close the genuine K-flatness input needed to descend presheaf total tensor to a derived tensor operation. This is standard first-quadrant homological algebra, not an RH endpoint and not new scientific knowledge.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, no open dependency
- [x] 2 → 3  formalized: targeted Lean theorem/module, targeted build green, new-declaration axiom audit PASS
- [ ] 3 → 4  publication-ready: not applicable; internal standard infrastructure

## Corpus audit

`scripts/formal_tools.py research "K-flat bounded componentwise projective total tensor quasi-isomorphism Stokes"` found no project theorem with this statement. Reusable project results are:

- degree-zero projective module-presheaf tensor preserves quasi-isomorphisms;
- total tensor by a componentwise-projective complex preserves monomorphisms and exact short complexes categorically;
- outer quasi-isomorphisms force the middle quasi-isomorphism in a morphism of short exact nonnegative complex sequences.

Mathlib has K-projectivity for bounded-above projective complexes and general total-complex machinery, but no K-flat total-tensor theorem or total-complex spectral-sequence/exact-row endpoint found by API audit.

## External state of art and novelty verdict

- Stacks Project, [Lemma 21.17.8, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ), proves that a bounded-above complex of flat modules on a ringed site is K-flat by the first tensor spectral sequence.
- Spaltenstein, [Resolutions of unbounded complexes](https://www.numdam.org/item/CM_1988__65_2_121_0.pdf), defines K-flatness in §5, identifies single-degree K-flat complexes with flat modules in Proposition 5.2, and proves closure under distinguished triangles in Proposition 5.4(d).
- A nonnegative chain complex becomes a cochain complex bounded above at zero after the standard reindexing. Thus the strengthened statement is standard mathematics, not a novelty claim.

**Verdict:** `[REDISCOVERED] [BRIDGE]`. The contribution is a Lean bridge specialized to the project's nonnegative total tensor and module-presheaf APIs.

## Complete paper proof

Let `P`, `X`, and `Y` be nonnegative chain complexes of module presheaves, assume every `P_p` is projective, and let `f : X ⟶ Y` be a quasi-isomorphism. Write `T(X) = Tot(P ⊗ X)` and similarly for `Y`.

1. For `r : ℕ`, define the filtration subcomplex
   `F_r T(X)_n = ⨁_{p+q=n, p≤r} P_p ⊗ X_q`.
   Both components of total differential lower one of `p,q`, so they preserve `p≤r`. Every displayed coproduct is finite.
2. `F_0 T(f)` is the degree-translated map `P_0 ⊗ f`. More generally, the quotient morphism
   `Gr_r T(f) : F_r T(X)/F_{r-1} T(X) ⟶ F_r T(Y)/F_{r-1} T(Y)`
   is `P_r ⊗ f`, translated upward by `r`; its differential may differ by the fixed totalization sign `(-1)^r`, which does not change kernels, images, or homology.
3. Projectivity of `P_r` implies that degreewise left tensor by `P_r` maps quasi-isomorphisms to quasi-isomorphisms. Hence every `Gr_r T(f)` is a quasi-isomorphism.
4. For each successor stage there is a degreewise split short exact sequence of complexes
   `0 ⟶ F_{r-1} T(X) ⟶ F_r T(X) ⟶ Gr_r T(X) ⟶ 0`,
   natural in `X`, and likewise for `Y`. The base `F_0 T(f)` is a quasi-isomorphism by step 3. Inductively, the outer vertical arrows in the two short exact sequences are quasi-isomorphisms, so the middle arrow `F_r T(f)` is a quasi-isomorphism by the short-exact middle two-out-of-three theorem.
5. Fix `n`. Since `p,q≥0`, the inclusion `F_{n+1} T(X) ⟶ T(X)` is an isomorphism in the adjacent degrees used to define `H_n`: degrees `n+1`, `n`, and `n-1` when `n>0`, and degrees `1`, `0` when `n=0`. It therefore induces an isomorphism on `H_n`; the same holds for `Y`. The natural square with `F_{n+1} T(f)` conjugates `H_n(T(f))` to an isomorphism. Since `n` was arbitrary, `T(f)` is a quasi-isomorphism.

No global boundedness of `P` is needed: each fixed homological degree sees only one finite antidiagonal and stabilizes after a finite filtration stage.

## Lean realization

- `StokesNonnegativePrefixFiltration` constructs finite stupid prefixes, adjacent natural short
  exact sequences, and canonical inclusions into the original complex.
- `StokesFirstQuadrantTotalSingle` identifies totalization of a single row with a translated
  sign-twisted row and proves preservation of row quasi-isomorphisms.
- `StokesFirstQuadrantRowwiseQuasiIso` performs short-exact finite-prefix induction and proves
  direct degree-`n` stabilization at prefix `n + 1`, without spectral sequences.
- `StokesProjectiveComplexTensorKFlat.componentwiseProjectiveTotalTensorLeft_map_quasiIso`
  specializes the rowwise theorem using
  `ProjectivePresheafTensorFlat.projectiveTensorLeft_map_quasiIso` in every row.

## Hostile review

- Do not infer K-flatness from categorical exactness of the total-tensor endofunctor.
- Prove the filtration subcomplex, degreewise split quotient, graded-piece translation/sign comparison, and naturality; degree-zero flatness cannot be silently reused in another degree.
- Do not invoke convergence of an infinite filtration. The proof must use explicit stabilization at `F_{n+1}` for each `H_n`.
- Check degree zero separately because no degree `-1` exists.
- Projectivity is used only through the already-proved quasi-isomorphism preservation of `P_r ⊗ -`; do not add boundedness or other hypotheses.
- This theorem enables derived tensor descent only; it does not construct the derived sheaf tensor, enhanced category, irregular Riemann–Hilbert equivalence, arithmetic source, or RH proof.

## No-go closure

Not applicable: active positive construction.

## Log

- 2026-08-24 — created in 1-in-progress after project and mathlib API audits; short-exact quasi-isomorphism induction bridge already formalized.
- 2026-08-24 — external audit identified the stronger nonnegative theorem as the standard bounded-above K-flat result. Closed a finite-filtration paper proof, removed unnecessary boundedness, classified `[REDISCOVERED] [BRIDGE]`, and promoted to 2-fully-proven.
- 2026-08-24 — formalized the full finite-prefix proof, explicit stabilization, rowwise total
  quasi-isomorphism theorem, and componentwise-projective total-tensor K-flat specialization.
  Direct Lean checks, targeted module builds, and new-declaration axiom audit passed; promoted to
  3-formalized.
