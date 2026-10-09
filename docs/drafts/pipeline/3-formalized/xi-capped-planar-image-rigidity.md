# Planar image rigidity of the actual capped Xi factor

- **ID:** XI-CAPPED-PLANAR-IMAGE-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `HTGeometry/ParabolicOpenEmbedding.lean`, `RHTower/XiCappedNoBoundedEmbedding.lean`.
- **Parent:** `../1-in-progress/xi-capped-surface-uniformization.md`.
- **Statement:** The actual simply connected analytic Xi factor surface has no bounded injective analytic map to C; every analytic open embedding into C is surjective.

## Complete paper proof [PROVED HERE]

Let Xi=p∘G be the checked actual analytic factorization. If u:M→C were analytic, injective and bounded, then u∘G would be a bounded entire function. The corpus Liouville theorem makes it constant. Injectivity makes G constant, and hence Xi constant. The actual high-simple-zero theorem supplies a point where Xi is zero, while xi(0)=1/2. This contradiction excludes u. There is no hypothesis on Xi in the resulting existence theorem for the selected factor surface.

Now let u:M→C be an analytic open embedding. Its image U is open and homeomorphic to the simply connected M. If U is proper, the installed preparatory planar mapping lemma supplies f:C→C that maps U into the unit ball, is injective there, and has nonzero derivative there. Nonzero derivative implies differentiability; on the open U this gives analyticity. Thus f∘u is a bounded injective analytic map of M, contradicting the previous paragraph. Therefore U=C and u is surjective.

The private preparatory lemma is reused from the inspected installed `Mathlib/Analysis/Complex/RiemannMapping.lean` through Lean's `module`/`import all` mechanism. That source contains preparatory lemmas only. No full Riemann mapping theorem, intrinsic uniformization theorem or additional axiom is assumed.

## What remains

Existence of a global analytic open embedding remains unproved. The result reduces uniformization to that existence problem; it does not produce such a coordinate. The main image-cover conjecture and RH remain unproved. External novelty is unverified.

## Lean certificate

Actual theorem: `RHTower.XiMarkedMonodromy.xi_capped_factorization_planar_embeddings_surjective`. Both modules are wired, production leaf builds pass, all four explicit public declarations have standard-only axiom audits, and both final actual-source checks pass with empty logs.

- Audit input/output: `/tmp/hgt-xi-no-bounded-embedding-axioms.lean`, `/tmp/hgt-xi-no-bounded-embedding-axioms.log`.
- Final logs: `/tmp/hgt-ParabolicOpenEmbedding-final.log`, `/tmp/hgt-XiCappedNoBoundedEmbedding-final.log`.
- All modules are indexed. Latest global lint has eight unrelated unreachable-module errors and no own-module or forbidden-declaration errors; full snapshot in `xi-image-cover-analytic-capping.md`.

## Log

- 2026-10-09 — complete argument, public adapter to the installed preparatory lemma, actual unconditional corollaries, all proof checks passed.
