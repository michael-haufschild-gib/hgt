# Pre-quasi Gelfand two-sided singular defects (2026-08-03)

Publication-ready route resolves Skrepek, *Quasi Gelfand Triples*, IEOT 97 (2025), Conjectures 6.7 and 6.8 negatively in standard Hilbert model.

Core results:
- For closed densely defined injective dense-range positive embedding A, canonical negative partner is B=(A*)^{-1}.
- Compatible closed negative embeddings are exactly closed subspaces of Graph(B) with dense domain/range coordinate images; quasi iff full graph.
- Proper closed bi-dense graph subspace exists iff both graph coordinate maps lack inverse lower bounds. Equivalently B is unbounded and not bounded below. Codimension-one hyperplane always suffices.
- Explicit H=ell2(Bool x N) diagonal counterexample: B weights (k+1) on false channel and 1/(k+1) on true; A=B^{-1}; use graph parameter maps P=(1/(k+1),1), Q=(1,1/(k+1)) and normal v=(1/(k+1),1/(k+1)); v misses ran P and ran Q, so M=v^perp yields dense P(M),Q(M) but proper closed restriction.

Formal module: formal/GaloisForLFunctions/RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean
Umbrella: formal/GaloisForLFunctions/RHTower.lean
Headline Lean declarations: preQuasi_graph_le_canonical_graph; preQuasi_of_closed_biDense_canonicalGraphSubspace; preQuasi_quasi_iff_eq_canonicalNegative; twoSidedSingular_iff_hasProperClosedBiDenseSubspace; exists_hilbertPreQuasiPair_not_quasi.
Verification: direct lake env lean pass; targeted lake build module pass; #print axioms only propext/Classical.choice/Quot.sound; no sorry/admit/axiom/opaque/unsafe. Global formal_tools.py lint blocked only by unrelated pre-existing HTGeometry umbrella reachability errors (BesselOrder* and PowerSubstitutionJet).

Publication package: docs/drafts/pipeline/4-publication-ready/two-sided-singular-gelfand-defects/
Files: main.tex/main.pdf, PIPELINE_CARD.md, NOVELTY_AUDIT.md, CLAIM_TRACE_AUDIT.md, HOSTILE_REFEREE_REPORT.md.
Final PDF copy: output/pdf/two-sided-singular-defects-rigged-hilbert-spaces.pdf.
Tectonic clean compile; 10-page A4 PDF visually inspected.

Hostile verdict: publication quality at Proceedings AMS / Bulletin LMS short-paper tier; not Annals/JAMS/Inventiones scale. Novelty status remains [NOVELTY UNVERIFIED] pending independent expert and MathSciNet/zbMATH priority review, although published definition/conjectures, exact phrases, parent theory, citation descendants, and March 2026 arXiv revision were audited with no collision found.

Scope: does not prove PDE weak/strong traces differ; only shows pre-quasi axioms alone cannot force equality. No Banach-space classification claimed.