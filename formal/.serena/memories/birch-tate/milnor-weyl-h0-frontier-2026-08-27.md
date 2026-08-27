# Birch–Tate Milnor inverse frontier — 2026-08-27

Goal remains premise-free Birch–Tate. Research card: `docs/drafts/pipeline/1-in-progress/birch-tate-unconditional-lean.md`.

New Lean artifacts, narrow-built and imported by `HTGeometry.lean`:
- `MilnorKTwoDiagonalExtension.lean`: determinant-one diagonal central extension and Milnor Lemmas 12.1–12.2.
- `MilnorKTwoWeylAction.lean`: corrected adjacent actions, pure/signed Coxeter laws, arbitrary diagonal action, arbitrary Weyl generator/word formula, word-evaluation descent, action hom on full Weyl subgroup and `W₀`, semidirect precursor `MilnorWPre` with injective central Milnor K₂.
- `MilnorKTwoSignSubgroup.lean`: exact intrinsic classification `fin4MilnorH0_eq_signSubgroup`; `H₀` is sign diagonals with central coordinate in `ℤ·{-1,-1}`.

Current open core: construct faithful common-subgroup embedding of classified `H₀` into Milnor case-split `W₀` (signed monomial matrices if `{-1,-1}=0`; integral Steinberg/spin double cover otherwise), then amalgam `W` (Lemmas 12.4–12.5), Bruhat permutation construction (12.6–12.10), central extension of `SL₄(F)`, and Matsumoto injectivity. Do not assume injectivity or choose representatives circularly.

Exact source audit: Milnor §12 cocycle is non-strict `∏_{i≥j} c(u_i,v_j)`. Literature scan was cleaned from `tmp/pdfs`.

Verification: `lake build GaloisForLFunctions.HTGeometry.MilnorKTwoSignSubgroup` passed. `scripts/formal_tools.py lint` reached only unrelated existing failure: untracked `PositiveContactTropicalization` unreachable from umbrella. No full/umbrella build was run.

Use corpus research before continuation. Next promising infrastructure query: finite-field Milnor K₂ vanishing plus functoriality may prove `{-1,-1}≠0 → CharZero F`, required for Milnor case 2.