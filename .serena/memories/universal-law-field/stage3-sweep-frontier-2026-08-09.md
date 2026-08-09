# Universal-law-field Stage-2 → Stage-3 sweep (2026-08-09)

Working rule: take the **oldest card by mtime** in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`, formalize it unconditionally, then
`git mv` it to `3-formalized/universal-law-field/`, write a `-formalized.md` companion, add a row to
`2-fully-proven/universal-law-field/_LEAN-CERTIFICATION.md`, and append to
`docs/drafts/pipeline/_stage2-to-3-ledger.md`. All modules go into
`HTGeometry.UniversalLawField`.

## Certified and promoted (12 cards)

| ID | Lean module |
|---|---|
| ULF-CTX-1 | `HTGeometry.ConstitutiveParityContextuality` |
| ULF-IRR-1 | `HTGeometry.ConstitutiveIrreducibleInteraction` |
| ULF-TORS-1 | `HTGeometry.ConstitutiveDeterminantTorsion` |
| ULF-FILL-1 | `HTGeometry.ConstitutiveQuadraticFilling` |
| ULF-DOCT-1 | `HTGeometry.ConstitutiveDoctrineLattice` |
| ULF-ENDP-1 | `HTGeometry.ConstitutiveEndpointInsufficiency` |
| ULF-BULK-1 | `HTGeometry.ConstitutiveBulkBoundaryFusion` |
| ULF-MATCH-1 | `HTGeometry.ConstitutivePolyscopicMatching` |
| ULF-DGLU-1 | `HTGeometry.ConstitutiveDeterminantGluing` |
| ULF-FLUX-1 | `HTGeometry.ConstitutiveAbelianDeterminantFlux` |
| ULF-MOORE-1 | `HTGeometry.ConstitutiveMooreLawCell` |
| ULF-INV-1 | `HTGeometry.ConstitutiveStrictInversionCartier` |

## IN PROGRESS — resume here

**ULF-MPE-1** (`metric-phase-exactness-cost-winding-and-cofinal-strictness-law.md`, still Stage 2).
Module `HTGeometry.ConstitutiveMetricPhaseExactness` is built, wired, axiom-clean and certifies
**Theorem 1 and Theorem 2** in full (determinant amplitude, phase-blind Gram law and its
determinant, Gram eigenvectors = squared singular values, acyclicity, phase erasure vs determinant
separation, `2π`-periodicity, open log lift, winding `N`).
**Remaining: Theorem 3** — the cofinal Hilbert direct sum `⨁ T_{α_n,0}` on `ℓ²(ℕ;ℂ²)`: bounded,
injective, dense nonclosed proper range, `‖T_N⁻¹‖² → ∞`, determinant free energy `→ ∞`; plus the
operator-norm form of (4), `‖T⁻¹‖² = 1/(1−cos α)`. Needs a Hilbert-direct-sum / closed-range layer
(`lp (fun _ => EuclideanSpace ℂ (Fin 2)) 2` or similar) that the corpus does not yet carry.
Do **not** promote the card until Theorem 3 is closed. Status recorded in the card's own
"Lean certification status" section and in `_LEAN-CERTIFICATION.md` (partially certified list).

## Reuse graph — READ BEFORE STARTING A NEW CARD

- Parity/incidence over F₂: `ConstitutiveParityContextuality` (boundary, criterion, proper-face
  solvability, rank `|V|-1`, halving principle).
- Oriented multiplicative version over any abelian `A`: `ConstitutiveAbelianDeterminantFlux`.
  Sign specialization with the `2^β₁` count: `ConstitutiveDeterminantGluing`.
- Based two-term complexes / determinant history / winding: `ConstitutiveDeterminantTorsion`.
- Minimal L∞ law, colour faces, arity truncation: `ConstitutiveIrreducibleInteraction`.
- Van Kampen area / Heisenberg / reduced words: `ConstitutiveQuadraticFilling`.
- Matching-map phases and diagrams: `ConstitutivePolyscopicMatching`.
- `n`-th power law homology over ℝˣ / ℝ_{>0}: `ConstitutiveMooreLawCell`.
- Laurent inversion/Cartier: `ConstitutiveStrictInversionCartier`.

## Findings / corrections

- **ULF-MATCH-1 §4.1 corrected** (card §8): the parity Čech diagram over the subset poset is
  reconstructible, not contextual.
- **ULF-FLUX-1 scope**: `ker ∂_A ≅ A^{β₁}` not certified (no spanning-tree cycle basis in mathlib);
  numeric count certified over F₂ in ULF-DGLU-1.
- **ULF-INV-1 scope**: the derived equivalence (IC.4) and `Tor₁(S,S)` identification (IC.8) not
  certified (no derived-functor layer); the ring-level inputs are.

## Standing environment notes

- The formal lint gate intermittently reports "owned module unreachable"/"stale generated file" for
  modules a **concurrent agent** is mid-editing. Re-run `formal_tools.py index` then `lint`.
- Useful traps met this sweep: `List.Chain'` → `List.IsChain`; `abs_add` → `abs_add_le`;
  `Finset.card_insert_of_not_mem` → `..._of_notMem`; simp turns `↑(Real.cos α)` into
  `Complex.cos ↑α` (block with `-Complex.ofReal_cos`); `Pi.single a 1 v` needs the whole function
  ascribed; `exteriorPower` lives in namespace `ExteriorAlgebra`, notation `⋀[R]^n M`.
