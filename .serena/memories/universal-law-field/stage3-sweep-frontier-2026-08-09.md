# Universal-law-field Stage-2 → Stage-3 sweep (2026-08-09)

Working rule: take the **oldest card by mtime** in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`, formalize it unconditionally, then
`git mv` it to `3-formalized/universal-law-field/`, write a `-formalized.md` companion, add a row to
`2-fully-proven/universal-law-field/_LEAN-CERTIFICATION.md`, and append to
`docs/drafts/pipeline/_stage2-to-3-ledger.md`. All modules go into
`HTGeometry.UniversalLawField`.

## Certified and promoted (14 cards)

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
| ULF-MPE-1 | `HTGeometry.ConstitutiveMetricPhaseExactness` (+ `HTGeometry.HilbertBlockOperator`) |
| ULF-LSW-1 | `HTGeometry.ConstitutiveStabilityWall` |

`#print axioms` clean on every capstone.

## NEXT CARD

`isotropic-law-passive-gauge-intervention-port-and-open-projective-history-law.md` (mtime 11:28).

## Reuse graph — READ BEFORE STARTING A NEW CARD

- F₂ parity/incidence: `ConstitutiveParityContextuality`.
- Oriented multiplicative flux over any abelian `A`: `ConstitutiveAbelianDeterminantFlux`;
  sign case with the `2^β₁` count: `ConstitutiveDeterminantGluing`.
- Based two-term complexes / determinant history / winding: `ConstitutiveDeterminantTorsion`.
- Minimal L∞ law, colour faces, arity truncation: `ConstitutiveIrreducibleInteraction`.
- Van Kampen area / Heisenberg / reduced words: `ConstitutiveQuadraticFilling`.
- Matching-map phases and diagrams: `ConstitutivePolyscopicMatching`.
- `n`-th power law homology over ℝˣ / ℝ_{>0}: `ConstitutiveMooreLawCell`.
- Laurent inversion/Cartier: `ConstitutiveStrictInversionCartier`.
- 2×2 aperture blocks, Gram/singular values, filling energy, winding lift:
  `ConstitutiveMetricPhaseExactness`.
- **Operator-valued block diagonal on `lp K 2`**: `HTGeometry.HilbertBlockOperator`
  (`blockOperator`, injective / dense range / not surjective / nonclosed range). Mathlib has none;
  the corpus previously had only the *scalar* version
  (`RHTower.DeningerPrimeBlockGreenSummability`).
- **`Complex.arg` order on the upper half-plane**: `ConstitutiveStabilityWall`
  (`arg_div_eq_sub`, `arg_lt_arg_iff_cross_pos` — phase order = sign of the cross product).
  Mathlib has no arg-comparison lemma.
- Other existing pieces worth knowing:
  `HTGeometry.BoundedMultiplierHilbert.denseRange_of_orthogonal_trivial`,
  `HTGeometry.CompactOperatorDiscreteSpectrum.denseRange_of_isSelfAdjoint_of_injective`,
  `RHTower.DiagonalEllTwoOperator.diagonalOperator`,
  `NomologicalHomotopyGeometry.MinimalLawLeadingJet` (`MinimalLaw`, `MinimalLawEquiv`).

## Findings / scope notes

- **ULF-MATCH-1 §4.1 corrected** (card §8): the parity Čech diagram over the subset poset is
  reconstructible, not contextual.
- **ULF-FLUX-1**: `ker ∂_A ≅ A^{β₁}` not certified (no spanning-tree cycle basis in mathlib);
  numeric count certified over F₂ in ULF-DGLU-1.
- **ULF-INV-1**: derived equivalence (IC.4) and `Tor₁(S,S)` (IC.8) not certified (no
  derived-functor layer); the ring-level inputs are.
- **ULF-MATCH-1** Cor 2.4 (higher homotopy) out of chart; 0-truncated content certified.

## Standing environment notes

- The lint gate intermittently reports "owned module unreachable"/"stale generated file" for modules
  a **concurrent agent** is mid-editing (ConstraintRelativity, ConstraintFrameRelativity,
  DerivedSelectionGeometry, RHTower Eigen*). Re-run `formal_tools.py index` then `lint`. Running
  `lint --check-generated` twice in one command exceeds the 600 s tool timeout — run it once.
- Traps met: `List.Chain'`→`List.IsChain`; `abs_add`→`abs_add_le`;
  `Finset.card_insert_of_not_mem`→`..._of_notMem`; `pow_le_pow_left` needs `IsMulTorsionFree`
  (use a `Real.pow_rpow_inv_natCast` helper on nonnegatives); simp turns `↑(Real.cos α)` into
  `Complex.cos ↑α` (block with `-Complex.ofReal_cos`); `Pi.single a 1 v` needs the whole function
  ascribed; `exteriorPower` lives in namespace `ExteriorAlgebra`, notation `⋀[R]^n M`;
  `EuclideanSpace.single_apply` deprecated → `PiLp.single_apply`;
  `(f).comp hlim` gives `Real.cos ∘ α` — `rw [Real.cos_zero] at h; exact h`, not `simpa`;
  `push_neg` deprecated — use `rw [not_lt]` etc. (the lint gate fails on warnings).
