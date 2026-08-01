# Needs-audit unconditional Lean formalization ledger

- **Kind:** operational audit ledger; not a mathematical claim card
- **Scope:** every tracked card in `../2-fully-proven/needs-audit/` as of 2026-08-01
- **Goal:** map every dependency-closed paper theorem to an exact unconditional Lean theorem, prove missing infrastructure, wire area umbrellas, check axioms/lint/build, then promote its card to Stage 3.
- **Constraints:** no numerical/computational evidence; no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe`; search corpus before new Lean; `lake env lean <file>` during development; `lake build <module>` only at final audit; one foreground Lean process owned by this task; preserve unrelated dirty worktree changes.

## Promotion gate

A source card leaves `needs-audit` only after:

1. every dependency-closed theorem stated as proved in that card is represented exactly, without added route hypotheses or weakened conclusion;
2. every new declaration is unconditional and kernel-checked;
3. `#print axioms` reports only accepted logical foundations;
4. leaf file passes `lake env lean <file>`;
5. area umbrella imports the leaf and final `lake build <module>` passes;
6. formal lint and generated-index checks pass;
7. card records exact theorem/module and `[LEAN-PROVED]` status.

## Worktree isolation

Pre-existing edits exist in `formal/GaloisForLFunctions/HTGeometry.lean`,
`formal/GaloisForLFunctions/RHTower.lean`, `formal/LEAN_API.md`, `formal/lakefile.toml`, and several
untracked Lean modules. Other foreground Lean/Lake jobs were active at task start. Do not overwrite,
revert, or attribute those changes to this ledger. Re-inspect before touching shared umbrellas.

## Card manifest and audit state

Legend: `UNREAD` → `AUDITED` → `LEAN` → `GATED` → `PROMOTED`; `DEMOTE` means inherited Stage 2 evidence is not dependency-closed.

<!-- Entries are appended as card audits close. The canonical 79-file scope is the tracked contents of ../2-fully-proven/needs-audit/. -->

### Audit batch A

| Card | State | Exact audit result | Remaining Lean work |
|---|---|---|---|
| `affine-jet-packet-collision-completeness` | `AUDITED` | Paper theorem proves residual differential independence, exact collision matroid, and operator-rank corollary. Existing `AffineCollisionMatroid` and `AffineJetPacketCollisionCompletion` prove only abstract matroid/Baire assembly from an explicit input structure. | Construct compact-open multivariate entire-function carrier, arbitrary finite Hermite jet interpolation, affine chain-rule packet transport, determinant defects, and determinant-to-differential-independence/operator-rank conversion without packaged hypotheses. |
| `arxiv-2026-electrical-optical-frontier-harvest` | `AUDITED/N-A` | Literature/frontier harvest explicitly declares no formal output and introduces no local theorem to formalize. Cited external theorems are not project proof obligations. | None; verify documentation audit disposition rather than manufacture Lean wrappers. |
| `confocal-envelope-hull-completeness` | `AUDITED` | Every seven-part paper claim has named unconditional theorem in `HTGeometry/ConfocalEnvelopeHull.lean`; area umbrella imports module. | Re-run direct leaf and batched axiom audit; promote. |
| `dumitrescu-wolf-tangent-phase-wrap-obstruction` | `AUDITED` | Abstract tangent recurrence, Xi channels, reciprocal-zero divergence, ordinate enumeration, and actual endpoint obstruction are unconditional in four imported modules. | Re-run direct leaves and batched axiom audit; promote. |
| `theta-likelihood-modular-seam-transport` | `AUDITED` | Existing module proves source factorization, reflection balance, one-crossing/MLR laws, odd integrated jets, Möbius scattering, secant phase, and first barycenter. Card's exact theorem additionally asserts explicit odd score-polynomial representation and strict log-partition/KL identities. | Formalize score polynomials `(8)` and strict convexity/entropy consequences `(15)`--`(16)` exactly. |
| `xi-physical-endpoint-valuation-correction-odd-shuttle` | `AUDITED` | Source deductions `(PVC1)`--`(PVC10)` and balanced Dirichlet decomposition are formalized; falsified raw continuum cancellation is closed by unconditional local-stiffness theorem and exact tangent-renormalized positive survivor in `XiPhysicalEndpointLocalStiffness.lean`. | Re-run direct leaves and batched axiom audit; promote with false route and survivor status preserved. |
| `xi-transverse-aperture-projective-tangent-ultrametric` | `AUDITED` | Projective collapse, oriented tangent grade, valuation scaling, Brownian kernel, Laplace primitive, and actual Xi prime-power identity are exact in `XiTransversePrimeSourceProjectiveTangent.lean`. | Re-run direct leaf and batched axiom audit; promote. |
| `xi-transverse-gamma-valuation-schur-translation` | `AUDITED` | Exact Gamma-coordinate identity, Hardy shift, Schur translation, finite block positivity, and source marking are unconditional in `XiTransverseGammaValuationCoherence.lean`. | Re-run direct leaf and batched axiom audit; promote. |
| `xi-transverse-valuation-szego-true-aperture-metric` | `AUDITED` | Disk node, prime-power defect, successive layer, Vandermonde rank/Gram, completed Szegő metric, and pseudohyperbolic separation are unconditional in `XiTransverseValuationSzegoMetric.lean`. | Re-run direct leaf and batched axiom audit; promote. |

## Log

- 2026-08-01 — ledger created; 79 tracked cards, 38,432 total lines. Required project, formal, scientific-method, skill, and Serena memory guidance read. No task-owned Lean process started.
