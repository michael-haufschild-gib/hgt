# Integration audit: Locally Quantum, Globally Non-Hilbertizable

Stage: 3-formalized

Status: `[SOURCE AUDITED] [USEFUL CLAIMS INTEGRATED] [LEAN PROVED]`

Source: *Locally Quantum, Globally Non-Hilbertizable* (Zenodo record 21982163).

## Section-by-section disposition

| Source result | Corpus disposition |
|---|---|
| Proposition 2.3, face-surjectivity | `PSDPrincipalExtension.lean`; state and effect zero extensions, exact principal recovery, and trace preservation. |
| Proposition 2.4, local-effect decomposition | Not duplicated: finite conic-duality presentation is specific to the paper's ADT effect cone and has no current corpus consumer. Its reusable face-effect extension consequence is formalized by `MatrixEffect.zeroExtend`. |
| Proposition 3.1, product closure | Existing positive-semidefinite Kronecker closure in mathlib/corpus; no duplicate theorem added. |
| Definition 3.2 and Theorem 3.3, DCP versus CP | Existing ordered amplification framework in `MatrixOrderedMap.lean`, including `IsCompletelyPositive` and `isCompletelyPositive_iff_le_comap`; no parallel vocabulary added. |
| Hilbertization and dimension firewall | `GramRealizationFirewall.lean` and `ContextOrderRobustHilbertization.lean`; exact Gram realization and operator-norm robustness. |
| Strict balanced context hierarchy | `ContextOrderPSDHierarchy.lean` and `ContextOrderTransverseAction.lean`; all orders and exact positive/negative margins. |
| Delocalization/visibility threshold | `ContextOrderVisibilityThreshold.lean`; exact support threshold and noise wall. |
| Negative-inertia bound | `ContextAnomalyRankLaw.lean`; strengthened to every negative-definite subspace, without eigenvalue ordering. |
| Sharp frustration bound | `ContextFrustrationBound.lean`; lower bound and equality witness. |
| Perfect-link flatness | `PerfectUnitaryLinkFlatness.lean`; exact triangle holonomy identity. |
| Scalar triangle spectral wall | `TriangleHolonomySectorLaw.lean`; iff law including singular boundary. |
| Arbitrary-order non-Abelian anomalies | `RationalNonabelianContextAnomaly.lean`; exact rational all-order `1 ⊕ 2` construction, with same-kernel principal Wilson sector. |
| Wilson-walk support cumulants | `WilsonSupportCumulant.lean`; strengthened to arbitrary weighted finite support families over any commutative ring. |
| PSD descent filtration and noise persistence | `PSDContextFiltration.lean`; downward closure and exact threshold filtration. |

## Deliberate non-duplication

Expository state/effect definitions, ordinary matrix-power trace expansion, Newton identities, and
application prose were not reintroduced as project-specific declarations when their mathematical
content is already generic library algebra or not a standalone theorem. The paper-specific conic
presentation of the ADT dual effect cone was not recreated without a corpus consumer. The
four-context numerical benchmark was also not imported: corpus policy forbids computation-based
certificates, while exact symbolic triangle and arbitrary-order anomaly theorems subsume its
structural role.

## Audit boundary

This card records theorem integration, not endorsement of physical interpretation. Every listed
corpus result is a closed symbolic theorem. Minimal internal dimension two for the source's
arbitrary-order non-Abelian construction remains a literature result rather than a claimed Lean
result; corpus theorem uses exact rational internal dimension three and states that distinction in
its dedicated card.
