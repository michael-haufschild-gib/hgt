# Proofing Index

Status: SEARCH-register proofing workspace, 2026-06-21.

This directory contains one working proof file per conjecture or unproven theorem
claim drawn from `docs/consolidated/`. The target is not a literature summary.
Each file must contain an actual proof attempt, including any weakened theorem
that can be proved, and the precise obstruction where the full claim remains open.

## Coverage Status

| ID | Claim | Source | Proofing file | Status |
|---|---|---|---|---|
| C1 | Carrier is one oriented 2-form | `08` §1 | `08-c1-oriented-two-form.md` | attempted; weakened Stokes theorem proved |
| C2 | Carrier is affine weld holonomy | `08` §1 | `08-c2-affine-weld-holonomy.md` | attempted; scalar-holonomy no-go proved |
| C3 | Long-run coherence is phase Sobolev gap | `08` §1 | `08-c3-phase-sobolev-regularity.md` | attempted; H1 conditional bound proved |
| C4 | Divergent cross-lane correlation length | `08` §1 | `08-c4-cross-lane-correlation.md` | attempted; analytic-coupling lemma only |
| C5 | Genuine crossover scale sigma* | `08` §1 | `08-c5-crossover-scale.md` | attempted; analytic-statistic no-go proved |
| C6 | Inverse problem from primes plus boundary cocycle | `08` §1 | `08-c6-inverse-problem.md` | attempted; finite-jet obstruction isolated |
| B1 | Transport signatures force source-measure confinement | `08` §2, `03` §1 | `08-b1-source-measure-bridge.md` | attempted; argument-principle reduction proved |
| B2 | Detection plus confinement bridge | `08` §2, `03` §2 | `08-b2-two-lemma-bridge.md` | attempted; local detection proved, global confinement open |
| B3 | Off-line zero iff off-seam source-carrying defect | `08` §2 | `08-b3-rh-false-bridge.md` | attempted; conditional equivalence proved |
| APEX-A | Schanuel-for-prime-logs / algebraic corank | `08` §3 | `08-apex-a-schanuel-prime-logs.md` | attempted; two-prime homogeneous GS rung proved |
| APEX-B | Faithful positivity / all-degree RH positivity | `08` §3 | `08-apex-b-faithful-positivity.md` | attempted; equivalence/detection proved, vanishing open |
| APEX-C | Universal prime-side orthogonality | `08` §3 | `08-apex-c-universal-orthogonality.md` | attempted; rank-one obstruction proved |
| APEX-D | Native weld / C5-star branchhood lock | `08` §3 | `08-apex-d-native-weld-lock.md` | attempted; Door-2 reducibility criterion proved |
| C-2026-06-18-005 | Route-C arch-prime positivity | `08` §4 | `08-worklog-005-route-c-arch-prime-positivity.md` | attempted; conditional positivity reduction |
| C-2026-06-18-011 | Type-III rigidification | `08` §4 | `08-worklog-011-type-iii-rigidification.md` | attempted; Fredholm index-stability reduction |
| C-2026-06-18-001 | `D_infty` period-domain | `08` §4 | `08-worklog-001-period-domain.md` | attempted; conditional period-index reduction |
| C-2026-06-18-021 | Hodge-index realization | `08` §4 | `08-worklog-021-hodge-index.md` | attempted; comparison theorem isolated |
| C-2026-06-18-039 | Two-variable kernel | `08` §4 | `08-worklog-039-two-variable-kernel.md` | attempted; negative-square kernel reduction |
| C-2026-06-18-008 | Archimedean Iwasawa via Takesaki | `08` §4 | `08-worklog-008-archimedean-iwasawa.md` | attempted; FK determinant host isolated |
| C-2026-06-18-018 | `Q_3` / higher-Chowla | `08` §4 | `08-worklog-018-q3-higher-chowla.md` | attempted; faithful-index readout missing |
| DSS-cross | `{gamma_n}` algebraic independence | `08` §4 | `08-worklog-dss-cross.md` | attempted; exponential-period realization gap |
| Jensen TP-defect | Jensen non-real roots count `2 kappa_-` | `08` §4 | `08-worklog-jensen-tp-defect.md` | attempted; all-level hyperbolicity reduction |
| Meta-principle | Regularization manufactures transcendence | `08` §4 | `08-worklog-regularization-transcendence.md` | attempted; unrestricted principle rejected |
| C-2026-06-18-044 | FID sufficient for RH | `08` §4 | `08-worklog-fid-sufficient.md` | attempted; free-to-Weil bridge isolated |
| G-C10 | Source-built faithful-index object | `08` appendix | `08-gc10-source-built-faithful-index-object.md` | attempted; object construction missing |
| G-C11 | F1/Hodge polarization | `08` appendix | `08-gc11-f1-hodge-polarization.md` | attempted; Hodge comparison missing |
| G-C15 | One object, two entrances | `08` appendix | `08-gc15-one-object-two-entrances.md` | attempted; common carrier missing |
| G-C16 | Source-built Jacobi positivity | `08` appendix | `08-gc16-source-built-jacobi-positivity.md` | attempted; all-level operator missing |
| G-C17 | Uniform Jensen stability | `08` appendix | `08-gc17-uniform-jensen-stability.md` | attempted; uniformity missing |
| G-C18 | Faithful-index rigidity | `08` appendix | `08-gc18-faithful-index-rigidity.md` | attempted; no-margin index stability missing |
| G-C19 | Primitive Schur/Hodge equivalence | `08` appendix | `08-gc19-primitive-schur-hodge-equivalence.md` | attempted; projective/Hodge comparison missing |
| L-A..L-E | Required light-tower lemma-shapes | `07` §3 | not started | pending |
| Faithful-index spine | Source-built object, index equality, index vanishing, Hodge/F1 realization | `07` appendix | not started | pending |
| Build targets | Jacobi atlas, positive contraction, Jensen stability, Krein-Langer carrier, Schur/Hodge bridge, fake-family separation, no-margin | `07` appendix | not started | pending |
| Theorems A-L | Light tower detector ladder | `03` §3 | not started | pending |
| Five-form bridge package | Source object, faithful index, vanishing, fake-family, no-margin | `03` appendix | not started | pending |

## Working Rule

A file marked "attempted" does not mean the claim is proved. It means a genuine
mathematical proof attempt has been made and the remaining obstruction has been
named. Promotion to `[PROVED]` requires a complete proof or Lean evidence outside
this SEARCH-register workspace.
