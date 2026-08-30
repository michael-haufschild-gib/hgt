# ULF-SGOGM-2 — Lean certification record

Card: `split-recovery-formation-capital-monotonicity-functional-equation-neutrality-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules (both new)

| Module | Card sections |
|---|---|
| `GaloisForLFunctions.HTGeometry.SplitRecoveryFormationCapital` | §2, §3, §4, §5, §7.1, §8 |
| `GaloisForLFunctions.HTGeometry.CommonMarkovRecoveryNeutrality` | §6 |

Both are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`, which
`GaloisForLFunctions.HTGeometry` imports.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(RCN.2)`, `(RCN.3)` extended formation capital | `formationFactorizations`, `formationCapital`, `formationCapital_le_of_mem`, `formationCapital_mono`, `formationCapital_congr`, `formationCapital_eq_top_iff` |
| `(RCN.4)` the null space `ker W_*` and the minimizing factor | `coimageProjection` (with `hasOrthogonalProjection_ker`, `comp_coimageProjection`, `norm_coimageProjection_le`, `coimageProjection_eq_self_of_injective`), `minimalFactor`, `minimalFactor_mem` |
| §2 attainment | `formationCapital_eq_of_mem` — the infimum is realized by `minimalFactor W B` for any factorization `B` |
| §2 orthogonality and uniqueness | `hsInner_minimalFactor_eq_zero`, `hsInner_sub_left`, `minimalFactor_unique` |
| `(RCN.11)` | `formationFactorizations_comp` |
| **Theorem 3.1**, `(RCN.5)` | `formationFactorizations_subset_comp`, `formationCapital_comp_le` |
| **Theorem 3.1 I**, `(RCN.6)` | `formationFactorizations_comp_of_injective`, `formationCapital_comp_of_injective` |
| **Theorem 3.1 II**, `(RCN.7)` | `formationCapital_comp_of_leftInverse` |
| **Theorem 3.1 III**, `(RCN.8)`, `(RCN.9)` | `kernelErasure_of_formationCapital_lt` |
| **Theorem 3.1 IV**, `(RCN.10)` | `formationCapital_serial_le`, `formationCapital_serial_of_injective` |
| `(RCN.12)`, `(RCN.13)` | `formationCapital_equivTransport` |
| `(RCN.14)`, `(RCN.15)` | `formationCapital_fe_split` |
| `(RCN.18)` recovered Gramian, and its injectivity on the closed recovered carrier | `recoveredGramian`, `inner_recoveredGramian`, `eq_zero_of_inner_recoveredGramian_eq_zero` |
| `(RCN.19)` | `formationCapital_recovered` |
| `(RCN.19a)` | `formationCapital_eq_top_fe_split_iff` |
| `(RCN.20)` split packet laws | `splitPacketLaw`, with its finiteness instances |
| marginalization is a left inverse | `splitPacketLaw_fst` |
| `(RCN.21)` | `klDiv_splitPacketLaw`; Hellinger form `bhattacharyya_splitPacketLaw` |
| `(RCN.22)` | `splitPacketLaw_withDensity` |
| `(RCN.23)` | `lintegral_splitPacketLaw_comp_fst`, `eLpNorm_splitPacketLaw_comp_fst` |
| `(RCN.24)` | `commonRecovery_certificate` |
| `(RCN.25)`, `(RCN.26)` sharp countermodel | `RecoveryCountermodel.defect`, `recovery`, `hsNormSq_defect`, `formationCapital_defect = 1`, `recovery_comp_defect`, `formationCapital_recovery_defect = 0`, `formationCapital_recovery_lt` |
| `(RCN.27)` | `iSup_formationCapital_fe_split` |

`(RCN.16)` and the atomic-refinement wall of `(RCN.19a)` are quoted inputs from the orbit-capital
parent `ULF-SGOGM-1`, not claims of this card; what this card proves about them — the injectivity of
the recovered Gramian on the closed recovered carrier and the exact transport of the capital, hence
of the wall — is formalized above.  §7.2–§7.4 and §9 are scope commentary with no theorem content.

## Design note

The card justifies attainment by "the solution set is a closed affine subspace of the Hilbert space
`S₂(U,K)`", which would need completeness of the Hilbert–Schmidt operator space.  That is avoided:
the minimizer is produced explicitly as `coimageProjection W ∘L B`, i.e. by projecting every column
of an arbitrary factorization onto `(ker W)ᗮ`.  Its optimality is Hilbert–Schmidt Pythagoras against
the null factors, whose columns lie in `ker W`.  Nothing beyond completeness of `K` is used.

## Verification

* Both modules elaborate with 0 errors and 0 warnings and build.
* `#print axioms` over every public theorem of both modules (44 declarations) reports only
  `propext`, `Classical.choice`, `Quot.sound`.
