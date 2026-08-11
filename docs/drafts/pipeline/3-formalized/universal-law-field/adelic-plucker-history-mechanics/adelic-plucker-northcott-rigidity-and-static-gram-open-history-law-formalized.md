# Adelic Plücker--Northcott rigidity and static-Gram/open-history law — Lean record

- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/adelic-plucker-history-mechanics/adelic-plucker-northcott-rigidity-and-static-gram-open-history-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/AdelicPluckerHistoryMechanics.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`
- **Status:** [FORMALIZED] [FOUR-ORGAN FUSION] [NO PROJECT AXIOMS] [NOT RH]

## Certified mechanism

One finite diagonal intervention simultaneously:

1. evolves every maximal minor by its Plücker character;
2. reconstructs adjacent relative characters by normalized cross-ratio;
3. satisfies the exact all-place Kummer product formula;
4. has bounded complete and standard projective height exactly when relative history is periodic;
5. may leave the full Archimedean Gram matrix fixed while a non-torsion arithmetic response has
   strictly positive height growing exactly linearly.

The capstone declaration is `HTGeometry.adelicPluckerFusion_capstone`.  Standard projective-height
classification is `HTGeometry.pluckerProjectiveHeight_bounded_iff_periodic`.

## Audit

Direct file check and module build use the repository toolchain.  `#print axioms` for all capstones
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Verified in the foreground:

```text
lake env lean GaloisForLFunctions/HTGeometry/AdelicPluckerHistoryMechanics.lean
lake build GaloisForLFunctions.HTGeometry.AdelicPluckerHistoryMechanics
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint --check-generated
```

Leaf build completed 8,756 jobs; umbrella build completed 11,817 jobs.  Generated API indexes were
refreshed after certification.
