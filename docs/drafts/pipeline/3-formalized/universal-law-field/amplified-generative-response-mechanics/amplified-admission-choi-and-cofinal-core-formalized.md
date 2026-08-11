# Amplified admission Choi and cofinal core — formalized

- **Parent card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/amplified-generative-response-mechanics/amplified-admission-depth-escape-and-reduction-pencil-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.AmplifiedGenerativeAdmission`
- **Scope:** exact rank-one/Choi threshold and product-directed cofinal false-promotion core
- **Excluded:** full intermediate `k`-positive reduction-map theorem, arithmetic realization, RH

## Certified declarations

- `rankOneAdmissionPencil`
- `one_sub_rankOne_posSemidef`
- `rankOneAdmissionPencil_posSemidef_iff`
- `reductionChoiPencil`
- `reductionChoiPencil_posSemidef_iff`
- `reductionAmplifiedThreshold`
- `reductionAmplifiedThreshold_fixed_depth_uniform`
- `reductionAmplifiedThreshold_diagonal_not_uniform`
- `reductionAmplifiedThreshold_false_promotion`

The first capstone is the actual positive-semidefinite matrix law

\[
 cI-r|z\rangle\langle z|\succeq0\quad\Longleftrightarrow\quad c\ge r
\]

for a normalized ray and `r>0`.  Specializing `r=n` certifies the Choi-matrix threshold of the
reduction pencil.  The second capstone certifies that the exact threshold profile `min(n,k)` has a
finite bound at every separately fixed depth but no bound on the complete diagonal.

The module is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Formal boundary

Lean does not yet certify that `id_(M_k) tensor (c Tr(.) I - id)` is positive exactly when
`c >= min(k,n)`.  That upgrade needs a formal Schmidt/SVD decomposition or an equivalent
rank-sensitive trace inequality.  The paper proof is dependency-closed, but this record claims
formal credit only for the Choi endpoint and cofinal logic above.
