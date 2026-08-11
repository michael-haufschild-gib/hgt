# Gap-free energy-defect centralizer tube (2026-08-11)

## Result
New Lean module: `formal/GaloisForLFunctions/HTGeometry/FiniteUnitaryEnergyDefectLaw.lean`, wired into `HTGeometry.lean`.

For finite Hermitian H and unitary U, with `E(A)=Re tr(A* A)`:
`E(HU-UH)=2(Re tr(H^2)-Re tr(H U* H U))`.
Also `E(A)=sum_{i,j}|A_ji|^2`, hence `E(A)=0 iff A=0`, and full adjoint autocorrelation iff `HU=UH`.
For nonzero traceless Hermitian H on D>=2:
`Pr_Haar{||HU-UH||_HS^2 <= tr(H^2)} <= 4/(D^2-1)`.
No spectral gap/nondegeneracy/dictionary size.

## Verification
- `lake env lean GaloisForLFunctions/HTGeometry/FiniteUnitaryEnergyDefectLaw.lean` passes.
- `lake build GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw` passes (only inherited warnings).
- #print axioms all five headline theorems: only propext, Classical.choice, Quot.sound.
- no stale Lean process, diff check clean.

## Cards
- New Stage 3: `docs/drafts/pipeline/3-formalized/finite-unitary-energy-defect-law.md`.
- Master `static-local-complexity-law.md` appended.

## Conjecture loop / hostile boundary
- Tangent rigidity does NOT imply ECH: exact kernel classification is not pointwise exponentially small easy leverage for every off-diagonal eigenprojector.
- Zlokapa–Allen–Harrow 2607.19852 does not transfer: channel/all-input; late time uses fresh disjoint blocks/system growing with time.
- Fixed-H temporal k-design papers use time/seed ensembles or quenches and do not prove a single-endpoint Brown ramp.
- Exact defect law advances approximate-tube normalization but Haar rarity cannot be transferred to adaptive static-local endpoints. It does not prove Brown growth.

## Next exact core
Prove a quenched selector-aware Bellman escape bound inside the low energy-defect sector, after explicit return and fast-forwardable-carrier removal. Do not revert to full-Haar decay, minimum gaps, or tangent-rigidity=>ECH.