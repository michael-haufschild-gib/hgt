# Coprime deletion multiplication-fibre architecture (2026-09-05)

Status: RETIRED after generic-mechanism and factorization collision.

- Literal deletion coefficient: `a_q(n)=1-q[q|n]`.
- Rejected C4: pointwise 2×3 fusion has mass 0 and first moments ±6, but integer moment depends on cyclic origin and orientation residue is 0 in ZMod 6. Corpus `MobiusLaplaceCriterionFrontier` also contains same two-prime inclusion-exclusion geometry. Do not revive moment/Möbius derivative selector.
- Positive C5 finite survivor: grid `w(m,n)=a_2(m)a_3(n)`, 1≤m≤2, 1≤n≤3. Every row and column sum is 0. Multiplication collapses (1,2),(2,1) into product fibre 2 with opposite weights. Before signed aggregation, positive/negative fibre masses retain cancellation odometer 1 at product 2 and 0 elsewhere. Pre-collapse squared mass 12, post-collapse mass 10, defect 2.
- Retirement evidence: `ConstitutiveTVConflictColoring` already proves exact fibre overlap as min(positive mass, negative mass); `SignedCancellationQuotient`, `ConstitutiveCausalJordanFormation`, and `AbelianRepairLeastAction` provide quotient loss, reserve cocycle, and odometer semantics. `MobiusCoprimeProductSignExtraction` already treats signed product-pair mass. Proposed cofinal count factors through a Dirichlet polynomial times ζ².
- Lean:
  - `RHTower/CoprimeBlockCarryTransgression.lean`: `coprimeBlockMomentOrientation_noGo`, closed capstone.
  - `RHTower/CoprimeBlockMultiplicationFiber.lean`: `coprimeBlockMultiplicationFiber_closed`.
  - both imported by `RHTower.lean`; direct checks and targeted builds pass. Current global lint is blocked by an unrelated concurrently added unreachable Brizard module.
  - #print axioms: only propext, Classical.choice, Quot.sound.
- Architecture verdict: generic signed-measure specialization, not independent producer. Do not continue.
- Runpod scan script/report at `docs/drafts/pipeline/2-fully-proven/computations/coprime-deletion-multiplication-fibres/`; scan retired before execution after theoretical route failure. Earlier wrong-host probe is invalid; exact supplied endpoint authentication later succeeded. No numeric conclusions.
- Main card: `docs/drafts/pipeline/1-in-progress/rh-corpus-architecture-audit-2026-09-05.md`.
- STATUS facts: F679, CANNOT-304, CANNOT-305.

Current survivor: `mem:rh/euler-deletion-quasi-shuffle-scaling-architecture-2026-09-05`.
