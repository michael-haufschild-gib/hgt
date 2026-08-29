# HB actual balanced spin-two coefficient extraction

- **ID:** C-A.9u
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md
- **Statement:** The literal actual balanced spin-two truncated moment differs from its Bochner scalar multiple by exactly the first and second paired cusp-top currents.

## Goal

Close the final finite-height integral seam before the actual completed balanced `++-` coefficient.
The theorem must integrate the genuine completed-Poincare densities over the standard truncated
modular domain; it may not define a regularized value, boundary current, or coefficient by the
desired equality.

Exact RH chain reduced by this theorem:

`actual balanced moment extraction -> zero finite parts of both paired cusp currents -> actual
completed balanced ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94
source/clock factorization -> horizon-boundary relative-cocycle gain equality -> Re(s)=1/2 on every
Xi fibre -> RH`.

## Gates

- [x] 0 -> 1 in-progress: corpus-derived source-pure statement and route-kill criterion
- [x] 1 -> 2 fully-proven: dependency-closed paper proof by compact-domain integration
- [x] 2 -> 3 formalized: Lean module, targeted build, and axiom audit green
- [ ] 3 -> 4 publication-ready: standalone paper and external review

## Theorem

For actual completed-Poincare parameters `P`, `Q` in the existing absolute-convergence chamber and
every premise-free subtype height `Y : {Y : R // 1 <= Y}`, Lean proves

`balancedMoment(Y) - bochnerCoefficient * scalarMoment(Y)
  = secondPairedCuspTop(Y) + (gradientShift + 1) * firstPairedCuspTop(Y)`.

It also proves the equivalent literal-coordinate identity with both paired truncated Green bulks.
The scalar and balanced moments are genuine set integrals of the actual source densities.

## Proof

1. Establish joint compact-cell continuity of the actual scalar triple density and balanced
   spin-two density from the completed-Poincare source and its first and second jets.
2. Deduce integrability over the compact standard truncated modular domain.
3. Integrate the exhaustive pointwise balanced-density decomposition.  The two existing defect
   moments already contain the factor `2`, leaving coefficients `1` and `gradientShift + 1`.
4. Substitute the premise-free first and second standard-measure Green--Stokes theorems.

This eliminates every possible noncusp, Fubini, tensor-normalization, regularity, and boundary
remainder at finite height.  The paired cusp currents are the complete obstruction.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualBalancedSpinTwoCoefficientExtraction`
- Headline theorems:
  `d4BM_actualBalancedSpinTwoTruncatedMoment_defect_decomposition`,
  `d4BM_actualBalancedSpinTwoTruncatedMoment_eq_pairedCuspTop`,
  `d4BM_actualBalancedSpinTwoTruncatedMoment_eq_pairedTruncatedBulk`
- Direct check: `lake env lean` passes.
- Targeted audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualBalancedSpinTwoCoefficientExtraction`
  passes at `12475/12475`.
- Axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Lint: new module has no forbidden declaration and is reachable.  Repository lint remains red
  only on unrelated shared-worktree umbrella-reachability debt.

## Novelty and hostile audit

Corpus search found the pointwise exhaustive actual-source identity, both defect moments, both
literal Green theorems, and both cusp-current closures, but no integrated actual coefficient
theorem.  Primary-source audit through 2026-08-29 found general regularized automorphic integration
but not this source-normalized completed-Poincare balanced Maass finite-height identity.  Claim is
therefore narrow: corpus-new and not found in audited literature.

The theorem survives the route-kill test with no remainder.  Corpus no-go results nevertheless
show the scalar coefficient cannot be prematurely promoted to a source-faithful gain: two-branch
covariance fails off-line, signed four-sector scalarization cancels the detector, arbitrary response
correction is vacuous, and global gain equality is RH-equivalent.  Next step must retain the actual
negative BM leg and conserved left-QNM/source incidence.

## Log

- 2026-08-29 -- `[PAPER-PROVED] [LEAN-PROVED] [SIGNIFICANT PREMISE DISCHARGED]` C-A.9u closed.
