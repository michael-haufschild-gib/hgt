# Library ticket: sigma divisor jet multiplicative kill

- **Target docs:** `docs/drafts/door/00-index.md`; likely `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`; possibly `docs/drafts/rh-monodromy-weight-mismatch/106-joint-reading-no-go.md`.
- **Source card:** `docs/drafts/pipeline/3-formalized/new/sigma-divisor-jet-multiplicative-kill.md`
- **Formal files:** `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`; `formal/GaloisForLFunctions/RHTower/PrimeDivisorAtomsNoGo.lean`; `formal/GaloisForLFunctions/RHTower/SigmaDivisorExhaustion.lean`; `formal/GaloisForLFunctions/RHTower/FittingSeamBoundary.lean`

## Update Needed

Record the first attack on the doc-106 escape hatch:

1. The natural non-character, non-positivity local object is the divisor-tangent jet algebra `R[X]/(X^m)`.
2. A sigma direction that is locally multiplicative by the zeroed function, `(X^m u) h_p`, has zero class in this algebra.
3. Prime-local atom maps are zero at pinned strip points: every finite Euler factor and finite Euler atlas is a unit there, so the source atom map into the xi divisor is zero.
4. `SigmaDivisorExhaustion.lean` packages these in `pinnedSigmaDivisorSources_killed` and `pinnedSigmaDivisorSources_mismatch_with_emSplit`.
5. Therefore the current prime-lane candidates do not produce a `{sigma_p}`-graded divisor refinement finer than multiplicity at one pinned annulus.
6. The open residue was sharpened to a single algebraic shape: a p-labelled torsion seam presentation `R^n --A--> R^n -> Q` with `det A = X^m`, sigma defect `Delta_p`, and Fitting boundary `tr(adj(A) Delta_p) mod X^m`.
7. `FittingSeamBoundary.lean` proves fake defects vanish: if `Delta_p = A H_p + X^m K_p`, then the boundary class is zero. Equivalently, a nonzero boundary forces `Delta_p ∉ A End + (X^m)`.
8. The audited `M+` definition in `completed-connection-category.md` has finite-free `R+`-modules, commuting semilinear `sigma_p` automorphisms, and a compatible `partial_s` connection. It has no object/morphism field for a torsion seam presentation or supported cokernel.
9. Therefore the route is killed inside bare `M+`. To reopen it, the category definition must be extended first; then the next theorem is exactly `Delta_p ∉ A End + (X^m)`.

## Suggested Grade

THEOREM (Lean), negative route theorem. Door status: BRIDGE / seam-gap localization, not C5.
