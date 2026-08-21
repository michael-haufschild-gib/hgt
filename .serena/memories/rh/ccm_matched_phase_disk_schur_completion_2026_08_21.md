# CCM matched phase disk / Schur completion

Formalized module:
- formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedPhaseDiskSchurCompletion.lean
- wired into formal/GaloisForLFunctions/RHTower.lean after covariant transmutation
- note: docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/ccm-matched-phase-disk-schur-completion.md

New corpus-native law:
- Let C_n be matched cosine profile, S_n matched sine profile.
- Define D_n = integral 2 exp(log n/2) cosh(r/2) (1+cos(2 pi r xi)).
- Pointwise radial matrix [[C-density,S-density],[S-density,D-density]] is PSD; determinant reduces by cosh^2-sinh^2=1 to a square.
- Reused HTGeometry.integralMatrixKernel_posSemidef to integrate the RHTower radial density.
- Exact matched radius gives C_n + D_n = 2 w_n.
- Hence S_n^2 <= C_n D_n and (C_n-w_n)^2+S_n^2 <= w_n^2.

Literal half-angle vector [sin(pi log n xi), -cos(pi log n xi)] gives:
P_n = w_n(1+cos(2 pi log n xi)) - (cos(...) C_n + sin(...) S_n) >= 0.
The bracket is the real oriented matched-cell symbol.

On actual Sonin head f:
matched prime-minus-polar cell + R_n(f) = 2 integral P_n |Ff|^2 >= 0,
where exact coefficient-faithful reserve
R_n(f) = 4 w_n ||f||^2 - w_n E_f(log n).
This supplies a genuine local Schur diagonal for the reflection-even covariant Suzuki current.

Verification:
- scratch/direct leaf Lean passed
- exact leaf build passed: lake build GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseDiskSchurCompletion
- capstone axioms only propext, Classical.choice, Quot.sound
- no sorry/admit/axiom/opaque/unsafe
- no umbrella build

Current hard gate:
Transport finite sums of the non-summable exact reserves R_n(f) through the literal completed Gamma/Robin/holonomy producer without coefficient replacement. Then insert into reducing finite exceptional Schur block. This is now global transport, not local matched-cell sign.