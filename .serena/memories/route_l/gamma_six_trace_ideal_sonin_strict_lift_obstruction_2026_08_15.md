# Route L Gamma-six trace-ideal/Sonin strict-lift obstruction (2026-08-15)

Paper and Lean theorem closed.

Module: `formal/GaloisForLFunctions/RHTower/DeningerGammaSixTraceIdealSoninStrictLiftObstruction.lean`.
Card: `docs/drafts/pipeline/1-in-progress/deninger-gamma-six-trace-ideal-sonin-strict-lift-obstruction.md`.

Let `Bsrc = W6(T6) - (1/6) T6`, the literal complete Gamma-six Wold coface. Existing theorem makes `Bsrc` rectangular Schatten one. A `DeningerGammaSixTraceIdealSoninComparison` is a complex-linear map from the rectangular source operator space to the fixed Sonin physical operator space sending all Schatten-one source operators to compact operators. Its strict defect at grade `a` is the fixed aperture-one `(2,3)` Sonin receiver minus the image of `Bsrc`.

New exact theorem:
- the strict defect has exactly the fixed receiver's essential norm under every such comparison;
- it obeys `|Delta_23(a)|/sqrt(6) <= essentialNorm(defect)`;
- existence of an exact trace-ideal comparison on the complete coface is equivalent to `a=0`.

This kills grade-uniform relative-cyclic, determinant/joint-torsion, Dixmier-trace, and arbitrary trace-class-correction repairs. Those packages cannot change the Calkin class. It does not prove RH.

Exact surviving open core: construct comparison only on actual Xi divisor locus, using a genuinely nonlocal multi-place consequence of `Xi(rho)=0` to prove fibrewise trace-ideal-preserving compactness while retaining multiplicity, ordinary-prime provenance, and both reflected marked branches. New theorem proves such comparison cannot extend as an exact free-grade family.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/DeningerGammaSixTraceIdealSoninStrictLiftObstruction.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.DeningerGammaSixTraceIdealSoninStrictLiftObstruction` passed.
- wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.
- capstone and exact-lift classification axioms: `[propext, Classical.choice, Quot.sound]`.
- global no-build lint reached new module but failed only on seven unrelated concurrently unwired modules: `GammaVerticalRatioUniform`, `CompactTestTransformOrder`, `MultipleSineBottomCubeSeparation`, `MultipleSineFaceLabelDescent`, `MultipleSineFaceLatticeCube`, `MultipleSineFaceSeparation`, `NewtonIrrationalPositiveVertex`.

Primary literature audit: Kaad--Nest 1408.3851, Migler 1403.4882, Kaad 0804.1589, Lord--Sedaev--Sukochev math/0501131. Parent invariants found, no source-specific collision.