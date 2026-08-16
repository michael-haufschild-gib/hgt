Route Q complex-phase boundary repair is closed by a sharp unconditional Lean theorem in `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryComplexPhaseWall.lean`.

Let w be the Xi-Hurwitz orientation vector, e its absolute companion, b₊=(w+e)/2, b₋=(w-e)/2, E=||w||²=-Q(w). Lean proves w ⟂ e, b₊ ⟂ b₋, each boundary norm²=E/2, and
Q(α b₊ + β b₋) = -Re(conj α · β) E.
Off RH (E>0), nonnegative energy iff Re(conj α · β)≤0. Such coefficients satisfy the sharp bound
1 ≤ normSq(α-1)+normSq(β-1),
hence their fusion has distance² at least E/2 from w. Any complex phase sequences αₙ,βₙ→1 combined with separated source packets converging to b₊,b₋ have fusion energy→-E and are eventually negative off RH.

Interpretation: complexification enlarges the null cone but null directions are not cofinal directions. Post-split scalar phases cannot repair Route Q; a viable repair must be source-native and change geometry before boundary splitting.

Card: `docs/drafts/pipeline/3-formalized/route-q-complex-phase-boundary-wall.md`.
Module is wired into `formal/GaloisForLFunctions/RHTower.lean`. Direct Lean compile, exact leaf build, axiom audit, and forbidden-token scan passed. No umbrella/full build. Route frontier map is read-only and was not edited for this result. No RH claim.