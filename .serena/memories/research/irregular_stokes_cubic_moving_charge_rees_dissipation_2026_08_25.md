# Irregular Stokes cubic moving-charge Rees dissipation (2026-08-25)

## Result

Formalized exact behavior of any common-rank-magnitude-preserving moving cubic Xi Malgrange landing between complete threshold contraction and unit Rees scale.

For
- `x₀ : landing genus d (fun _ _ => 0)`,
- `x₁ : landing genus d (fun _ _ => 1)`,
- `commonRank(x₀)^2 = commonRank(x₁)^2`,

write (T_j=\sum_a \mathrm{terminalEnergy}_a(x_j)) and (B_1=\sum_a \mathrm{blockEnergy}_a(x_1)). Then:
[
T_0=T_1+B_1,qquad B_1>0,qquad T_1<T_0.
]

Thus the surviving alternative after fixed-charge diagonal Rees transversality is genuinely dissipative: any viable rank-magnitude-preserving source incidence must move charge and lose terminal microstalk energy by exactly canonical block coarea. Physical-rank sign reversal does not evade the law. Terminal-isometric/unitary transport is impossible.

## Proof mechanism

- Contracted global positive energy is exactly terminal energy.
- Unit global positive energy is terminal plus block energy.
- Both landing values equal the same negative cubic Xi target.
- The unique global rank-square terms cancel because common-rank squares agree.
- Any landing charge is nonzero; orbit surjectivity makes a branch lift nonzero; pendant-cut faithfulness makes total unit block coarea strictly positive.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMovingChargeReesDissipation.lean`
- Card: `docs/drafts/pipeline/3-formalized/route-p-cubic-moving-charge-rees-dissipation.md`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Frontier map remained untouched/read-only.

## Verification

Targeted module check passed. The sole public theorem depends exactly on `[propext, Classical.choice, Quot.sound]`. Scratch and generated dependency/module `.olean` files were removed.

## Novelty/audit

Corpus had fixed-charge diagonal Rees transversality but no moving-charge terminal dissipation theorem. Prior focused audit of irregular RH, wild harmonic/twistor D-modules, and filtered/polynomial Rees structures found no completed-Xi contracted-to-unit energy law. Absence is an audit inference.

Related memories: `mem:research/irregular_stokes_cubic_microlocal_witt_signature_2026_08_25`, `mem:research/irregular_stokes_cubic_diagonal_rees_transversality_2026_08_25`, `mem:research/irregular_stokes_cubic_local_ramification_capacity_2026_08_25`.

## Next target

Combine dissipation with an actual source transport invariant. Any candidate preserving common-rank magnitude and terminal norm is now ruled out. A viable source-to-Stokes incidence must either change rank magnitude or exhibit quantified terminal-energy loss equal to activated block coarea.
