# Cubic wall--Xi Malgrange microlocal Witt-signature rigidity

- **ID:** route-p-cubic-microlocal-witt-signature
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** irregular-RH Route P cubic wall audit
- **Statement:** Every coefficient-generated global irregular-Stokes landing of the negative cubic wall--Xi Malgrange residual lies in the sole physical-rank Lorentz channel, has exact negative inertia one and zero radical, and on a one-puncture sphere requires normalized Puiseux root slope strictly above one. The conditional two-scale Rees-rigid branch annihilates every threshold charge, but subsequent pendant-faithfulness proves that branch empty.

## Goal

Determine which channel of the actual irregular microlocal Riemann--Hilbert decomposition can carry
the first odd wall--Xi Malgrange anomaly.  This removes all local microstalk, terminal, threshold,
and Rees-deformation channels from the cubic producer search without assuming RH or a landing
exists.

## Gates

- [x] 0 → 1 in-progress: well-posed variable-domain classification; source target is canonical Xi cubic Malgrange residual
- [x] 1 → 2 fully-proven: dependency-closed paper proof below; no open mathematical input
- [x] 2 → 3 formalized: targeted Lean check passed; all thirty-one new declarations have only `propext`, `Classical.choice`, `Quot.sound`
- [ ] 3 → 4 publication-ready: standalone exposition and broader literature audit remain

## Approach

For a nonnegative multi-Rees parameter, global coefficient-generated Stokes data satisfy

`W(x) = P_Rees(x) + c_global · rank(x)^2`,

where `P_Rees(x) ≥ 0`, the rank-zero hyperplane is positive definite, and negative inertia plus
radical dimension is at most one.  A landing charge is defined by the variable-domain equation

`W(x) = m₂ - m₀³/4`.

The existing unconditional cubic orientation theorem gives `m₂ - m₀³/4 < 0`.  Therefore:

1. `x ≠ 0` and `rank(x) ≠ 0`, since every nonzero rank-zero charge has positive Witt value.
2. `c_global < 0`; otherwise both terms in the decomposition are nonnegative.
3. `P_Rees(x) < -c_global · rank(x)^2`, so the global rank debt strictly pays every positive local channel.
4. The landing charge is a negative vector, hence negative inertia is positive.  The universal upper bound makes it exactly one.
5. Negative inertia one plus the joint inertia/radical bound forces radical dimension zero.
6. Expanding the global coefficient gives `fusionCoefficient < Σ(root - 1)`.  For genus zero with one marked point, the fusion coefficient vanishes, forcing the unique normalized Puiseux root slope strictly above one.  Hence every slope-at-most-one landing fibre is empty.
7. If the global rank debt is identified at identity scale with the canonical raw Euler/Gamma--Wold cubic defect `S`, exact decomposition gives `P_Rees = S + (m₂ - m₀³/4)`.  The unconditional raw-source overshoot then forces
   `(1999/2000)S < P_Rees < S` and `1999·(-(m₂ - m₀³/4)) < P_Rees`.
8. If one fixed charge lands at Rees parameters `0` and `1`, subtracting the two exact decompositions gives `Σ blockEnergy = 0`.  Each summand is nonnegative with strictly positive cut length, so every local block energy and every threshold cut charge vanish.
9. Vanishing cut charges makes every Rees block identically zero for arbitrary real parameters.  Thus two-scale landing extends automatically to the full real multi-Rees parameter space.
10. Under raw Euler rank debt, the positive cancellation identity at parameter zero contains only terminal orbit energy.  Therefore the bounds in step 7 hold for terminal energy alone.
11. Subsequent pendant-cut faithfulness shows step 8 annihilates every orbit coordinate, hence the charge itself.  This contradicts the negative cubic landing.  Therefore the two-scale Rees-rigid fiber and its raw-Euler refinement are empty; step 10 is a valid but vacuous conditional consequence.

The argument is uniform over all coefficient-generated Puiseux systems, genera, marked-point
families, and nonnegative Rees parameters.

## No-go closure

- **Exact killing theorem/mechanism:** positivity of the global Rees Witt form on the common-rank-zero hyperplane contradicts the strictly negative cubic wall--Xi Malgrange residual.
- **Strongest positive survivor:** every landing has nonzero common physical rank, negative global rank coefficient, strict rank-debt domination, exact negative inertia one, zero radical, and a sharp one-puncture-sphere slope threshold `root > 1`. Under identity-scale raw Euler rank debt at one fixed scale, positive microlocal energy lies strictly between `1999/2000` and `1` times raw debt. Follow-up theorem proves every contracted landing has strictly positive unit-Rees drift equal to total block coarea.
- **New insight:** missing cubic producer cannot be local Stokes/microstalk data, a Rees change of local thresholds, or a tame/slope-one one-puncture-sphere model. Global rank debt alone is insufficient for canonical raw Euler source. Canonical coefficient-generated crossing is necessarily Rees-transverse: viable producer must change charge/carrier or break fixed-charge two-scale covariance.
- **Status:** dependency-closed Lean formalization complete. Conditional Rees-rigid terminal-energy branch is retired as empty by `route-p-cubic-diagonal-rees-transversality.md`. No landing existence or RH claim.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity.lean`

Capstone:

- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rigidity`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_rigidity`

Supporting declarations:

- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankDebt_gt_positive`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sigNeg_eq_one`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_radical_finrank_eq_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_fusion_lt_rootDefects`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_root_gt_one`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one`
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_of_slope_le_one`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_fraction`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_lt_rawDebt`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_target`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_cancellation`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_total_blockEnergy_eq_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_local_blockEnergy_eq_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_cutCharge_eq_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_positive_parameter_eq_zero`
- `routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_landing_all_parameters`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_eq`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_gt_fraction`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_lt_rawDebt`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_gt_target`
- `routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_rigidity`

## Literature audit

Primary-source search found general Malgrange/Jimbo--Miwa--Ueno tau theory, irregular
Riemann--Hilbert correspondence via enhanced sheaves, and topological Stokes calculations.  No
source found couples the completed Riemann Xi cubic Malgrange residual to a global Puiseux
microlocal Witt-signature classification.  Absence is an audit inference, not a priority claim.
Focused Rees audit likewise found generalized irregular Riemann--Hilbert existence criteria
([Bolibruch--Malek--Mitschi](https://arxiv.org/abs/math/0410483)), irregular connection-map
deformations ([Xu](https://arxiv.org/abs/1507.07149)), and irregular Hodge filtrations
([Castaño Domínguez--Sevenheck](https://arxiv.org/abs/1707.03259)), but no completed-Xi theorem
deriving threshold-charge annihilation or terminal-energy cancellation from two-scale Rees landing.

## Log

- 2026-08-25 — local-channel no-go closed; exact global Lorentz/signature survivor formalized
- 2026-08-25 — identity-scale raw Euler rank debt forces `>1999/2000` positive microlocal cancellation; formalized
- 2026-08-25 — two-scale Rees landing annihilates every threshold charge, extends to all parameters, and localizes raw cancellation to terminal orbit energy; formalized
- 2026-08-25 — follow-up pendant-faithfulness proves two-scale branch empty; terminal-energy specialization marked vacuous and replaced by strict Rees drift
