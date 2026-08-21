# ULF-LGPD-2 — Lean certification record

**Card:** `reflexive-polarization-synchronization-conservation-cubic-transport-and-properness-law.md`
**Status:** fully formalized, unconditional, axiom-clean.

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstitutiveReflexivePolarizationSynchronization.lean` | scalar shadow (pre-existing) |
| `formal/GaloisForLFunctions/HTGeometry/ReflexivePolarizationVectorSynchronization.lean` | 21 (new) |
| `formal/GaloisForLFunctions/HTGeometry/ReflexivePolarizationCubicTransport.lean` | 48 (new) |

Both new modules are wired into `GaloisForLFunctions.HTGeometry` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (RPS.1)–(RPS.3) | channel forms, residuals, local and fused velocities | `PolarizationPacket` (`form`, `residual`, `localVelocity`, `fusedVelocity`, `symm`, `local_eq`, `fused_eq`), `fusedForm` |
| (RPS.4)–(RPS.5) | the three powers | `localPower`, `fusedPower`, `syncTension` |
| (RPS.6) | balance law `Σ H_i(v_i − v) = 0` | `PolarizationPacket.balance` |
| (RPS.7) | `P_loc = P_fus + S` | `PolarizationPacket.localPower_eq_fusedPower_add_syncTension` |
| (RPS.8) | `S ≥ 0`, `S = 0 ⟺ v_i = v` | `syncTension_nonneg`, `syncTension_eq_zero_iff` |
| (RPS.9) | reconstruction of the residuals | `PolarizationPacket.residual_eq` |
| uniqueness | the constitutive equations determine the velocities | `localVelocity_unique`, `fusedVelocity_unique` |
| (RPS.10)–(RPS.12) | `C³` potentials, targets, the fused source correction flow | `ReflexiveFlow`, `hessianForm`, `thirdForm`, `residual`, `hess`, `third`, `localVel` |
| (RPS.17) | `ė_i = −H_i v`, `Ḣ_i = T_i(v,·,·)` | `hasDerivAt_residual`, `hasDerivAt_hess` (from `hasDerivAt_fderiv_curve`, `hasDerivAt_hessianForm_curve`) |
| — | the local velocity **is** differentiable | `posDefDualEquiv`, `localVel_eq_inverse`, `differentiableAt_inverse_hess`, `differentiableAt_localVel`; fused: `fusedVel_eq_inverse`, `differentiableAt_velocity` |
| (RPS.18) | `H_i v̇_i = −H_i v − T_i(v,v_i,·)` | `third_add_hess_localAccel`; fused: `sumThird_add_fusedHess_accel` |
| (RPS.13) | `Ṗ_loc = −2P_fus − Σ T_i(v,v_i,v_i)` | `hasDerivAt_channelPower`, `sum_hess_velocity_localVel`, `hasDerivAt_locPower` |
| (RPS.14) | `Ṗ_fus = −2P_fus − Σ T_i(v,v,v)` | `hasDerivAt_fusPower` |
| (RPS.15) | `Ṡ = Σ (T_i(v,v,v) − T_i(v,v_i,v_i))` | `hasDerivAt_tension` |
| (RPS.16) | `Ṡ = −Σ (2T_i(v,v,δ_i) + T_i(v,δ_i,δ_i))` | `delta`, `third_localVel_expand`, `hasDerivAt_tension_delta` (using `thirdForm_symm_right`) |
| (RPS.19) | quadratic formations: `Ṡ = 0` | `hasDerivAt_tension_zero` |
| (RPS.20) | `v̇ = −v`, `δ̇_i = 0`, `v(t) = e^{−t}v(0)` | `accel_eq_neg_velocity`, `localAccel_eq_neg_velocity`, `hasDerivAt_delta_zero`, `velocity_eq_exp_smul` |
| (RPS.21)–(RPS.22) | homogeneous amplification and scaling of the velocities | `PolarizationPacket.amplify` (its `local_eq`/`fused_eq` fields), with `localVelocity_unique`/`fusedVelocity_unique` making the scaling the unique solution |
| (RPS.23) | `r²` scaling of all three powers | `localPower_amplify`, `fusedPower_amplify`, `syncTension_amplify` |
| (RPS.24) | bounded amplified local power ⟺ every residual vanishes | `bounded_localPower_iff` |
| (RPS.25) | bounded amplified fused power ⟺ total neutrality | `bounded_fusedPower_iff` |
| (RPS.26) | bounded amplified tension ⟺ synchronization | `bounded_syncTension_iff` |

## New reusable results

* `thirdForm_symm_right` — the third response is symmetric in its last two slots. mathlib's
  symmetry API stops at the second derivative; this differentiates the pointwise Hessian symmetry
  through `HasFDerivAt.clm_apply` against constant directions.
* `posDefDualEquiv`, `bijective_of_posDef`, `finrank_dual_eq` — a positive definite continuous
  bilinear form identifies a finite-dimensional space with its continuous dual.
* `hasDerivAt_fderiv_curve`, `hasDerivAt_hessianForm_curve` — the Fréchet chain rule along a curve.
* `bounded_geometric_iff` — a nonnegative real is zero exactly when its geometric amplifications
  stay bounded.

## Verification

* `lake env lean` on both modules: 0 errors, 0 warnings.
* `#print axioms` on all 69 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`. Hypotheses are exactly the card's standing
  data: symmetric positive definite channel forms, `C³` potentials, a nonempty finite channel set,
  and a finite-dimensional carrier.
