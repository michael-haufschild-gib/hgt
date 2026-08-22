# CCM-FU Möbius dilation / unit-Riesz frontier (2026-08-22)

Formal modules:
- `formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorDilationChannels.lean`
- `formal/GaloisForLFunctions/RHTower/CCMFUSuzukiMobiusDivisorUnitRieszWeld.lean`

New exact laws:
1. Clipped dilation weights are capped endpoint differences and telescope on every cofinal tail.
2. `sum_mobiusClippedAbelKernel_tail`: kernel tail is exactly `Σ μ(d)(√M-√(nd))`.
3. `mobiusClippedAbelKernel_eq_rieszTailGradient`: signed FU kernel is q-gradient of one Möbius–Riesz tail; escaped coefficient is zero.
4. `divisorDefect_kernel_eq_increment_rieszTail`: cumulative divisor-defect pairing equals local `log−τ+2γ` source paired with transported tail.
5. `primeFreeDivisorIncrement_mobius_convolution_eq_atom`: coefficientwise Möbius collapse is exactly `Λ−1` plus sole Gamma atom at 1.
6. `increment_rieszTail_eq_completedPrimePolarGamma_window`: direct source-faithful equality with literal completed prime–polar Riesz window.
7. `sqrtGap_eq_half_aperture_mul_unitApertureWeight`: Riesz gap equals half aperture times Suzuki unit-aperture critical profile.
8. `unitApertureWindow_eq_resolvent_add_sourceFreeEdge`: actual FU/Suzuki window equals critical Mellin–Chebyshev resolvent plus explicit Gamma-minus-lattice source-free edge.
9. `tendsto_unitApertureWindow_sub_resolvent_zero`: source-free edge tends to zero.

Scientific frontier:
- Boundary formation, complete/terminal transport, Gamma edge, FU region coupling, and convergence to critical resolvent are closed exactly.
- Route O, CCM-FU, Suzuki, actual-head Route O, and G-CE criteria share same hard signed arithmetic scalar after explicit source-free correction.
- Remaining RH-bearing datum is uniform boundedness/sign control of actual completed `Λ−1+Gamma@1` unit-aperture window / critical Mellin–Chebyshev resolvent. Separate absolute, local, raywise, head, or graph-energy bounds cannot supply it.
- Do not rediscover resolvent boundedness criteria; corpus already has them. Seek new invariant controlling this scalar while retaining prime–polar cancellation.

Verification:
- Both files pass `lake env lean`.
- Target `lake build GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorUnitRieszWeld` passes.
- Main theorem axiom audits show only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired; route map untouched.