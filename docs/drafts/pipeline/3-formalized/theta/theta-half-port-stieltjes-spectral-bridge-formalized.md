# The theta half-port as a positive Stieltjes spectral measure — Lean certificate

- **Paper card:** `theta-half-port-stieltjes-spectral-bridge.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral` (all theta
  statements); general layer `GaloisForLFunctions.HTGeometry.LorentzianCosineIntegral`
  (complex-width Lorentzian integrals by Fourier inversion of `e^{iw|y|}`),
  `GaloisForLFunctions.HTGeometry.StieltjesPrincipalValueBoundary` (Poisson versus truncation,
  `O(η)`), `GaloisForLFunctions.HTGeometry.OnePortStieltjesTransform` (one-port sources: density,
  Stieltjes representation, boundary sheets, principal value),
  `GaloisForLFunctions.HTGeometry.MaximalMultiplicationSelfAdjoint` (maximal multiplication by a
  real symbol on `L²(μ)` is self-adjoint; bounded resolvent),
  `GaloisForLFunctions.HTGeometry.OnePortSpectralModel` (the model `L²(σ dt/(1+t))`, (2a), no
  eigenvalues); corpus `ThetaCuspOneSidedConnection` (Ward reduction), `ThetaRenewalExitDensity`
  (seam identity), `ThetaRenewalLogKernel`/`ThetaRenewalCoshFactorization` (`D = c e^{-Q̂}`),
  `ThetaCuspAbelBoundaryPairing` (square-phase formula (8) of the rational-cusp card)
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean for all six modules;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

Dictionary: `k = thetaCuspFullSource`, `ω = -deriv thetaCuspFullSource`,
`h = thetaOneSidedConnection = onePortConnection thetaCuspFullSource`,
`σ = thetaPortDensity = onePortDensity thetaCuspFullSource`,
`m(ζ) = onePortStieltjes thetaCuspFullSource ζ = h(upperRoot ζ)`, `upperRoot ζ = i(-ζ)^{1/2}`,
`μ = onePortSpectralMeasure thetaCuspFullSource`, `A = onePortOperator thetaCuspFullSource`,
`1 = onePortUnit`, `c = Θ 1 = evenKernel 0 1`, `a = 1/4`, `C(r) = thetaRenewalRealCos r`,
`S(r) = thetaRenewalRealSin r`, `D = thetaRenewalDenominator`, `M_u = wardMellin u`,
`h_s = thetaShiftConnection s`, `σ_s = thetaShiftDensity s`, `Ξ = Xi`. The principal value
`PV ∫₀^∞ g(t)/(t - τ) dt` is the limit, as `ε → 0⁺`, of `∫_{(0,∞) \ [τ-ε, τ+ε]} g(t)/(t - τ) dt`.

| Card item | Lean theorem |
|-|-|
| `k` positive, strictly decreasing on `[0,∞)`; every right tail is a one-port source | `strictAntiOn_thetaCuspFullSource`, `onePortSource_thetaShift`, `onePortSource_thetaCuspFullSource` |
| `h` entire; `Ξ(z) = h(z) + h(-z)`; `Ξ(u) = 2 Re h(u)` | `differentiable_thetaOneSidedConnection`, `XiC_eq_thetaOneSidedConnection_add`, `Xi_eq_two_mul_re_thetaOneSidedConnection` |
| (1) `σ(t) > 0` | `thetaPortDensity_pos` |
| (1) locally smooth | `contDiffOn_thetaPortDensity` |
| (1) `O(√t)` at zero, `O(t^{-1/2})` at infinity | `thetaPortDensity_le_sqrt`, `thetaPortDensity_le_inv_sqrt` |
| (1) `∫₀^∞ σ(t)/(1+t) dt < ∞` | `integrableOn_thetaPortDensity_div` |
| (2) `m(ζ) = h(w) = ∫₀^∞ σ(t)/(t - ζ) dt`, `w² = ζ`, `Im w > 0` | `thetaStieltjes_eq`, `thetaOneSidedConnection_eq_stieltjes` (general: `OnePortSource.onePortConnection_eq_stieltjes`, `integral_Ioi_one_sub_cos_div_sq_sub_sq`) |
| (2) `Im m(ζ) > 0` for `Im ζ > 0` | `im_thetaStieltjes_pos` |
| (2) `m(-r²) = h(ir) > 0` | `thetaStieltjes_neg_sq` |
| (2a) `A` self-adjoint on `L²(μ)`, `1` of finite norm, `(A - ζ)⁻¹` bounded two-sided inverse, `m(ζ) = m(-1) + (ζ+1)⟨1, (A-ζ)⁻¹1⟩` | `isSelfAdjoint_thetaPortOperator`, `thetaStieltjes_eq_resolvent` (general: `maximalMul_isSelfAdjoint`, `maximalMul_mulResolvent`, `mulResolvent_maximalMul`, `inner_const_mulResolvent_const`, `OnePortSource.onePortStieltjes_eq_resolvent`) |
| (3) boundary sheets `m(u² + i0) = h(u)`, `m(u² - i0) = h(-u) = conj h(u)` | `tendsto_thetaStieltjes_upper`, `tendsto_thetaStieltjes_lower` |
| (3) `σ(u²) = Im h(u)/π` | `thetaPortDensity_sq` |
| (3) `Ξ(u) = 2 PV ∫₀^∞ σ(t)/(t - u²) dt` | `tendsto_thetaPrincipalValue_Xi` (general: `tendsto_re_stieltjes_sub_truncated`, `OnePortSource.tendsto_onePortPrincipalValue`) |
| (3) remarks: `m₊(u²) ≠ 0`; a real Xi zero is not an eigenvalue of `A` | `thetaOneSidedConnection_ne_zero`, `thetaPortOperator_eigenvector_eq_zero` |
| (4) `πσ(u²) = c[r - e^{-C(r)}(r cos S(r) + a sin S(r))] > 0`, `r = u/2` | `pi_mul_thetaPortDensity_sq_eq_renewal` (with `thetaRenewalDenominator_neg_I_mul`) |
| (4a) `πσ(u²) = u(c-1)/2 - ((u²+1/4)/4) Im M_u`, `Ξ(u) = 1/2 - ((u²+1/4)/2) Re M_u` | `pi_mul_thetaPortDensity_sq_eq_ward`, `Xi_eq_ward` |
| (4c) `Im M_u < 2u(c-1)/(u²+1/4)`; the same through formula (8) of the rational-cusp card | `im_wardMellin_lt`, `im_squarePhaseRepresentation_lt` |
| (4b) `((u²+1/4)/4) Im M_u = c e^{-C(u/2)}[(u/2) cos S(u/2) + a sin S(u/2)] - u/2` | `wardMellin_im_eq_renewal` |
| (5) `Im h(u) = ∫ k sin(ux) = (1/u)∫ ω(1 - cos ux) > 0` | `im_thetaOneSidedConnection_eq` |
| (6) `∫σ/(t + r²) = h(ir)` | `thetaStieltjes_neg_sq`, `thetaOneSidedConnection_eq_stieltjes` at `w = ir` |
| (7) `h_s`, `σ_s = Im h_s(√t)/π > 0`; (1)–(2) for each tail | `thetaShiftConnection`, `thetaShiftDensity_pos`, `thetaShiftDensity_eq`, `thetaShiftConnection_eq_stieltjes` |
| (8) `∂_s h_s(z) = -k(s) - iz h_s(z)` | `hasDerivAt_thetaShiftConnection` (with `thetaShiftConnection_eq_tail`, `hasDerivAt_thetaTail`) |
| (9) `∂_s P = -k(s) + uI`, `∂_s I = -uP` | `hasDerivAt_re_thetaShiftConnection`, `hasDerivAt_im_thetaShiftConnection` |
| (10) `∂_s σ_s(t) = -(√t/π) PV ∫₀^∞ σ_s(q)/(q - t) dq`, `s ≥ 0` | `thetaShiftDensity_flow` |
| (11) `∂_s σ_s(u²)|_{s=0} = -(u/(2π)) Ξ(u)` | `hasDerivAt_thetaShiftDensity_seam` |

## Proof-route notes

- The Stieltjes representation (2) is proved directly for every `w` in the upper half-plane,
  without the identity theorem: after `t = u²` and Tonelli, the inner integral is the complex-width
  Lorentzian formula `∫₀^∞ (1 - cos ux)/(u² - w²) du = (πi/(2w))(1 - e^{iwx})`, obtained by Fourier
  inversion of `e^{iw|y|}`.
- The principal value in (3) and (10) is reached through the conjugate-Poisson average
  `Re m(u² + iη)`: the defect kernel `K_η(d) = d/(η² + d²) - 1_{|d|>η}/d` is odd with
  `|d K_η(d)| ≤ η²/(η² + d²)`, and `σ` is Lipschitz at `u²` with constant `(∫ x k)/(π u)` because
  `|sin p - sin q| ≤ |p - q|`; the difference is `O(η)`. The upper root of `u² + iη` is written in
  real coordinates, so the limit uses only continuity of `h` on the closed upper half-plane.
- In (7)–(11) the tail density is taken as the card defines it, `σ_s(t) = Im h_s(√t)/π`, so the flow
  is differentiable at every real `s`; for `s ≥ 0` it coincides with the one-port density of the
  tail and inherits positivity, the Stieltjes representation and the principal-value formula.
