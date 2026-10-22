# Rational-cusp boundary law for the completed theta source — Lean certificate

- **Paper card:** `theta-rational-cusp-boundary-law.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower`,
  `GaloisForLFunctions.RHTower.ThetaRationalCuspBoundary`,
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOneSidedConnection`,
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAbelBoundaryPairing`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

Dictionary: `ϑ = jacobiThetaSum`, `κ = thetaBoundarySource`, `k = thetaCuspFullSource`
(on the strip `thetaCuspStripSource`), `y₀ = cuspPoint p q = 2ip/q`,
`G_{p,q} = gaussQ (-p) q` (`gaussQ a q = Σ_{r mod q} e(a r²/q)`), `G_{p,q}(ℓ) = rationalCuspCoeff p q ℓ`,
`L_{p,q} = cuspAmplitude p q`, `H = thetaOneSidedConnection`, `F_z = rotatedConnectionIntegrand z`,
`M_z = wardMellin z`, `α_z = wardExponent z`, `A(α) = abelArcTerm α`,
`I_n(α) = abelRayTerm α (iπn²)` (damped: `abelRayTerm α (abelRate n φ)`), `Q = squarePhasePotential`,
`U_z, V_z = thetaLeftSourceMode, thetaRightSourceMode`.

| Card item | Lean theorem |
|-|-|
| `k(x) = κ(e^{2x})` on `|Im x| < π/4`; series form | `thetaCuspStripSource_eq_boundarySource`, `thetaBoundarySource_eq_tsum` |
| residue-class Poisson at `y₀ + ε` (complex `ε`, identity theorem) | `jacobiThetaSum_cusp_ofReal`, `jacobiThetaSum_cusp`, `norm_cuspCoeff_le` |
| exponentially small remainder and its derivatives | `exists_norm_cuspRemainder_le`, `exists_norm_deriv_cuspRemainder_le`, `cpow_mul_thetaBoundarySource_cusp` |
| (1) `ε^{5/2} κ(y₀+ε) → (3G/2q) y₀^{9/4}`, every `p, q > 0` | `tendsto_thetaBoundarySource_cusp` |
| `|G_{p,q}| = √q` (`q` odd) | `norm_cuspGauss_of_odd`, `norm_gaussQ_of_odd` |
| square law `G² = χ₄(q) q`, `0`, `2qi·χ₄(a)` | `gaussQ_sq`, `gaussQ_sq_of_odd`, `gaussQ_prime_sq`, `gaussQ_two_pow_sq`, `gaussQ_sq_of_four_dvd`, `gaussQ_eq_zero_of_mod_four_eq_two` |
| fourth powers `q²`, `0`, `-4q²` | `gaussQ_pow_four` |
| (1a) `L⁴/i = 81/(16q²) (2p/q)^9 · {1, 0, -4}` | `cuspAmplitude_pow_four_div_I` |
| unboundedness at odd-denominator cusps | `tendsto_norm_thetaBoundarySource_cusp`, `cuspAmplitude_ne_zero` |
| zero-charge points `q ≡ 2 mod 4`: `κ → 0`; the endpoint `y₀ = i` | `tendsto_thetaBoundarySource_cusp_zero_charge`, `tendsto_thetaBoundarySource_I_add` |
| density of `2p/q`, odd `q`, on the boundary | `exists_cusp_log_near`, `log_cuspPoint_re`, `log_cuspPoint_im` |
| natural boundary of `|Im x| < π/4` (both edges, conjugate statement) | `not_exists_continuation_thetaCuspStripSource_upper`, `thetaCuspStripSource_conj`, `not_exists_continuation_thetaCuspStripSource` |
| (2) rotated connection branch for every `0 < φ < π/2`, all `z` | `thetaOneSidedConnection_eq_rotated`, `integral_Ioi_eq_rotated`, `norm_thetaBoundarySource_le` |
| `Ξ(z) = H(z) + H(-z)` | `XiC_eq_thetaOneSidedConnection_add` |
| `U_z - V_z = -i e^{-izx} Ξ(z)` | `thetaLeftSourceMode_sub_right` |
| (3) `H(z) = 1/4 + (iz/2)(ϑ(1)-1) - ((z²+1/4)/4) M_z`, all complex `z` | `thetaOneSidedConnection_eq_ward`, `integral_cexp_mul_thetaCuspTailDerivative_succ`, `integral_cexp_mul_thetaCuspTailDerivative_zero` |
| `M_z` entire | `differentiable_wardMellin` |
| (4) `Ξ(z) = 1/2 - ((z²+1/4)/4)(M_z + M_{-z})` | `XiC_eq_wardMellin` |
| rotated Ward integral at interior angles | `wardMellin_eq_rotated` |
| damped ray = absolutely convergent atom sum | `integral_ray_eq_tsum`, `integral_cpow_mul_cexp_eq_abelRayTerm` |
| arc endpoint `ϑ(e^{iθ}) → 0` as `θ ↑ π/2` | `tendsto_jacobiThetaSum_arc`, `exists_norm_jacobiThetaSum_arc_le` |
| twisted Poisson `ϑ(i+w) = w^{-1/2} Σ e^{-π(m+1/2)²/w}` | `jacobiThetaSum_I_add` |
| (5) `M_z = A(α_z) + 2e^{iπ(α_z+1)/2} Σ I_n(α_z)`, `Im z > -3/2` | `wardMellin_eq_abelPairing` |
| `I_n` as convergent improper integral | `tendsto_integral_abelRayTerm_square` |
| (6) IBP form with `e^{-iπn²} = (-1)^n`; bound `(1/πn²)(1 + |α|/(-Re α))` | `abelRayTerm_square`, `cexp_neg_I_pi_sq`, `norm_abelRayTerm_square_le` |
| same bound uniformly for damped rays `0 ≤ φ < π/2` | `norm_abelRayTerm_le` |
| `Σ (-1)^n/n² = -π²/12` | `tsum_neg_one_pow_div_sq` |
| `Q` continuous, bounded, two-periodic, mean zero, `Q(1) = -π²/12` | `continuous_squarePhasePotential`, `norm_squarePhasePotential_le`, `squarePhasePotential_add_two`, `integral_squarePhasePotential`, `squarePhasePotential_one` |
| (7) `Q(r+1) + Q(r) = Q(4r)/2` | `squarePhasePotential_parity` |
| (8) `M_z = A(α_z) + 2e^{iπ(α_z+1)/2}[iπ/12 + (α_z/iπ)∫₁^∞ r^{α_z-1} Q(r) dr]` | `wardMellin_eq_squarePhasePotential` |
