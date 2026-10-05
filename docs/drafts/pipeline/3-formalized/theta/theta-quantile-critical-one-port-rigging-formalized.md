# The Xi divisor is charged at a critical singular-metric port — Lean certificate

- **Paper card:** `theta-quantile-critical-one-port-rigging.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - corpus, already present: the theta quantile normal form (`HedenmalmQuantileNormalForm`: `quantileUnitary`, `integral_comp_quantile`, `measurePreserving_quantile_unitInterval`), the canonical metric `thetaMetricOperator = M_h` (`HedenmalmQuantileMetric`, `HedenmalmThetaSourceUnconditional`), the pinned primitive `V` and its boundary defect `V + V* = |1⟩⟨1| − |1⟩⟨t| − |t⟩⟨1|` (`HedenmalmPinnedVolterraBoundaryDefect`, `HedenmalmPinnedBoundaryTwoPort`), the slice moment `∫ q K(·,s) = −Q(s)` (`HedenmalmQuantileSliceMoment`), the divisor eigenvectors of the compact source inverse and their weighted energy (`HedenmalmThetaCompactDivisorEigenmode`, `HedenmalmThetaSourceModeNormalization`), the source modes `sourceModeI/U/F` (`HedenmalmPrimeTranslationAnomaly`), `xiC_thetaSource`, the theta envelopes (`HedenmalmThetaKernelEnergy`), and from the cross-frequency card the quotient `D`, its eigenvalue law and the mean-zero space;
  - new: `ThetaQuantileOnePortPencil` (pencil, symmetry, positivity, neutral-port reality), `ThetaQuantileFlatNormalForm` ((2a)–(2c), density, ports, `f_L`), `ThetaQuantileHalfPowerThreshold` (range criterion, real powers by functional calculus, odd-sector law, (3), (5), `b`), `ThetaQuantileChargedPort` ((4), (6), suppressed pencil), `ThetaQuantileTwoEndedSelector` (item 4, (7)–(9)).
- **Verification (2026-10-05):** targeted `lake build --old` of each new module; final `lake env lean` audit of each source with no errors; a `Lean.collectAxioms` sweep over all 481 constants of the five modules finds only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** only the card's quantifiers (`α ≥ 0`; `0 < Im z < 1` in item 4; `Ξ_C(z) = 0` where stated). Stronger forms: the weak form (2c) holds for all mean-zero vectors, not only compactly supported ones; (2b) holds on all of `L²(0,1)`.

Dictionary: `H₀ = meanZeroSpace` (as a Hilbert space `MeanZeroL2`), `P = meanZeroProj`, `h = metricSymbol thetaSource` (`metricReal` its modulus), `q = thetaQuantileSpeed`, `T = onePortMetric` on `L²(0,1)` and `meanZeroMetric` on `H₀`, `D = thetaQuotientOperator`, `A = onePortPrimitive`, `b = onePortOutputVector` (`outputVec₀` in `H₀`), `β = onePortInput`, `‖f‖_T² = metricEnergy f`, `u_f = flatField f`, `∫_{−∞}^x u_f = flatPrimitive f x`, `ρ = thetaSource.normalized` (`outPortLp` in `L²(ℝ)`), `T^α = opRpow meanZeroMetric α` (Mathlib's `T ^ α` by the continuous functional calculus), `Q = quantileVec` (`quantileVec₀`), `f_L = portTestVector L`, `f_z = portEigenmode z`, `G_z = flatPrimitiveMode z`, `u_z = flatMode z`, `C_z = flatConnection z`.

| Card item | Lean theorem |
|-|-|
| **(1)** `T D = A − b β` on `H₀`; `M_h B = i V` | `onePortMetric_thetaQuotientOperator`, `thetaMetricOperator_thetaKernelOperator`, `meanZeroProj_thetaKernelOperator` |
| `T` positive, injective on `H₀`; `A` self-adjoint | `isPositive_onePortMetric`, `onePortMetric_injOn`, `metricEnergy_pos`, `isSelfAdjoint_onePortPrimitive`, `inner_pinnedVolterra_add_adjoint` |
| **(2a)** `‖f‖_T² = ∫|u_f|²`, `∫f = ∫u_f`, `β(f) = −i∫ x u_f`, `∫hf = ∫ρu_f` | `metricEnergy_eq_integral_flatField`, `integral_flatField`, `onePortInput_eq_flat`, `inner_onePortOutputVector` |
| **(2b)** `β(f) = −i∫₀¹ Q f` | `onePortInput_eq_quantile` (`pinnedVolterraFun_eq_integral`, `sliceMoment_eq_neg_quantileFun`) |
| **(2c)** `⟨g,Af⟩ = i∫ū_g ∫_{−∞}^x u_f`, `⟨g,Tf⟩ = ∫ū_g u_f`, `⟨g,b⟩ = ∫ū_g ρ`; `Vf(F(x)) = ∫_{−∞}^x u_f` | `inner_onePortPrimitive_flat`, `inner_onePortMetric_flat`, `inner_onePortOutputVector_right`, `pinnedPrefix_cdfFun` |
| every compactly supported mean-zero `u` is some `u_f`, `f = u(Q)/h ∈ H₀` | `preFlat`, `flatField_preFlat`, `preFlat_mem_meanZeroSpace`, `memLp_preFlatFun` |
| **image of `H₀` dense in `L²(ℝ)`**: the energy completion is flat `L²` | `dense_flatLp_meanZeroSpace`, `norm_flatLp` |
| outgoing port `ρ ∈ L²`; incoming coordinate `x ∉ L²` | `memLp_normalized`, `not_memLp_coordinate` |
| output functional has exact norm `‖ρ‖₂` | `norm_inner_onePortOutputVector_le`, `exists_inner_onePortOutputVector_gt` |
| `f_L`: `∫f_L = 0`, `‖f_L‖_T² = 2L³/3`, `β(f_L) = −2iL³/3`; **`β` has no bounded extension to the `T`-energy** | `portTestVector_ae`, `portTestVector_mem`, `metricEnergy_portTestVector`, `onePortInput_portTestVector`, `not_exists_onePortInput_bounded` |
| `Q ∈ L²(0,1)`, `Q(1−t) = −Q(t)`, `Q ∈ H₀` | `memLp_quantileFun`, `isOddVec_quantileVec`, `quantileVec₀` |
| reflection commutes with `T`; on the odd sector `T` is `M_h` and **`T^α = M_{h^α}`** | `commute_meanZeroMetric_reflection`, `coe_meanZeroMetric_pow_ae`, `coe_aeval_meanZeroMetric_ae`, `coe_rpow_meanZeroMetric`, `cfc_apply_eq_of_approx`, `spectrum_meanZeroMetric_subset` |
| **(5)** `Q ∈ range(T^α) ⟺ ∫Q²/h^{2α} < ∞ ⟺ ∫x²ρ^{1−2α} < ∞` | `memLp_quantilePowQuotient_iff`, `integrable_sq_mul_normalized_rpow_iff` |
| **(3)** `Q ∈ range(T^α) ⟺ α < 1/2` (`α ≥ 0`) | `exists_opRpow_eq_quantileVec_iff` |
| **`b ∈ range(T^{1/2})`** (positive-operator range criterion) | `exists_opRpow_half_eq_outputVec`, `mem_range_of_norm_inner_le`, `norm_opRpow_half_meanZeroMetric` |
| **`b ∉ range(T)`** (`f = 1 + cq`, `∫q = ∞`) | `not_exists_meanZeroMetric_eq_outputVec`, `not_integrable_thetaQuantileSpeed` |
| **(4)** `f_z ∈ H₀`, `D f_z = −z⁻¹ f_z`, `β(f_z) = −z⁻¹ ≠ 0` for every Xi zero | `portEigenmode_mem`, `thetaQuotientOperator_portEigenmode`, `onePortInput_portEigenmode`, `onePortInput_portEigenmode_ne_zero`, `inner_constMode_divisorVec` (`∫v_z = √M`) |
| `ker β` eigenmodes have real eigenvalues; the suppressed pencil `Af = λTf` is real and contains no `f_z` | `im_eq_zero_of_onePortInput_eq_zero`, `im_eq_zero_of_onePortPrimitive_eq`, `onePortPrimitive_portEigenmode_ne`, `onePortOutputVector_ne_zero` |
| **(6)** `Σ_{first N copies} |β(f_z)| = (1/(2π)+o(1))(log N)²` (multiplicity) | `tendsto_xiPortChargeSum_div_log_sq`, `xiPortChargeSum_eq` |
| **item 4**: `G_z' = u_z = −izG_z − ρ`, two-sided decay | `hasDerivAt_flatPrimitiveMode`, `norm_flatPrimitiveMode_le` |
| `u_z ∈ L²(ℝ)`, `∫u_z = 0`, `−i∫xu_z = −1/z`, `iz∫G_z = −1` | `memLp_flatMode`, `integral_flatMode`, `flatMode_charge`, `integral_flatPrimitiveMode` |
| **(7)** `i∫_{−∞}^x u_z = −z⁻¹(u_z + ρ)` | `flatMode_onePort_equation` |
| **(9)** `G_z = C_z e^{−izx} − e^{−izx}∫_{−∞}^x e^{izy}ρ`, `C_z = Ξ_C(z)/M` | `flatPrimitiveMode_eq`, `flatConnection_eq` |
| forbidden left exponential: `e^{izx}u_z(x) → −izC_z` | `tendsto_sourceChar_mul_flatMode_atBot` |
| **(8)** `∫|u_z|²/ρ < ∞ ⟺ Ξ_C(z) = 0` (`u_z/ρ ∈ L²(ρdx)`) | `integrable_flatModeWeightedDensity_iff`, `norm_div_normalized_sq_mul`, `not_integrable_flatModeWeightedDensity`, `integrable_flatModeWeightedDensity_of_zero` |
| at a zero `u_z(Q)/h = f_z`; off the divisor `u_z(Q)/h ∉ L²(0,1)` | `portEigenmode_ae_flatModePullback`, `memLp_flatModePullback_iff` |

The card proves no orientation of the charged port and no zero exclusion; none is formalized.
