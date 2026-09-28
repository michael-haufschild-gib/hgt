# Prime-deletion causal modes and the Gaussian boundary trace — Lean certificate

- **Paper card:** `sqb-prime-deletion-causal-mode-escape.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaPrimeDeletionCausalMode`; inputs
  `ThetaPrimeDeletionMellin` (atom and deletion Mellin laws, `thetaAtomMellinFactor`),
  `ThetaPrimeDeletionSpectralEscape` (`PrimeExhaustion`, compact-local convergence, `k_S`
  transforms, `thetaAtomMellinFactor_ne_zero`), `ThetaSieveBidirectionalCuspVariation`
  (`thetaSieveResidual`), `ThetaZeroDivisionSource` (tail calculus),
  `HTGeometry.TwoSidedExponentialMoments`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build` of the module; `lake --old env lean` clean (no warnings);
  `#print axioms` of all 23 main theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

Notation: `U_{f,ω} = rightCausalResponse f ω`, `k_S = thetaPrimeDeletion S thetaCuspFullSource`,
`h = fun t => thetaCuspSourceTerm t 1`, `H(ω) = thetaAtomMellinFactor ω`, `S_j` a
`PrimeExhaustion`. The Xi-zero hypothesis is `XiC (I * ω) = 0`.

| Card item | Lean theorem |
|-|-|
| `U_{f,ω}(x) = e^{-ωx} ∫_x^∞ e^{ωt} f(t) dt` | `rightCausalResponse` |
| `(∂_x + ω) U_{f,ω} = -f` | `hasDerivAt_rightCausalResponse` |
| `∫ e^{ωt} k_S = XiC(iω) ∏(1 - p^{-1/2-ω}) = 0` at an Xi zero | `integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource` (existing), used in `thetaPrimeDeletion_causalMode` |
| (1) left-anchored formula `U = -e^{-ωx} ∫_{-∞}^x e^{ωt} k_S` | `rightCausalResponse_eq_neg_left`, `thetaPrimeDeletion_causalMode` |
| two-ended rapid decay: `‖U_{k_S,ω}(x)‖ ≤ C_N e^{-N|x|}` for every `N`; `U_{k_S,ω} ∈ L²(ℝ)` | `exists_norm_rightCausalResponse_le`, `memLp_two_rightCausalResponse`, `thetaPrimeDeletion_causalMode` |
| common integrable majorant on `[x₀,∞)`, dominated convergence | `PrimeExhaustion.tendsto_setIntegral_Ioi_abs_exp_mul_thetaSieveResidual`, `norm_rightCausalResponse_le` |
| (2) `U_{k_{S_j},ω} → U_{h,ω}` locally uniformly (in fact uniformly on every `[x₀,∞)`) | `PrimeExhaustion.tendstoUniformlyOn_rightCausalResponse` |
| `H(ω) = ∫ e^{ωt} h = (ω - 1/2) Γ(ω/2 + 5/4) π^{-ω/2-1/4}`, `H(ω) ≠ 0` in the strip | `integral_cexp_mul_thetaSeedAtom` (existing), `thetaAtomMellinFactor_ne_zero_of_abs_re_lt` |
| (3) `lim_{x→-∞} e^{ωx} U_{h,ω}(x) = H(ω)`; finite-`S` trace `0` | `tendsto_cexp_mul_rightCausalResponse_seed`, `tendsto_cexp_mul_rightCausalResponse_atBot`, `thetaPrimeDeletion_causalMode` |
| (4) the two iterated limits `0` and `H(ω) ≠ 0` | `PrimeExhaustion.boundaryTrace_tendsto`, `PrimeExhaustion.boundaryTrace_noncommute` (literal `limUnder` form) |
| `|U_{h,ω}(x)| ~ |H(ω)| e^{-Re ω x}` at the negative cusp | `tendsto_norm_rightCausalResponse_seed_mul_exp` |
| `Re ω ≥ 0`: `U_{h,ω} ∉ L²(-∞,0)` | `not_integrableOn_sq_norm_rightCausalResponse_seed`, `not_memLp_two_rightCausalResponse_seed` |
| (5) `Re ω ≥ 0`: `‖U_{k_{S_j},ω}‖²_{L²(ℝ)} → ∞` | `PrimeExhaustion.tendsto_integral_sq_norm_rightCausalResponse` |

The two-ended decay, the left formula and the zero boundary trace hold at every zero of
`w ↦ XiC(iw)`; the strip condition `|Re ω| < 1/2` is used only for `H(ω) ≠ 0`.
