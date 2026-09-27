# Hidden grade duality of source phase work versus prime-seam energy — Lean certificate

- **Paper card:** `stc-source-work-grade-duality.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCSourceWorkGradeDuality`,
  `GaloisForLFunctions.RHTower.STCSourceWorkSeamEnergy`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`W = stcSourceWork`, `E = stcSeamEnergy`, `t* = stcDualGrade t`, `J = stcWorkDual`, `h = stcWorkShape`.

| Card item | Lean theorem |
|-|-|
| (1) work profile; value at a Xi-divisor copy | `stcSourceWork_eq`, `sourceTailSoninPhaseWork_eq_stcSourceWork`, `sourceTailSoninPhaseWork_eq_shape` |
| (2) `E` exponential and `sinh²` forms; equals canonical seam energy at any height | `stcSeamEnergyTerm_eq_rpow`, `stcSeamEnergy_eq_rpow`, `stcSeamEnergy_eq_orbitwise` |
| convergence for `|t| < 1` | `summable_stcSeamEnergyTerm` |
| (3) `J` involution, `h∘J = h`, `J(0,1) ⊆ (0,1)`, unique fixed point `1/3` | `stcWorkDual_involutive`, `stcWorkShape_dual`, `stcWorkDual_mem`, `stcWorkDual_eq_self_iff` |
| (4) `t*`, `W(t*) = W(t)`, `t** = t`, `t* = t ⟺ t = 1/√3` | `stcDualGrade_mem`, `stcSourceWork_dualGrade`, `stcDualGrade_involutive`, `stcDualGrade_eq_self_iff` |
| `E` strictly increasing on `[0,1)` | `stcSeamEnergy_strictMonoOn` |
| no `Φ` with `E = Φ ∘ W` | `not_exists_stcSeamEnergy_factor_through_work` |
| `E(t) → 0`, `t* → 1-`, `E(t*) → ∞`, `W → 0` as `t → 0+` | `tendsto_stcSeamEnergy_zero`, `tendsto_stcDualGrade_zero`, `tendsto_stcSeamEnergy_one`, `tendsto_stcSeamEnergy_dualGrade`, `tendsto_stcSourceWork_zero` |
| no comparison `E ≤ Φ(W)` with `Φ` bounded near zero | `no_bounded_stcSourceWork_comparison` |
| (5) `E(1-δ) = F(δ) - 2F(1) + F(2-δ)` | `stcSeamEnergy_one_sub` |
| `F(δ) = δ^{-2} + O(1)` (convergent remainder) | `exists_tendsto_primeLogSquareMoment_sub_pole` |
| (6) `W(1-δ) ~ (log 2)²δ/8`, `E(1-δ) ~ δ^{-2}`, `E/W ~ 8δ^{-3}/(log 2)²` | `tendsto_stcSourceWork_one_sub_div`, `tendsto_sq_mul_stcSeamEnergy_one_sub`, `tendsto_cube_mul_stcSeamEnergy_div_work` |
| (7) `W'(t) = 2ct(1-3t²)/(1+t²)³` and its sign | `hasDerivAt_stcSourceWork`, `stcSourceWorkSlope_sign` |
| `(W(t), sign W'(t))` determines `t` | `stcSourceWork_branch_injective` |
| summed normalized Bockstein squares diverge for `t ≠ 0` | `not_summable_normalizedRouteRPrimeGammaBockstein_normSq`, `stcSourceWork_ne_zero_iff` |
