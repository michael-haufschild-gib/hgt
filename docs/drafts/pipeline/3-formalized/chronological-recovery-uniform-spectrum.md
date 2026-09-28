# Uniform recovery growth and the exact spectral disc

**Status:** Lean-complete (Stage 3-formalized): the growth inequality, the uniform root limit, `‖U^d‖`, the spectral radius, the spectrum, the adjoint eigenvectors, and the identification of `ℓ²(ℕ,ℂ)` with the complexification are proved in Lean; axioms `propext`, `Classical.choice`, `Quot.sound` only. No moment positivity or gap log-convexity is assumed. Priority of this application is unestablished.

Let δ_k be the physical recovery gaps, and let ρ be the exact constant in [the exponential-rate proof](chronological-recovery-exponential-rate.md). Then

`lim_(d→∞) (sup_(k≥0) δ_(k+d)/δ_k)^(1/d) = ρ`.

This is stronger than the previously obtained limit for δ_d alone: the starting grade k can vary arbitrarily with d. Consequently the complexification of the actual recovery multiplier U has spectrum exactly `{z∈ℂ : |z|≤ρ}`. In particular its spectral radius is ρ.

## The cancellation that makes the estimate uniform

Write T_d(r) for the monic degree-d weighted minimizer, t_d for its norm, and S_d for its positive root sum. Set T_0=1 and t_0=1. Its homogeneous lift is the polynomial

`H_d(u,c)=c^d T_d(u/c)=u^d−S_d u^(d−1)c+terms divisible by c²`.

This notation denotes homogenization, including at c=0, and uses no division there. Its physical norm equals t_d by the established boundary reduction. For d≥1 form

`A_d=H_d+S_d c H_(d−1)`.

The coefficient of c is now zero, while the coefficient of c⁰ is u^d. Therefore A_d belongs to the actual observation algebra A=ℝ[u,c²,c³], and multiplication by it on B/A agrees with multiplication by u^d. Also 0≤c≤1 on the physical section, so

`‖A_d‖_physical ≤ t_d+S_d t_(d−1) ≤ t_d+(d/4)t_(d−1) =: B_d`.

Here the root bound 0<r_j<1/4 gives S_d<d/4. The direct use of H_d would be invalid: its missing c coefficient is nonzero. The correction is essential.

Take an attained normalized residual P of degree k+1, whose c coefficient is u^k and whose physical norm is δ_k. The c coefficient of A_d P is exactly u^(k+d). Thus A_d P is an admissible residual for δ_(k+d). Pointwise multiplication and the supremum norm give, for every k≥0 and d≥1,

`δ_(k+d) ≤ B_d δ_k`.

Since t_d^(1/d)→ρ>0, also B_d^(1/d)→ρ. Indeed B_d≥t_d; both terms in its displayed definition have dth-root limit ρ, and the dth root of their sum has that same limit. On the other hand the supremum over k is at least δ_d/δ_0, whose dth root tends to ρ. Squeezing proves the asserted uniform limit.

## Spectrum, with both inclusions proved

Use the orthonormal basis b_k=[u^k c]/δ_k. On the complexified Hilbert space,

`U b_k=(δ_(k+1)/δ_k)b_(k+1)`.

Its dth power sends distinct basis vectors to orthogonal vectors. Consequently

`‖U^d‖=sup_k δ_(k+d)/δ_k`.

For |z|>ρ the norm-convergent series Σ_(d≥0)U^d/z^(d+1) is a two-sided inverse of zI−U: convergence follows from the uniform root limit, and multiplication of its partial sums telescopes. This proves the outer spectral bound without assuming a normal dilation.

For |λ|<ρ, the vector

`v_λ=Σ_(k≥0) λ^k(δ_0/δ_k)b_k`

converges in Hilbert norm by the root test and is nonzero. Boundedness of U* and the basis formula give U*v_λ=λv_λ. Hence U−conj(λ)I is not invertible. The whole open disc lies in the spectrum, and closedness supplies its boundary. This proves equality with the closed disc.

## Relation to the unresolved obstruction

The [degree-17 numerical square witness](../1-in-progress/chronological-recovery-moment-problem.md) suggests that the squared gaps do not have a positive moment measure. Its sign still needs an exact proof. The uniform growth theorem above is independent of that sign and is a positive result exposed by investigating the obstruction. It does not prove the separate inequality δ_(k+1)²≤δ_kδ_(k+2), ratio convergence, or positivity of the recovery commutator.

The former formal dependencies (weighted alternation/coefficient duality and the rate theorem) are now Lean theorems; see the table below.

## Lean formalization

Modules in `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/`, wired into `HTGeometry.lean`.

| Card statement | Lean declaration | Module |
|-|-|-|
| Homogeneous lift `H_d = c^d T_d(u/c)` has physical norm `t_d` | `cubicHomogeneousLift`, `cubicHomogeneousCapacity_lift` | `CubicRecoveryUniformGrowth` |
| Corrected lift `A_d = H_d + S_d c H_(d−1)`: `c⁰`-coefficient `u^d`, zero `c`-coefficient, norm `≤ t_d + S_d t_(d−1) ≤ t_d + (d/4) t_(d−1) = B_d` | `cubicCorrectedOptimizer`, `cubicCorrectedOptimizer_coeff_top/_pred`, `cubicWeightedIntervalNorm_corrected_le`, `cubicOptimizerRootSum_le` | same |
| Physical norm is submultiplicative on products of homogeneous observations | `mul_mem_cubicHomogeneousSpace`, `cubicHomogeneousCapacity_mul_le` | same |
| **`δ_(k+d) ≤ B_d δ_k`** for all `k ≥ 0`, `d ≥ 1` | `cubicGradedRecoveryGap_add_le` | same |
| **`lim_d (sup_k δ_(k+d)/δ_k)^(1/d) = ρ`** | `tendsto_cubicRecoveryUniformGrowth` | same |
| Complexification: `U_ℂ` on `ℓ²(ℕ,ℂ)`, `ι` (basis coordinates) isometric, `U_ℂ ∘ ι = ι ∘ U`, `(x,y) ↦ ιx + iιy` bijective | `complexRecoveryShift`, `recoveryRealEmbedding`, `norm_recoveryRealEmbedding`, `complexRecoveryShift_realEmbedding`, `recoveryComplexification_bijective`, `complexRecoveryShift_complexification` | `CubicRecoverySpectralDisc` |
| `U^d` on the basis; **`‖U^d‖ = sup_k δ_(k+d)/δ_k`** | `complexRecoveryShift_pow_apply`, `norm_complexRecoveryShift_pow` | same |
| Spectral radius `ρ` (outer inclusion via Gelfand's formula) | `spectralRadius_complexRecoveryShift`, `norm_le_of_mem_spectrum_complexRecoveryShift` | same |
| For `|λ|<ρ`: `v_λ ∈ ℓ²`, `v_λ ≠ 0`, `U*v_λ = λv_λ`; `U − μ` not surjective | `memℓp_recoveryEigen`, `adjoint_complexRecoveryShift_eigenvector`, `not_surjective_complexRecoveryShift_sub` | same |
| **Spectrum = `{|z| ≤ ρ}`** | `spectrum_complexRecoveryShift` | same |

**Verification.** `lake env lean` on both modules: clean. `lake build` of the top module: passed.
`#print axioms` for 10 capstones: `[propext, Classical.choice, Quot.sound]`.

