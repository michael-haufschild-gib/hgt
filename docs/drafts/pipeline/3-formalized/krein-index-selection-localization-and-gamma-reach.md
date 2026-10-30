# Krein index: one selective square, infinite flip index, low-mode localization, Gamma reach

- **ID:** kisp-f
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/krein-index-selection-and-producer-2026-10-30.md
- **Statement:** Unconditional theorems on where the Weil-kernel index can select `ζ` and what a producer must pay.

## 1. The selective content of the atomic index is one square

**Theorem.** For the atomic kernel `D·1 − P_N` with the pole entering as the hyperplane
`Σ c_n n^{−1/2} = 0`, the pole indices (negative index on that hyperplane) of any two sign gauges
`ω² = 1` differ by at most one, at every `N` and `D`. In the window `L − 2 log 2 < D < L`,
`L = log N − γ`, the pole index of `ζ` is `0` and that of the Liouville twin is `1`.

**Proof.** A sign gauge acts on the exact-ratio prime kernel by congruence, so every gauge has the
full index `κ` of `ζ` (`hermNegIndex_gaugeAtom_eq`). One linear condition costs at most one square:
a maximal negative subspace meets the hyperplane in codimension `≤ 1`. Hence every pole index lies
in `[κ − 1, κ]`. The window values are the carrier theorems `eventually_hermQuad_atom_nonneg_on_pole`
and `eventually_exists_neg_on_pole_liouville`.

**Lean** (`HeckeKreinToeplitz/TheSelectiveIndexOfTheAtomicKernelIsOneSquare`): `negIndexOn`,
`hermNegIndex_le_negIndexOn_ker_add_one`, `poleNegIndex`, `poleNegIndex_gauge_le_add_one`,
`abs_poleNegIndex_gauge_sub_zeta_le_one`, `eventually_poleNegIndex_window`.

## 2. `ζ` and a single-prime flip never both have finite index

**Theorem.** Let `f` be a nonzero real `C²` test supported in `[−a, a]`, `2a ≤ log p`. Then
`κ(K_ζ) = ∞` or the Weil kernel of the `p`-flipped weight (pole and Gamma of `ζ`) has `κ = ∞`.
On the finite stratum the twin has at least `n − #(right zeros)` negative squares for every `n`,
on the tower of `p` alone.

**Proof.** (i) On `p^d` the twin kernel is `K_ζ(p^d) + C r^{|d|}[d odd]`, `C = 2 log p ‖f‖²`,
`r = p^{−1/2}`: only odd powers of `p` change, and the short support isolates the lag `|d| log p`.
(ii) On the finite stratum `K_ζ = B + Σ_ρ h_ρ`, `B(p^d) = Σ_γ w_γ e^{−i d γ log p}` with `w_γ ≥ 0`
summable (on-line zeros), and finitely many hyperbolic pairs. (iii) Blocks `a_k e^{ilθ₀}`,
`l < L`, at positions `kG`: the pure-point energy is `≤ n Σ|a_k|² Σ_γ w_γ |D_L(θ_γ − θ₀)|²`; a grid
of `L` frequencies has exact average `|D_L|²`-mass `L` (orthogonality of roots of unity), so Markov
controls the light atoms and `|D_L(x)| ≤ π/dist(x, 2πℤ)` controls finitely many heavy ones; a
frequency `θ₀` near `π` has pure-point energy `≤ εL`. The odd Poisson block at `θ₀ ≈ π` has energy
`≤ −C L r/2` (the neighbours carry `−(L−1)r`, the detuning costs `δ L·2r/(1−r)²`). Cross terms
between blocks are `≤ n L² C r^{G+1−L}`. Each pair vanishes on one linear condition. So the form is
negative definite on a subspace of dimension `≥ n − #R`.

**Lean** (`HeckeKreinToeplitz/APurePointSpectrumIsThinAtMostFrequencies`,
`HeckeKreinToeplitz/OnTheFiniteStratumEveryFlipHasInfiniteIndex`): `dirichletBlock`,
`sum_grid_normSq_dirichletBlock`, `norm_dirichletBlock_le_of_far`, `card_near_le`,
`exists_frequency_thin`; `weightKernel`, `weightKernel_flip_tower`, `oddPoisson_block_le`,
`re_blockSum_pp_le`, `re_blockSum_flip_le`, `negIndex_flip_eq_top_of_finite`,
`negIndex_zetaKernel_eq_top_or_flip`.

## 3. The low complete-Weil spectrum lives on the low conductors

**Theorem.** Under a prime-defect reserve and Ramanujan norm quasimodes at overlap `c` (tilted unit
spline: every `c > 0`), for every threshold `T` off the completed energies and every `ε > 0`,
eventually in `N`: every normalized Ramanujan vector `v_m`, `E_m(c) < T`, is within `ε` of the
spectral subspace below `T`, and every vector of that subspace is within `ε` (relatively) of
`span{v_m : E_m(c) < T}`. Along a diagonal schedule `c_N → ∞` with thresholds in `(T, T + 1]` the
second statement holds with `ε_N = 1/(s(N) + 1) → 0`.

**Proof.** Davis–Kahan: outside the sublevel every eigenvalue is `≥ T`, so
`‖v_m − P v_m‖ ≤ ‖A v_m − E_m v_m‖/(T − E_m) → 0`. The exact count gives `dim U = #{m : E_m < T}`;
the projections `P v_m ∈ U` have Gram within `η` of the identity, so they form a basis with
`Σ a_m² ≤ 2‖x‖²`; then `‖x − Σ a_m v_m‖ ≤ Σ|a_m| τ`.

**Lean** (`RenormalizedArithmeticPotentialTheory/TheLowCompleteWeilSpectrumLivesOnTheLowConductors`):
`exists_combination_of_near_orthonormal`, `completeWeilLowSpace`, `finrank_completeWeilLowSpace`,
`norm_sub_eigenProjection_le`, `eventually_completeWeil_lowSpace_near_ramanujan`,
`tiltedUnitSpline_lowSpace_near_ramanujan`, `exists_schedule_of_forall_eventually`,
`exists_overlap_schedule_lowSpace_near_ramanujan`.

## 4. The Gamma reserve pays Euler heads up to the square of the depth

**Theorem.** If `cost(P) = Σ_{p∈P} 4 log p/(√p − 1) ≤ log A`, Gamma minus the complete mixed Euler
source of `P` has negative index `≤ A` at every horizon; in general `≤ ⌈exp cost(P)⌉`. The head
`p ≤ Y` costs `≤ 32 √Y log Y`. The prime costs are not summable, so every depth `A` is exceeded by
some head.

**Proof.** `log A ≤ cellGammaWeight A` and the tail estimate `|tail| ≤ cost·energy/weight` give
nonnegativity on the kernel of the `A` detail readouts. `√p − 1 ≥ √p/4` and `Σ_{n≤Y} n^{−1/2} ≤ 2√Y`
bound the head. Each prime cost is `≥ 1/p` and `Σ 1/p` diverges.

**Lean** (`ArithmeticIndexDescent/TheGammaReservePaysEulerHeadsUpToTheSquareOfTheDepth`):
`abs_finiteEulerMixed_tail_le_of_cost`, `finiteEulerGamma_negative_dimension_le`,
`finiteEulerGamma_negative_dimension_le_exp`, `eulerHead`, `finiteEulerMixedGammaCost_eulerHead_le`,
`eulerHead_negative_dimension_le`, `not_summable_primeEulerMixedWeightTotal`,
`exists_eulerHead_cost_gt`.

## 5. Every finite flip set has infinite index

**Theorem.** For every nonempty finite set of primes `S` and every `n` there is `c₀` such that at
every overlap `c ≥ c₀` the `S`-flipped twisted complete Weil matrix eventually (in `N`) has at least
`n` negative eigenvalues. Hence, over real `C²` tests `g` of compact support,
`sup_g κ(K_{ω_S, g}) = ∞` on `ℚ_{>0}`, while for `Λ` the same supremum is `κ(K_ζ)`.

**Proof.** Let `Q = Π_{p∈S} p²` and `Y_S` the flip packet on the divisors of `Q`. For conductors `m`
prime to `Q` the vectors `e_m Y_S` have limit form `Σ_{d|Q} β_d² E_{md}(c) + τ_S`: Ramanujan modes are
multiplicative (`e_{md} = e_m e_d`), dilation invariant for `(k, m) = 1`, and the period mean
factors over coprime moduli, so cross terms between distinct `m` vanish. `τ_S < 0` and
`E_{md}(c) → 0` for fixed `m`, so `n` primes `m > Q` give `n` negative blocks at large `c`. On the
horizon the Gram matrix of the weight kernel is `Re W_λ` of the atomic test, i.e. the twisted
complete Weil matrix; the explicit-formula functional is real on real tests (the Fourier transform
of a real function is conjugate-symmetric and the Gamma bracket is even), so the real negative
eigenvectors span a complex negative subspace. For `Λ` every test sees at most the right zeros and
the cubic spline sees all of them.

**Lean** (`RenormalizedArithmeticPotentialTheory/EveryLowConductorSeesTheFlipSet`,
`HeckeKreinToeplitz/EveryFlipSetHasInfiniteIndexOnTheHeckeLattice`):
`eventually_flip_negative_eigenvalues`, `exists_overlap_flip_negIndex_ge`;
`im_weilFullFunctional_ofReal`, `im_weightKernel`, `hermQuad_gram_weightKernel_horizon`,
`exists_test_le_negIndex_weightKernel_finiteFlip`, `iSup_negIndex_weightKernel_finiteFlip_eq_top`,
`iSup_negIndex_weightKernel_primeFlip_eq_top`, `iSup_negIndex_weightKernel_vonMangoldt`.

## 6. The index of a growing Euler head is unbounded

**Theorem.** For every `K`, once `Y` is large, at every horizon `X ≥ max(K, (K + 1)Y − 1)` Gamma
minus the complete mixed Euler source of the head `p ≤ Y` is negative definite on a `K`-dimensional
space. No bound on the negative index holds for all heads, and for every `A > 0` the heads
`p ≤ (log N)^A` at horizon `N` have negative index tending to infinity.

**Proof.** Pair the details `a ≤ K` with the coarse windows `C_b = 1_{log Y + [log 2b, log(2b+2))}`,
`b ≤ K`. The reverse orientation of the source vanishes, and the source of `(e_a, C_b)` is
`B_Y[a,b] = ∫ h_a T_Y`, `T_Y(u) = Σ_{m ≤ Y} (2Λ(m)/√m) 1[2bYe^{−u} ≤ m < (2b+2)Ye^{−u}]` up to the
proper prime powers above `Y`, which cost `≤ 288·2·(Y(b+1))^{1/4}` (`Σ_{n≤M, n not prime} Λ(n)/√n ≤
144 M^{1/4}`). By `Σ_{n≤x} Λ(n)/√n ~ 2√x`, `T_Y/√Y → s_b = 4(√min(β,1) − √min(α,1))` pointwise with
a Chebyshev bound, so `B_Y/√Y → L[a,b] = ∫ h_a s_b` (dominated convergence). On the pair `a`,
`s_b = 0` for `b > a` and `s_a = 4 − 4√(2a)e^{−u/2}`, so `L` is lower triangular with diagonal
`−4√(2a) J_a`, `J_a = ∫ h_a e^{−u/2} > 0` by strict convexity of `e^{−s/2}`. Hence
`Σ_b (Lᵀx)_b² ≥ σ‖x‖²`. With coarse coefficients `(s/√Y)Lᵀx`: Gamma `≤ 4‖x‖² Γ_H + 4(s²/Y)‖L‖²‖x‖² Γ_C`
(disjoint supports, translation invariance of the windows' Lévy energy), the source
`≥ s(σ − ‖L‖ E_Y)‖x‖²` with `E_Y → 0`. With `sσ = 4Γ_H + 1` the form is `< 0` for large `Y`. For
`Y = ⌊(log N)^A⌋` the window condition `(K + 1)Y ≤ N` holds eventually since `(log N)^A = o(N)`.

**Lean** (`ArithmeticIndexDescent/TheSharpEulerHeadCouplesDetailsToFarWindows`,
`ArithmeticIndexDescent/TheIndexOfAGrowingEulerHeadIsUnbounded`): `tendsto_headWindowMass`,
`sum_nonprime_vonMangoldt_div_sqrt_le`, `abs_eulerHead_tsum_sub_le`,
`averageSectionProfile_coarseWindow`, `integerMixedSource_detailUnit_coarseWindow`,
`tendsto_headCoupling`, `headCouplingLimit_eq_zero_of_lt`, `headCouplingLimit_self_neg`,
`haarExpMoment_pos`; `finiteEulerMixedSource_sum`, `exists_sq_vecMul_ge`,
`eventually_eulerHead_negative_family`, `not_exists_uniform_eulerHead_index`,
`eventually_logPowerHead_negative_family`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  `lake --old env lean` on each module; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`
