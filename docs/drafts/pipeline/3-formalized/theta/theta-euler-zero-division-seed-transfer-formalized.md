# Zero division commutes with the theta Euler resolvent — Lean certificate

- **Paper card:** `theta-euler-zero-division-seed-transfer.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaSeedHalfLineDivision` (the literal seed and
  its half-line bounds, `k`-/`h`-dominated functions, the Euler resolvent `R_S`, commutation of the
  outward sine operator with every resolvent, iterated half-line divisions and their seeds),
  `GaloisForLFunctions.RHTower.ThetaSeedTransferQuartet` (real partial-fraction combinations,
  the rational sources `u_N` and seeds `v_N`, the general positive seed transfer and the quartet
  theorem), `GaloisForLFunctions.RHTower.ThetaTailScalingAsymptotics` (functions with the theta
  tail, Laplace asymptotics, one division raises the tail order by one, `k/h → 1`),
  `GaloisForLFunctions.RHTower.ThetaGaussianBaseCommutator` (the Gaussian base `ψ`, `Lψ = 0`,
  `h = ψ'' − ψ/4`, the commutator (3) and its non-vanishing),
  `GaloisForLFunctions.RHTower.ThetaTwoEndedTailLaw` (the sharp tail law (4), the two-ended
  filtration (5), the full-space equality, the infinite case, seed transfer of every direction,
  flatness), `GaloisForLFunctions.RHTower.ThetaTailIntegralCalculus` (tail integrals, shear Fubini,
  Cauchy's formula, the resolvent identity `T_β = β² I²(1 − T_β)`, tail series and their symbols,
  the closed form of the combination symbol), `GaloisForLFunctions.RHTower.ThetaTailGermExpansion`
  (expansions in `e^{-2x}`, the Gaussian integration by parts, the Watson expansion of `u_N/k`,
  recursive recovery, faithfulness of the germ, the causal kernel and its Laplace transform).
  `GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization` was extended in place (`listComb`,
  its specification `listComb_spec`, transforms and smoothness of list divisions); its dependent
  endpoint modules were rechecked.
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build` of every module; `lake env lean` audit clean (no errors,
  no warnings) on the seven new modules, on the extended realization module and on its dependents
  `ThetaEndpointDivisorClassification`, `ThetaEndpointHarmonicCompleteness`,
  `ThetaEndpointDefectIndex`, `ThetaEndpointMomentFiltration`, `ThetaEndpointPositiveDeformation`,
  `ThetaEndpointLpDefect`, `GaussianControlEndpointIncompleteness`; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all 329 declarations of the eight modules; no
  `sorry`; lint reports nothing for these modules.  The only hypotheses are the card's own
  quantified objects (a first-quadrant zero `α`, a selection `l` of first-quadrant zeros, a real
  numerator `N` of degree `≤ D`, finiteness or infiniteness of the off-line configuration, the
  deformation parameter, the orders `J, d`).

Dictionary: `h = thetaCuspLogSeed`, `k = thetaCuspFullSource`, `F = XiC`,
`Fourier(u) = sourceTransform u`; `T_α^+ = outwardSine α`; the resolvent
`(R_S g)(x) = Σ_{n∈S} n^{-1/2} g(x + log n)` is `seedResolvent S g` (`S = univ` for all integers,
`S = (N+1).smoothNumbers` for the primes `≤ N`); `R_N h = finitePrimeThetaCuspSource N`;
`h`-dominated half-line functions form `SeedDominated`; iterated divisions of a function along a
list are `halfListDivision L`, of the seed `seedListDivision L`, of the reflected source
`thetaListDivision L`; the real partial-fraction combination realizing `e(z²)/P_L(z)` is
`listComb L e`; for a selection `l`, `L = quadrantListOf l`, `P_L = listDivisor L`, `D = |L|`,
`u_N = rationalSource l N`, `v_N = rationalSeed l N`; the quartet direction `r(w) = w/P(w)` gives
`u_α = quartetSource α`, `v_α = quartetSeed α`; `ψ = thetaGaussBase`, `L = gaussBaseOperator`;
`W_{J,d} = twoEndedSources J d`, the partial-fraction directions of a selection form
`rationalSelection l`, `u = O(e^{-4dx} k)` is `tailOrderSubmodule d`; `I = tailIntegral`,
`g = O(e^{-2Px} f)` is `TailSmall f P g`; the symbol `ρ` of `u_N` is `realCombSymbol l N`,
`κ_j = causalKernelCoeff l N j = ρ_{j+1}`, `K = causalKernel l N`, `G = gaussTailBase`.

| Card item | Lean theorem |
|-|-|
| `n^{-1/2} h(x + log n)` is the literal source term; `h > 0` on `x ≥ 0`; `h(x+t) ≤ C e^{9t/2 − π e^{2x}(e^{2t}−1)} h(x)` | `rpow_neg_half_mul_thetaCuspLogSeed`, `thetaCuspLogSeed_pos`, `thetaCuspLogSeed_shift_le`, `thetaCuspLogSeed_eq` |
| **`R h = k` on `x ≥ 0`**; finite-prime truncations | `seedResolvent_univ_thetaSeedC`, `seedResolvent_smoothNumbers_thetaSeedC` |
| absolute convergence of the resolvent sums and the Green integrals for the seed and every finite iterate | `SeedDominated.absolute_convergence`, `SeedDominated.summable_seedResolvent`, `SeedDominated.norm_seedResolvent_le`, `seedDominated_thetaSeedC`, `seedDominated_halfListDivision`, `seedDominated_seedListDivision` |
| **`T_α^+(R h) = R(T_α^+ h)`, `T_α^+(R_N h) = R_N(T_α^+ h)`** on `x ≥ 0` (Tonelli–Fubini, shift commutation) | `outwardSine_seedResolvent`, `outwardSine_thetaSourceC_eq_seedResolvent`, `outwardSine_finitePrimeSource_eq_seedResolvent` |
| products of outward operators, real linear combinations of conjugate-parameter pairs | `seedResolvent_halfListDivision`, `seedResolvent_seedListDivision`, `seedResolvent_smoothNumbers_seedListDivision`, `seedResolvent_finset_sum`, `seedResolvent_re`, `seedResolvent_listComb` |
| `T_α^+ h/h` bounded on `[0,∞)`, `O(e^{-2x})`, `→ 0`; the same for every nonempty finite iterate | `SeedDominated.exists_norm_outwardSine_le`, `SeedDominated.tendsto_outwardSine_div`, `seedListDivision_tail` |
| repeated complex zero division through the multiplicity; real partial fractions of the proper `r` | `exists_source_mul_listDivisor`, `listComb_spec`, `thetaListDivision_eq_halfListDivision` |
| `u_N`: real, even, `C^∞` (smooth reflection), `|u_N| ≤ Ck`, `Fourier(u_N) P_L = F N(z²)`, tail and mass; `v_N` bounded by `Ch`, `u_N = R v_N` on `x ≥ 0`, seed tail | `rationalSource_spec`, `rationalSeed_spec`, `contDiff_listComb`, `seedDominated_listComb`, `tendsto_listComb_seed_sub_div` |
| **positive seed transfer** for every `u_N`: `k + εu > 0`, `h + εv > 0` on `x ≥ 0`, the Euler identity for the pair, the real divisor of `F`, the transform `F (P_L + εN(z²))/P_L`, unchanged vanishing moments | `rational_seed_transfer` |
| **the quartet**: `Fourier(u_α) = z² F/P_α`, `u_α = R v_α`, `u_α/k → 0`, `v_α/h → 0`; positivity, Euler identity, same mass, same leading tail, exactly the real divisor, quartet removed, other zeros kept, off-quartet zeros of `F (P_α + εz²)/P_α` | `quartetSource_spec`, `quartetSeed_spec`, `quartet_seed_transfer` |
| `P_α + εz²` has degree `deg P_α`, no real root for `ε > 0`, roots near the quartet for small `ε` | `quartet_perturbed_divisor` |
| `ψ = e^{x/2 − π e^{2x}}`: `Lψ = 0`, `h = ψ'' − ψ/4`, `∂(T_α^+ψ) = T_α^+(∂ψ)` | `gaussBaseOperator_thetaGaussBase`, `thetaCuspLogSeed_eq_gaussBase`, `hasDerivAt_outwardSine_gaussBase` |
| **(3)** `[L, T_α^+]ψ = −2πα e^{2x} ∫₀^∞ sin(αt)(e^{2t} − 1) ψ(x+t) dt` | `gaussBase_commutator` |
| the defect is not identically zero for `α ≠ 0` (in fact `e^{4x}[L,T_α^+]ψ/ψ → −α²/π²`, so it is nonzero near `+∞`) | `tendsto_gaussBase_commutator`, `gaussBase_commutator_eventually_ne_zero` |
| `h ∼ 4π² y^{9/4} e^{−πy}(1 − 3/(2πy))`, `k/h → 1`, `f(x + τ/y)/f(x) → e^{−2πτ}` with an exponential majorant | `thetaCuspLogSeed_eq_gaussTailBase`, `tendsto_thetaCuspFullSource_div_seed`, `thetaTypeTail_seed`, `thetaTypeTail_source` |
| **(4)** `e^{4dx} u_N/k` and `e^{4dx} v_N/h` both tend to `(−1)^d c/(2π)^{2d} ≠ 0` (`d ≥ 0`) | `tendsto_rationalSource`, `tendsto_rationalSeed`, `tail_limit_ne_zero`, `tendsto_listComb`, `tendsto_integral_kernel` |
| first `J` even moments vanish ⇔ `w^J ∣ N`; `u_N = O(e^{-4dx}k)` ⇔ `deg N ≤ D − d` | `rationalSource_mem_twoEndedSources_iff`, `divisorBasisComb_mem_twoEndedSources_iff` |
| **(5)** `dim = max(D − J − d + 1, 0)` for the partial-fraction directions of a selection | `finrank_rationalSelection_inf_twoEndedSources` |
| (5) is an equality for the full bounded source-difference space (finitely many quartets) | `finrank_twoEndedSources` |
| infinitely many quartets: every `W_{J,d}` is infinite-dimensional | `not_finiteDimensional_twoEndedSources` |
| every direction has a bounded seed difference of tail order `e^{-4dx}` and small perturbations are positive with positive seed, the Euler identity, the real divisor, the first `J` moments and the tail agreement | `twoEnded_seed_transfer`, `twoEnded_seed_transfer_of_finite`, `exists_rationalSource_of_mem_rationalSelection` |
| no nonzero rational defect is flat to all orders; the germ determines `N` | `rationalSource_flat_iff`, `rationalSource_germ_injective` |
| `ρ(w) = N(−1/w²)/P_L(−1/w²)`: `ρ · ∏(1 + β²X²) = ∏β² · X^{2D} N(−1/X²)`, real coefficients | `realCombSymbol_mul_symbolDen`, `combSymbol_mul_symbolDen`, `coeff_combSymbol_eq_ofReal`, `map_conj_combSymbol` |
| **Watson expansion**: `u_N/k ∼ ρ₀ + Σ_{n≥0} a_n y^{−n−1}`, `a_n = κ_n/(2π)^{n+1} + Σ_{j<n} c_{n,j} κ_j` with universal `c_{n,j}` | `rationalSource_tail_germ`, `hasExpansion_rationalSource`, `tailTable_self`, `tailTable_zero` |
| the diagonal never vanishes: the tail coefficients recover every `κ_j` recursively; agreement of the full germs forces equal symbols | `triangular_recovery`, `eq_zero_of_sum_exp_small`, `causalKernelCoeff_eq_of_germ_eq` |
| the causal kernel `K(t) = Σ κ_j t^j/j!` (entire, of exponential growth) with Laplace transform the proper part of `r(−s²)`: `(ρ₀ + ∫₀^∞ K e^{−st}) P_L(is) = N(−s²)` | `causalKernel`, `summable_causalKernel`, `causalKernel_laplace`, `exists_realCombSymbol_bound` |

Proof routes that differ from the paper.  The sharp coefficient (4) is proved by iterating the
one-step tail law (`tendsto_outwardSine`: `e^{4jx}g/f → a` implies `e^{4(j+1)x}T_β g/f → aβ²/(2π)²`,
from the scaling limit `f(x + τe^{-2x})/f(x) → e^{-2πτ}` and dominated convergence) through the
partial-fraction recursion, instead of expanding the causal kernel at `t = 0`.  The Watson expansion
is proved through the operator identity `T_β = β² I²(1 − T_β)` (shear Fubini on the quarter plane),
which expresses every combination as `Σ ρ_m I^m k` to all orders, followed by the exact
integration by parts `I G_q = G_{q+1}/(2π) + ((5/4 − q)/π) I G_{q+1}` for the Gaussian base and the
algebra of expansions in `e^{-2x}` (products and inverses); the constants
`c_{n,j} = [w^{n+1}] 𝓘^{j+1}(4π² − 6πw)/(4π² − 6πw)` depend only on the first atom.  The
faithfulness of the germ is proved both through (4) (`rationalSource_flat_iff`) and through the
Watson coefficients (`causalKernelCoeff_eq_of_germ_eq`, for arbitrary pairs of selections).  The
non-vanishing of (3) is proved in the stronger form of an explicit nonzero limit instead of the
paper's contradiction through the first-order equation.
