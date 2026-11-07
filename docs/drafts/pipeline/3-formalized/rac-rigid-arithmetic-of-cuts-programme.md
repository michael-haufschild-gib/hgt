# Rigid Arithmetic of Cuts (RAC) programme

- **ID:** RAC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.6, §2.9
- **Statement:** how the exact statement `N(x) = ⌊x⌋` constrains its zeros by operations with no sign that are not linear floor identities.

## Goal
Lean folder `formal/GaloisForLFunctions/RigidArithmeticOfCuts/`, umbrella `RigidArithmeticOfCuts.lean`, foundational `README.md`.
Answer the questions of §2.9, build the tools of §2.9, test the criteria of §2.9.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: 28 modules, each checked with `lake --old env lean`

## Answers

| Q | Answer | Lean |
|---|---|---|
| What replaces Frobenius | The carry `⌊k{x}⌋`, never constant; bounded multiplicities have no Frobenius. Curves: kernel = recurrence of rank `deg P`. `ℤ`: Hecke action on the kernel | `not_exists_constant_carry`, `not_hasFrobenius_of_bounded`, `rank_curveKernel`, `exists_mul_of_hecke_invariant` |
| Nonlinear functional seeing a zero and surviving the twin | `ζ A^k` has order `m − k`; the Selberg ledger has gap `4 L N Σ b(e)/e + O(N^{3/4})` on every filter | `sees_of_lt`, `exists_abs_selberg_gap_sub_le`, `tendsto_selberg_twin_gap` |
| Primes recur at a zero | Prime returns have positive density at every length; at a zero the returns of `ζ` are rare, so the tail fails | `exists_density_primeReturnSet`, `primeReturnSet_subset_zetaReturnSet`, `exists_primeReturn_not_zetaReturn` |
| Single off-line zero | No contradiction from any named class; a power bound on the parity ledger would confine zeros, and it has no source | `forall_hasSum_abelStep_mod_zero_iff`, `twistPoly_eq_zero_of_parity_bound` |
| Closest fake | One fake at infinite level; tight fakes converge to it; no lower radius at finite level | `eq_pronic_of_forall_isFakePrimeMeasure`, `tendsto_pronic_of_tight`, `isFakePrimeMeasure_translate` |
| Rotated relation | Equal modulus is RH; polynomial coefficients are refuted; unrestricted coefficients are vacuous | `riemannHypothesis_iff_forall_norm_eq`, `squaredXi_no_polynomial_rotation`, `exists_normalized_entire_vacuous_rotated_relation` |

## Paper proofs

**Uniqueness of the fake.** Dilates of producers give `T(j) ≤ A/j`, and `hasRate_vk` makes `A → 1`, so `W = 1/r − T ≥ 0` (`cutTail_le_inv`). `W − 1/r` is nondecreasing, so block sums are controlled and `W` is summable (`summable_of_cut_kernel`). The cut identity (`sum_Icc_mul_mod`) gives `W(kℕ) = S/k` (`uniform_multiples_of_cut_kernel`). The Euler product at the edge, `Π(1 − 1/p) → 0`, forces `W = 0` (`eq_zero_of_uniform_multiples`).

**Tight fakes.** Compactness of a product of intervals gives a limit along subsequences. Dominated convergence keeps the moments of each level, so the limit is a fake at every level, hence pronic (`isFakePrimeMeasure_of_tendsto`, `tendsto_pronic_of_tight`).

**Zeros are the kernel.** Summation by parts gives `Σ U_s(r)(r mod k) = (1 − k^{1−s}) ζ(s)` on `Re s > 0` (`hasSum_abelStep_mod`). Independence of `k ↦ k^w` separates finite combinations (`eq_zero_of_sum_mul_one_sub_cpow`).

**Filter law.** `conv(Λ−2b, Λ−2b) = Λ∗Λ − 4Λ∗b + 4b∗b` (`selbergWeight_filteredTwin`). The ledger of `Λ∗b` is `Σ_e b(e) log(stencil integer at ⌊N/e⌋)`, each within `L + E(1 + log N)` of `L N/e`, and `Σ_{e≤N} b(e) ≤ ψ(√N)` (`abs_ledger_conv_sub_le`). The piece `b∗b` is below `even∗even`, of size `N^{3/4}` (`ledger_conv_even_le`). The even mass reindexes through squares, `Σ_{e≤N} Λ_even(e)/e = Σ_{j≤√N} Λ(j)/j²` (`harmonicMass_even`), with limit `−ζ′/ζ(2)` (`ofReal_primeSquareMass`).

**The tail.** Effective Kronecker gives a return in each window of length `T₀`. Chord subadditivity (`one_sub_cos_add_le`) and `1 − cos x ≤ x²/2` widen each return to an interval of fixed length, so density is positive (`exists_density_primeReturnSet`). At a zero, `riemannZeta_eq_zero_iff_returnExponent` gives measure `≤ T^θ`, `θ < 1`, for returns of `ζ` on a disc. Subtracting gives the theorem. Above the abscissa, phases of composites are bounded by `Ω(n)` times the prime bound (`norm_phase_sub_one_le`), and the tail is summable.

**Effective Kronecker.** On `S = divisors(R^D)`, `|log a − log b| ≥ 1/Q` separates frequencies (`one_div_le_abs_log_sub_log`). The density `|B|²` integrates off-diagonal terms to size `1/T`, and `∑ a_p cos(t log p − θ_p)` against it counts pairs differing by one prime (`abs_integral_boxDensity_mul_cos_sub_le`, `card_sub_card_filter_le`, `exists_height_phase_return`).

**Parity.** `Σ_{d|n} λ(d) = 1_□(n)` gives `Σ_k L(x/k) = ⌊√x⌋` (`floorSum_liouvilleR`), and inversion gives `L(x) = Σ_{d≤√x} M(x/d²)` (`liouvilleR_eq_squareMertens`). The Mellin transform of the parity ledger is `s⁻¹ D_{cλ}(s) ζ(2s)/ζ(s)`. A power bound makes it holomorphic to the right of its exponent, so a zero of `ζ` there with `Re ρ > ½` must be a zero of the twist (`twistPoly_eq_zero_of_parity_bound`).

**Extremal angle.** `arg w → 0` along zeros (`finite_setOf_le_zeroSlope`), so the maximal angle is attained under `¬RH` (`exists_zero_of_maximal_angle`). Termwise `‖1 − tu‖² − ‖1 − t̄u‖² = 4 Im t Im u`, with `Im u ≥ 0` at the extremal zero (`norm_tprod_lt_norm_tprod`, `norm_squaredXi_conj_lt`). Cancelling the boundary zero and differentiating `‖g(e^{iθ})‖²` at `θ = 0` gives the Stieltjes sign (`im_second_div_first_nonpos`, `im_stieltjes_nonpos`).

**Infinite defect.** `D(t) m^{it}` is a finite sum of Bohr integrands at frequencies `log m ± log n`. Cauchy on the rectangle `[½, ¾]` with the convexity bound moves `tendsto_zeta_line_mul_char_average_log` to the critical line (`tendsto_critical_average_sub`). The mean is `m^{-½}(a(m) − G(1))` (`tendsto_stencilDefect_average`). A sublinear defect makes `a` constant, and induction on divisors gives `g = c δ₁` (`eq_zero_of_stencilCount_const`, `eq_zero_of_defect_sublinear`).

**Purity.** At a root, imaginary part gives `y = 0` or `2 q x = t`. Both cases give `q |u|² = 1` when `t² ≤ 4q`. Above the bound two real roots with product `1/q` cannot both have square `1/q` (`normSq_of_root`, `isPureKernel_iff`).

## No-go closure

| No-go | Positive survivor | Status |
|---|---|---|
| Exact ledgers see zeros | Order law of the pieces `ζ A^k`, residue at simple zeros | Lean: `meromorphicOrderAt_ledgerSymbol`, `tendsto_mul_ledgerSymbol` |
| Selberg ledger breaks parity | Exact gap law, every filter seen at scale `N`, constant `→ 0` | Lean: `exists_abs_selberg_gap_sub_le`, `levelConstant_pos`, `tendsto_levelConstant` |
| Prime returns transport a zero | Effective recurrence of Dirichlet polynomials; half-plane return theorem | Lean: `exists_zero_in_every_window`, `primeReturnSet_subset_zetaReturnSet` |
| Polynomial rotation of `Q` | Extremal modulus, equal-modulus equivalence, Stieltjes sign | Lean: `norm_squaredXi_conj_lt`, `riemannHypothesis_iff_forall_norm_eq`, `im_stieltjes_nonpos` |
| Unrestricted rotated coefficients | Exact local alternative; see `5-failed/rotated-relations-with-unrestricted-balanced-coefficients.md` | Lean: `balanced_relation_zero_or_modulus_eq` |
| Stencil near `ζ` in FE distance | Bohr coefficients on the line; mean law of the defect | Lean: `tendsto_critical_average_log`, `tendsto_stencilDefect_average` |
| New zeros by added generators | Exact factorization right of the count exponent | Lean: `exists_numerator_eq_mul` |
| Linear stencil over a curve past the trivial bound | Purity is the trace bound | Lean: `isPureKernel_iff` |

## Open

Parity source; growing levels; degree `≥ 3` ledgers; kernel beyond power laws; finite-level radius; integer-norm one-offs; smallest FE defect of a one-off; coefficient classes; second-order extremal law; pointwise bounds between `y ≍ log T` and VK. See the README, §9.

## Log
- 2026-11-07 — created in 1-in-progress
- 2026-11-07 — moved to 3-formalized
