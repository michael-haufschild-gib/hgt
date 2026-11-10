# Infinite-rank purity theory (programme)

- **ID:** IRP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — programme
- **Source:** docs/reports/review-0911/fable.md §7
- **Statement:** the infinite-rank counterpart of each finite-rank purity mechanism, with its price;
  conversions from law to point; answers to Q1–Q8 and tests 1–5 of the README, each by a theorem of
  the folder.

## Goal
Folder `formal/GaloisForLFunctions/InfiniteRankPurityTheory/`, umbrella
`InfiniteRankPurityTheory.lean` (wired into `MainTheorems.lean`), README in the folder. Unconditional
Lean only, no computations.

## Gates
- [x] 0 → 1  in-progress: README draft
- [x] 1 → 2  paper proofs (below and module docstrings)
- [x] 2 → 3  every module checked with `lake --old env lean`, empty output

## Paper proofs

### P1. Kronecker over ℤ: integral trace-class Frobenius modules are Tate
Data: distinct modes `ρ_i`, weights `b_i`, `Re ρ_i ≤ A < m`, `Σ ‖b_i‖(1+‖ρ_i‖)^m < ∞`, weight set
without infinite ascending chain (`WeightsWellFounded`). If `t(n) = Σ b_i n^{ρ_i} ∈ ℤ` for all large
`n`, then `b_i ≠ 0 ⇒ ρ_i ∈ {0,…,m−1}` (`tate_of_integral_trace`).
1. `d/dx Σ b_i x^{ρ_i} = Σ b_i ρ_i x^{ρ_i−1}` for `x > 1` (`hasDerivAt_frobTrace`).
2. `‖Δ^m t(x)‖ ≤ K x^{A−m}` by induction with the mean value inequality
   (`exists_norm_fwdDiff_iter_frobTrace_le`).
3. `Δ^m t(n)` is an integer tending to `0`, hence `0` for `n ≥ n₀` (`fwdDiff_iter_eventually_zero`);
   Newton: `t` is a polynomial with no coefficient of index `≥ m` on `n ≥ n₀`
   (`exists_polynomial_of_fwdDiff_iter_zero`).
4. `Π_{k<m}(S_p − p^k)` kills that polynomial and multiplies the weight of `ρ` by
   `Π_{k<m}(p^ρ − p^k)` (`tateDilation_polynomial`, `tateDilation_frobTrace`).
5. Uniqueness and growth (`re_le_of_frobTrace_bound`, `eq_zero_of_frobTrace_eventually_zero`,
   `frobTrace_bound_iff`): take the top visible weight `σ`; divide the trace at `2^a 3^b` by
   `(2^a 3^b)^σ`; a Cesàro mean in `a`, then one in `b`, isolates the modes with
   `2^{ρ} = 2^{ρ_{i₀}}` and `3^{ρ} = 3^{ρ_{i₀}}`; `cpow_two_three_injective` gives `ρ = ρ_{i₀}`.
6. `2^{ρ_i} = 2^k`, `3^{ρ_i} = 3^{k'}` give `ρ_i = k`.
Corollaries: traces in `ℤc` (`tate_of_trace_in_zmultiples`); with `ρ ↔ 1−ρ` only `0, 1`
(`tate_of_integral_trace_dual`); nothing visible in the open strip (`not_visible_in_open_strip`); no
trace-class family of zeros of `ξ` is integral (`eq_zero_of_integral_trace_of_xi_zeros`).

### P2. Kronecker for one Frobenius
Summable tower in the closed disc with integer level sums: one `τ ≥ 1` makes every weighted point of
the circle a `τ`-th root of unity and the inner level sums vanish eventually
(`kronecker_oneFrobenius`); with distinct modes and moduli without ascending chain the rank is finite
(`kronecker_oneFrobenius_injective`). Split `S = U + I`; `I → 0`; `U` has large almost periods
(`exists_almostPeriod`), so `U(ν) ∈ ℤ`; an almost period of precision `½` is a period; the tower with
weights `c(z^τ − 1)` has zero level sums and Cesàro means give `(w^τ − 1)·weight(w) = 0`.
Sharpness at positive weight: the limit-periodic tower (`exists_pure_integral_tower_of_infinite_rank`),
`S(ν) = Σ_{2^k ∣ ν} 2^{ν−k}`.

### P3. Purity by parity; the line law of the Eisenstein constant term
`θ = E'/E`, `E = ξ(2s)Y^s`, `E' = ξ(2s−1)Y^{1−s}`, is a real Schur function on `Re s > ½` for `Y ≥ 1`
(`norm_constantTermDual_le`, from `BlackHoleRingdown.norm_xi_two_mul_le`). A zero of
`(s−1)E + sE'` right of the line is a point where `θ = −(s−1)/s`; the right side is conformal onto the
disc; two solutions give two fixed points of a self-map of the disc, so `θ = −b₁` identically, false
at `s = 1` (`eqOn_of_two_agreements`, `hermiteBiehler_indexOne`, `constantTerm_indexOne`). Hence no
non-real zero off the line for every `Y ≥ 1` and every `s` (`lineLaw`). Sharp: a real zero in
`(x₁, 1)` for large `Y` (`exists_unique_exceptionalParameter`); index two admits a non-real pair
(`indexTwo_admits_nonreal_pair`).

### P4. Symmetries of the zero divisor
`s ↦ as + b` preserves all orders of `ξ` iff `(a,b) ∈ {(1,0), (−1,1)}`; anti-affine likewise
(`preservesXiDivisor_affine_iff`, `preservesXiDivisor_antiaffine_iff`). A high zero forces `Im a = 0`;
a contraction makes the iterates of a zero accumulate at the fixed point; a vertical period `τ` gives
`N(kτ) = kN(τ)` against `N(T) ≥ (1/4π)T log T`.

### P5. Elimination with an attained top
Summable tower in the closed disc, weights of nonnegative real part, one mode of positive weight on
the circle: the level sums do not tend to zero along a thick set (`not_small_on_thick_of_circle_mode`).
Window means: `norm_windowMean_sub_le` (circle error small for long windows, inner error small for far
windows), `merged_eq_zero_of_small_on_runs`. Consequences: `norm_le_one_of_thick_bounded_levelSums`,
`curveDatum_unitary_of_thick_bounded_trace`, `lag_bound_iff_of_attainedTop`,
`riemannHypothesis_iff_attainedTop_and_thick_lag_bounded`. For the lag of `ζ` along a full progression
the dichotomy is `RHTower.riemannHypothesis_or_not_attained_of_forall_le`.

### P6. Semicontinuity of the index
If eventually every member of a locally uniformly convergent sequence of entire functions has at most
one zero in an open set, so has the limit (`zeros_subsingleton_of_tendstoLocallyUniformly`); RH iff
`ξ` is a limit of real entire functions with at most one zero right of the line
(`riemannHypothesis_iff_limit_of_indexOne`).

### P7. The index law at any index
Schur function `θ` on `Re s > ½`; Blaschke product of degree `≤ κ`: `B = N/(εN^*)`,
`N^*(s) = conj N(1 − s̄)`, `deg N ≤ κ`, `‖ε‖ = 1`, `N^* ≠ 0`, `‖N‖ ≤ ‖N^*‖` on the half-plane
(`IsBlaschke`). Claim: agreement at `κ + 1` points forces `θ = B` (`eqOn_of_card_agreements`); hence at
most `κ` agreements if `θ ≠ B` somewhere (`encard_agreements_le`).
1. Schwarz on the half-plane: a Schur `f` with `f(s₀) = 0` has `‖f‖ ≤ ‖b_{s₀}‖`
   (`norm_le_norm_defectFactor`), so `f = φ b_{s₀}` with `φ` Schur
   (`exists_quotient_by_defectFactor`); applied to `M_v ∘ θ`, `v = θ(s₀)`, `‖v‖ < 1`
   (`exists_schur_reduction`).
2. One step on `B`: `D = εN^*`, `N' = N − vD` vanishes at `s₀`, `N' = (X − s₀)N₁`, `deg N₁ ≤ κ − 1`.
   Reflection: `(N')^* = N^* − v̄ε̄N` and `(N')^* = −(X − (1 − s̄₀))N₁^*`, so
   `D − v̄N = −ε(X − (1 − s̄₀))N₁^*` and `M_v ∘ B = [N₁/(−εN₁^*)] b_{s₀}`. `N₁^* ≠ 0` since
   `‖v̄N‖ < ‖D‖`; `‖N₁‖ ≤ ‖N₁^*‖` by step 1 applied to `M_v ∘ B`, at `s₀` by continuity
   (`IsBlaschke.reduce`).
3. Induction on `κ`: at an agreement `s₀`, if `‖B(s₀)‖ = 1` both are constant (maximum modulus);
   otherwise reduce both, the other agreements persist since `b_{s₀} ≠ 0` there, and `M_v` is
   injective on the closed disc (`mobius_injOn`). Degree zero: `B` is a unimodular constant.
Products `c Π b_w` are in the class (`isBlaschke_prod`). Hermite–Biehler sums
`P_W E − c P_{W♯} E'`: at most `card W` zeros right of the line (`hermiteBiehler_index`); real data:
at most `κ/2` above the real axis (`two_mul_encard_upper_zeros_le`). Sharp: the `cosh` model
`P_W P_{W♯}(e^{s−½} + e^{½−s})` vanishes right of the line exactly on `W` (`index_attained`).

### P8. The threshold `4πe^{−γ}`
`D_Y(x) = xξ(2x−1) − (1−x)ξ(2x)Y^{2x−1}` has the sign of the constant term at `x ∈ (½, 1)`,
`D_Y(½) = 0`, and decreases in `Y`. `ξ'(1) = Λ₀(1)/2 = ½ + γ/4 − ¼ log 4π`
(`RHTower.hasDerivAt_xi_one_archimedeanGenusZeroSum`, Mathlib `completedRiemannZeta₀_one`),
`ξ'(0) = −ξ'(1)`; so `D_Y'(½) = ½(log 4πe^{−γ} − log Y)` (`hasDerivAt_defect_half`).
- `Y > Y*`: `D_Y < 0` just right of `½`, the constant term is `½` at `1`: a zero
  (`exists_exceptionalParameter_of_threshold_lt`).
- `1 ≤ Y < Y*` with a zero `x₁`: at `Y₂ ∈ (Y, Y*)`, `D_{Y₂}(x₁) < 0`, `D_{Y₂} > 0` near `½`, value
  `½` at `1`: two zeros right of the line, against the index bound
  (`constantTerm_ne_zero_of_lt_threshold`).
- `Y = Y*` with a zero `x₁`: a point `x' ∈ (½, x₁)` is a zero at exactly one height `Y'`;
  `Y' < Y*` gives a zero at a height in `[1, Y*)`, `Y' = Y*` two zeros at `Y*`, `Y' > Y*` two zeros
  at `Y'` by persistence (`constantTerm_ne_zero_at_threshold`).
Result: `exists_exceptionalParameter_iff`, `re_eq_half_of_constantTerm_eq_zero`.

### P9. A family reads the strip of its fixed part
`F_Y = (s−1)G(2s)Y^s + sG(2s−1)Y^{1−s}`. If `G` is real entire, `G ≠ 0` and
`‖G(w−1)‖ ≤ ‖G(w)‖` on `Re w > 1`, `G(1) ≠ 0`, then `F_Y` is of index one for `Y ≥ 1`
(`pencil_indexOne`, an instance of P3). For a finite divisor `Z` in `Re ≥ 0` with
`Z = {1 − ρ̄}`: `‖w − 1 − ρ‖ ≤ ‖w − (1 − ρ̄)‖` for `Re w ≥ 1`, so
`‖G_Z(w−1)‖ ≤ Π‖w − (1−ρ̄)‖ = ‖G_Z(w)‖` (`norm_divisorPoly_sub_one_le`). Every finite `M` in the
closed strip without `0, 1` symmetrizes to such a divisor (`exists_fixedPart_with_lineLaw`).
Converse: `F_Y Y^{−s} = (s−1)G(2s) + sG(2s−1)Y^{1−2s}`; near a non-real zero `w₀/2` of the first
term with `Re w₀ > 1` the second is `≤ M Y^{−2η}`; sphere domination plants a zero
(`exists_nonreal_zero_pencil_of_zero_right`). Equivalence for divisors without real points:
`divisorPencil_lineLaw_iff`.

### P10. Trace class at a Frobenius; sequences that are not traces
`TraceClassAt q m`: `Σ‖b_i‖q^{Re ρ_i}(1+‖ρ_i‖)^m < ∞`. Dilation: `t(qx) = Σ b_i q^{ρ_i} x^{ρ_i}`
(`frobTrace_dilate`). Differences of step `h`: `‖Δ_h^m T(y)‖ ≤ K y^{A−m}`
(`exists_norm_fwdDiff_iter_frobTrace_le`); `Δ_1^m t(x) = Δ_{1/q}^m T(x/q)`, so `Δ^m t(n) → 0`
(`tendsto_fwdDiff_iter_frobTrace_of_traceClassAt`). Integral ⇒ eventually polynomial; with distinct
modes and no ascending chain ⇒ Tate, with the duality only `0, 1`
(`exists_polynomial_of_integral_trace_at`, `tate_of_integral_trace_at`,
`tate_of_integral_trace_dual_at`).
- Euler product: `f` supported on prime powers; `g(n) = f(pn)` is a trace; for `p^a > m`,
  `Δ^m g(p^a) = (−1)^m f(p^{a+1})` because `p(p^a + k)`, `0 < k < p^a`, is not a prime power; so
  `f(p^k) → 0` (`not_isTrace_of_primePower_support`); `Λ(2^k) = log 2`
  (`not_isTrace_vonMangoldt`).
- Integer sequence with consecutive differences equal to `a` and to `b ≠ a` infinitely often: a
  trace would be eventually a polynomial `P`, and `P(X+1) − P` would be two constants
  (`not_isTrace_of_two_jumps`); Mertens (`μ(4k) = 0`, `μ(p) = −1`), `π`.
- Lag module: `Σ‖1/(ρ(1−ρ))‖ < ∞`, and `‖1/(ρ(1−ρ))‖(1+‖ρ‖) ≥ 1/‖ρ‖` with `Σ1/‖ρ‖ = ∞`
  (`lagModule_traceClassAt_zero`, `lagModule_not_traceClassAt_one`).

### P11. Traces determine the module; the glued square
Merged module on `range ρ` with weights `Σ_{ρ_i = w} c_i`: same trace (fibrewise sums), distinct
modes, so P1 step 5 applies (`mergedWeight_eq_zero_of_frobTrace_bound`,
`frobTrace_bound_iff_mergedWeight`); at a Frobenius `q` by
dilation, the merged weight is multiplied by `q^w`. Two modules with equal traces: the difference
module on the disjoint union has trace zero (`mergedWeight_eq_of_frobTrace_eventually_eq`).
Archimedean fibre: `Σ_k x^{−2k} = x²/(x²−1)`, of trace class at `2` of every order since
`Σ(1+2k)^m 4^{−k} < ∞`; hence forced (`archimedeanFibre_forced`). `Λ + n²/(n²−1)`: a trace minus a
trace is a trace, and `Λ` is none; order zero: a trace of order zero tends to zero, the Lefschetz
numbers are `≥ 1` (`not_isTrace_gluedLefschetz`, `not_isTrace_pointCount`).

### P12. Conjugacy classes and constituents of the module
`M = ⊕ ℂ(−ρ_i)` (finitely supported vectors), `Frob_n e_i = n^{ρ_i} e_i` (`frobAct`).
- `T` linear with `T Frob_p = Frob_p T`: comparing the `j`-th components of `T Frob_p e_i` and
  `Frob_p T e_i` gives `(p^{ρ_i} − p^{ρ_j})(T e_i)_j = 0` (`cpow_eq_of_commute`); equal eigenvalues
  have equal moduli `p^{Re ρ}`, so equal weights (`re_eq_of_commute`); with `p = 2, 3` and distinct
  modes `j = i` (`eq_of_commute_two_three`). Conjugate-linear `T`: `p^{ρ_j} = conj p^{ρ_i} =
  p^{ρ̄_i}`, so `ρ_j = ρ̄_i` (`eq_conj_of_semilinear_commute`).
- Stable subspace `W`, `v ∈ W`, `v_i ≠ 0`: induction on a finite set containing the support of `v`
  besides `i`; for `j₀ ≠ i` one of `p = 2, 3` has `p^{ρ_{j₀}} ≠ p^{ρ_i}`, and
  `(Frob_p − p^{ρ_{j₀}}) v ∈ W` has no component at `j₀` and a nonzero one at `i`
  (`single_mem_of_stable`).

### P13. Kronecker and growth with merged modes at any Frobenius
Integral trace ⇒ eventually a polynomial `P` with `P.coeff i = 0` for `i ≥ m` (P10). The module on
`Fin m` with modes `k` and weights `P.coeff k` has trace `P(n)` (`frobTrace_tate`). Traces determine
merged weights (P11), and the Tate module carries nothing off `0, …, m−1`
(`mergedWeight_eq_zero_of_integral_trace`); with visible modes closed under `w ↦ 1 − w`:
`k + l = 1` (`mergedWeight_dual_of_integral_trace`). Growth: the merged module of the dilated module
has trace `t(n) = T(n/q)`; if its visible weights are `≤ s` then `‖T(x)‖ ≤ (Σ‖C‖) x^s` for `x ≥ 1`
(`norm_frobTrace_le_of_re_le`); the converse is P11 (`frobTrace_bound_iff_mergedWeight_at`).

### P14. Families under a measure
- Elimination at radius `R`: apply P5 to `z/R` (`norm_le_of_thick_levelSums_le`).
- Amortization: `‖S(ν)‖^k ≤ C(BR^k)^ν` gives `‖S(ν)‖ ≤ max(C,1)(B^{1/k}R)^ν`, so the modes are
  `≤ B^{1/k}R`; `B^{1/k} → 1` (`norm_le_of_amortized_levelSums`).
- Atom: `μ{ω₀}‖S_{ω₀}(ν)‖^k ≤ ∫‖S_ω(ν)‖^k dμ` (`member_norm_le_of_family_moments`).
- Fixed part: `∫(F + V) = F` when `∫V = 0`, so `‖F‖ ≤ ∫‖F + V‖`; `‖F + V‖² = ‖F‖² +
  2 Re(F̄V) + ‖V‖²` integrates to `‖F‖² + ∫‖V‖²` (`integral_norm_sq_fixedPart_add`); then P5
  (`fixedPart_norm_le_one_of_mean_bounded`, `fixedPart_norm_le_one_of_excess_bounded`).

### P15. The line law over limits; the index in limits
- `a_n G_{Z_n} → G` locally uniformly, `Z_n` symmetric in `Re ≥ 0`: `‖G(w−1)‖ ≤ ‖G(w)‖` is a limit
  of inequalities; a zero of `G` with `Re > 1` would be a limit of zeros of `a_n G_{Z_n}`, which lie
  in `Re ≤ 1` (`a_n ≠ 0` eventually since `G(1) ≠ 0`); then P9 (`pencil_lineLaw_of_tendsto`). `ξ`
  satisfies the hypotheses of P9 directly (`xi_mem_pencil_class`).
- `κ + 1` zeros of the limit in an open `U` have disjoint balls inside `U`, each eventually
  containing a zero of `P_n`: `κ + 1` distinct zeros of `P_n` in `U`
  (`encard_zeros_le_of_tendstoLocallyUniformly`, `encard_xi_zeros_le_of_limit`).

### P16. The chain condition is exact
Modes `ρ_i` with `‖ρ_i‖ ≤ R`, `Σ‖c_i‖ < ∞`, power sums `Σ_i c_i ρ_i^k = 0` for `k ≥ 1`. For `x > 0`:
`x^{ρ_i} = Σ_k (ρ_i log x)^k/k!`; the double series is dominated by `‖c_i‖ (R|log x|)^k/k!`, so
`t(x) = Σ_k (log x)^k/k! Σ_i c_i ρ_i^k = Σ_i c_i` (`frobTrace_eq_tsum_of_powerSums_zero`). The positive
Wolff measure of `HTGeometry.CircleQuadraturePositive` has distinct nodes with `5/4 ≤ ‖ρ_i‖ ≤ 10`,
positive summable masses, vanishing power sums, and the node `5/4` of mass one. Normalized to total
mass one: trace `1` at every `x > 0`, trace class of every order, a visible mode `5/4`
(`exists_integral_traceClass_module_not_tate`). If its weights had no ascending chain, P1 would make
`5/4` a natural number (`wolff_not_weightsWellFounded`).

### P17. Elimination of a mode accessible from infinity
Summable tower, `‖z_i‖ ≤ R`, `‖S(ν)‖ ≤ C r^ν` at every level. `Φ(w) = Σ c_i/(w − z_i)`.
1. `‖w‖ > R`: `c_i/(w − z_i) = Σ_ν c_i z_i^ν/w^{ν+1}`, absolutely summable in `(i, ν)`; so
   `Φ(w) = Σ_ν S(ν)/w^{ν+1} =: Ψ(w)` (`towerResolvent_eq_levelSeries`).
2. `Ψ` is analytic on `‖w‖ > r` (terms bounded by `|C|(r/r')^ν/r'` on `‖w‖ > r' > r`)
   (`analyticAt_levelSeries`); `Φ` is analytic at every point at positive distance `d` from the modes
   (terms bounded by `2‖c_i‖/d` on the ball of radius `d/2`) (`analyticAt_towerResolvent`).
3. Mode `z_j`, `‖z_j‖ > r`, path `γ` from `z_j` to a point with `‖γ(1)‖ > R`, staying in `‖w‖ > r`
   and off the closure of the modes for `t > 0` (for instance the segment `z_j(1+t)`): `Φ = Ψ` near
   the far end, both analytic on the path, so `Φ = Ψ` on it.
4. `z_j` isolated with gap `δ`: for `‖w − z_j‖ ≤ δ/2`,
   `(w − z_j)Φ(w) = m_j + Σ_{z_i ≠ z_j} c_i (w − z_j)/(w − z_i)`, the sum bounded by
   `(2/δ)(Σ‖c_i‖)‖w − z_j‖` (`norm_merged_le_of_isolated`). With `Ψ` bounded near `z_j`:
   `‖m_j‖ ≤ K ε` for all small `ε`, so `m_j = 0` (`merged_eq_zero_of_accessible`,
   `merged_eq_zero_of_radially_visible`).
For `ζ`, tower `e^{ℓ(ρ−1)}` with lag weights: `Φ(νℓ) = O(e^{aνℓ})` gives `r = e^{ℓ(a−½)}`; a zero with
`Re ρ₀ > ½ + a` has `‖mode‖ > r` and positive merged weight (`lag_not_small_of_accessible`,
`riemannHypothesis_of_lag_bounded_of_accessible`). Sharp: the positive Wolff measure has level sums
`0` for `ν ≥ 1` (so the bound holds with `r = 0`) and positive masses, hence no isolated node is
accessible (`wolff_node_not_accessible`).

### P18. The index counts the zeros of the defect right of the line
Defect `P_{W₊}P_{W₋}`, `W₊` right of the line, `W₋` left. `F = 0` right of the line iff
`(E'/E)·P_{W₋♯}/P_{W₋} = c⁻¹ P_{W₊}/P_{W₊♯}`; `P_{W₋♯}/P_{W₋} = Π_{w∈W₋} b_{1−w̄}` is a Blaschke product
since `1 − w̄` lies right of the line, so the left side is a Schur function and P7 applies with
`κ = card W₊` (`hermiteBiehler_index_general`).

### P19. On the flow the weight filtration needs no chain condition
Module `(b, ρ)`, `Σ‖b_i‖ < ∞`, `Re ρ_i ≤ A`, finitely many modes in every disc. `t(x) = Σ b_i x^{ρ_i}`
is continuous on `x ≥ 1`. `M(w) = ∫_1^∞ t(x) x^{−w−1} dx` (Mellin transform of `t·1_{x≥1}` at `−w`).
1. `Re w > A`: term by term (`Σ_i ∫‖b_i x^{ρ_i−w−1}‖ = Σ‖b_i‖/(Re w − Re ρ_i) < ∞`),
   `M(w) = Σ b_i/(w − ρ_i)` (`flowMellin_eq_towerResolvent`).
2. `‖t(x)‖ ≤ C x^s` on `x ≥ 1`: `M` is analytic on `Re w > s` (Mathlib's
   `mellin_differentiableAt_of_isBigO_rpow`) (`analyticAt_flowMellin`).
3. Mode `ρ_j`, `Re ρ_j > s`: isolated with gap `δ ≤ 1`; choose `ε ∈ (0, δ)` different from the
   finitely many `Im ρ_i − Im ρ_j` with `‖ρ_i‖` bounded by a constant covering the path; the path
   `ρ_j → ρ_j + iε → A + 1 + i(Im ρ_j + ε)` meets no mode, and a locally finite set of modes is
   closed. P17 step 4 with `Ψ = M` (`merged_eq_zero_of_continuation`) gives weight zero
   (`mergedWeight_eq_zero_of_flow_bound`). Converse by the merged module (`flow_bound_iff`).
Zero motive with lag weights: locally finite (`RHTower.finite_xiZeroCopy_band`), positive real
parts (`zeroMotive_flow_bound_iff`). Sharp: the Wolff module is not locally finite and has trace `1`
on the flow.

### P20. No family of zeros is integral, whatever their real parts
Module with finitely many modes in every disc, `0 < Re ρ_i ≤ 1`, `Σ‖b_i‖(1+‖ρ_i‖)² < ∞`, `t(n) ∈ ℤ`
for large `n`.
1. `Δ²t(n) → 0` (weights `≤ 1 < 2`), integers: `t(n) = c₀ + c₁n` for `n ≥ n₀` (P1 steps 1–3).
2. `v_q(x) = t(qx) − q t(x)` is the trace of the module `(b_i(q^{ρ_i} − q), ρ_i)`
   (`frobTrace_dilate_sub`); at integers `v_q(n) = c₀(1 − q)`.
3. `t' ` is the trace of `(b_iρ_i, ρ_i − 1)`, with weights `≤ 0`, so `‖t(y) − t(a)‖ ≤ K(y − a)` for
   `1 < a ≤ y` (`norm_frobTrace_sub_le`). With `n = ⌊x⌋`:
   `v_q(x) = [t(qx) − t(qn)] − q[t(x) − t(n)] + c₀(1 − q)` is bounded on the flow.
4. P19: the module of step 2 carries no weight at a mode with `Re > 0`:
   `(q^{ρ_j} − q)·m_j = 0` for `q = 2, 3`; `m_j ≠ 0` forces `2^{ρ_j} = 2`, `3^{ρ_j} = 3`, so `ρ_j = 1`
   (`mergedWeight_eq_zero_of_integral_locallyFinite`).
Distinct zeros of `ξ` are locally finite, lie in `0 < Re < 1`, and `1` is no zero
(`eq_zero_of_integral_trace_of_distinct_xi_zeros`).

### P21. Index zero: the half-shift family
`E(s) = G(s + ½)`, `E'(s) = G(s − ½)`: `E ≠ 0` and `‖E'‖ ≤ ‖E‖` right of the line when `G ≠ 0` and
`‖G(w − 1)‖ ≤ ‖G(w)‖` on `Re w > 1`. P7 with `κ = 0`: `E − cE'` has no zero right of the line unless
it vanishes identically there (`hermiteBiehler_indexZero`, `halfShift_ne_zero`). For `G = ξ`: if
`ξ(s + ½) = c ξ(s − ½)` right of the line, a zero `ρ` gives `ξ(ρ + 1) = 0`; so the sum is not
identically zero; `F(1 − s) = −cF(s)` for `c = ±1` reflects the left half-plane
(`re_eq_half_of_xi_halfShift_eq_zero`, Taylor's theorem).

### P22. The zeros contain no class of one Frobenius
Let `0 < Re s < 1`, `P > 0`, `K_s(x) = {e^x} e^{−sx}` on `x ≥ 0`, so `∫_0^∞ K_s = 1/(s−1) − ζ(s)/s`
(`RHTower.integral_Ioi_zero_fract_exp`).
1. *Periodization.* `H(y) = Σ_{k≥0} K_s(y + kP)` converges with `‖K_s(y + kP)‖ ≤ e^{−kP·Re s}` for
   `y ≥ 0`. Unfolding: `∫_0^P H = Σ_k ∫_{kP}^{(k+1)P} K_s = ∫_0^∞ K_s` (`integral_ladderSum`). With
   `ω_n = 2πn/P` the character `e^{−iω_n y}` is constant along the translates, so
   `H(y) e^{−iω_n y}` is the periodization of `K_{s_n}`, `s_n = s + iω_n` (`ladderSum_add_mul_I`).
2. *Polar part.* `E = e^{(1−s)P} ≠ 1` and `∫_0^P e^{(1−s)y} e^{−iω_n y}/(E − 1) dy = 1/(1 − s_n)`
   (`integral_polar_mul_exp`). Hence `G = H + e^{(1−s)y}/(E − 1)` has
   `∫_0^P G e^{−iω_n y} = −ζ(s_n)/s_n` for every `n ∈ ℤ` (`integral_ladderDefect_mul_exp`,
   `fourierCoeffOn_ladderDefect`).
3. *Limits.* `K_s` is right-continuous with left limit `K_s^-(x) = (e^x − ⌈e^x⌉ + 1)e^{−sx}`. By
   dominated convergence `G(0^+) = Σ_k K_s(kP) + 1/(E−1)` and
   `G(P^-) = Σ_k K_s^-((k+1)P) + E/(E−1)`. Since `K_s(0) = 0` and
   `K_s(kP) − K_s^-(kP) = −J_k e^{−skP}` with `J_k = 1` if `e^{kP} ∈ ℤ` and `0` otherwise,
   `G(0^+) − G(P^-) = −Σ_{k≥0} J_k e^{−skP}` (`ladderDefect_limits_sub`).
4. *The jump is not zero.* `{k : e^{kP} ∈ ℕ} = k₀ℕ` or `{0}` (`RHTower.dvd_of_mem_expNatSet`), so the
   series is `1/(1 − e^{−sk₀P})` or `1` (`tsum_jumpTerm_ne_zero`).
5. *No jump with summable coefficients.* If `f ∈ L²(a, b]` has `Σ_n ‖c_n(f)‖ < ∞`, the series
   `Σ c_n e_n` converges uniformly to a continuous periodic `g`; in `L²` both `f` and `g` are the
   sum of the Fourier series, so `f = g` almost everywhere, and one-sided limits of `f` at `a` and
   `b` are `g(a) = g(b)` (`endpoint_limits_eq_of_summable_fourierCoeffOn`).
6. With `P = 2π/T`: `Σ_n ‖ζ(ρ + inT)/(ρ + inT)‖ < ∞` contradicts 3–5
   (`not_summable_norm_riemannZeta_div`). So every vertical progression in the strip has infinitely
   many points that are not zeros (`exists_riemannZeta_ne_zero_progression`); none consists of
   zeros of `ξ` (`not_forall_xi_progression`); for `q > 1` the class `{ρ' : q^{ρ'} = q^ρ}` is not
   contained in the zero set (`exists_conjugate_not_zero`); `ξ` vanishes on the zero set of no
   `q^{−s} − u`, `u ≠ 0` (`exists_zero_localFactor_not_zero`), of no polynomial in `q^{−s}` with a
   nonzero root, and on the zeros of no eigenvalue of a curve datum
   (`exists_curve_zero_not_zero`). The hypothesis of
   `RHTower.periodicityDichotomy_zeta_iff_riemannHypothesis` is discharged.

### P23. No sequence of zeros approaches a class of one Frobenius
Notation of P22; `s_n = s + 2πin/P`.
1. *Bessel.* For measurable `K` on the half-line with `‖K(y + kP)‖ ≤ u_k` on `(0, P]`, `Σu_k < ∞`,
   the samples `∫_0^∞ K(x) e^{−2πinx/P} dx` are the Fourier coefficients of `Σ_k K(y + kP)` times
   `P` (P22.1), so they are square summable (`summable_sq_norm_integral_mul_exp`). Hence
   `a_n = ∫K_{s_n}` and `b_n = ∫xK_{s_n}` are in `ℓ²`, the latter with `‖xK_s(x)‖ ≤ (2/σ)e^{−σx/2}`
   (`summable_sq_norm_integral_ladderKernel`, `summable_sq_norm_integral_ladderMoment`). Parseval
   for `G` of P22.2 gives `Σ‖ζ(s_n)/s_n‖² < ∞` (`summable_sq_norm_riemannZeta_div`).
2. *Taylor.* For `‖η‖ ≤ σ/2`: `‖e^{−ηx} − 1 + ηx‖ ≤ ‖η‖²x²e^{σx/2}` and `x² ≤ (32/σ²)e^{σx/4}`, so
   `‖∫K_{s+η} − ∫K_s + η∫xK_s‖ ≤ M(σ)‖η‖²` (`norm_integral_ladderKernel_taylor_le`).
3. *A zero near `s_n`.* If `ζ(s_n + η_n) = 0` and `‖η_n‖ ≤ min(σ, 1−σ)/4`, then
   `∫K_{s_n+η_n} = 1/(s_n + η_n − 1)`, `∫K_{s_n} = 1/(s_n − 1) − z_n` with `z_n = ζ(s_n)/s_n`, and
   `z_n = [∫K_{s_n+η_n} − ∫K_{s_n} + η_n b_n] − η_n b_n − [1/(s_n+η_n−1) − 1/(s_n−1)]`. The last
   bracket is `−η_n/((s_n+η_n−1)(s_n−1))` with `‖1/(s_n+η_n−1)‖ ≤ 2/(1−σ)` and
   `‖1/(s_n−1)‖ ≤ ‖a_n‖ + ‖z_n‖`. So
   `‖z_n‖ ≤ M‖η_n‖² + ‖η_n‖‖b_n‖ + (2/(1−σ))‖η_n‖(‖a_n‖ + ‖z_n‖)`.
4. With `η ∈ ℓ²` the right side is summable (products of `ℓ²` sequences), for all but finitely many
   `n`; so `Σ‖z_n‖ < ∞` (`summable_norm_riemannZeta_div_of_ladder`), against P22.6
   (`not_cofinite_riemannZeta_eq_zero_of_sq_summable`, `not_cofinite_xi_eq_zero_near_class`).

### P24. Half of a class of one Frobenius
Let `D` be bounded and measurable on the period `P = 2π/d`, with coefficients
`c_m = ∫_0^P D(y) e^{−idmy} dy`, `m ≥ 0`, `A = Σ‖c_m‖ < ∞`, right limit `L_a` at `0` and left limit
`L_b` at `P`.
1. *Conjugate Cauchy pairing.* For `0 ≤ r < 1`, `(1 − re^{−idy})^{−1} = Σ_m r^m e^{−idmy}` uniformly,
   so `∫ D (1 − re^{−idy})^{−1} = Σ_m r^m c_m` and its norm is `≤ A`
   (`norm_integral_mul_conjCauchy_le`).
2. *Poisson bound.* With `k = (1 − re^{idy})^{−1}`: `k + k̄ = 1 + p`, `p ≥ 0` the Poisson kernel of
   mass `P`, and `k − k̄ = 2i Im k`. So `2i∫D·Im k = ∫D p + ∫D − 2∫D k̄`, of norm `≤ MP + 3A`
   (`norm_integral_mul_kernelIm_le`).
3. *Folding.* `Im k(P − y) = −Im k(y)`, so `∫_0^P D·Im k = ∫_0^{P/2} (D(y) − D(P − y)) Im k(y) dy`
   (`integral_mul_kernelIm_fold`).
4. *Jump.* `Im k ≥ 0` on `(0, P/2]` with `∫_0^{P/2} Im k = d^{−1} log((1+r)/(1−r))`, and
   `Im k ≤ 1/(1 − cos²(dδ))` on `(δ, P/2]`. If `‖D(y) − D(P − y) − J‖ ≤ ‖J‖/2` on `(0, δ]`, then
   `(‖J‖/2)·d^{−1} log((1+r)/(1−r)) ≤ (MP + 3A)/2 + (2M + ‖J‖)(P/2)/(1 − cos²(dδ))`
   (`half_norm_mul_integral_kernel_le`, `jump_mul_log_le`). The right side does not depend on `r`,
   so `J = L_a − L_b = 0` (`endpoint_limits_eq_of_summable_halfCoeff`).
5. With `D = G` of P22 and `d = T`: `c_m = −ζ(s_m)/s_m` (`halfCoeff_ladderDefect`), so
   `Σ_{n≥0} ‖ζ(ρ + inT)/(ρ + inT)‖ = ∞` (`not_summable_nat_norm_riemannZeta_div`); the lower half by
   `ζ(s̄) = \overline{ζ(s)}`; the `ℓ²` ladder by P23.3 on the index set `ℕ`
   (`not_eventually_riemannZeta_eq_zero_near_halfClass`).

### P25. A factor with a Dirichlet series is pure
Let `F` be holomorphic and bounded on `Re s > x`, equal to an absolutely convergent Dirichlet
series on `Re s > u₀`, not identically zero, `F(ρ₀) = 0`, `Re ρ₀ > x`.
1. *Recurrence.* `ρ₀` is isolated; on a circle of radius `ρ` about it `‖F‖ ≥ m > 0`. `F` is almost
   periodic on a closed strip containing the disc
   (`GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries`): every interval of length `L`
   contains `τ` with `‖F(z + iτ) − F(z)‖ ≤ m/3` on the disc. Then `‖F(ρ₀ + iτ)‖ ≤ m/3 < 2m/3 ≤
   ‖F(z + iτ)‖` on the circle, so `F(· + iτ)` has a zero in the disc
   (`RHTower.DeBruijn.exists_zero_of_norm_lt_sphere_on`), and every `t` with `|t − τ| < ρ` carries
   a zero into the disc of radius `2ρ` about `ρ₀ + it` (`exists_thick_zero_shifts`).
2. *Density.* For `½ < Re ρ₀ < 1` and small `r` the shifts carrying a zero of `ζ` into the disc of
   radius `r` about `ρ₀ + iτ` have density zero (`RHTower.zetaZeroShiftSet_density_zero`). For
   `0 < Re ρ₀ < ½` the map `s ↦ 1 − s̄` sends zeros in the strip to zeros and the disc about `ρ₀`
   to the disc about `1 − ρ̄₀`, with the same shifts (`zetaZeroShiftSet_subset_reflect`,
   `exists_zetaZeroShiftSet_density_zero`).
3. If every zero of `F` in `Re s > x` were a zero of `ξ` and `Re ρ₀ ≠ ½`, then `0 < Re ρ₀ < 1`, the
   thick relatively dense set of 1 would lie in the zero shifts of `ζ`, of positive lower density
   (`RHTower.eventually_le_volume_of_relativelyDense`), against 2
   (`exists_zero_not_xi_zero_of_re_ne_half`, `re_eq_half_of_zeros_subset_xi`).
4. A Dirichlet polynomial is entire, bounded on every half-plane `Re s > x`, and not identically
   zero there; so a Dirichlet polynomial whose zeros are zeros of `ξ` has them on the critical line
   (`re_eq_half_of_dirichletPolynomial_zeros_subset_xi`).

### P26. A Dirichlet polynomial with a functional equation is not a factor
`D(s) = Σ a_n n^{−s}` with real coefficients, `a_1 ≠ 0`, and `‖D(1 − s)‖ = N^{Re s − ½}‖D(s)‖`, `N > 1`.
Suppose every zero of `D` is a zero of `ξ`.
1. By P25 all zeros lie on `Re s = ½`; `D` is zero-free right of the line.
2. *Bounded below.* On `Re s ≥ C₀` the constant term dominates. If `inf_{Re s ≥ σ}‖D‖ = 0` for some
   `σ > ½`, take `s_k` with `D(s_k) → 0`; the twists `(n^{−i Im s_k})_n` and `Re s_k` have a
   convergent subsequence; the twisted polynomials `D(· + i Im s_k)` converge locally uniformly to
   a Dirichlet polynomial `D_∞ ≢ 0` with a zero of real part `≥ σ`; by Hurwitz `D` has zeros right
   of the line.
3. *Monotone modulus.* `W(s) = N^{s/2}D(s)` has `‖W(1 − s̄)‖ = ‖W(s)‖`. For `δ > 0`,
   `W(s − δ)/W(s)` is bounded on `Re s ≥ ½ + δ/2` (step 2) and of modulus one on its boundary;
   Phragmén–Lindelöf gives `‖W(s − δ)‖ ≤ ‖W(s)‖`, hence `Re(W'/W) ≥ 0` on `Re s > ½`.
4. *Boundary.* `σ ↦ ‖W(σ + it)‖²` is even about `½`, so `Re(W'/W)(½ + it) = 0` where `D ≠ 0`.
5. *Dirichlet series.* By step 2 and the half-plane Wiener lemma
   (`ArithmeticOrientationTheory.WienerAlgebraAt.isUnit_of_le_norm_lSeries`) `1/D` has an
   absolutely convergent Dirichlet series at `3/2`; so `Φ = W'/W = ½ log N + D'/D` has one, with
   real coefficients and constant term `½ log N`.
6. `RHTower.AtomDomination.eq_zero_of_herglotz_dirichlet_criticalCarrier` gives `½ log N = 0`
   (`exists_zero_not_xi_zero_of_functionalEquation`).
7. *Complex coefficients*, with `‖D(1 − s̄)‖ = N^{Re s − ½}‖D(s)‖`: `E(s) = D(s)·conj D(s̄)` has the
   coefficients `a ⋆ ā`, which are real, the constant term `‖a_1‖²` and the functional equation with
   `N²`; a zero of `E` that is not a zero of `ξ` is a zero of `D` or the conjugate of one
   (`exists_zero_not_xi_zero_of_functionalEquation_complex`).

### P27. Zeros on the line force the functional equation; no factor with a constant term
`D(s) = Σ a_n n^{−s}`, `a_1 ≠ 0`, `a_{n₀} ≠ 0` for some `n₀ ≥ 2`, all zeros on `Re s = ½`.
1. *Reflection.* `D^♯(s) = conj D(1 − s̄) = Σ ā_n n^{−(1−s)}` is entire, and `ρ = 1 − ρ̄` on the line,
   so `D^♯` vanishes at each zero `ρ` of `D` to the same order: `D^♯/D` has a finite nonzero limit
   at `ρ` (`tendsto_reflPoly_div`). Through the meromorphic normal form the quotient is an entire
   function `g` without zeros, `g D = D^♯` (`exists_entire_quotient`).
2. *Strips.* Take a height `T₀` with `D(½ + iT₀) ≠ 0`; `D` has no zero on the horizontal line at
   height `T₀`, so `‖D‖ ≥ μ > 0` on its segment across a strip `x₁ ≤ Re s ≤ x₂`. `D` is almost
   periodic: the almost periods `τ` with `‖D(s + iτ) − D(s)‖ ≤ μ/2` on the strip are relatively
   dense, so every interval of a fixed length contains a height at which `‖D‖ ≥ μ/2` across the
   strip. On the rectangle between two such heights the maximum principle bounds `g` by its values
   on the boundary: the two horizontal sides, where `D` is bounded below and `D^♯` above, and the
   two vertical sides, where `g` is bounded by hypothesis (`exists_bound_on_strip`).
3. *Far left and right.* For `Re s ≥ C₀`, `‖D(s)‖ ≥ ‖a_1‖/2`; for `Re s ≤ −C₁` the top term
   dominates, `‖D(s)‖ ≥ ½‖a_{N_t}‖ N_t^{−Re s}` (`exists_left_bound`). So `‖g(s)‖ ≤ A e^{B‖s‖}`.
4. A zero-free entire function of exponential type is `e^{αs+β}`
   (`RHTower.exists_eq_exp_affine_of_ne_zero`). `‖g‖ = 1` on the line gives `Im α = 0` and
   `‖g(s)‖ = e^{α(Re s − ½)}`; the growth of `D` to the left gives `α > 0`. With `N = e^α`:
   `‖D(1 − s̄)‖ = N^{Re s − ½}‖D(s)‖` (`exists_functionalEquation_of_zeros_on_line`).
5. If every zero of `D` were a zero of `ξ`, P25 puts the zeros on the line, step 4 gives the
   functional equation and P26 a contradiction (`exists_zero_not_xi_zero_of_constantTerm`).
6. *Lowest frequency dividing the others.* If `m ∣ n` on the support, `D(s) = m^{−s} D₁(s)` with
   `D₁(s) = Σ a_{mk} k^{−s}`, which has a constant term and the zeros of `D`
   (`exists_zero_not_xi_zero_of_dvd`).

### P28. Polynomials in one base
If `n = m β^{k_n}` on the support, `β > 1`, then `n^{−s} = m^{−s}(β^{−s})^{k_n}` and
`D(s) = m^{−s} Q(β^{−s})`, `Q = Σ a_n X^{k_n}`. The `k_n` are distinct, so `Q` has two nonzero
coefficients; writing `Q = X^d R`, `R(0) ≠ 0`, `R` is not constant and has a root `u ≠ 0`
(`exists_ne_zero_root`). The zeros of `D` contain the class `β^{−s} = u`, which by P22 is not
contained in the zeros of `ξ` (`exists_zero_not_xi_zero_of_oneBase`). Two terms `n₁ < n₂` are the
case `m = n₁`, `β = n₂/n₁` (`exists_zero_not_xi_zero_of_two_terms`).

### P29. On the flow the trace determines the module; the two involutions
Modules with `Σ‖b_i‖ < ∞`, finitely many modes in every disc.
1. *Merged weights.* For `g : ℂ → ℂ` with `Σ b_i g(ρ_i)` summable, summation along the fibres of
   `i ↦ ρ_i` gives `Σ_i b_i g(ρ_i) = Σ_{w ∈ ℂ} m(w) g(w)`, `m(w) = Σ_{ρ_i = w} b_i`
   (`hasSum_mergedWeight_mul`).
2. *Uniqueness.* If two modules with weights bounded above have the same trace on `x ≥ 1`, the
   module on `ι ⊕ κ` with weights `(b, −c)` has trace `0` there; it is locally finite, and by P19
   with the bound `0 · x^s`, `s < Re w`, its merged weight at every one of its modes vanishes. That
   weight is `m_b(w) − m_c(w)` (`mergedWeight_eq_of_frobTrace_eq_on_flow`).
3. *Central normalization.* For modes in a strip, `φ(u) = Σ b_i e^{u(ρ_i − ½)}` converges for all
   real `u`, `t(e^u) = e^{u/2} φ(u)` (`frobTrace_exp`), the module `(b, 1 − ρ)` has trace `φ(−u)`
   and merged weights `m(1 − w)`, the module `(b̄, ρ̄)` has trace `conj φ(u)` and merged weights
   `conj m(w̄)`.
4. By 1 and 2: `φ(−u) = φ(u)` for all `u` iff `m(1 − w) = m(w)` for all `w`
   (`centralTrace_neg_iff`); `conj φ = φ` iff `conj m(w̄) = m(w)` (`conj_centralTrace_iff`).

### P30. Castelnuovo–Severi on the flow is purity and effectivity
Module in a strip `a ≤ Re ρ_i ≤ A`, `Σ‖b_i‖ < ∞`, locally finite; `φ` as in P29.
1. *Defect.* With `Γ_u · Γ_v = e^v(1 + e^{u−v} − t(e^{u−v})) = e^u + e^v − e^{(u+v)/2}φ(u − v)` and
   `D = Σ c_k Γ_{t_k}`, `d₁ = Σ c_k`, `d₂ = Σ c_k e^{t_k}`:
   `d̄₁d₂ + d̄₂d₁ − Σ c̄_i c_j Γ_{t_j}·Γ_{t_i} = Σ conj(c_i e^{t_i/2}) φ(t_j − t_i) c_j e^{t_j/2}`
   (`castelnuovoSeveri_defect`). So the inequality for all divisors is positive definiteness of
   `φ` (`castelnuovoSeveri_iff_positiveDefinite`). The pairing is symmetric iff `φ` is even iff
   the module is self-dual (`graphPairing_comm_iff`).
2. *Form on a pure module.* If `m(w) ≠ 0 ⇒ Re w = ½`, then `conj(w − ½) = −(w − ½)` on the visible
   modes and by P29.1 `Σ c̄_i φ(t_j − t_i) c_j = Σ_w m(w) ‖Σ_j c_j e^{t_j(w − ½)}‖²`
   (`hasSum_quadraticForm`). With `m ≥ 0` the form is `≥ 0`.
3. *Positivity gives purity.* `‖φ(u)‖ ≤ φ(0)`, so `‖t(x)‖ ≤ φ(0) x^{1/2}` on `x ≥ 1`; by P19 no
   visible mode has `Re w > ½`. The dual module has trace `φ(−u)`, with the same bound: no visible
   mode has `Re w < ½` (`re_eq_half_of_positiveDefinite`).
4. *Positivity gives effectivity.* Fix `w₀` on the line, `h > 0`. With `t_k = kh`,
   `c_k = e^{−kh(w₀−½)}/(N+1)`, `0 ≤ k ≤ N`, step 2 gives the nonnegative real
   `Σ_w m(w) ‖(N+1)^{−1} Σ_{k ≤ N} z_w^k‖²`, `z_w = e^{h(w − w₀)}`, `‖z_w‖ = 1` on the visible modes.
   As `N → ∞` (dominated by `‖m(w)‖`, summable) it tends to `A(h) = Σ_{z_w = 1} m(w)`. For
   `h = 1/(n+1) → 0`, `z_w = 1` with `w ≠ w₀` forces `‖w − w₀‖ ≥ 2π/h`, so `A(h) → m(w₀)` by
   dominated convergence. A limit of nonnegative reals is one (`effective_of_positiveDefinite`).
5. `positiveDefinite_centralTrace_iff`, `castelnuovoSeveri_iff`.
6. *Zero motive.* Lag weights `1/(ρ(1−ρ))`: summable, modes in `0 < Re < 1`, locally finite. Every
   zero is visible (positive real parts do not cancel), so purity is RH; under RH
   `ρ(1 − ρ) = ‖ρ‖²` and the weights are positive (`zeroMotive_castelnuovoSeveri_iff`).

### P31. No Dirichlet polynomial is a factor of `ξ`
Every Dirichlet polynomial with at least two terms has a zero that is not a zero of `ξ`
(`exists_zero_not_xi_zero`). Proof on its own card:
`irp-no-dirichlet-polynomial-is-a-factor-of-xi.md` (K: the constant terms on the two sides of the
line agree, by the jumps of the fractional part and Möbius inversion; A: a zero-free exponential
polynomial is bounded below; B: its logarithmic derivative expands absolutely up to the zeros;
C: the constant terms of `D'/D` are `−log` of the lowest and of the highest frequency).

## Modules
| Module | Content |
|---|---|
| ADefectOfIndexOneIsPureOffTheRealAxis | `rightHalf`, `defectFactor`; `eqOn_of_two_agreements`, `agreement_subsingleton`, `im_eq_zero_of_agreement`, `hermiteBiehler_indexOne` |
| TheEisensteinConstantTermIsPureByParity | `constantTerm`; `constantTerm_indexOne`, `im_eq_zero_of_constantTerm_eq_zero`, `lineLaw`, `lineLaw_gammaZeta` |
| TheIndexBoundIsAttained | `exists_unique_exceptionalParameter`, `exceptionalParameter_mem`, `exceptionalParameter_mono`, `indexTwo_admits_nonreal_pair` |
| CesaroMeansReadTheModesOfASummableTower | `towerSum`; `tendsto_cesaro_towerSum`, `merged_eq_zero_of_tendsto_zero`, `exists_almostPeriod` |
| CesaroMeansOnThickSets | `windowMean`; `norm_windowMean_sub_le`, `merged_eq_zero_of_small_on_runs` |
| BoundedIntegralTracesOfOneFrobeniusAreTorsion | `kronecker_oneFrobenius`, `inner_weight_eq_zero`, `kronecker_oneFrobenius_injective` |
| AtPositiveWeightIntegralityDoesNotBoundTheRank | `lpMode`, `lpWeight`; `exists_pure_integral_tower_of_infinite_rank` |
| TwoFrobeniiDetermineATraceClassModule | `frobTrace`, `WeightsWellFounded`; `cpow_two_three_injective`, `re_le_of_frobTrace_bound`, `frobTrace_bound_iff` |
| IntegralTraceClassModulesOverTheIntegersAreTate | `tate_of_integral_trace`, `tate_of_trace_in_zmultiples`, `tate_of_integral_trace_dual`, `not_visible_in_open_strip` |
| NoTraceClassFamilyOfZerosIsIntegral | `eq_zero_of_integral_trace_of_xi_zeros` and its finite and one-line forms |
| TheSymmetriesOfTheZerosAreTheTwoInvolutions | `PreservesXiDivisor`; `preservesXiDivisor_affine_iff`, `preservesXiDivisor_antiaffine_iff` |
| EliminationNeedsOnlyAnAttainedTop | `norm_le_one_of_thick_bounded_levelSums`, `curveDatum_unitary_of_thick_bounded_trace`, `lag_bound_iff_of_attainedTop`, `riemannHypothesis_iff_attainedTop_and_thick_lag_bounded` |
| TheIndexIsSemicontinuous | `zeros_subsingleton_of_tendstoLocallyUniformly`, `encard_zeros_le_of_tendstoLocallyUniformly`, `encard_xi_zeros_le_of_limit`, `riemannHypothesis_iff_limit_of_indexOne` |
| OverTheIntegersEveryModeIsItsOwnConjugacyClass | `frobAct`; `cpow_eq_of_commute`, `re_eq_of_commute`, `eq_of_commute_two_three`, `eq_conj_of_semilinear_commute`, `single_mem_of_stable` |
| KroneckerOverTheIntegersNeedsNoDistinctModes | `mergedWeight_eq_zero_of_integral_trace`, `mergedWeight_dual_of_integral_trace`, `frobTrace_bound_iff_mergedWeight_at` |
| WithoutTheChainConditionKroneckerOverTheIntegersFails | `frobTrace_eq_tsum_of_powerSums_zero`, `frobTrace_wolff`, `exists_integral_traceClass_module_not_tate`, `wolff_not_weightsWellFounded` |
| AModeAccessibleFromInfinityIsEliminated | `towerResolvent`, `levelSeries`; `towerResolvent_eq_levelSeries`, `analyticAt_levelSeries`, `analyticAt_towerResolvent`, `merged_eq_zero_of_continuation`, `merged_eq_zero_of_accessible`, `merged_eq_zero_of_radially_visible`, `wolff_node_not_accessible`, `lag_not_small_of_accessible`, `riemannHypothesis_of_lag_bounded_of_accessible` |
| OnTheFlowTheWeightFiltrationNeedsNoChainCondition | `flowTrace`, `flowMellin`, `flowPath`; `analyticAt_flowMellin`, `flowMellin_eq_towerResolvent`, `mergedWeight_eq_zero_of_flow_bound`, `flow_bound_iff`, `zeroMotive_flow_bound_iff` |
| TheZerosContainNoClassOfOneFrobenius | `ladderKernel`, `ladderSum`, `ladderDefect`, `jumpTerm`; `endpoint_limits_eq_of_summable_fourierCoeffOn`, `integral_ladderSum`, `fourierCoeffOn_ladderDefect`, `tsum_jumpTerm_ne_zero`, `ladderDefect_limits_sub`, `not_summable_norm_riemannZeta_div`, `exists_riemannZeta_ne_zero_progression`, `not_forall_xi_progression`, `exists_conjugate_not_zero`, `exists_zero_localFactor_not_zero`, `exists_zero_polynomial_not_zero`, `exists_curve_zero_not_zero`, `aperiodicZeroAt_riemannZeta`, `periodicityDichotomy_zeta_iff_riemannHypothesis` |
| NoSequenceOfZerosApproachesAClassOfOneFrobenius | `ladderMoment`, `taylorConstant`; `integral_tsum_translates_mul_exp`, `summable_sq_norm_integral_mul_exp`, `summable_sq_norm_riemannZeta_div`, `norm_integral_ladderKernel_taylor_le`, `summable_norm_riemannZeta_div_of_ladder`, `not_cofinite_riemannZeta_eq_zero_of_sq_summable`, `not_cofinite_xi_eq_zero_near_class` |
| HalfOfAClassOfOneFrobeniusIsNotInTheZeroSet | `halfCoeff`; `norm_integral_mul_conjCauchy_le`, `norm_integral_mul_kernelIm_le`, `integral_mul_kernelIm_fold`, `half_norm_mul_integral_kernel_le`, `jump_mul_log_le`, `endpoint_limits_eq_of_summable_halfCoeff`, `halfCoeff_ladderDefect`, `not_summable_nat_norm_riemannZeta_div`, `exists_nat_riemannZeta_ne_zero_progression`, `exists_nat_riemannZeta_ne_zero_progression_down`, `not_eventually_riemannZeta_eq_zero_near_halfClass`, `exists_nat_conjugate_not_zero` |
| AFactorWithADirichletSeriesIsPure | `exists_thick_zero_shifts`, `riemannZeta_one_sub_conj_eq_zero`, `zetaZeroShiftSet_subset_reflect`, `exists_zetaZeroShiftSet_density_zero`, `exists_zero_not_xi_zero_of_re_ne_half`, `re_eq_half_of_zeros_subset_xi`, `norm_finiteDirichletPolynomial_le`, `exists_zero_dirichletPolynomial_not_xi_zero`, `re_eq_half_of_dirichletPolynomial_zeros_subset_xi` |
| AZeroFreeDirichletPolynomialIsBoundedBelow | `twistPoly`, `vtwist`; `finiteDirichletPolynomial_add_mul_I`, `exists_far_bound`, `tendstoLocallyUniformly_twistPoly`, `exists_le_norm_of_zeroFree` |
| ADirichletPolynomialWithAFunctionalEquationIsNotAFactor | `dirDeriv`, `dirW`, `dirPhi`; `norm_dirW_one_sub_conj`, `norm_dirW_sub_le`, `re_dirPhi_nonneg`, `re_dirPhi_eq_zero`, `exists_real_coeff_dirPhi`, `exists_zero_not_xi_zero_of_functionalEquation`, `exists_zero_not_xi_zero_of_functionalEquation_complex` |
| NoFamilyOfZerosIsIntegralWhateverTheirRealParts | `norm_frobTrace_sub_le`, `frobTrace_dilate_sub`, `mergedWeight_eq_zero_of_integral_locallyFinite`, `eq_zero_of_integral_trace_of_distinct_xi_zeros` |
| AFamilySeesItsMeanAndItsMembersOfPositiveMass | `norm_le_of_amortized_levelSums`, `member_norm_le_of_family_moments`, `integral_norm_sq_fixedPart_add`, `fixedPart_norm_le_one_of_mean_bounded`, `fixedPart_norm_le_one_of_excess_bounded` |
| ASchurFunctionReducesAtEveryNode | `mobius`; `norm_le_norm_defectFactor`, `exists_quotient_by_defectFactor`, `exists_schur_reduction`, `mobius_injOn` |
| ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints | `pstar`, `IsBlaschke`; `IsBlaschke.reduce`, `eqOn_of_card_agreements`, `encard_agreements_le`, `isBlaschke_prod`, `hermiteBiehler_index`, `hermiteBiehler_index_general`, `pencil_index_general`, `hermiteBiehler_indexZero`, `halfShift_ne_zero`, `re_eq_half_of_xi_halfShift_eq_zero`, `two_mul_encard_upper_zeros_le`, `index_attained` |
| TheExceptionalParameterIsBornAtFourPiExpMinusGamma | `threshold`, `defect`; `hasDerivAt_xiReal_one`, `hasDerivAt_defect_half`, `exists_exceptionalParameter_iff`, `re_eq_half_of_constantTerm_eq_zero` |
| TheLineLawSeesTheStripAndNotTheLine | `pencil`, `divisorPoly`, `symmetrize`; `pencil_indexOne`, `pencil_lineLaw`, `exists_fixedPart_with_lineLaw`, `pencil_lineLaw_of_tendsto`, `xi_mem_pencil_class`, `exists_nonreal_zero_pencil_of_zero_right`, `divisorPencil_lineLaw_iff` |
| TheLefschetzNumbersOfTheIntegersAreNotTraces | `TraceClassAt`, `IsTrace`; `tendsto_fwdDiff_iter_frobTrace_of_traceClassAt`, `tate_of_integral_trace_at`, `not_isTrace_of_primePower_support`, `not_isTrace_vonMangoldt`, `not_isTrace_of_two_jumps`, `not_isTrace_mertens`, `not_isTrace_primeCounting`, `lagModule_not_traceClassAt_one` |
| TheArchimedeanFibreIsATraceAndTheFiniteContactsAreNot | `mergedWeight`, `evenJet`; `mergedWeight_eq_zero_of_frobTrace_bound_at`, `mergedWeight_eq_of_frobTrace_eventually_eq`, `archimedeanFibre_forced`, `not_isTrace_gluedLefschetz`, `not_isTrace_pointCount` |
| ADirichletPolynomialWithItsZerosOnTheLineHasAFunctionalEquation | `reflPoly`; `tendsto_reflPoly_div`, `exists_entire_quotient`, `exists_bound_on_strip`, `exists_functionalEquation_of_zeros_on_line`, `exists_zero_not_xi_zero_of_constantTerm`, `exists_zero_not_xi_zero_of_dvd`, `exists_ne_zero_root`, `exists_zero_not_xi_zero_of_oneBase`, `exists_zero_not_xi_zero_of_two_terms` |
| OnTheFlowCastelnuovoSeveriIsPurityAndEffectivity | `centralTrace`, `graphPairing`; `hasSum_mergedWeight_mul`, `mergedWeight_eq_of_frobTrace_eq_on_flow`, `centralTrace_neg_iff`, `conj_centralTrace_iff`, `hasSum_quadraticForm`, `re_eq_half_of_positiveDefinite`, `effective_of_positiveDefinite`, `positiveDefinite_centralTrace_iff`, `graphPairing_comm_iff`, `castelnuovoSeveri_defect`, `castelnuovoSeveri_iff`, `zeroMotive_castelnuovoSeveri_iff` |
| TheConstantTermsOnTheTwoSidesOfTheLineAgree | `fractSeries`; `mellin_fractSeries`, `fractSeries_eq`, `tsum_jump_eq`, `tsum_eq_of_tsum_dvd`, `constantTerms_agree`, `tsum_scale_eq_zero`, `tsum_left_eq_const`, `eq_const_mul_riemannZeta_div`, `exists_differentiableOn_deriv_mul_div`, `norm_le_of_good_heights` |
| TheInverseOfAnExponentialPolynomialExpandsWhereItIsBoundedBelow | `expPoly`, `Word`, `wordMass`, `freqMonoid`, `LogIndex`; `hasSum_inv_expPoly_words`, `norm_wordMass_le`, `summable_exp_neg_freqMonoid`, `hasSum_inv_expPoly`, `hasSum_logWeight`, `sum_exp_eq_expPoly` |
| AZeroFreeExponentialPolynomialIsBoundedBelow | `exists_le_norm_expPoly_of_zeroFree`, `hasSum_logWeight_of_zeroFree` |
| NoDirichletPolynomialIsAFactorOfXi | `exists_zero_not_xi_zero` |

## Reductions (README §12)
Purity over `ℤ` is reduced to one of: an index bound of one for `ξ`; a crude count on a thick set of
levels of one tower together with an attained abscissa; a crude count on all levels of one tower
together with one off-line zero whose mode is accessible from infinity; the sign of the pairing of
the Frobenius graphs on the flow (Castelnuovo–Severi, which for the zero motive is RH). Integrality forces Tate twists in trace
class at any Frobenius, and the zero motive has order exactly zero, so it cannot act on the zero
motive; no rigid transport exists and every equivariant map of the module over `ℤ` is diagonal; a
family reads only the closed strip of its fixed part, and under a measure its moments contain the
fixed part with mass one.

## Log
- 2026-11-09 — created
- 2026-11-10 — 13 modules formalized; card to 3-formalized
- 2026-11-10 — 19 modules: index law at any index, threshold `4πe^{−γ}`, fixed part, trace class at a Frobenius, glued square
- 2026-11-10 — 22 modules: conjugacy classes and constituents, Kronecker and growth with merged modes at any Frobenius, families under a measure, line law over limits, semicontinuity at any index
- 2026-11-10 — 23 modules: the chain condition is exact (Wolff module)
- 2026-11-10 — 24 modules: elimination of a mode accessible from infinity by the resolvent; the index counts the zeros of the defect right of the line
- 2026-11-10 — 25 modules: on the flow the weight filtration of a locally finite module is its growth filtration
- 2026-11-10 — 26 modules: no family of distinct zeros is integral, without a chain condition; families with any polynomial defect
- 2026-11-10 — index zero: half-shift family, Taylor's theorem
- 2026-11-10 — 27 modules: the zeros contain no class of one Frobenius (divergence along every vertical progression in the strip)
- 2026-11-10 — 28 modules: no two-sided sequence of zeros within `ℓ²` of a class of one Frobenius; Parseval for the zeta values along a progression
- 2026-11-10 — 30 modules: half classes (one-sided divergence and `ℓ²` ladders at every real part); a factor with a Dirichlet series is pure
- 2026-11-10 — 32 modules: a Dirichlet polynomial with a constant term and a functional equation is not a factor of `ξ` (real and complex coefficients)
- 2026-11-10 — 34 modules: zeros on the line force the functional equation of a Dirichlet polynomial, so no Dirichlet polynomial with a constant term and a further term is a factor; lowest frequency dividing the others; one base and two terms; on the flow the trace determines the module, the functional equation is self-duality, Castelnuovo–Severi is purity and effectivity. Open: Dirichlet polynomials in several bases without constant term whose lowest frequency does not divide the others
- 2026-11-10 — 38 modules: no Dirichlet polynomial with two terms is a factor of `ξ`, whatever its support (jump law of the fractional part, Möbius inversion, exponential polynomials with real frequencies); the open case of the previous entry is closed
- 2026-11-10 — rigidity of two-sided expansions: the left expansion is constant and `F = −β ζ(s)/s` on the strip
