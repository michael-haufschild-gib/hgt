# Infinite-Rank Purity Theory (IRP)

Namespace `GaloisForLFunctions.InfiniteRankPurityTheory`; umbrella `InfiniteRankPurityTheory.lean`;
28 modules. Specification: §7 of
[the review-0911 report](../../../docs/reports/review-0911/fable.md).

*Weil numbers without finite rank, without moduli, in law and at a point.*

## 1. Motivation

A Frobenius module of finite rank is pure for reasons that all use the rank: the characteristic
polynomial is rational, its roots are permuted by a Galois group, bounded integer traces are periodic
(Kronecker), the determinant has a weight, the module moves in a family, the intersection form has
one positive square, the Lefschetz numbers are traces. The zero motive of `ζ` is the module
`M = ⊕ ℤ(−ρ)` on which the Frobenius at `n` acts by `n^ρ`, with the pairing `ρ ↔ 1 − ρ` and the
archimedean involution `ρ ↦ ρ̄`. Its rank is infinite and it has no moduli.

IRP asks, for each finite-rank mechanism, what replaces it when the rank is infinite and the object
is rigid, what the replacement costs, and how a statement about the distribution of the eigenvalues
(*in law*) becomes a statement about every eigenvalue (*at a point*). The Riemann hypothesis is the
statement that the two involutions of the zero set coincide: `ι : ρ ↦ 1 − ρ` and `c : ρ ↦ ρ̄`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Summable tower | `towerSum c z ν` | modes `z_i`, weights `c_i` with `Σ‖c_i‖ < ∞`; level sums `S(ν) = Σ c_i z_i^ν`: one Frobenius, any rank |
| Weight at a point | `∑' i, if z i = w then c i else 0`, `mergedWeight c ρ w` | the total weight carried at `w`; modes may repeat |
| Frobenius module over `ℤ` | `frobTrace b ρ x` | modes `ρ_i`, weights `b_i`; the Frobenius at `n` acts by `n^{ρ_i}`; trace `t(n) = Σ b_i n^{ρ_i}` |
| The module itself | `frobAct ρ n` | `⊕_i ℂ(−ρ_i)` as finitely supported vectors; the Frobenius at `n` multiplies the `i`-th line by `n^{ρ_i}` |
| Trace class at a Frobenius | `TraceClassAt q m b ρ` | `Σ ‖b_i‖ q^{Re ρ_i} (1 + ‖ρ_i‖)^m < ∞`; at `q = 1` the weighted rank is finite, at `q ≥ 2` infinitely many modes of weight tending to `−∞` are allowed |
| Trace | `IsTrace m f` | `f` is at all large integers the trace of a module of trace class of order `m` at some Frobenius, with weights below `m` |
| Weights without ascending chain | `WeightsWellFounded ρ` | every nonempty set of weights `Re ρ_i` has a greatest element |
| Tate polynomial, dilation operator | `tatePoly p m`, `tateDilation p m` | `Π_{k<m}(X − p^k)`; `Π_{k<m}(S_p − p^k)`, `S_p f(x) = f(px)` |
| Archimedean fibre | `evenJet k` | the modes `0, −2, −4, …`, each of weight one; trace `n²/(n² − 1)` |
| Half-plane, defect factor | `rightHalf`, `defectFactor w`, `defectInv w` | `Re s > ½`; `b_w(s) = (s − w)/(s − 1 + w̄)`, a conformal map onto the disc |
| Disc automorphism | `mobius v` | `M_v(z) = (z − v)/(1 − v̄ z)` |
| Reflected polynomial | `pstar P` | `P^*(s) = conj(P(1 − s̄))` |
| Blaschke product of degree `≤ κ` | `IsBlaschke κ B` | `B = N/(ε N^*)` on the half-plane, `deg N ≤ κ`, `‖ε‖ = 1`, `N^* ≠ 0`, `‖N‖ ≤ ‖N^*‖` |
| Divisor polynomial, reflected divisor | `divisorPoly Z`, `reflectDivisor W`, `symmetrize M` | `Π(s − ρ)`; `{1 − w̄}`; the closure of `M` under `ρ ↦ ρ̄`, `ρ ↦ 1 − ρ̄` |
| Constant term | `constantTerm Y`, `constantTermReal`, `defect Y` | `(s−1) ξ(2s) Y^s + s ξ(2s−1) Y^{1−s}`; its sign on the real axis `x ξ(2x−1) − (1−x) ξ(2x) Y^{2x−1}` |
| Family over a fixed part | `pencil G Y` | `(s−1) G(2s) Y^s + s G(2s−1) Y^{1−s}`; `pencil xi Y = constantTerm Y` |
| Family under a measure | `towerSum c z ν + V ν ω` | level sums `F(ν) + V_ω(ν)` over a probability space, the variable part of mean zero |
| Threshold | `threshold` | `4π e^{−γ}` |
| Window mean | `windowMean c z w N L`, `circleError`, `innerError` | mean of `S(ν) w^{−ν}` over `N < ν ≤ N + L`, with its two error terms |
| Resolvent, Laurent series | `towerResolvent c z w`, `levelSeries c z w` | `Φ(w) = Σ c_i/(w − z_i)`, analytic off the closure of the modes; `Σ_ν S(ν) w^{−ν−1}`, equal to `Φ` outside the modes |
| Trace on the flow, its Mellin transform | `flowTrace b ρ`, `flowMellin b ρ w` | `t(x) = Σ b_i x^{ρ_i}` for real `x ≥ 1`; `∫_1^∞ t(x) x^{−w−1} dx`, equal to the resolvent `Σ b_i/(w − ρ_i)` right of all weights |
| Laplace kernel of `ζ`, its periodization | `ladderKernel s`, `ladderSum s P`, `ladderDefect s P`, `jumpTerm s P k` | `{e^x} e^{−sx}`, with `∫_0^∞ = 1/(s−1) − ζ(s)/s`; the sum of its translates by `kP`, `k ≥ 0`; the same with the polar part `e^{(1−s)y}/(e^{(1−s)P} − 1)` added; the jump at `kP`: `e^{−skP}` if `e^{kP} ∈ ℕ`, else `0` |
| First moment of the kernel, Taylor constant | `ladderMoment s`, `taylorConstant σ` | `x {e^x} e^{−sx}`; the constant of `∫K_{s+η} = ∫K_s − η∫xK_s + O(‖η‖²)` at real part `σ` |
| Limit-periodic tower | `LPIndex`, `lpMode`, `lpWeight` | modes `2ω`, `ω^{2^k} = 1`, weight `4^{−k}` |
| Wolff module | `wolffWeight`, `HTGeometry.CircleQuadraturePositive.ppoint` | nodes of a positive Wolff measure as modes, its normalized masses as weights; all power sums `Σ c_i ρ_i^k`, `k ≥ 1`, vanish |
| Divisor-preserving map | `PreservesXiDivisor A` | `ord_{A s} ξ = ord_s ξ` for every `s` |
| Tower of `ζ` at its abscissa | `abscissaMode ℓ Θ` | modes `e^{ℓ(ρ − Θ)}` with the lag weights `1/(ρ(1−ρ))` |
| Zero motive of `ζ` | `RHTower.XiZeroCopy`, `RHTower.weilLagFunction` | zeros of `ξ` with multiplicity; `Φ(L) = Σ e^{L(ρ−½)}/(ρ(1−ρ))` |

## 3. Language

- **Pure**: every mode is fixed by `ιc`. **`c`-pure**: every non-real mode is fixed by `ιc`. Purity is
  `c`-purity together with the absence of real exceptional modes.
- **Exceptional parameter**: a real mode off the centre line, `s(1 − s) < ¼`.
- **Index**: the number of zeros of the defect right of the line; zeros of the defect left of the
  line do not count.
- **Schur function**: a holomorphic function bounded by one on the half-plane. **Node**: a point at
  which a Schur function is reduced.
- **In law / at a point**: a statement in law bounds a count, a density or a growth rate of the
  exceptional set; a statement at a point excludes a mode. A **conversion** turns one into the other.
- **Visible** mode: one whose total weight is nonzero.
- **Trace class at `q`**: the Frobenius at `q` has an absolutely convergent trace. **Order**: the
  number of derivatives of the trace that remain of trace class.
- **Trace-integral**: the traces lie in a discrete subgroup of `ℂ`. **Tate**: all visible modes are
  natural numbers, so the trace is a polynomial.
- **Fixed part** of a family: the object entering every member.
- **Conjugacy class** of a mode: the modes into whose lines a Frobenius-equivariant map can send its
  line. Over one Frobenius `q` it is the **class** of `ρ`: the modes with the eigenvalue `q^ρ`, the
  vertical progression `ρ + 2πik/log q`. **Constituent**: a Frobenius-stable subspace of the module.
- **Attained top**: the largest modulus of a tower, or the largest real part of a configuration, is
  attained by a mode.
- **Thick** set of levels: contains arbitrarily long runs arbitrarily far out.
- **Locally finite** module: finitely many modes in every disc. Its mode set is closed and discrete
  and has no walls.
- **Accessible** mode: an isolated mode joined to a point beyond all modes by a path that otherwise
  avoids the closure of the modes. **Radially visible**: the path is the outward segment. A mode
  that is not accessible lies behind a **wall** of modes.
- **Price** of a mechanism: the exact statement over `ℤ` to which it reduces purity.

## 4. Mechanisms

1. **Two agreements force identity.** A holomorphic self-map of the disc with two fixed points is the
   identity. A Schur function on the half-plane that meets `c·b_w` at two points equals it.
2. **Schur reduction.** For a Schur function `θ` and a node `s₀`, `M_{θ(s₀)} ∘ θ = φ · b_{s₀}` with
   `φ` a Schur function. One step keeps every other agreement of two Schur functions and lowers the
   degree of a Blaschke product by one.
3. **Reflection of polynomials.** With `D = ε N^*`: if `N − vD = (X − s₀) N₁` then
   `D − v̄N = −ε (X − (1 − s̄₀)) N₁^*`. Degrees drop without factoring into roots.
4. **Parity.** Complex conjugation acts freely on non-real exceptional points. An index `κ` leaves at
   most `κ/2` of them above the real axis.
5. **Reflection decreases `ξ`.** All zeros lie left of `Re = 1`, so `‖ξ(2s−1)‖ ≤ ‖ξ(2s)‖` on
   `Re s ≥ ½`. For a divisor in the closed strip the factor at `ρ` is paired with the factor at
   `1 − ρ̄`: `‖w − 1 − ρ‖ ≤ ‖w − (1 − ρ̄)‖` for `Re w ≥ 1`.
6. **The slope at the centre.** The constant term on the real axis vanishes at `x = ½` for every
   `Y`; its slope there is `½(log 4πe^{−γ} − log Y)`, from `ξ'(1) = ½ + γ/4 − ¼ log 4π`.
7. **Sphere domination.** `F_Y(s) Y^{−s} = (s−1) G(2s) + s G(2s−1) Y^{1−2s}`; the second term is
   uniformly small near a zero of the first when `Y` is large.
8. **Cesàro means.** `(1/N) Σ_{ν<N} S(ν) w^{−ν}` tends to the weight at `w`; on a window the error
   splits into a circle term, small for long windows, and an inner term, small for far windows.
9. **Almost periods.** Dirichlet approximation on finitely many unimodular modes, the tail paid in
   weight; for an integer-valued sequence an almost period of precision `½` is a period.
10. **The integrality gap.** An integer of modulus `< 1` is zero.
11. **Derivatives lower weights.** `d/dx Σ b_i x^{ρ_i} = Σ b_i ρ_i x^{ρ_i−1}`; the `m`-th forward
    difference of any step is an `m`-fold mean of the `m`-th derivative, hence `O(x^{A−m})`: a trace
    is smooth at infinity.
12. **Dilation.** The trace at `qx` is the trace of the module `(b_i q^{ρ_i}, ρ_i)` at `x`.
13. **Euler products jump.** A sequence supported on the prime powers has `m`-th differences
    `± f(p^{a+1})` along `n = p^a` after dilation by `p`.
14. **Newton and dilation operators.** A vanishing `m`-th difference gives a polynomial;
    `Π_{k<m}(S_p − p^k)` kills it and multiplies the weight of the mode `ρ` by `Π_{k<m}(p^ρ − p^k)`.
15. **Two primes separate the modes.** `2^s = 2^t` and `3^s = 3^t` force `s = t`. Repeated modes are
    merged along the fibres of `i ↦ ρ_i`. On the module, `Frob_p − p^{ρ_j}` removes the line of `ρ_j`
    and keeps every line with another eigenvalue: equivariant maps are diagonal and stable subspaces
    are sums of lines.
16. **No contraction.** Under a contracting affine map the iterates of a zero accumulate at the fixed
    point, against the isolation of zeros.
17. **No period.** A vertical period makes the zero count linear along its multiples.
18. **Hurwitz.** Zeros of a locally uniform limit are limits of zeros.
19. **Amortization.** From `‖S(ν)‖^k ≤ C_k (B R^k)^ν` for every `k` the modes are at most `B^{1/k} R`
    for every `k`, hence at most `R`: the growth of the base is paid once and divided by the power.
20. **The mean.** With a variable part of mean zero, `F = ∫ S_ω` and `∫‖S_ω‖² = ‖F‖² + ∫‖V_ω‖²`.
21. **Power sums.** For bounded modes `Σ c_i x^{ρ_i} = Σ_k (log x)^k/k! · Σ_i c_i ρ_i^k`: vanishing
    power sums give a constant trace.
22. **Resolvent continuation.** `Φ(w) = Σ c_i/(w − z_i)` equals `Σ_ν S(ν) w^{−ν−1}` outside the modes; a
    bound `S(ν) = O(r^ν)` continues the series to `‖w‖ > r`; along a segment free of modes the two
    agree up to an isolated mode, where `(w − z_j)Φ(w)` tends to its weight. The segment may be any
    path off the closure of the modes.
23. **No walls on the flow.** A locally finite set of modes is closed and discrete: a short vertical
    step and a horizontal segment at a height missing the finitely many modes nearby join any mode
    to the half-plane right of all weights. The Mellin transform of the trace is the resolvent there.
24. **Positive real parts do not cancel.** The lag weights `1/(ρ(1−ρ))` have positive real part, so
    every point of every tower of `ζ` is visible.
25. **The integers jump across every period.** The Laplace kernel `{e^x} e^{−sx}` of `ζ` jumps at
    `x = log m`. Summed over its translates by a period `P`, the jumps at `kP` with `e^{kP} ∈ ℕ`
    add up to a geometric series over the multiples of the least such `k`, which never vanishes;
    the Fourier coefficients of the sum, polar part removed, are `−ζ(s + 2πin/P)/(P(s + 2πin/P))`.
26. **Summable Fourier coefficients leave no jump.** A square integrable function on a period with
    absolutely summable Fourier coefficients agrees almost everywhere with the continuous sum of
    its series, so its one-sided limits at the two ends of the period coincide.
27. **Bessel on the lattice of a period.** The samples `∫_0^∞ K(x) e^{−2πinx/P} dx` of a kernel with
    uniformly summable translates are the Fourier coefficients of the sum of its translates, hence
    square summable. Applied to the Laplace kernel, to its first moment and to the periodization
    itself: the Laplace integrals, their derivatives in `s` and the values `ζ(s_n)/s_n` along a
    progression are in `ℓ²`.
28. **Perturbing a zero.** If `ζ(s + η) = 0`, the Laplace representations at `s` and `s + η` and
    the second order Taylor bound give `ζ(s)/s = η/((s−1)(s+η−1)) − η∫xK_s + O(‖η‖²)`: a product of
    `η` with `ℓ²` sequences along a progression.

## 5. The dictionary

| Finite rank | Infinite-rank counterpart | Theorem | Price over `ℤ` |
|---|---|---|---|
| Newton–Girard elimination | window means on summable towers | `merged_eq_zero_of_small_on_runs`, `norm_le_one_of_thick_bounded_levelSums` | none |
| Finitely many eigenvalues | the top weight is attained: for towers of any rank on thick sets of levels; for the lag of `ζ` along a full progression already in `RHTower` (`riemannHypothesis_or_not_attained_of_forall_le`) ; below the top, a mode accessible from infinity is eliminated on all levels, and only a wall of modes protects a mode | `norm_le_one_of_thick_bounded_levelSums`, `riemannHypothesis_iff_attainedTop_and_thick_lag_bounded`, `merged_eq_zero_of_accessible`, `riemannHypothesis_of_lag_bounded_of_accessible` | an attained abscissa (`RHTower.AttainedTop`) or one accessible off-line zero, in place of well-foundedness (ZAL) |
| Closedness of the set of weights | the same statement at the top; Wolff towers show it cannot be dropped | `lag_bound_iff_of_attainedTop`; `InfiniteRankWeilTheory.exists_tower_bounded_without_wellFounded` | landing at the top |
| Conjugates share their absolute value | over one Frobenius an equivariant map preserves the weight; over `ℤ` it is diagonal, and the rigid symmetries of the divisor are `1, ι, c, ιc` | `re_eq_of_commute`, `eq_of_commute_two_three`, `eq_conj_of_semilinear_commute`, `preservesXiDivisor_affine_iff`, `preservesXiDivisor_antiaffine_iff` | no conjugation relates two zeros, and no class of one Frobenius lies in the zero set (`exists_conjugate_not_zero`); what remains is AAL |
| Irreducibility of the characteristic polynomial | the module is semisimple without multiplicity, its constituents are the sets of modes; no family of distinct zeros of trace class of order two is integral, whatever their real parts, and none has an Euler product | `single_mem_of_stable`, `eq_zero_of_integral_trace_of_distinct_xi_zeros`, `not_isTrace_of_primePower_support` | B13 for the exceptional set |
| Integer traces ⇒ Kronecker | one Frobenius, weight zero: finite rank and torsion; all Frobenii of `ℤ`, trace class at any Frobenius, modes repeated at will: Tate; for locally finite modules in the strip no chain condition is needed | `kronecker_oneFrobenius_injective`, `tate_of_integral_trace`, `mergedWeight_eq_zero_of_integral_trace`, `mergedWeight_eq_zero_of_integral_locallyFinite`; exact in the chain condition: `exists_integral_traceClass_module_not_tate` | the zero motive is not of trace class |
| Determinant weight from the pairing | integral and dual: only the modes `0` and `1` | `tate_of_integral_trace_dual`, `mergedWeight_dual_of_integral_trace` | the weight of a zero is fixed only if `ιc` fixes it (`SignFreePurityMechanisms`) |
| One positive square (Hodge index) | a defect of degree `κ` has at most `κ` exceptional points, at most `κ/2` above the real axis; at `κ = 0`: purity; at `κ = 1`: `c`-purity; the pole of `ζ` is one defect | `encard_agreements_le`, `hermiteBiehler_index`, `hermiteBiehler_index_general`, `hermiteBiehler_indexZero`, `two_mul_encard_upper_zeros_le`, `lineLaw` | index `≤ 1` for `ξ` itself is RH (`ArithmeticOrientationGeometry.riemannHypothesis_iff_encard_rightZeros_lt_two`) |
| Specialization lowers weights | a bound on the index passes to locally uniform limits; along the Eisenstein tower the exceptional parameter is born at `4πe^{−γ}` and persists | `encard_zeros_le_of_tendstoLocallyUniformly`, `exists_exceptionalParameter_iff`, `exceptionalParameter_mono` | `ξ` as a limit of index-one objects is RH |
| Integral lattice stable under Frobenius | none under three prime Frobenii | `RHTower.not_exists_joint_eigenfunctional_three_primes` | — |
| A family with big monodromy | moments of the full traces see every member of positive mass by amortization and the fixed part as their mean; purity of all members of a family without a measure is the closed strip of the fixed part, never its line | `member_norm_le_of_family_moments`, `integral_norm_sq_fixedPart_add`, `fixedPart_norm_le_one_of_mean_bounded`, `pencil_lineLaw_of_tendsto`, `divisorPencil_lineLaw_iff` | moments of the full traces, which contain the fixed part with mass one |
| A Frobenius with zero derivative | one Frobenius makes the zeros full classes `ρ + 2πik/log q`; the zeros of `ζ` contain no class of any Frobenius, `Σ_n ‖ζ(ρ + inT)‖/‖ρ + inT‖ = ∞` on every vertical progression in the strip; an endomorphism of `ℤ[X]` with zero derivative is an evaluation, and order `m` at the primes of `S` costs `log‖a‖ ≥ m·θ(S)` with equality | `not_summable_norm_riemannZeta_div`, `exists_conjugate_not_zero`, `exists_curve_zero_not_zero`; `SignFreePurityMechanisms.exists_eq_C_eval_of_derivative_eq_zero`, `mul_sum_log_le_log_abs`, `log_prod_pow_eq` | the product formula is an identity: vanishing costs its own count |
| The Lefschetz trace formula | traces determine a trace-class module whose weights have no ascending chain; on the flow the growth of the trace reads the weights of every locally finite module; the Lefschetz numbers of `Spec ℤ` are not traces of any order | `mergedWeight_eq_of_frobTrace_eventually_eq`, `flow_bound_iff`, `not_isTrace_vonMangoldt`, `not_isTrace_mertens` | the formula over `ℤ` is an identity of distributions |
| The square of the curve | the archimedean fibre is the module of even jets and is forced by its Lefschetz numbers; the finite contacts are not a trace | `archimedeanFibre_forced`, `not_isTrace_gluedLefschetz`, `not_isTrace_pointCount` | a diagonal whose Frobenii are outside trace class |
| The diagonal and Riemann–Roch | Weil's archimedean form minus the pole is the limit of the forms on the packets of the degree points and of the invariant combs of the glued object; in the index calculus the diagonal carries one defect, the pole | `AbsoluteGeometryOfSpecZ.tendsto_degreeForm`, `AbsoluteGeometryOfSpecZ.tendsto_combForm`; `constantTerm_indexOne`, `not_isTrace_gluedLefschetz` | the positivity of that limit form is Weil's criterion; its carrier is outside trace class |

## 6. Questions and answers

| # | Question | Answer | Lean |
|---|---|---|---|
| Q1 | **Kronecker.** What does integrality of the traces force at infinite rank? | *One Frobenius, weight zero:* a summable tower in the closed disc with integer level sums has finite rank; its visible modes are roots of unity of one order. *One Frobenius, positive weight:* nothing; the limit-periodic tower is pure, of trace class, integral at every level and of infinite rank. *All Frobenii of `ℤ`:* an integral module of trace class of order `m` at any Frobenius, with weights `< m` without ascending chain and modes repeated at will, carries weight only at the Tate twists `0, …, m−1`; its trace is eventually a polynomial; the same for traces in `ℤc`. *Locally finite modules in the strip:* with finitely many modes in every disc, weights in `0 < Re ρ ≤ 1` and trace class of order two, integer traces leave weight only at the mode `1`, with no chain condition: integrality at the integers bounds the dilated trace `t(qx) − q t(x)` on the whole flow. *The chain condition is exact for general modules:* the Wolff module has distinct bounded modes, positive weights, trace class of every order and trace `1` at every Frobenius, and carries weight at `5/4`; its weights have an ascending chain. *With the duality:* only `0` and `1` remain, the modes of `H⁰` and `H²`; no visible mode lies in the open strip. *Traces in `ℤ log p`:* a sequence supported on the prime powers that survives along the powers of one prime is no trace at all. | `kronecker_oneFrobenius`, `kronecker_oneFrobenius_injective`, `exists_pure_integral_tower_of_infinite_rank`, `tate_of_integral_trace`, `tate_of_integral_trace_at`, `mergedWeight_eq_zero_of_integral_trace`, `exists_polynomial_of_integral_trace_at`, `tate_of_trace_in_zmultiples`, `tate_of_integral_trace_dual_at`, `mergedWeight_dual_of_integral_trace`, `not_visible_in_open_strip`, `not_isTrace_of_primePower_support`, `mergedWeight_eq_zero_of_integral_locallyFinite`, `exists_integral_traceClass_module_not_tate`, `wolff_not_weightsWellFounded` |
| Q2 | **Irreducibility.** In which sense is `ξ` irreducible? | Over `ℂ` the Frobenius module `⊕ ℂ(−ρ)` with distinct modes is semisimple without multiplicity: a subspace stable under the Frobenii at `2` and `3` contains every line on which one of its vectors has a component, so the constituents are the sets of modes and the simple ones are the single modes. Over `ℤ` no constituent is arithmetic inside trace class: a family of distinct zeros with weights of trace class of order two and integer traces at all large integers has all weights zero, whatever the real parts of the zeros; and no trace of any order is supported on the prime powers without dying out along the powers of each prime. So `ξ` has no factor of trace class with integral traces or with an Euler product: its only arithmetic constituent is the whole. Over one Frobenius it has no constituent of finite rank: `ξ` vanishes on the zero set of no local factor `q^{−s} − u`, `q > 1`, `u ≠ 0`, hence of no polynomial in `q^{−s}` with a nonzero root, and on the zeros of no eigenvalue of a curve over a finite field. Irreducibility gives no purity: what purity needs is B13. | `single_mem_of_stable`, `eq_zero_of_integral_trace_of_distinct_xi_zeros`, `mergedWeight_eq_zero_of_integral_locallyFinite`, `eq_zero_of_integral_trace_of_xi_zeros`, `not_isTrace_of_primePower_support`, `exists_zero_localFactor_not_zero`, `exists_zero_polynomial_not_zero`, `exists_curve_zero_not_zero` |
| Q3 | **Conjugacy.** Which zeros are forced to share a depth? | Over one Frobenius `p` a linear map commuting with it sends the line of `ρ` into the lines of the modes with the same eigenvalue `p^ρ`, and these have the weight of `ρ`: conjugates share their depth, and the class of `ρ` is its vertical progression. The zeros contain no such class, at any real part: for `ρ` in the open strip and any step `T > 0`, `Σ_{n ∈ ℤ} ‖ζ(ρ + inT)‖/‖ρ + inT‖ = ∞`, so infinitely many conjugates of every zero over every Frobenius are not zeros; the same values are square summable. Nor do zeros approach a class: no two-sided sequence of zeros lies within a square summable distance of a vertical progression in the strip. Over `ℤ` a map commuting with the Frobenii at `2` and `3` is diagonal: every zero is alone in its class. A conjugate-linear equivariant map sends `ρ` to `ρ̄`: the only conjugation is the archimedean one. On the side of the function, the affine and anti-affine maps preserving the zero divisor are `1, ι, c, ιc`; there is no contraction and no vertical period. | `cpow_eq_of_commute`, `re_eq_of_commute`, `not_summable_norm_riemannZeta_div`, `exists_riemannZeta_ne_zero_progression`, `exists_conjugate_not_zero`, `summable_sq_norm_riemannZeta_div`, `not_cofinite_riemannZeta_eq_zero_of_sq_summable`, `not_cofinite_xi_eq_zero_near_class`, `eq_of_commute_two_three`, `eq_conj_of_semilinear_commute`, `preservesXiDivisor_affine_iff`, `preservesXiDivisor_antiaffine_iff`, `not_preserves_vertical_period`, `not_preserves_of_norm_lt_one` |
| Q4 | **Fixed part.** What does a family prove about the object common to all its members? | *Under a measure:* the fixed part is the mean of the family and the excess of the second moment over the variance, `∫‖S_ω‖² = ‖F‖² + ∫‖V_ω‖²`; a bound for the first moment of the full traces, or for that excess, on a thick set of levels puts a fixed part with an attained top in the closed disc, at any rank. A member of positive mass is seen by amortization: moments `∫‖S_ω(ν)‖^k ≤ C_k (B R^k)^ν` for all `k` put it in the disc of radius `R`. The moments must be those of the full traces; the variable part does not contain `F`. *Without a measure:* purity of every member reads the closed strip of the fixed part and nothing inside it. The family `F_Y = (s−1)G(2s)Y^s + sG(2s−1)Y^{1−s}`, `Y ≥ 1`, satisfies the line law over every finite configuration of zeros in the closed strip, over every locally uniform limit of such with no bound assumed on the limit, and over `ξ`; a non-real zero of `G` right of `Re = 1` produces a non-real zero right of the line in every member with `Y` large; for finite divisors without real points the line law of all members is equivalent to the closed strip. The half-shift family `G(s + ½) ± G(s − ½)` has no defect and is pure over every such fixed part; over `ξ` this is Taylor's theorem. With any polynomial defect in place of the pole, every member has as many zeros right of the line as the defect has there at most, again whatever the zeros of `G` inside the strip. *By limits:* a bound on the index of the members passes to a limit member, never to a common factor. | `integral_fixedPart_add`, `integral_norm_sq_fixedPart_add`, `fixedPart_norm_le_one_of_mean_bounded`, `fixedPart_norm_le_one_of_excess_bounded`, `norm_le_of_amortized_levelSums`, `member_norm_le_of_family_moments`, `pencil_indexOne`, `exists_fixedPart_with_lineLaw`, `pencil_lineLaw_of_tendsto`, `xi_mem_pencil_class`, `exists_nonreal_zero_pencil_of_zero_right`, `divisorPencil_lineLaw_iff`, `pencil_index_general`, `halfShift_ne_zero`, `re_eq_half_of_xi_halfShift_eq_zero`, `encard_zeros_le_of_tendstoLocallyUniformly` |
| Q5 | **The glued square.** What do its Lefschetz numbers force, and what does a diagonal carry? | The archimedean part `n²/(n² − 1)` is a trace: of the module of even jets `0, −2, −4, …`, of trace class of every order at the Frobenius `2` and not at the identity, and every module of trace class at `2` with weights without ascending chain and that trace carries weight one at each even jet and zero elsewhere. The finite contacts `Λ(n)` are not a trace of any order at any Frobenius, hence neither is the Lefschetz number `Λ(n) + n²/(n² − 1)` nor the point count of `SurfaceOfSpecZ`. So a diagonal carries a module outside trace class of every positive order: the zero motive. Smoothed by the lag weights `1/(ρ(1−ρ))` it is of trace class of order exactly zero, its trace along a tower is the lag `Φ(νℓ)`, which is the smoothed prime deviation, and the trace formula holds in that form and in no sharper one. In the index calculus the diagonal carries one defect: the pole. | `frobTrace_evenJets`, `evenJets_traceClassAt`, `evenJets_not_traceClassAt_one`, `archimedeanFibre_forced`, `not_isTrace_gluedLefschetz`, `not_isTrace_pointCount`, `lagModule_traceClassAt_zero`, `lagModule_not_traceClassAt_one`, `weilLagFunction_eq_towerSum`, `riemannHypothesis_iff_attainedTop_and_thick_primeDeviation`, `constantTerm_indexOne` |
| Q6 | **Weight filtration.** What is it on an infinite-rank module? | The filtration by the growth of the traces. *On the flow:* for every module with finitely many modes in each disc, `t(x) = O(x^s)` for real `x ≥ 1` exactly when no weight is carried at a mode of weight `> s`, with no condition on the weights; for the zero motive with its lag weights, `Σ_ρ x^ρ/(ρ(1−ρ)) = O(x^s)` on the flow exactly when every zero has real part `≤ s`. *At the integers:* for a module of trace class at any Frobenius whose weights have no ascending chain, `t(n) = O(n^s)` at the integers exactly when no weight is carried at a mode of weight `> s`, repeated modes merged, read on the integers `2^a 3^b` alone; traces determine the merged weights. Without the chain condition both fail: the Wolff module has the bounded trace `1`, the trace of the unit Tate module, and weight at `5/4`. With its lag weights the zero motive of `ζ` is of trace class of order zero at every Frobenius and of order one at none; with an attained abscissa `β₀` the lag along one tower is `O(e^{aνℓ})` exactly when `β₀ − ½ ≤ a`. The Lefschetz numbers `Λ(n)` of the scaling flow, the Mertens function, which is the defect of the orientation cover, and the prime counting function are not traces of any order: their explicit formulas do not converge in trace class. | `flow_bound_iff`, `zeroMotive_flow_bound_iff`, `frobTrace_bound_iff`, `frobTrace_bound_iff_mergedWeight_at`, `frobTrace_wolff`, `mergedWeight_eq_of_frobTrace_eventually_eq`, `lagModule_traceClassAt_zero`, `lagModule_not_traceClassAt_one`, `lag_bound_iff_of_attainedTop`, `not_isTrace_vonMangoldt`, `not_isTrace_mertens`, `not_isTrace_primeCounting` |
| Q7 | **Semicontinuity.** How do weights behave along towers and in limits? | A bound `κ` on the number of zeros in an open set passes to locally uniform limits: if `ξ` is a limit of entire functions with at most `κ` zeros right of the line it has at most `κ` there, and RH holds iff `ξ` is a limit of real entire functions with at most one. Along the Eisenstein tower the index is `0` for `1 ≤ Y ≤ 4πe^{−γ}`, where the constant term is pure, and `1` above, where the exceptional parameter exists, persists and increases; as `Y → ∞` the members divided by `Y^s` tend to `(s−1)G(2s)` and inherit its zeros right of the line. | `encard_zeros_le_of_tendstoLocallyUniformly`, `encard_xi_zeros_le_of_limit`, `riemannHypothesis_iff_limit_of_indexOne`, `exists_exceptionalParameter_iff`, `re_eq_half_of_constantTerm_eq_zero`, `exceptionalParameter_mono`, `exists_nonreal_zero_pencil_of_zero_right` |
| Q8 | **Law and point.** Which conversions exist at infinite rank, and what does each cost? | Five. (i) *Index:* a defect of degree `κ` plus reality leaves at most `κ/2` non-real pairs, none at `κ = 1`; price: an index bound. (ii) *Integrality gap:* an integer below one in modulus vanishes; price: trace class. (iii) *Attained top:* a crude bound on a thick set of levels of one tower excludes every weight above it; price: the top is attained. Below the top the same bound on all levels excludes every mode accessible from infinity; price: one accessible off-line zero. (iv) *Positive mass:* moments of a family bound each member of positive mass, and the fixed part with mass one; price: moments of the full traces for all powers. (v) *Recurrence:* a period turns one exceptional mode into a positive density; `ζ` has none. Purity of all members of a family without a measure is not a conversion: it reads the strip of the fixed part. | `encard_agreements_le`, `two_mul_encard_upper_zeros_le`, `tate_of_integral_trace`, `norm_le_one_of_thick_bounded_levelSums`, `merged_eq_zero_of_accessible`, `member_norm_le_of_family_moments`, `fixedPart_norm_le_one_of_mean_bounded`, `not_preserves_vertical_period`, `divisorPencil_lineLaw_iff` |

## 7. Tests

| Test | How it is met |
|---|---|
| Weil's theorem for curves without finite rank at the decisive step | `curveDatum_unitary_of_thick_bounded_trace`: traces bounded on a thick set of levels give unitarity; the decisive step `norm_le_one_of_thick_bounded_levelSums` allows any rank and any number of modes on a circle |
| The Lagarias–Suzuki line law without the truncated Eisenstein series | `lineLaw`, `lineLaw_gammaZeta`: for every `Y ≥ 1` and every non-real `s` off the line, in the whole plane; `exists_exceptionalParameter_iff`, `re_eq_half_of_constantTerm_eq_zero`: a real exceptional pair exactly for `Y > 4πe^{−γ}`, purity for `1 ≤ Y ≤ 4πe^{−γ}`. Inputs: `ζ ≠ 0` on `Re ≥ 1`, the functional equation, the pole as one defect, reality, `ξ'(1)` |
| Failure on the impure models | §10 |
| Not uniform in real characters unless it excludes exceptional zeros | purity by parity proves `c`-purity only, and provably no more: the real exceptional parameter exists above the threshold (`exists_exceptionalParameter_iff`) |
| Integer norms in a free abelian monoid against lengths in a non-abelian group | integer norms carry the Frobenii at consecutive integers, where the integrality gap closes (`tate_of_integral_trace`) and Euler products jump (`not_isTrace_of_primePower_support`), and at two primes with incommensurable logarithms, which separate all modes (`cpow_two_three_injective`); one Frobenius leaves the rank free (`exists_pure_integral_tower_of_infinite_rank`) and makes the zeros of a curve full classes, of which the zeros of `ζ` contain none: one period sees the jumps of the integers only at the powers of one base (`tsum_jumpTerm_ne_zero`, `exists_curve_zero_not_zero`); an index-one object has a real exceptional parameter as a surface with a small eigenvalue has (`exists_exceptionalParameter_iff`, `HTGeometry.selbergSmallEigenvalue_offCritical`) |

## 8. Tools

| # | Tool | Module |
|---|---|---|
| T1 | Index-one rigidity on the half-plane; Hermite–Biehler sums with one real defect | `ADefectOfIndexOneIsPureOffTheRealAxis` |
| T2 | Schwarz lemma and Schur reduction on the half-plane; injectivity of `M_v` | `ASchurFunctionReducesAtEveryNode` |
| T3 | Reflected polynomials, the class of finite Blaschke products, its closure under one Schur step and under multiplication by a defect factor | `ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints` |
| T4 | Cesàro means and almost periods of summable towers | `CesaroMeansReadTheModesOfASummableTower` |
| T5 | Window means on thick sets, with separate circle and inner errors | `CesaroMeansOnThickSets` |
| T6 | Calculus of traces: derivative, forward differences of any step, Newton polynomial | `IntegralTraceClassModulesOverTheIntegersAreTate` |
| T7 | Tate dilation operators `Π(S_p − p^k)` | `IntegralTraceClassModulesOverTheIntegersAreTate` |
| T8 | Two-prime separation of modes; growth reads weights | `TwoFrobeniiDetermineATraceClassModule` |
| T9 | Trace class at a Frobenius, dilation, the class of traces and its closure under differences and dilations | `TheLefschetzNumbersOfTheIntegersAreNotTraces` |
| T10 | Merged modes: the merged module, uniqueness and growth with repeated modes | `TheArchimedeanFibreIsATraceAndTheFiniteContactsAreNot` |
| T11 | Families over a fixed part: divisor polynomials, symmetrization, the reflection bound, sphere domination for large `Y` | `TheLineLawSeesTheStripAndNotTheLine` |
| T12 | The defect on the real axis and its slope at the centre; `ξ'(0)`, `ξ'(1)` | `TheExceptionalParameterIsBornAtFourPiExpMinusGamma` |
| T13 | Divisor symmetries: no contraction, no period | `TheSymmetriesOfTheZerosAreTheTwoInvolutions` |
| T14 | Hurwitz count in an open set, at any index | `TheIndexIsSemicontinuous` |
| T15 | The Frobenius module as vectors: equivariant maps, stable subspaces, separation by `Frob_p − p^{ρ_j}` | `OverTheIntegersEveryModeIsItsOwnConjugacyClass` |
| T16 | Kronecker and growth with merged modes at any Frobenius; the Tate module of a polynomial | `KroneckerOverTheIntegersNeedsNoDistinctModes` |
| T17 | Elimination at any radius, amortization over powers, mean and second moment of a family | `AFamilySeesItsMeanAndItsMembersOfPositiveMass` |
| T18 | Traces from power sums: `Σ c_i x^{ρ_i} = Σ_k (log x)^k/k! · Σ_i c_i ρ_i^k` for bounded modes | `WithoutTheChainConditionKroneckerOverTheIntegersFails` |
| T19 | The resolvent of a tower: Laurent expansion in the level sums, analyticity off the modes, the weight at an isolated mode as a residue, continuation along paths | `AModeAccessibleFromInfinityIsEliminated` |
| T20 | The trace on the flow: continuity, Mellin transform, its continuation under a growth bound, its identity with the resolvent; the path around locally finite modes | `OnTheFlowTheWeightFiltrationNeedsNoChainCondition` |
| T21 | From the integers to the flow: the dilated trace `t(qx) − q t(x)`, the Lipschitz bound of a trace with weights `≤ 1` | `NoFamilyOfZerosIsIntegralWhateverTheirRealParts` |
| T22 | Fourier series on a period: absolutely summable coefficients leave no jump across the period | `TheZerosContainNoClassOfOneFrobenius` |
| T23 | The Laplace kernel of `ζ` at any `s` in the strip: forward periodization, unfolding, Fourier coefficients, one-sided limits, the jump series | `TheZerosContainNoClassOfOneFrobenius` |
| T24 | Bessel on the lattice of a period for kernels with summable translates; Parseval for the zeta values along a progression | `NoSequenceOfZerosApproachesAClassOfOneFrobenius` |
| T25 | The first moment of the Laplace kernel and the second order Taylor bound of the Laplace integral, uniform in the height | `NoSequenceOfZerosApproachesAClassOfOneFrobenius` |

## 9. Pillar theorems

| Theorem | Lean |
|---|---|
| Two agreements force identity; at most one exceptional point; purity by parity | `eqOn_of_two_agreements`, `agreement_subsingleton`, `im_eq_zero_of_agreement`, `hermiteBiehler_indexOne` |
| A Schur function reduces at every node | `norm_le_norm_defectFactor`, `exists_quotient_by_defectFactor`, `exists_schur_reduction` |
| The index law: a defect of degree `κ` has at most `κ` exceptional points, at most `κ/2` above the real axis; attained by every configuration | `IsBlaschke.reduce`, `eqOn_of_card_agreements`, `encard_agreements_le`, `isBlaschke_prod`, `hermiteBiehler_index`, `hermiteBiehler_index_general`, `two_mul_encard_upper_zeros_le`, `index_attained` |
| The Eisenstein constant term is pure off the real axis for every `Y ≥ 1` | `norm_constantTermDual_le`, `constantTerm_indexOne`, `im_eq_zero_of_constantTerm_eq_zero`, `lineLaw`, `lineLaw_gammaZeta` |
| The exceptional parameter is born at `4πe^{−γ}`: it exists exactly above, persists and increases; below, the constant term is pure | `hasDerivAt_xiReal_one`, `hasDerivAt_defect_half`, `exists_exceptionalParameter_iff`, `re_eq_half_of_constantTerm_eq_zero`, `exceptionalParameter_mem`, `exceptionalParameter_mono` |
| Index zero: the half-shifts `ξ(s + ½) ± ξ(s − ½)` have all their zeros on the line | `hermiteBiehler_indexZero`, `halfShift_ne_zero`, `re_eq_half_of_xi_halfShift_eq_zero` |
| Index two admits a non-real pair | `indexTwo_admits_nonreal_pair` |
| The line law of a family sees the strip of its fixed part and not the line | `pencil_indexOne`, `pencil_lineLaw`, `norm_divisorPoly_sub_one_le`, `exists_fixedPart_with_lineLaw`, `pencil_lineLaw_of_tendsto`, `exists_nonreal_zero_pencil_of_zero_right`, `divisorPencil_lineLaw_iff`, `pencil_index_general` |
| Under a measure a family sees its mean and its members of positive mass | `norm_le_of_amortized_levelSums`, `member_norm_le_of_family_moments`, `integral_fixedPart_add`, `integral_norm_sq_fixedPart_add`, `fixedPart_norm_le_one_of_mean_bounded`, `fixedPart_norm_le_one_of_excess_bounded` |
| Cesàro means read the weight at a point; almost periods | `tendsto_cesaro_towerSum`, `merged_eq_zero_of_tendsto_zero`, `exists_almostPeriod` |
| Window means on thick sets | `norm_windowMean_sub_le`, `merged_eq_zero_of_small_on_runs` |
| Kronecker for one Frobenius at infinite rank | `kronecker_oneFrobenius`, `inner_weight_eq_zero`, `kronecker_oneFrobenius_injective` |
| At positive weight integrality does not bound the rank | `norm_lpMode`, `exists_int_lp_levelSum`, `lp_infinite_rank`, `exists_pure_integral_tower_of_infinite_rank` |
| Two Frobenii determine a trace-class module; growth is the weight filtration; with repeated modes and at any Frobenius | `cpow_two_three_injective`, `re_le_of_frobTrace_bound`, `frobTrace_bound_iff`, `frobTrace_bound_iff_mergedWeight`, `frobTrace_bound_iff_mergedWeight_at`, `mergedWeight_eq_of_frobTrace_eventually_eq` |
| Kronecker over `ℤ`: integral trace-class modules are Tate, at any Frobenius and without distinct modes | `hasDerivAt_frobTrace`, `exists_norm_fwdDiff_iter_frobTrace_le`, `tateDilation_frobTrace`, `tate_of_integral_trace`, `tate_of_integral_trace_at`, `mergedWeight_eq_zero_of_integral_trace`, `mergedWeight_dual_of_integral_trace`, `not_visible_in_open_strip` |
| The chain condition is exact: an integral trace-class module with trace `1` at every Frobenius that is not Tate | `frobTrace_eq_tsum_of_powerSums_zero`, `frobTrace_wolff`, `exists_integral_traceClass_module_not_tate`, `wolff_not_weightsWellFounded` |
| A trace is smooth at infinity; sequences with an Euler product or with two recurring jumps are not traces | `tendsto_fwdDiff_iter_frobTrace_of_traceClassAt`, `IsTrace.tendsto_fwdDiff`, `not_isTrace_of_primePower_support`, `not_isTrace_of_two_jumps` |
| The Lefschetz numbers of `Spec ℤ` are not traces; the zero motive has order exactly zero | `not_isTrace_vonMangoldt`, `not_isTrace_mertens`, `not_isTrace_primeCounting`, `lagModule_traceClassAt_zero`, `lagModule_not_traceClassAt_one` |
| The archimedean fibre is forced by its Lefschetz numbers; the glued Lefschetz numbers are not a trace | `frobTrace_evenJets`, `archimedeanFibre_forced`, `not_isTrace_gluedLefschetz`, `not_isTrace_pointCount` |
| No family of distinct zeros is integral, whatever their real parts; Kronecker for locally finite modules in the strip without a chain condition | `eq_zero_of_integral_trace_of_distinct_xi_zeros`, `mergedWeight_eq_zero_of_integral_locallyFinite`, `eq_zero_of_integral_trace_of_xi_zeros` |
| The symmetries of the zeros are the two involutions | `preservesXiDivisor_affine_iff`, `preservesXiDivisor_antiaffine_iff` |
| The zeros contain no class of one Frobenius: `Σ_n ‖ζ(ρ + inT)‖/‖ρ + inT‖ = ∞` on every vertical progression in the strip | `endpoint_limits_eq_of_summable_fourierCoeffOn`, `integral_ladderSum`, `fourierCoeffOn_ladderDefect`, `tsum_jumpTerm_ne_zero`, `not_summable_norm_riemannZeta_div`, `exists_riemannZeta_ne_zero_progression`, `not_forall_xi_progression`, `exists_conjugate_not_zero`, `exists_zero_localFactor_not_zero`, `exists_curve_zero_not_zero` |
| No sequence of zeros approaches a class of one Frobenius: the zeta values along a progression are in `ℓ²` and not in `ℓ¹`, and an `ℓ²` ladder of zeros would make them summable | `summable_sq_norm_integral_mul_exp`, `summable_sq_norm_riemannZeta_div`, `norm_integral_ladderKernel_taylor_le`, `summable_norm_riemannZeta_div_of_ladder`, `not_cofinite_riemannZeta_eq_zero_of_sq_summable`, `not_cofinite_xi_eq_zero_near_class` |
| Over `ℤ` every mode is its own conjugacy class; the module is semisimple without multiplicity | `re_eq_of_commute`, `eq_of_commute_two_three`, `eq_conj_of_semilinear_commute`, `single_mem_of_stable` |
| Elimination needs only an attained top | `not_small_on_thick_of_circle_mode`, `norm_le_one_of_thick_bounded_levelSums`, `curveDatum_unitary_of_thick_bounded_trace` |
| A mode accessible from infinity is eliminated; RH from a bounded lag along one tower and one accessible off-line zero | `towerResolvent_eq_levelSeries`, `analyticAt_levelSeries`, `analyticAt_towerResolvent`, `merged_eq_zero_of_accessible`, `merged_eq_zero_of_radially_visible`, `wolff_node_not_accessible`, `lag_not_small_of_accessible`, `riemannHypothesis_of_lag_bounded_of_accessible` |
| On the flow the weight filtration of a locally finite module is its growth filtration; for the zero motive it reads the abscissa | `analyticAt_flowMellin`, `flowMellin_eq_towerResolvent`, `mergedWeight_eq_zero_of_flow_bound`, `flow_bound_iff`, `zeroMotive_flow_bound_iff` |
| RH is an attained abscissa plus one crude count on a thick set of levels | `lag_not_small_of_attainedTop`, `lag_bound_iff_of_attainedTop`, `riemannHypothesis_iff_attainedTop_and_thick_lag_bounded`, `riemannHypothesis_iff_attainedTop_and_thick_primeDeviation`, `riemannHypothesis_or_not_attainedTop` |
| The index is semicontinuous, at any index | `zeros_subsingleton_of_tendstoLocallyUniformly`, `encard_zeros_le_of_tendstoLocallyUniformly`, `im_eq_zero_of_limit_of_indexOne`, `riemannHypothesis_iff_limit_of_indexOne` |

All are unconditional.

## 10. Calibration

| Model | Present | Reading | Lean |
|---|---|---|---|
| Curves over `𝔽_q` | finite rank, functional equation | bounded traces on a thick set give unitarity; the top is attained because the rank is finite | `curveDatum_unitary_of_thick_bounded_trace` |
| Zeros of a curve attached to one eigenvalue | one Frobenius | a full class `ρ + 2πik/log q`; not all of its points are zeros of `ξ` | `exists_curve_zero_not_zero` |
| Eisenstein constant term, `Y ≥ 1` | functional equation, pole, reality, `ζ ≠ 0` on `Re ≥ 1` | index one: `c`-pure; pure for `Y ≤ 4πe^{−γ}`; one real exceptional parameter in `(½, 1)` for `Y > 4πe^{−γ}`, which persists and moves to `1` | `lineLaw`, `exists_exceptionalParameter_iff`, `exceptionalParameter_mono` |
| Half-shifts `ξ(s + ½) ± ξ(s − ½)` | functional equation, reality, `ζ ≠ 0` on `Re ≥ 1`, no pole | index zero: pure, unconditionally; the same over every fixed part with zeros in the closed strip | `re_eq_half_of_xi_halfShift_eq_zero`, `halfShift_ne_zero` |
| Family over a finite divisor in the closed strip | functional equation, reality, one defect | every member satisfies the line law; the divisor may contain any quartet off the line | `exists_fixedPart_with_lineLaw`, `divisorPencil_lineLaw` |
| Family over a divisor with a non-real point right of `Re = 1` | functional equation, reality | the line law fails for all large `Y` | `exists_nonreal_zero_pencil_of_zero_right`, `divisorPencil_lineLaw_iff` |
| `cosh` model of a configuration `W` | functional equation, order one, defect of degree `card W` | vanishes right of the line exactly on `W`: every index is attained by every configuration; one quartet is a real defect of degree two with a non-real pair | `index_attained`, `indexTwo_admits_nonreal_pair` |
| Archimedean fibre | modes `−2k`, weight one | trace class at the Frobenius `2` of every order, not at `1`; determined by its trace `n²/(n² − 1)` | `evenJets_traceClassAt`, `evenJets_not_traceClassAt_one`, `archimedeanFibre_forced` |
| `Λ`, Mertens, `π`, the point count of `SurfaceOfSpecZ` | Euler product or integer jumps | not a trace of any order at any Frobenius | `not_isTrace_vonMangoldt`, `not_isTrace_mertens`, `not_isTrace_primeCounting`, `not_isTrace_pointCount` |
| Golden datum | integer traces, functional equation, finite rank | traces unbounded on every thick set; integrality at positive weight forces nothing | `InfiniteRankWeilTheory.goldenDatum_not_thick_trace_bounded` |
| Limit-periodic tower | purity, trace class, integer level sums | infinite rank: one Frobenius does not bound the rank | `exists_pure_integral_tower_of_infinite_rank` |
| Wolff module | distinct bounded modes, positive weights, trace class of every order, integer traces at every Frobenius | not Tate: weight at `5/4`; its weights have an ascending chain, so Kronecker, uniqueness and the growth filtration do not apply; as a tower its level sums vanish from level one on and no isolated node is accessible from infinity: a wall | `exists_integral_traceClass_module_not_tate`, `wolff_not_weightsWellFounded`, `wolff_node_not_accessible` |
| Wolff tower | positive weights, both symmetries, bounded level sums | every mode off the circle; its top is not attained, so elimination does not apply | `InfiniteRankWeilTheory.exists_tower_bounded_without_wellFounded` |
| Integer-norm one-off | Euler product, integer norms | ZAL holds and AAL fails: an isolated top, which is attained | `InfiniteRankWeilTheory.integerNormOneOff_zal_not_aal` |
| Approaching Euler product | Euler product, integer norms, linear counting | a top pair over infinitely many zeros approaching the line: landing fails, the top is attained | `ArithmeticPositiveDuality.ApproachingIntegerNormEulerProduct.exists_approaching_integer_norm_euler_product` |
| Approaching `cosh` model | functional equation, reality, order one | zeros approach the line without landing | `InfiniteRankWeilTheory.exists_approachingModel_not_landingLaw` |
| Non-tempered pair | functional equation, Euler product | every critical zero `ρ` gives the zeros `ρ ± a` off the line | `RHTower.xi_symmetricShiftProduct_criticalZero_pair_off_critical_line` |
| Cosine and heat towers of `ξ` | functional equation, reality | the width contracts along the tower | `RHTower.DeBruijn.cosineShift_zeros_im_sq_le` |
| Surfaces with a small eigenvalue | self-adjointness | `c`-pure with real exceptional parameters, as an index-one object | `HTGeometry.selbergSmallEigenvalue_offCritical` |
| Zeros of `ξ` | everything | symmetries `1, ι, c, ιc`; no class of one Frobenius and no sequence within `ℓ²` of one; no integral constituent of trace class of order two, whatever the real parts; order zero with the lag weights; with an attained abscissa one tower reads it | `preservesXiDivisor_affine_iff`, `exists_conjugate_not_zero`, `eq_zero_of_integral_trace_of_distinct_xi_zeros`, `lagModule_not_traceClassAt_one`, `lag_bound_iff_of_attainedTop` |

## 11. Traps

| Trap | Truth |
|---|---|
| The line law needs the spectral theory of the modular surface | it needs `ζ ≠ 0` on `Re ≥ 1`, the functional equation, the pole and reality |
| The line law says something about the zeros of `ζ` in the strip | it holds over every fixed part with zeros in the closed strip; it sees the strip and not the line |
| A family over `ξ` whose members are all pure says something about `ξ` | the half-shifts `G(s + ½) ± G(s − ½)` are pure over every fixed part with zeros in the closed strip |
| An index bound gives purity | it gives `c`-purity; the real exceptional parameter exists exactly for `Y > 4πe^{−γ}` |
| Parity extends to any finite index | index `κ` allows `κ/2` non-real pairs, and the `cosh` models attain them |
| The index law needs the roots of the Blaschke product | one Schur step and the reflection of polynomials suffice |
| Elimination needs finitely many modes above every radius | it needs the top to be attained; modes may accumulate at the top circle from inside and fill it |
| An attained top is automatic | Wolff towers: positive weights, bounded level sums, top not attained |
| Without an attained top a crude count along one tower says nothing | on all levels it excludes every off-line zero whose mode is accessible from infinity; only a wall of modes protects a zero, and walls exist (`wolff_node_not_accessible`) |
| Every zero of the defect counts in the index | only those right of the line; zeros left of the line become Blaschke factors |
| A crude count along one tower only gives AAL | with an attained abscissa it is the zero-free half-plane |
| Integer traces bound the rank | only at weight zero; the limit-periodic tower is pure, integral and of infinite rank |
| Integer traces at all integers are compatible with modes in the strip | in trace class of order above the weight they force Tate twists |
| Trace class means finite weighted rank | that is trace class at the identity; the archimedean fibre is of trace class at the Frobenius `2` only |
| The explicit formula is a trace formula | `Λ`, the Mertens function and `π` are not traces of any order at any Frobenius, with any modes |
| One prime sees a mode | only modulo `2πi/log p`; two primes separate |
| Distinct modes are needed to read weights from growth | repeated modes merge along the fibres; the merged weights are determined |
| The zero set might have a hidden symmetry | its affine and anti-affine symmetries are `1, ι, c, ιc`, and every Frobenius-equivariant linear map of the module over `ℤ` is diagonal |
| An off-line zero might come with its whole vertical progression, as a zero of a column of one prime does | no vertical progression in the strip consists of zeros, at any real part; the periodicity dichotomy of `ζ` is RH itself (`periodicityDichotomy_zeta_iff_riemannHypothesis`) |
| Zeros might still follow a class of one Frobenius approximately | no two-sided sequence of zeros is within a square summable distance of a vertical progression in the strip (`not_cofinite_xi_eq_zero_near_class`) |
| The periodization argument belongs to the critical line | with the polar part removed it gives the Fourier coefficients `−ζ(s_n)/(P s_n)` at every real part of the strip |
| Kronecker needs distinct modes | the merged weights of an integral module vanish off the Tate twists |
| For the zeros of `ξ` integrality needs a chain condition on their real parts | the zeros are locally finite and lie in the strip: integrality at the integers reaches the flow, where no chain condition is needed |
| The chain condition on the weights is a technical hypothesis | without it an integral trace-class module has trace `1` at every Frobenius and a visible mode `5/4` |
| The chain condition, the attained top and accessibility are properties of the zeros | they are costs of sampling the flow at discrete levels; on the whole flow a locally finite module needs none of them |
| The line law over a fixed part needs a bound on the fixed part | it holds over every limit of finite divisors in the closed strip; the bound passes to the limit |
| A family proves the purity of its fixed part | without a measure a family is pure over an impure fixed part; under a measure the fixed part is the mean, seen only by moments of the full traces |
| Weights can appear in a limit | zeros of a limit are limits of zeros; they can only leave |

## 12. What the field reduces purity to

Each mechanism reduces purity to one statement whose strength is fixed by a theorem.

| Statement | Proved relation | Proved boundary |
|---|---|---|
| **A crude count on the whole flow** | equivalent to the bound on the zeros, with no further input (`zeroMotive_flow_bound_iff`) | at the discrete levels of one tower a wall of modes can hide a zero (`wolff_node_not_accessible`) |
| **A crude count on a thick set of levels of one tower** | with an attained abscissa it is equivalent to RH (`riemannHypothesis_iff_attainedTop_and_thick_lag_bounded`, in primes `riemannHypothesis_iff_attainedTop_and_thick_primeDeviation`) | without it there remain two worlds: RH, or an abscissa no zero attains (`riemannHypothesis_or_not_attainedTop`) |
| **The abscissa is attained** | follows from ZAL when RH fails (`RHTower.exists_attainedTop_of_zerosApproachLine`); makes one tower read the abscissa exactly (`lag_bound_iff_of_attainedTop`); may be replaced by one off-line zero whose mode in the tower is accessible from infinity (`riemannHypothesis_of_lag_bounded_of_accessible`) | cannot be dropped for towers (`InfiniteRankWeilTheory.exists_tower_bounded_without_wellFounded`) |
| **Index at most one for `ξ`** | equivalent to RH, also as a limit of index-one objects (`riemannHypothesis_iff_limit_of_indexOne`) | an index `κ` leaves `κ/2` non-real pairs and every configuration attains it (`two_mul_encard_upper_zeros_le`, `index_attained`); proved for the Eisenstein constant term, where the one defect is the pole (`constantTerm_indexOne`) |
| **A family over `ξ`** | its line law holds (`lineLaw`); under a measure the fixed part is bounded by the moments of the full traces (`fixedPart_norm_le_one_of_mean_bounded`) | the line law holds over every fixed part in the closed strip (`exists_fixedPart_with_lineLaw`, `pencil_lineLaw_of_tendsto`), and the moments contain the fixed part itself (`integral_norm_sq_fixedPart_add`): no reduction |
| **Integrality** | forces Tate twists in trace class at any Frobenius, with modes repeated at will (`mergedWeight_eq_zero_of_integral_trace`) | the zero motive has order exactly zero (`lagModule_not_traceClassAt_one`) and its Lefschetz numbers are not traces (`not_isTrace_vonMangoldt`) |
| **Transport** | no rigid form exists: the divisor has the two involutions (`preservesXiDivisor_affine_iff`), the module over `ℤ` only diagonal equivariant maps (`eq_of_commute_two_three`), and no class of one Frobenius lies in the zero set or is approached in `ℓ²` by zeros (`exists_conjugate_not_zero`, `not_cofinite_xi_eq_zero_near_class`) | the approximate form is AAL (`InfiniteRankWeilTheory`, `ZeroConfigurationGeometry`) |

## 13. Context

| Neighbour | Interface |
|---|---|
| InfiniteRankWeilTheory | thick sets, lag weights and their positivity, `cosh` models, the golden and Wolff towers; IRP proves its elimination step with an attained top in place of well-foundedness |
| ArithmeticCastelnuovoSeveri | `CurveDatum` |
| RHTower | `ξ`, its reality and orders, `ξ'(1) = Λ₀(1)/2` (`hasDerivAt_xi_one_archimedeanGenusZeroSum`), the Lagarias–Suzuki modulus theorem, zero counts, the divergence of `Σ 1/‖ρ‖`, sphere domination (`exists_zero_of_sphere_domination`), the lag function, its growth along the whole flow and its attained-top dichotomy along full progressions, the line law by Maass–Selberg (`lagariasSuzuki_ne_zero`, `Y > 1`, strip); the Laplace representation of `ζ` by the fractional part, the exponent monoid of a period, and Putnam's theorem on the critical line for one-sided progressions (`exists_riemannZeta_critical_ne_zero`); IRP proves the two-sided divergence at every real part and removes the hypothesis of `RHTower.periodicityDichotomy_zeta_iff_riemannHypothesis` |
| BlackHoleRingdown | the inner bound `‖ξ(2w)‖ ≤ ‖ξ(1+2w)‖`, the location of the zeros; no sequence of zeros within an `ℓ²` perturbation of a one-sided progression on the critical line (`not_eventually_riemannZeta_eq_zero_of_sq_summable`) |
| HTGeometry | simultaneous Dirichlet approximation, independence of prime logarithms, Selberg's spectral parameter |
| FiniteFreeProbability | Hurwitz for entire functions; the Jensen tower |
| SurfaceOfSpecZ | the point count `Λ(n) + 1 + 1/(n² − 1)` of the Frobenius; IRP shows it is not a trace and splits it into a forced archimedean module and the finite contacts |
| AbsoluteGeometryOfSpecZ | the Λ-square and its missing diagonal |
| HyperbolicArakelovTheory | the defect of the orientation cover is the Mertens function; IRP shows it is not a trace |
| ArithmeticWeightTheory | the arithmetic families (gauge torus, characters, vertical line, Hecke eigenforms) and their orthogonality: the computed moments are those of the variable part; IRP supplies the tower statements for any family: the fixed part is the mean, the excess of the second moment, and the strip of a family without a measure |
| ZeroConfigurationGeometry | the three atoms and the abscissa laws |
| SignFreePurityMechanisms | separation by the height; the price of Frobenius lifts: an endomorphism of `ℤ[X]` with zero derivative is an evaluation, and the cost of vanishing at primes is the product formula with equality |
| SelbergClass, ArithmeticPositiveDuality, ArithmeticKunnethTheory | the degree gap; the relocation obstruction (a factor tending to `1` on a vertical line loses the Dirichlet series); the tensor moment bound in finite rank, which amortization extends to towers with an attained top |

## 14. Success criteria and contributions

IRP succeeds when each question of §6 has a theorem-level answer (a positive theorem, or a sharp
no-go with its positive survivor), each test of §7 is met by a theorem, and each row of the dictionary
names its price. The tables of §5, §6 and §7 name the theorem for each entry.

A **contribution** is unconditional; states which structures it uses (functional equation, Euler
product, pole, reality, integrality); says on which calibration models it holds and fails; says
whether it is a statement in law or at a point and, if it is a conversion, names its price; and is not
a restatement of an RH-equivalent already in the corpus.

## 15. Big picture

Four finite-rank mechanisms survive at infinite rank as theorems, each with a sharp boundary.

*The index.* A completed function whose Hermite–Biehler half has a defect with `κ` zeros right of the
line has at most `κ` zeros on each side of the line, and reality leaves at most `κ/2` non-real pairs; every
configuration attains the bound. The pole of `ζ` is one defect: the constant term of the Eisenstein
series is `c`-pure for every `Y ≥ 1`, from `ζ ≠ 0` on `Re ≥ 1` alone, pure up to `Y = 4πe^{−γ}`, and
carries one real exceptional pair above. For `ξ` itself an index bound of one is RH.

*Integrality.* Bounded integer traces of one Frobenius force finite rank and torsion at any rank. The
Frobenii at all integers force Tate twists as soon as the module is of trace class, at any Frobenius,
of an order above its weight; one Frobenius at positive weight forces nothing.

*The trace formula.* Traces determine a trace-class module whose weights have no ascending chain,
with repeated modes, and its weight filtration is its growth filtration. On the whole flow this
holds for every locally finite module with no condition on the weights: the chain condition, the
attained top and accessibility are costs of sampling the flow at discrete levels. The archimedean fibre of the glued square is such a module and
is forced by its Lefschetz numbers. The finite contacts are not: a trace is smooth at infinity and an
Euler product jumps. So the zero motive lies outside trace class of every positive order, and its
Lefschetz formula is an identity of distributions.

*Elimination.* A crude bound on a thick set of levels of one tower excludes every weight above it
as soon as the top weight is attained, at any rank and with any number of modes on a circle. The
infinite-rank replacement of "finitely many eigenvalues" is closedness of the weight set at its top,
not well-foundedness of the tower. Below the top a second mechanism acts on all levels: the
resolvent continues along any path free of modes, and a mode above the growth rate that is
accessible from infinity carries no weight. Only a wall of modes protects a mode.

Two mechanisms do not survive. Conjugacy has no rigid form: the zero divisor has the two involutions
and nothing else, and over `ℤ` every Frobenius-equivariant map of the module is diagonal, so each
zero is alone in its class. Over one Frobenius the conjugates of a zero are its vertical
progression, and no progression consists of zeros or is approached by zeros in `ℓ²`: the zeta
values along it are square summable against `1/n` and not summable. A family proves nothing about its fixed part: without a measure the
line law holds over every configuration of zeros in the closed strip, and under a measure the
moments that would bound the fixed part contain it with mass one. What a proof of purity over `ℤ` must
supply is therefore one of: an index bound for `ξ`, or a crude count along one tower together with an
attained abscissa or one accessible off-line zero.
