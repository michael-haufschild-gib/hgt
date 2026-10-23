# Nine-field research programme: 250 significant contributions

- **ID:** nine-fields-250-20261023
- **Stage:** 1-in-progress
- **Type:** PROGRAMME LEDGER
- **Source:** user goal of 2026-10-23 (APT, BiScale, THIM, BVI, ACT, SRT, AIP, ACCE, SSIC).
- **Statement:** 250 significant, unconditional, Lean-audited contributions to the nine programmes.

## Rules in force

All nine READMEs read in full; they are read-only. No hgtl7 skill. Corpus search tool before
Mathlib and before rg/grep. Unconditional Lean only; one foreground `lake --old env lean` at a time;
no full or umbrella builds; wire finished leaves into their umbrella; no heartbeat raises; no
computations. Not counted: constant improvements, no-gos alone, renamings, proof lemmas.
Missing dependency oleans are built one at a time with `lake --old env lean -o` (CLAUDE.md rule 4).

## Accepted contributions: 6 / 250

1. THIM — the horizon limit commutes with the receiver exactly from half damping (candidate 1).
2. THIM — the universal hyperplane on the whole critical Wiener algebra (candidate 3).
3. THIM — a paid receiver continues the Dirichlet series across its abscissa; prime-mean quantization (candidate 2).
4. THIM — the half-damped hyperplane law has an exact logarithmic threshold; little-o pole law (candidate 4).
5. THIM — the half-damped receiver is the logarithmic energy of the partial pole sums (candidate 5).
6. THIM — critical Wiener perturbations of the smooth power have uniformly paid rows (candidate 6).

## Candidate 1 (THIM): the horizon limit commutes with the receiver exactly from half damping

**Open problem (THIM README §5, the parity pair):** whether signed rows can be uniformly bounded
while their pointwise limit is unpaid, or conversely.

**Theorem (paper proof complete).** On `𝒞(1, ε)`, `ε ≥ 0`: "rows uniformly paid ⇔ weight paid" holds
for every weight iff `ε ≥ 1/2`.
1. Every weight: uniformly bounded dyadic rows ⇒ paid (Fatou in the weight at fixed cutoff).
2. `ε > 1/2`: weight and all rows paid by one constant. `ε = 1/2`: row energy `≤ 2E + 17K²`
   (drift `Nτ_N² ≤ 4K²`, sawtooth `≤ 3K√N`).
3. `0 ≤ ε < 1/2`: explicit paid `c ∈ 𝒞(1, ε)` with unbounded row receivers (lacunary windowed
   dipoles `N = 2^{Lt}`, `w = 2^{Mt}`, cutoff `2^{Qt}`).

**Lean:** `TransHorizonIncidenceMechanics/TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping.lean`
(`horizonLimit_commutes_with_receiver_iff`). Status: compiled, axioms `propext`, `Classical.choice`,
`Quot.sound`; wired into the THIM umbrella.

## Candidate 2 (THIM): a paid receiver continues the Dirichlet series across its abscissa

**Theorem (paper proof complete).** If `Σ|c(d)|d^{-θ} < ∞` for `θ > a` and the receiver of `c` is
paid, then `Φ(s) = Σ_n A(n)(n^{-s} − (n+1)^{-s})` is holomorphic on `Re s > 1/2` and equals
`ζ(s)(C(s) − m)` on `(a, 1)`. For `1/2 < a < 1`: `C` is Lipschitz at `a`, and any exact power order
`|C(a+u) − L| ≍ u^α`, `α > 0`, is a positive integer.

**Application (quantization).** Below half damping a completely multiplicative `±1` pattern whose
flipped primes have Dirichlet density `ρ` is unpaid unless `ρ ∈ {1/2, 1}` (`Σ f(n)n^{-w} ≍
(w−1)^{2ρ−1}`). Not covered by the pole law, which gives only boundedness (`ρ ≥ 1/2`).

**Lean:** `TransHorizonIncidenceMechanics/APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa.lean`
(`exists_holomorphic_continuation`, `exists_abs_dirichletSeries_sub_le_mul`,
`exists_nat_eq_of_rpow_bounds_at_abscissa`, `not_receiverBounded_of_primeMean`,
`not_receiverBounded_of_flippedDensity`). Status: compiled, axioms `propext`, `Classical.choice`,
`Quot.sound`; wired into the THIM umbrella. General form: a paid completely multiplicative `|f| ≤ 1`
weight below half damping has logarithmic prime mean `ν ∈ {0, −1}`.

## Candidate 3 (THIM): the universal hyperplane on the whole critical Wiener algebra

**Theorem (paper proof complete).** `0 < ε < 1/2`, `Σ_j |k(j)| j^{-1/2} < ∞`: `k ⋆ d^{-ε}` is paid
iff `K(1 − ε) = 0`. Finite kernels were known (`receiverBounded_dirichletConv_unit_iff`).
Sufficiency: `k = Σ_j k(j)(δ_j − j^{-(1−ε)}δ_1)`; each pole-free dilation `b_j` has `E(b_j) ≤ C/j`
(below `j` by the convolution law and `|A_q(n)| ≤ Cn^{1−ε}`; beyond `j` by the sharp hyperbola bound
`|A_c(n)| ≤ Σ_{d≤D}|c(d)| + 4BnD^{-1-ε}` at `D = ⌊√(jn)⌋`); Minkowski over truncations and continuity
of the energy at fixed cutoff. No divisor-problem asymptotic is needed.

**Lean:** `TransHorizonIncidenceMechanics/CriticalWienerPerturbationsOfTheSmoothPowerAreDecidedAtThePole.lean`
(`receiverBounded_dirichletConv_unit_iff_critical`). Status: compiled, axioms `propext`,
`Classical.choice`, `Quot.sound`; wired into the THIM umbrella.

## Candidate 4 (THIM): the half-damped hyperplane law has an exact logarithmic threshold

**Theorem (proved).**
1. Little-o pole law: `Σ_d |c(d)| d^{-θ} < ∞` (`θ > 1/2`) and paid ⇒ `√u |C(1/2+u) − m| → 0`
   (head of the Mellin pairing `O(1)`, tail `√(tail energy)·O(u^{-1/2})`, `|ζ(σ)| ≥ 1`).
2. At `ε = 1/2`, `E(b_j) = O((1 + log j)/j)`; on `Σ_j |k(j)| j^{-1/2} √(1 + log j) < ∞`:
   `k ⋆ d^{-1/2}` paid ⇔ `K(1/2) = 0`.
3. `k = Σ_r 2^{-(r+1)} J_r^{1/2} δ_{J_r} − δ_1`, `J_r = 2^{4^{r+1}}`: in every `(1 + log j)^α`-weighted
   algebra, `0 ≤ α < 1/2`, `K(1/2) = 0`, unpaid (probe `u_R = 4^{-(R+1)}`, `√u_R |C| ≥ 1/2`).
4. Hyperplane law on the critical Wiener algebra ⇔ `ε < 1/2`.

**Lean:** `TransHorizonIncidenceMechanics/TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold.lean`
(`tendsto_sqrt_mul_abs_dirichletSeries_sub_mean`, `receiverBounded_dirichletConv_unit_half_iff`,
`not_receiverBounded_dirichletConv_lacunaryKernel`, `criticalWiener_hyperplaneLaw_iff_lt_half`,
`halfDamped_hyperplaneLaw_logarithmic_threshold`). Status: compiled, axioms `propext`,
`Classical.choice`, `Quot.sound`; wired into the THIM umbrella.

## Candidate 5 (THIM): the half-damped receiver is the logarithmic energy of the partial pole sums

**Theorem (proved).** For every `k` with `Σ_j |k(j)| j^{-1/2} < ∞` and `S_k(n) = Σ_{j≤n} k(j) j^{-1/2}`:
`|√E_T(k ⋆ d^{-1/2}) − 2|Z| (Σ_{n≤T} S_k(n)²/(n+1))^{1/2}| ≤ B` for all `T`, with
`Z = lim (Σ_{d≤N} d^{-1/2} − 2√N) ≤ −1`; hence paid ⇔ `Σ_n S_k(n)²/(n+1) < ∞`. Exact criterion for
every critical Wiener kernel (answers THIM §5 "criteria for individual kernels beyond absolute classes").
Inputs: hyperbola asymptotic `A_q(n) = 2Z√n + O(n^{1/4})`, convolution law, Minkowski over dilations.

**Lean:** `TransHorizonIncidenceMechanics/TheHalfDampedReceiverIsTheLogarithmicEnergyOfThePartialPoleSums.lean`
(`abs_halfRemainder_le`, `abs_sqrt_weightPronicEnergy_dirichletConv_unit_half_sub_le`,
`receiverBounded_dirichletConv_unit_half_iff_summable_partialPoleSum`). Status: compiled, axioms
`propext`, `Classical.choice`, `Quot.sound`; wired into the THIM umbrella.

## Candidate 6 (THIM): the convolution structure prevents the dipole obstruction

**Theorem (proved).** For `0 < ε < 1/2` and `Σ_j |k(j)| j^{-1/2} < ∞`: the dyadic rows of `k ⋆ d^{-ε}`
(own means) are uniformly paid ⇔ `k ⋆ d^{-ε}` paid ⇔ `K(1−ε) = 0`. Contrast: on `𝒞(1, ε)` the
commutation fails below `1/2` (contribution 1). Answers, for this class, THIM §5 "which structure
prevents the dipole obstruction". Mechanism: rows of pole-free dilations have energy `O(1/j)` uniformly
in the horizon; finite decomposition `row(k⋆q) = Σ_{j≤N} k(j) row(b_j) + P_N row(q)` with
`|P_N| ≤ N^{-(1/2−ε)} ‖k‖` paying `‖row(q)‖ = O(N^{1/2−ε})`.

**Lean:** `TransHorizonIncidenceMechanics/CriticalWienerPerturbationsOfTheSmoothPowerHaveUniformlyPaidRows.lean`
(`exists_weightPronicEnergy_dyadicRow_poleFreeDilation_le`, `rows_bounded_of_critical`,
`rows_bounded_iff_receiverBounded_dirichletConv_unit`, `rows_bounded_iff_dirichletConv_unit_poleValue_eq_zero`).
Status: compiled, axioms `propext`, `Classical.choice`, `Quot.sound`; wired into the THIM umbrella.

## Checked and not pursued

- Pole law for kernels absolutely convergent at the abscissa: done by another agent
  (`APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa.lean`).
- Exact Plancherel law `E(c) = lim (1/2π)∫|ζ(σ+it)(C(σ+it)−m)|²/|σ+it|² dt`: the Báez-Duarte
  transform in receiver language; kept only as motivation.
