# Kubalalika weighted near-diagonal tail: the Lean build

- **ID:** `kubalalika-weighted-tail-lean`
- **Stage:** 1-in-progress
- **Type:** LEAN INFRASTRUCTURE
- **Opened:** 2026-08-23
- **Blocks:** `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/kubalalika-parity-weighted-near-diagonal-tail.md`

## Target

```lean
theorem weighted_near_diagonal_tail_isBigO :
    ∃ C : ℕ, (fun T : ℝ => ‖E_Λ T‖) =O[atTop] fun T => T ^ (53/54 : ℝ) * (Real.log T) ^ C
```
with `E_Λ(T) = Σ_{V ≤ m ≤ T(1+ε)} Λ(m) Σ_{R ≤ r ≤ εm, r ≡ m (2)} e(T log(1+r/m))/r`,
`ε = T^{-1/4}`, `V = T/((1+ε)log²T)`, `R = T^{1/4}`.

## Why the sources cannot simply be cited

The card's `(2)`, `(3)`, `(4)` are Granville--Ramaré Thm 9/9' and Babu--Sankaranarayanan Thm 1,
transferred to the reciprocal phase by the card's stability lemma.  Formalising means REPROVING
them: Vaughan's identity, then derivative tests on each one-variable descendant phase.  The corpus
already owns the derivative test and, crucially, the exact algebra that makes every descendant
phase reciprocal.

## What is already Lean-closed (2026-08-23)

- `RHTower/Sieve/SecondDerivativeTest.lean` — `second_derivative_test'`:
  `‖Σ_{n<N} e(g(x₀+n))‖ ≤ 8Nh√λ + 12/√λ` when `λ ≤ g'' ≤ hλ`.  (Corpus, pre-existing.)
- `RHTower/NearDiagonalPhaseCurvature.lean` … `NearDiagonalInnerSum.lean` — the whole dyadic chain
  for `F_{T,r}`, ending in
  `‖Σ_{A≤m<B} e(F_{T,r}(m))‖ ≤ 2500√(Tr/(36πA)) + 22√(36π/(Tr))·√(B³)`.  (Corpus, pre-existing.)
- `RHTower/Sieve/VaughanIdentity.lean` — Vaughan's identity as a ring identity in
  `ArithmeticFunction ℝ`, plus the vanishing of the type-II second factor below `V`.
- `RHTower/Sieve/DilatedNearDiagonalSum.lean` — `F_{T,r}(d·u) = F_{T,r/d}(u)`, so every TYPE-I
  inner sum is a near-diagonal sum at the scaled offset.  Type I needs no new derivative test.
- `RHTower/Sieve/ReciprocalPhaseStability.lean`, `VonMangoldtParityCorrection.lean`,
  `PSeriesTailAboveCutoff.lean`, `NearDiagonalOffsetBookkeeping.lean` — the stability lemma, the
  parity correction `Σ_{m ≤ N, 2|m} Λ(m) ≤ log N`, and the `r`-tail bookkeeping.

### New this session

- `RHTower/Sieve/CurvedPhaseBlockSum.lean` — **the chain, abstracted**.  `CurvedPhase φ φ' φ'' Y M₀`
  asks only for `Y/(36πM³) ≤ φ'' ≤ 90·Y/(36πM³)` on every dyadic block `[M,2M]` with `M ≥ M₀`, and
  yields
  ```
  ‖curvedSum φ A B‖ ≤ 2500√(Y/(36πA)) + 22√(36π/Y)·√(B³).
  ```
  The geometric collapse and the dyadic cover are phase-independent and are reused from the
  near-diagonal modules.
- `RHTower/Sieve/DifferencePhaseCurvature.lean` — **the algebraic identity that makes type II work**:
  ```
  F''_{s₁}(u) − F''_{s₂}(u) = (T/2π)·(s₁−s₂)(2u+s₁+s₂)/((u+s₁)²(u+s₂)²),
  ```
  because `s(2u+s) = (u+s)² − u²` makes the cross terms cancel exactly.  Hence
  `CurvedPhase (F_{s₁} − F_{s₂}) … (T(s₁−s₂)) (4s₁)`: the difference phase has the SAME reciprocal
  curvature profile, at scale `T(s₁−s₂)`.  The constant `4s₁ ≤ M` is what keeps the curvature ratio
  under the `90` that `block_algebra` is calibrated for — `(2+1/4)⁵ = 57.7 ≤ 90`.
  The near-diagonal phase itself is registered as a `CurvedPhase` too.
- `RHTower/Sieve/BilinearCauchySchwarz.lean` — Cauchy--Schwarz on the outer variable and the exact
  correlation expansion `Σ_d ‖Σ_m b_m z_{d,m}‖² = Σ_{m₁,m₂} b_{m₁} \bar b_{m₂} Σ_d z_{d,m₁}\bar z_{d,m₂}`,
  plus its norm form.
- `RHTower/Sieve/TypeIICorrelation.lean` — the two identities are glued:
  `Σ_{d} e(F_{T,r}(m₁d)) \overline{e(F_{T,r}(m₂d))} = curvedSum (F_{r/m₁} − F_{r/m₂}) A B`,
  and the resulting bound
  ```
  ≤ 2500√(T(r/m₁ − r/m₂)/(36πA)) + 22√(36π/(T(r/m₁−r/m₂)))·√(B³).
  ```

## Remaining layers

- `VC3` assemble the type-II bound: diagonal `m₁ = m₂`, off-diagonal via `norm_sum_correlation_le`,
  divisor-bounded coefficients, and the sum over pairs.
- `VC4` assemble the type-I bound from `norm_dilated_nearDiagonalSum_le` and a divisor-sum bound.
- `VC5` combine through Vaughan into `S_r(I)` for a dyadic block `I ⊂ [M,2M]`.
- `VC6` dyadic assembly over `M` and summation over `r` to the card's `T^{53/54}`.

## Log

- 2026-08-23 — Opened.  Five new modules; the type-II difference phase is now known to be a curved
  phase, which is the step the card's stability lemma only asserts asymptotically.

## The exponent budget, computed (2026-08-23) — the target is reachable, and better than `53/54`

Before building the Vaughan bookkeeping I checked what the corpus's OWN tools deliver, so that the
target is not chased with insufficient technology.  Write `X = Tr/2π`, `M` for the dyadic block of
the `m`-sum, `D` for the dyadic block of the long Vaughan variable, `H = M/D`, `h = |m₁−m₂|`.

**Available inner estimates.**
- Second-derivative test (curved-phase chain): `‖Σ_{[A,B)} e(φ)‖ ≪ √(Y/A) + √(B³/Y)`.
- Kuzmin--Landau (`Sieve/KuzminLandauInterval.lean`, now instantiated for the difference phase):
  when `|φ'| ≤ 1/2` on the whole range, `‖Σ‖ ≪ B²/Y + 1`.

**Type I.**  Inner sum at offset `r/d` over `k ∈ [M/d, 2M/d)` gives `√(Tr/M) + M^{3/2}/(√(Tr)·d)`;
summing over `d ≤ D₀ = UV` with logarithmic weights,

    type I ≪ L^C [ D₀·√(X/M) + M^{3/2}/√X ].

**Type II.**  After Cauchy--Schwarz on the long variable and the correlation expansion,
`Y = T|s₁−s₂| ≍ X h D²/M²`.  Kuzmin--Landau applies exactly when `h ≲ M²/X`; beyond that the
second-derivative test does.  Summing over `h ≤ H` and the `H` pairs at each `h`,

    |S₄|² ≪ L^C [ DM + M³/X + √X·M^{3/2}/D + M^{5/2}/√X ].

Cauchy--Schwarz may be taken on EITHER variable (the phase is `F(dm) = F(md)`, so the same lemma
serves both), which replaces `D` by `M/D`.  Taking the better of the two for each `D` gives
`min(A(D), B(D))` with `A ≤ B` exactly when `D ≥ √M`, so the maximum of the minimum over the whole
dyadic range `D ∈ (W, M/W]` is attained at BOTH endpoints and equals

    |S₄| ≪ L^C [ M/√W + X^{1/4}M^{1/4}√W + M^{5/4}X^{-1/4} ].

**Optimisation.**  With `U = V = W`, balancing `W²√(X/M)` against `M/√W` gives
`W = M^{3/5}X^{-1/5}` and

    S_r(I) ≪ L^C [ M^{7/10}X^{1/10} + M^{5/4}X^{-1/4} + M^{3/2}X^{-1/2} ].

**Assembly.**  With `M ≪ T`, `X = Tr/2π`, `R = T^{1/4} ≤ r ≤ εT = T^{3/4}`:

    Σ_r (1/r)·T^{4/5}r^{1/10}  ≪ T^{4/5}·(T^{3/4})^{1/10} = T^{7/8},
    Σ_r (1/r)·T·r^{-1/4}       ≪ T·(T^{1/4})^{-1/4}      = T^{15/16},
    Σ_r (1/r)·T·r^{-1/2}       ≪ T·(T^{1/4})^{-1/2}      = T^{7/8}.

    E_Λ(T) ≪ T^{15/16}·L^C.

`15/16 = 0.9375 < 53/54 = 0.98148…`, so the corpus's own toolkit proves a STRICTLY STRONGER bound
than the card claims, and the card's `(5)` follows.  Granville--Ramaré and
Babu--Sankaranarayanan are therefore not needed as inputs at all: what the card's stability lemma
transfers asymptotically, `DifferencePhaseCurvature.lean` and `DifferencePhaseKuzminLandau.lean`
prove EXACTLY, by the two cancellations

    F'_{s₁} − F'_{s₂} = −(T/2π)(s₁−s₂)/((u+s₁)(u+s₂)),
    F''_{s₁} − F''_{s₂} = (T/2π)(s₁−s₂)(2u+s₁+s₂)/((u+s₁)²(u+s₂)²).

Two side conditions must be carried through the formal proof and are satisfied in the whole range:
`r ≤ M` (offset below the block), and `λ = T r d²/(36π M³) ≤ 1` for the type-I inner sums, which at
the optimal `D₀ = W² = M^{6/5}X^{-2/5}` reads `T^{1/2} ≪ T^{5/8}`.

### New module

- `RHTower/Sieve/DifferencePhaseKuzminLandau.lean` — the first-derivative identity, its
  monotonicity and two-sided size bounds, and
  `norm_curvedSum_diffPhase_kuzminLandau : ‖curvedSum (F_{s₁} − F_{s₂}) A B‖ ≤ 75πB²/(16T(s₁−s₂)) + 1`
  whenever `4s₁ ≤ A` and `T(s₁−s₂)/(2πA²) ≤ 1/2`.  The band index is `m = −1`: the derivative is
  negative, monotone increasing, and confined to `[−1+δ, −δ]` with `δ = 8T(s₁−s₂)/(25πB²)`.
- `RHTower/Sieve/TypeIIEnergyBound.lean` — `norm_typeII_sq_le`, and the off-diagonal correlation
  bound in either order of the pair.
- `RHTower/Sieve/TypeIBound.lean` — `norm_typeI_le`, term by term through the dilation identity.

### Remaining

- `VC5a` divisor-square moment `Σ_{d ≤ D} d(d)² ≪ D L³` (for `Σ_d |a_d|²`).
- `VC5b` Abel summation to remove the `log k` weight from the `log ∗ μ_V` term.
- `VC5c` the convolution-to-double-sum rearrangement for the three Vaughan pieces.
- `VC6` the dyadic and `r` assembly with the optimisation above.

## VC5a and VC5c closed (2026-08-23)

- `RHTower/Sieve/DivisorSquareMoment.lean` — **`sum_card_divisors_sq_le : Σ_{n ≤ N} d(n)² ≤ N·H_N³`**,
  the coefficient moment the type-II Cauchy--Schwarz needs (`|a_d| ≤ 1 + d(d)`).  Elementary and
  fully reusable:
  - `d(n)² = Σ_{a,b ≤ N} 1_{a∣n}1_{b∣n}`, so the sum counts pairs;
  - `#{n ≤ N : a∣n ∧ b∣n} = N / lcm(a,b) ≤ N·gcd(a,b)/(ab)` (`Nat.Ioc_filter_dvd_card_eq_div`
    plus `Nat.gcd_mul_lcm`);
  - Gauss's identity `Σ_{g ∣ m} φ(g) = m` (`Nat.sum_totient`) as an indicator sum over `[1,N]`
    turns the `gcd` into a third factor: `Σ_g φ(g)·(Σ_{g∣a} 1/a)² = Σ_g φ(g)H_{N/g}²/g² ≤ H_N³`.
  Also lands `invSum`, `sum_inv_multiples_real` (`Σ_{n ≤ N, g∣n} 1/n = H_{N/g}/g`) and
  `divisors_eq_filter_Icc`.
- `RHTower/Sieve/DirichletConvolutionRearrange.lean` — **`sum_conv_mul_eq`**: for a block
  `I ⊆ [1, L]`,
  ```
  Σ_{n ∈ I} (f ∗ g)(n)·w(n) = Σ_{(d,k) ∈ [1,L]² , dk ∈ I} f(d)·g(k)·w(dk).
  ```
  The bijection is `⟨n,(d,k)⟩ ↦ (d,k)` between `I.sigma (·.divisorsAntidiagonal)` and the filtered
  product.  This is the single rearrangement all three Vaughan pieces go through.

Remaining: `VC5b` (Abel summation to strip the `log k` weight of the `log ∗ μ_V` term) and `VC6`
(the dyadic and `r` assembly).

## VC5b and the first Vaughan piece (2026-08-23)

- `RHTower/Sieve/AbelIcoWeight.lean` — `norm_sum_Ico_mul_le_of_bounded_partial_mono`: the corpus's
  `range`-form Abel inequality (`AbelIncreasingWeight.lean`, already owned) shifted to `[A, B)`.
  This is all `VC5b` needs; the weight `log k` is nonnegative and nondecreasing there.
- `RHTower/Sieve/TypeILogWeight.lean` — `norm_sum_log_ndExp_le`: the type-I inner sum WITH the
  logarithmic weight,
  ```
  ‖Σ_{k∈[A,B)} log k · e(F_{T,r}(k·d))‖ ≤ 2·(block bound at (A,B))·log(B−1),
  ```
  using that the block bound is increasing in the right endpoint (`ndBlockBound_mono`), so the
  supremum over prefixes is attained at `B`.
- `RHTower/Sieve/DivisorFibreInterval.lean` — `filter_mul_mem_Ico`: for `b ≥ 1` the fibre
  `{a : a·b ∈ [A,B)}` is the interval `[(A−1)/b + 1, (B−1)/b + 1)`.
- `RHTower/Sieve/ConvolutionBlockTypeI.lean` — `sum_conv_mul_Ico_eq`: the two previous facts
  combined,
  ```
  Σ_{n∈[A,B)} (f ∗ g)(n)·w(n) = Σ_{b≤L} g(b)·Σ_{a ∈ [(A−1)/b+1, (B−1)/b+1)} f(a)·w(ab).
  ```
- `RHTower/Sieve/ZetaConvolutionTypeI.lean` — `ndPhaseExp`, `ndPhaseExp_mul`, `fibreBound`, and
  `norm_sum_zeta_conv_ndPhaseExp_le`: the FIRST Vaughan piece `(ζ ∗ c)` is estimated term by term
  by the near-diagonal block bound at the scaled offset `r/b` over the fibre interval.

Remaining: the `log ∗ μ_V` piece (same shape, with `TypeILogWeight`), the type-II piece (range
restriction to `k > U`, `m > V`, then `TypeIIEnergyBound`), and `VC6`.

## The second Vaughan piece, and the coupled type-II range (2026-08-23)

Corpus searches run before each module (`scripts/formal_tools.py research`): "Kusmin Landau first
derivative test", "exponent pair van der Corput second derivative test", "type I type II bilinear
Vaughan", "sum of divisor function squared", "convolution rearrangement divisorsAntidiagonal",
"masked fibre correlation type II coupled block".  Assets found and REUSED rather than rebuilt:
`Sieve/SecondDerivativeTest.lean`, `Sieve/KuzminLandauInterval.lean`, `Sieve/AbelIncreasingWeight.lean`,
the whole `NearDiagonal*` chain, `HTGeometry/VanDerCorputInequality.lean`, `harmonicSum_le_one_add_log`.

- `RHTower/Sieve/LogConvolutionTypeI.lean` — `norm_sum_log_conv_ndPhaseExp_le`: the SECOND Vaughan
  piece `log ∗ μ_V`, estimated fibre by fibre with the Abel factor `2 log` of the fibre endpoint.
  The empty-fibre case is discharged separately (`Real.log 0 = 0`).
- `RHTower/Sieve/DivisorFibreInterval.lean` — refactored to export the pointwise
  `mem_fibre_iff : a·b ∈ [A,B) ↔ a ∈ [(A−1)/b+1, (B−1)/b+1)`.
- `RHTower/Sieve/TypeIIFibreCorrelation.lean` — the structural fact that makes the type-II half
  work despite the coupling `d·m ∈ I`:
  - `mem_fibre_symm : m ∈ fibre(d) ↔ d ∈ fibre(m)` (the constraint is symmetric);
  - `maskedNdExp`, whose masking restores the product structure the correlation expansion needs;
  - **`sum_masked_correlation_eq`**: the correlation attached to a pair `(m₁, m₂)` equals
    ```
    Σ_{d ∈ [max(P, A_{m₁}, A_{m₂}), min(Q, B_{m₁}, B_{m₂}))} e(F(m₁d))·conj e(F(m₂d)),
    ```
    an honest INTERVAL — exactly the input of `norm_sum_corr_le` and
    `norm_curvedSum_diffPhase_kuzminLandau`.

Remaining: the type-II assembly (masking + `sum_normSq_inner_le` + the two correlation regimes),
the third Vaughan piece's coefficient bounds, and `VC6`.

## VC5 CLOSED — the whole Vaughan decomposition of `S_r(I)` is Lean-proved (2026-08-23)

Searches run first each time (`formal_tools.py research`): "masked type II energy Cauchy Schwarz
coupled range", "correlation Kuzmin Landau regime off diagonal pair", "diagonal correlation
unimodular sum card interval", "Vaughan decomposition block sum three pieces", "arithmetic function
mul_apply divisorsAntidiagonal zeta coercion", "truncated von Mangoldt Moebius convolution
coefficient bound", "one minus zeta moebius truncated coefficient divisor bound".  No duplicates.

- `TypeIIMaskedEnergy.lean` — `sum_typeII_masked_eq` (the coupled double sum IS a masked bilinear
  form) and `norm_typeII_masked_sq_le`.
- `TypeIICorrelationRegimes.lean` — `norm_masked_correlation_diag_le` (the diagonal costs the
  length of the outer range), and `norm_sum_ndExp_corr_kuzminLandau_abs_le` (the sub-resonant
  regime, either order of the pair).
- `VaughanBlockDecomposition.lean` — **`sum_vonMangoldt_block_decomp`**: on a block above `U`,
  `Σ Λ(n)w(n)` is exactly `−(ζ∗Λ_U∗μ_V) + (log∗μ_V) + ((Λ−Λ_U)∗(1−ζμ_V))` summed against `w`.
- `ConvolutionCoercion.lean` — `coe_mul_apply`, `coe_zeta_mul_apply'`, `coe_log_mul_apply'`.
- `VaughanTypeIPieces.lean` — `abs_truncAF_moebius_le_one`, and
  `abs_truncAF_conv_le_log : |(Λ_U ∗ μ_V)(b)| ≤ log b` (from `Λ ∗ ζ = log`).
- `VaughanTypeIEstimates.lean` — `norm_zeta_piece_le`, `norm_log_piece_le`.
- `VaughanTypeIICoefficients.lean` — `card_divisorsAntidiagonal`,
  `vonMangoldt_sub_truncAF_eq_zero`, `abs_vonMangoldt_sub_truncAF_le`,
  `abs_one_sub_zeta_mul_moebius_le : |(1 − ζμ_V)(m)| ≤ 1 + d(m)`.
- `VaughanTypeIIEstimate.lean` — `typeIILong`, `typeIIShort`, `sum_typeII_piece_eq`,
  `norm_typeII_piece_sq_le`.
- `VonMangoldtBlockEstimate.lean` — **the milestone**:
  ```
  ‖Σ_{n ∈ [A,B)} Λ(n)·e(F_{T,r}(n))‖
      ≤ Σ_{b ≤ L} log b · fibreBound(b)
        + Σ_{b ≤ L} 2·fibreBound(b)·log(fibre endpoint)
        + √(typeIIEnergy).
  ```

Everything remaining (`VC6`) is optimisation: choosing `U = V = W = M^{3/5}X^{-1/5}`, bounding the
coefficient energy by `DivisorSquareMoment`, splitting the correlation sum into diagonal /
sub-resonant / super-resonant, and summing over the dyadic blocks and over `r`.

## VC6, first half: energies and the dyadic split (2026-08-23)

Searches first: "Chebyshev psi upper bound linear explicit constant" (found and reused
`exists_chebyshevPsiReal_le_linear`), "sum of von Mangoldt squared", "dyadic decomposition finite
range union of blocks" (found and reused `Sieve/AdicBlocks.lean`'s
`norm_sum_Icc_le_sum_dyadic_blocks`), "dyadic block filter equals Ico".

- `TypeIICoefficientEnergy.lean` —
  `exists_sum_typeIILong_sq_le : Σ_{d ≤ L} |(Λ−Λ_U)(d)|² ≤ C·L·log L`
  (`|Λ−Λ_U| ≤ Λ ≤ log L` and `Σ Λ = ψ(L) ≤ C L`), and
  `sum_typeIIShort_sq_le : Σ_{m ≤ L} |(1−ζμ_V)(m)|² ≤ 2L + 2L·H_L³`
  (`(1+x)² ≤ 2 + 2x²`, then the divisor second moment).
- `DyadicBlockIco.lean` — `dyadic_block_eq_Ico`: the corpus's `⌊log₂ n⌋`-indexed block of `[1,M]`
  IS `[2^j, min(2^{j+1}, M+1))`, so the interval-shaped block estimates apply to it.
- `TypeIIDyadicBlocks.lean` — `blockTypeIIEnergy` and **`norm_typeII_piece_le_sum_blocks`**:
  ```
  ‖type-II piece‖ ≤ Σ_{j ≤ log₂ L} √(blockTypeIIEnergy j).
  ```
  Splitting the long variable dyadically BEFORE Cauchy--Schwarz is what makes the estimate
  nontrivial: on the whole range the coefficient energy is proportional to `L` while the diagonal
  is proportional to the block length, and the two only balance blockwise.

Every structural step of the card is now Lean-closed.  What remains is purely quantitative:
bounding `blockTypeIIEnergy j` by diagonal + sub-resonant + super-resonant contributions, choosing
`U = V = W`, and summing over the blocks and over `r`.

## VC6, second half: the pair split and both off-diagonal regimes (2026-08-23)

Search first: "double sum split diagonal off diagonal erase pair sum finset" — the corpus owns
`HTGeometry.sum_pair_eq_diag_add_offDiagonal`, but only in `Fintype`/sigma form; the type-II energy
is indexed by `Finset.Icc 1 L`, so the `Finset`/`erase` form is new and is documented as such.

- `PairSumSplit.lean` — `sum_pair_split` and `diag_pair_sum_le`: the diagonal of the type-II energy
  costs only `(block length)·Σ_m |a_m|²`, because every diagonal correlation term is unimodular.
- `OffDiagonalCorrelationBounds.lean` — both regimes for an off-diagonal pair on a dyadic block
  `[P, Q)`.  The correlation actually runs over `[P', Q') ⊆ [P, Q)`, and one monotonicity step in
  each variable (`curvedLambda` is antitone in the scale, `√(Q'³) ≤ √(Q³)`, `Q'² ≤ Q²`) restores
  the block's own endpoints:
  ```
  second derivative:  ≤ 2500√(Y/(36πP)) + 22√(36π/Y)·√(Q³),
  Kuzmin--Landau:     ≤ 75πQ²/(16Y) + 1,          Y = T|r/m₁ − r/m₂|.
  ```
  The empty-interval case is discharged separately in the sub-resonant branch.

Remaining: organise the off-diagonal pairs by `h = |m₁ − m₂|` (so that
`|r/m₁ − r/m₂| = r·h/(m₁m₂)`), choose `U = V = W`, and sum over the blocks and over `r`.

## The effective short range (2026-08-23)

`EffectiveShortRange.lean` supplies the fact that makes the type-II diagonal proportional to the
BLOCK length rather than to `L`:

- `masked_correlation_eq_zero_of_large` / `_of_small` — on the block `[P,Q)` the masked correlation
  vanishes identically unless the fibre of the short value meets the block;
- `sum_masked_correlation_conj` — the masked correlation is conjugate-symmetric, so the same holds
  in the second coordinate;
- **`effective_short_range`** — the surviving short values lie in
  `[(A−1)/(Q−1) + 1, (B−1)/P + 1)`, an interval of length `≍ M/P`.

At `A ≍ M`, `B ≍ 2M`, `P ≍ D`, `Q ≍ 2D` this is `≍ 1.5·M/D`, exactly the count the exponent budget
assumes.  Card 12 now stands at 32 Lean modules, all axiom-clean.

## The pair gap scale (2026-08-23)

`RHTower/Sieve/PairGapScale.lean` — the algebra the `h`-sum runs on:

- **`abs_inv_diff : |r/m₁ − r/m₂| = r·|m₂ − m₁|/(m₁m₂)`**;
- `le_abs_inv_diff` / `abs_inv_diff_le` — two-sided versions when the pair is confined to
  `[M₀, M₁]`, giving `r h/M₁² ≤ |Δ| ≤ r h/M₀²` with `h = |m₂ − m₁|`.

Combined with `effective_short_range` (which puts both members of a contributing pair inside an
interval of length `≍ M/D`), the curvature scale of an off-diagonal correlation on the block
`[D, 2D)` is `Y = T|Δ| ≍ T r h D²/M²`, exactly the scale the exponent budget uses.

## The `h`-organisation of the off-diagonal total (2026-08-23)

Searches: "off diagonal pair sum grouped by gap h at most two values", "Nat.dist fiber count pairs
gap".  The corpus's `Sieve/OffDiagonalSwap.sum_erase_swap` is stated for `Fin N` with `univ`; the
type-II energy is indexed by an arbitrary `Finset`, so the `Finset` form is new.

- `GapGroupedPairSum.lean` — `card_filter_dist_le_two`: at most two elements realise a given gap
  (they are `m₁ + h` and `m₁ − h`); `sum_row_gap_le`: one row of the off-diagonal sum of a
  gap-only weight is `≤ 2Σ_{h≤H}G(h)`, by `Finset.sum_fiberwise_of_maps_to` along `m₂ ↦ dist m₁ m₂`;
  `sum_offdiag_gap_le`: the whole sum is `≤ 2|S|Σ_{h≤H}G(h)`.
- `GapWeightedPairSum.lean` — `sum_erase_eq_sum_ite_finset`, `sum_erase_swap_finset`, and
  **`sum_offdiag_weighted_le`**:
  ```
  Σ_{m₁}Σ_{m₂≠m₁} |b(m₁)||b(m₂)|·G(dist) ≤ (Σ_m |b(m)|²)·(2Σ_{h≤H}G(h)).
  ```
  The weights are decoupled by `|b₁||b₂| ≤ (|b₁|²+|b₂|²)/2`; the second half is handled by swapping
  the order of summation and `Nat.dist_comm`.

This is the step the exponent budget calls the `h`-sum.  The three gap sums it feeds are all
already available: `Σ_{h≤H}√h ≤ H^{3/2}` (trivial), `Σ_{h≤H}h^{-1/2} ≤ 2√H`
(`RHTower/SqrtTelescopeSums.sum_inv_sqrt_le`), and `Σ_{h≤H}h^{-1} ≤ 1 + log H`
(`invSum` / `harmonicSum_le_one_add_log`).

Card 12: 37 modules.

## The gap-only correlation bound (2026-08-23)

Searches: "sum of square roots over interval bound H to the three halves", "monotonicity of two
term block bound in curvature scale Y", "Nat.dist cast to real absolute value difference".

DUPLICATION FOUND AND RECORDED: `invSum` (introduced in `DivisorSquareMoment.lean`) is literally
`RHTower.harmonicSum` of `HarmonicTriangularProjection.lean`.  `GapSums.lean` now records
`invSum_eq_harmonicSum := rfl` and derives `invSum_le_one_add_log` from the corpus's
`harmonicSum_le_one_add_log` rather than reproving it.

- `GapSums.lean` — the three gap sums: `Σ_{h≤H}√h ≤ H√H` (new, trivial),
  `Σ_{h≤H}h^{-1/2} ≤ 2√H` (corpus `SqrtTelescopeSums.sum_inv_sqrt_le`), and
  `Σ_{h≤H}h^{-1} ≤ 1 + log H` (corpus, via the identification above).
- `CorrelationGapBound.lean` — `blockPairBound`, its monotonicity in the curvature scale
  (increasing through the first term, decreasing through the second), `cast_natDist`, and
  **`norm_masked_correlation_gap_le`**: for a pair confined to `[M₀, M₁]`,
  ```
  ‖correlation‖ ≤ 2500√(T r h/(M₀²·36πP)) + 22√(36π M₁²/(T r h))·√(Q³) =: gapCorrBound h,
  ```
  a function of the gap `h = dist(m₁,m₂)` alone.  This is exactly the `G(h)` that
  `sum_offdiag_weighted_le` consumes.

Card 12: 39 modules.
