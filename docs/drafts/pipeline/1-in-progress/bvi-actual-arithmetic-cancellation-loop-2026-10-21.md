# BVI: the missing actual arithmetic cancellation — conjecture loop

- **ID:** BVI-AAC-2026-10-21
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop (research → derive → formalize)
- **Source:** `formal/GaloisForLFunctions/BezoutValuationIncidence/README.md` §5 (receiver, interior
  martingale "signed sum over moduli", single-modulus statistics of the actual Möbius row);
  `docs/reports/review-2110/hard-obstacles-summary.md` Q5.
- **Statement:** produce unconditional, Lean-verified cancellation of the *actual* Möbius / damped
  Möbius row in BVI coordinates, measured in the README units (damping, exponent θ), and locate exactly
  where each mechanism stops.

## Goal

The receiver `E_T(ε) = Σ_{n≤T} A_ε(n)²/(n(n+1))` of `c_ε(d) = μ(d)d^{-ε}` is bounded for `ε ≥ 1/2`
and unknown below; a bound at one fixed `ε < 1/2` is a zero-free half-plane. The actual arithmetic
cancellation that the corpus does not yet use inside BVI is the zero-free region itself. Each cycle
attacks one concrete missing statement; failures are recorded with their positive survivor.

## Gates
- [x] 0 → 1  in-progress: frontier read (README §5, review-2110 Q5, WP4 ledger, THIM parity pair).
- [ ] 1 → 2  per-cycle paper proofs (below).
- [ ] 2 → 3  per-cycle Lean modules, wired into `BezoutValuationIncidence.lean`.

## Corpus inputs used (verified by search)
- VK Mertens: `RHTower.Sieve.exists_abs_sum_moebius_le_vk_rate`, eventual
  `2√(log N) ≤ log vkHeight N` (`eventually_vk_conditions`), so `|M(N)| ≤ B N e^{-√(log N)/12}`.
- THIM receiver objects: `weightCenteredPrefix`, `weightPronicEnergy`, `dampedSignWeight`,
  `weightPronicEnergy_pmPowerDamped`, hyperbola template `abs_weightCenteredPrefix_dampedSign_le`.
- BVI interior/complete energy comparison:
  `pmBezoutInteriorPronicEnergy_le_two_mul_discreteEnergy_add_half` (and converse).
- `HTGeometry.summable_exp_neg_sqrt_log_div`, `RHTower.sum_rpow_neg_head_le`,
  `HTGeometry.sum_shift_rpow_tail_le`.

## Cycle ledger

### C1 — the receiver is bounded in the zero-free band below half damping (DONE, Lean)
**Conjecture.** There is `E` such that for every horizon `T` and every damping
`ε ∈ [1/2 − 1/(80√(log T)), 1/2]` (and `ε ≥ 1/4`), `E_T(ε) ≤ E`; consequently the Bézout interior
energy is bounded on the same band.

**Paper proof.**
1. *Abel with linear partial sums.* If `|Σ_{d≤x}s(d)| ≤ Lx` for `D ≤ x ≤ X` and `w ≥ 0` is antitone
   on `(D, ∞)`, then `|Σ_{D<d≤X}s(d)w(d)| ≤ L(2D·w(D+1) + Σ_{D<d≤X}w(d))`
   (summation by parts; the weight `d ↦ d` telescopes against `w`).
2. *Blocks and tail.* With `L = Cρ(D)`: `|Σ_{D<d≤X}μ(d)d^{-α}| ≤ 5LX^{1−α}` (`0 ≤ α ≤ 1/2`),
   `|Σ_{d>D}μ(d)d^{-1-ε}| ≤ (2+1/ε)LD^{-ε}`.
3. *Hyperbola split at D.* `A_ε(n) = [short d ≤ D] + [long, along the cofactor k] − n·[tail]`,
   giving `|A_ε(n)| ≤ 3D^{1−ε} + 31·L·n·D^{−ε}` for `1 ≤ D ≤ n`, `ε ∈ [1/4,1/2]`.
4. *Choice of D.* `u = √(log n)`, `D = ⌊n e^{−u/20}⌋`; then `D ≥ √n`, `ρ(D) ≤ e^{−u/18}`, and
   `|A_ε(n)| ≤ K n^{1−ε} e^{−u/40}` uniformly in `ε ∈ [1/4, 1/2]`.
5. *Band.* For `n ≤ T` and `ε ≥ 1/2 − 1/(80√(log T))`: `n^{−2ε} ≤ n^{−1} e^{u/40}`, so each term is
   `≤ K² e^{−u/40}/n`, summable; small `n` use the trivial bound (`D = 1`, `L = 1`).

**Meaning.** First unconditional receiver bound below half damping: the damping unit moves from `1/2`
to `1/2 − c/√(log T)` at horizon `T`, paid by the zero-free region (VK ⟹ dVP rate). A fixed-width band
would be a zero-free strip (README §5), so the band profile is the zero-free profile.

**Lean.** `BezoutValuationIncidence/ReceiverBoundedInTheZeroFreeBandBelowHalfDamping.lean`:
`exists_receiver_le_on_zeroFreeBand`, `exists_interiorEnergy_le_on_zeroFreeBand`, tools
`abs_sum_Ioc_mul_le_of_linear`, `abs_weightCenteredPrefix_dampedSign_le_of_linear`,
`exists_abs_sum_moebiusReal_le_sqrtLog`, `exists_abs_weightCenteredPrefix_pmPowerDamped_le`.
`lake env lean` clean; axioms `propext, Classical.choice, Quot.sound`; wired.

### C2 — the Vinogradov–Korobov band (DONE, Lean)
**Statement.** `E_T(ε) ≤ E` for `1/4 ≤ ε ≤ 1/2`, `ε ≥ 1/2 − κσ(T)/(480 log T)`,
`σ = (log)^{3/5}(log log)^{-5/3}`; same for the interior energy.
**Proof.** As C1 with rate `g = κσ/24`, split `D = ⌊n e^{-g(n)/5}⌋`; shape lemmas: `σ` nondecreasing
from `exp(exp(25/9))` (via `log t/t^{9/25}` antitone), `σ/log` decreasing from `exp(e)`,
`σ(z) ≥ (4/9)σ(x)` when `log z ∈ [(4/9)log x, log x]`.
**Selectivity.** Width `(log T)^{-2/5}(log log T)^{-5/3}` exceeds the dVP width `(log T)^{-1/2}`; dVP
is the best possible zero-free region for Beurling systems (Diamond–Montgomery–Vorhauer), so the
extra width is paid by Vinogradov's mean value theorem, i.e. by the additive structure of ℕ.
**Lean.** `BezoutValuationIncidence/ReceiverBoundedInTheVinogradovKorobovBand.lean`:
`exists_receiver_le_on_vinogradovKorobovBand`, `exists_interiorEnergy_le_on_vinogradovKorobovBand`,
`exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk`, `vkScale_le_vkScale`, `vkScale_div_log_le`,
`four_ninths_mul_vkScale_le`. Clean, standard axioms, wired.

### C3 — the parity pair is separated on the band (DONE, Lean)
**Statement.** `|W_{c'}(e)| = |W_c(e)|` for every damping, and on the VK band `E_T(c_ε) ≤ E` while the
parity twin has `E_T(c'_ε) ≥ c(log(T+1) − log 100)` with one `c > 0`.
**Proof.** Twin drift constant `K_ε = ρ_ε/U_ε ≥ ρ_{1/4}/U_{1/4}` on `[1/4,1/2]`: `ρ_ε` increases
(Euler product, factorwise), `U_ε` decreases (local factors `1/(p^{1+ε}−2)` decrease); then the THIM
drift-cell bound and `log(T+1) − log a ≤ Σ_{a≤n≤T} 1/n`.
**Meaning.** Wall 16 (no sign-blind datum decides below half damping) has its visibility witness on the
band: the VK input reads the Möbius signs. **Lean.**
`BezoutValuationIncidence/ParityPairSeparatedOnTheVinogradovKorobovBand.lean`:
`parityPair_separated_on_vinogradovKorobovBand`, `parityTwin_receiver_ge`; standard axioms; wired.

### C4 — cofinal Möbius law uniform in the band ratio (KILLED: duplicate)
Identity `Σ_{d≤N}μ(d)⌊M/d⌋ = 1 − Σ_{k:⌊M/k⌋>N}(M(⌊M/k⌋) − M(N))` gives `|Σ_{k≤M}s_{N,μ}(k) − 1| ≪
Mρ(N)(1 + log(M/N))`. The corpus already has this `log B` law
(`exists_abs_sum_sieveSeq_moebiusReal_le_vk_quotient_windows`, BVI). No new content.

### C5 — Kátai single-modulus law for BVI kernels (KILLED: dominated)
Ramaré/Turán–Kubilius + Bézout correlations `e(k(p−q)m/d)` give `|Λ_d(f_Q)| ≤ (d²/Q)·O((log log P)^{-1/2})`
for every bounded multiplicative row and prime `d ∈ [P, Q/P³]`. The ℓ² large-sieve dispersion already
in BVI (C7/C8/C20 of WP4) saves `√(P/Q)` on averages over `d`, which dominates except at `P ≍ Q`, where
PNT partial summation suffices. **Positive survivor:** none beyond the sup-over-one-modulus form, judged
not worth formalizing. **Insight:** mechanism 5 by dilation alone saves at most `(log log)^{-1/2}`.

### C6 — receiver growth below half damping against the period energy (DONE, Lean)
**Statement.** For `1/4 ≤ ε < 1/2`: `E_T(ε) ≤ C T^{1−2ε} e^{−κσ(T)/270}` eventually, and
`E_N(ε) ≤ C e^{−κσ(N)/270} E_prim(N)` (period energy `≥ N^{1−2ε}/10368`, THIM).
**Proof.** Cells from the VK prefix bound; split at `√T`: below, the trivial exponent `(1−2ε)/2`
(absorbed since `σ/log → 0`); above, `σ(n) ≥ (4/9)σ(T)`.
**Meaning.** Quantifies README §5 ("the bound is carried by the pronic weighting below the first
period"): unconditionally the prefix receiver is smaller than the period energy by exactly the VK
factor. **Lean.** `BezoutValuationIncidence/ReceiverGrowthBelowHalfDampingAgainstThePeriodEnergy.lean`:
`eventually_receiver_le_growth`, `eventually_receiver_le_mul_periodEnergy`; split into small lemmas to
stay inside the default heartbeat budget; standard axioms; wired.

### C7 — multiplicative weights are decided at the primes on the band (DONE, Lean)
**Statement.** For multiplicative `|f| ≤ 1`: if `f(p) = −1` at every prime (μ, λ, …) the receiver of
`f d^{-ε}` is bounded uniformly on the VK band; if `f(p) = +1` and `f ≥ 0`, it is
`≥ (log(T+1) − log 100)/1024` for every `0 < ε ≤ 1/2`.
**Proof.** `f = (f⋆1) ⋆ μ`, `(f⋆1)(q)q^{-ε}` in the critical Wiener algebra with mass `G_ε ≤ G_{1/4}`;
THIM's finite convolution law `‖A_{g⋆c}‖ ≤ G‖A_c‖ + (√2+1)G|m_c|` with `0 < ρ_ε ≤ 1`; for `+1`, `f ≥ μ²`
and the squarefree drift. **Lean.** `BezoutValuationIncidence/MultiplicativeWeightsAreDecidedAtThePrimesOnTheBand.lean`:
`exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one`, `receiver_ge_log_of_primes_one`;
standard axioms; wired.

### C8 — the omitted residue class law of the prime row (DONE, Lean)
**Statement.** For every prime `p`, `Q · Λ_p(Λ·1_{(Q,2Q]}) → −(𝔅(p,0) − m_p)/(2(p−1)) =
−π²(p²−1)²/(144p²(p−1))`.
**Proof.** Kernel depends only on `n mod p`; classes `r ≢ 0` carry `W(Q)/(p−1) + o(1/Q)` by Dirichlet
(`WeakPNT_AP`) with a linear rate and Abel summation (`abs_sum_Ioc_mul_le_of_linear`); the centred
kernel has zero residue mean; class `0` holds at most one prime power in `(Q,2Q]`, so `O(log Q/Q²)`;
cubic part `O(p³ log Q/Q²)`; `Q·W(Q) → 1/2` by telescoping.
**Meaning (README Q5, fixed moduli).** The single-modulus statistic of the actual prime row is not
small: it is exactly the sieve term of the omitted residue class (the additive input "a residue
class omitted modulo p"), relative size `≍ 1/p` against trivial; the coprime classes cancel exactly.
**Lean.** `BezoutValuationIncidence/OmittedResidueClassLawOfThePrimeRow.lean`:
`tendsto_mul_kernelStatistic_primeWindowRow`, `eventually_abs_sum_classDefect_le`; standard axioms; wired.

### C9 — coupling of a fixed prime packet with the prime block (DONE, Lean)
**Statement.** For `c` supported on a finite set `S` of primes and `c'_Q = Λ·1_{(Q,2Q]}`:
`Q(B + mR' + βH') → −(π²/144) Σ_{p∈S} c(p)(1 − p^{-2})`.
**Proof.** Third-order cross-scale law (`abs_rowBilinear_sub_kernelStatistic_le`): equidistributed
main term with `Q S' → 1/2` (PNT via the two classes mod 2), kernel statistics by C8, fourth-order
error `O(Σ|c|p³ · log Q/Q²)`.
**Meaning (README tool 2 / "sign of a signed prime packet").** Against the actual prime block the
equidistributed main term is multiplied by `−p` at each prime: the omitted class reverses the sign;
positive packets couple negatively with weight `1 − p^{-2}`. Fixed small scale only.
**Lean.** `BezoutValuationIncidence/CrossScaleCouplingOfPrimePacketsWithThePrimeBlock.lean`:
`tendsto_mul_rowBilinear_primeWindowRow`, `tendsto_mul_sum_primeWindowRow_div_sq`; standard axioms; wired.

### C10 — single-modulus cancellation of the Möbius block (DONE, Lean)
**Statement.** For a fixed prime `p` and `0 < a < p`: `Σ_{n≤x, n≡a} μ(n) log n = o(x log x)`; every class
mass `Σ_{Q<n≤2Q, n≡r} μ(n)/n²` (class `0` included) is `o(1/Q)`; hence `Q Λ_p(μ_Q) → 0` and, for every
row `c` on a fixed finite prime set, `Q(B + mR' + βH')(c, μ_Q) → 0`. **Pair:** the prime block has
`Q Λ_p → −π²(p²−1)²/(144p²(p−1))` and coupling `−(π²/144)Σc(p)(1−p^{-2})`.
**Proof.** Twisted hyperbola `μ log = −μ⋆Λ` with `dm ≡ a ⟺ (p∤d, m ≡ a d̄)`; `WeakPNT_AP` uniformly over
the coprime classes (`|D_r(y)| ≤ εy + K`); main terms recombine to `Σ_{p∤d}μ(d)⌊x/d⌋ = O(x)` (coprime
Möbius harmonic bound `p/(p−1)`); class masses by Abel against `1/(n² log n)`; class `0` = block − coprime
classes, block mass by `M(x) = o(x)`.
**Meaning.** The actual arithmetic cancellation at one modulus, in its fixed-modulus form: the Möbius
signs cancel inside every residue class, which removes exactly the sieve term the primes carry. No rate,
no uniformity in `p` (the balanced regime needs `p` growing with `Q`).
**Lean.** `BezoutValuationIncidence/MoebiusEquidistributionInTheResidueClassesOfAPrime.lean`
(`eventually_abs_sum_class_moebius_log_le`, twisted swap `sum_Icc_mul_dirichletConv_twist`) and
`BezoutValuationIncidence/SingleModulusCancellationOfTheMoebiusBlock.lean`
(`singleModulus_pair_moebius_primes`); standard axioms; wired.

### C11 — the Möbius block beats the Type-II barrier (DONE, Lean)
**Statement.** (a) *Transfer law, every row.* For `c` on primes `≤ Q₀`, `c'` on `[A+1, A+L]`,
`x = c'/n²` and its `H`-window average `x̄`:
`|B + mR' + βH'| ≤ (π²/48)√(Σc²p²)√(L+H+2Q₀²)‖x̄‖₂ + √(2H)√(Σc²p)√(L+2Q₀²)‖x‖₂ + |Σx|Σ|c|/(6p) + cubic`.
(b) *Matomäki–Radziwiłł in linear windows.* For every monotone unbounded `H(Q) ≤ Q` growing by at most
one per doubling, `Σ_{Q≤t<2Q}(Σ_{t<n≤t+H}μ(n))² = o(H²Q)`. (c) *Corollary.* For every `ε > 0` and all
large `Q`, every row `c` on primes `p ≤ Q₀` with `8 log₂Q ≤ ε²p` has, against `μ·𝟙_{(Q,2Q]}`,
`|B + mR' + βH'| ≤ ε√(Σc²p²)√(Q+2Q₀²)Q^{-3/2} + |Σ_{Q<n≤2Q}μ(n)/n²|Σ|c|/(6p) + cubic`.
**Proof.** (a) Exact multiplier `X̄ = B_H X`, `B_H(1) = 1`, `|1 - B_H(ζ)| ≤ H|ζ-1|`; in the Fourier form
the averaged part keeps the weight `Σ|η-1|^{-4} ≤ p⁴/64`, the defect has weight
`2Hk Σ|η-1|^{-3} ≤ Hkp³/8`; powering by `k` permutes `T_p`; the classes `p | k` cancel because `x̄` and
`x` have the same mass; log-free large sieve over the primes. (b) From the corpus fibre MR
(`averagedMeanSquare_moebius_of_tendsto`) via the corpus fibre geometry (`exists_start_preimage`,
`fibreStartIdx_eq_of_start_interval`, `innerFibre_eq_Ioc`, `fibreLen_bounds`): on `m` ranges of starts
with `√x = 2(Y-1)`, `h = 2H(Y-1)`, linear windows are fibres up to `2 + 2(H+1)/m` points, and the start
determines the outer factor. (c) `H = log₂ Q`; Abel against `1/m²` on windows inside the block, the
`2H` edge windows trivially, so `‖x̄‖² = o(Q⁻³)` with `‖x‖² ≤ Q⁻³`.
**Meaning.** The first actual arithmetic cancellation of the Möbius row in the balanced regime: its
cross-scale remainder is `o` of the size of the large-sieve bound, which coherent rows attain (Type-II
barrier), uniformly in small-scale coefficients supported above `8 log₂Q/ε²`. Strength: a factor
`o(1)`, no exponent gain. A power gain past `θ = 6/5` needs power cancellation of `μ` in almost all
windows of length `≍ P`; by the transfer law (a) that is exactly the missing input.
**Lean.** `BezoutValuationIncidence/ShortWindowMeanSquareCarriesTheCrossScaleLoss.lean`
(`abs_rowBilinear_add_mean_add_beta_le_shortWindow`), `…/MoebiusCancelsInAlmostAllLinearShortWindows.lean`
(`tendsto_sum_sq_moebius_window_div`), `…/MoebiusBlockBeatsTheTypeTwoBarrier.lean`
(`eventually_abs_rowBilinear_moebiusWindowRow_le`); standard axioms; wired.

### C12 — short-window Möbius saving is the quasi-Riemann hypothesis (DONE, Lean)
**Statement.** With `E_α(Q) = Σ_{Q≤t<2Q}(Σ_{t<n≤t+⌈Q^α⌉}μ(n))²`:
`(∃ α ∈ (0,1), δ > 0, C, ∀ Q ≥ 1, E_α(Q) ≤ C Q^{1+2α-δ}) ↔ Θ < 1`, `Θ` the zero abscissa. Explicitly,
`Θ < 1` gives the saving at `α = (1+Θ)/2`, `δ = (1-Θ)/2`; a saving `(α, δ)` forces
`Θ ≤ max(1 - δ/2, α)`.
**Proof.** `⇐` Littlewood at the abscissa (`mobiusMertens_subpower_zetaZeroAbscissa`). `⇒` windows
telescope, `Σ_t (M(t+H)-M(t)) = Σ_{i<H}(M(2Q+i)-M(Q+i))`, so `|M(2Q)-M(Q)| ≤ √Q√E/H + 2H ≪ Q^γ`;
halving induction `|M(N)| ≤ K(N+1)^γ`; absolute-moment exponent law
(`zetaZeroAbscissa_le_of_sum_norm_mertens_le`).
**Meaning.** Closes the C11 route: the input the transfer law needs for an exponent gain of the
Möbius row in the balanced regime is equivalent to a fixed-width zero-free strip. Same profile as
the receiver (C1–C6): BVI's missing cancellation is, on every route built so far, a zero-free-region
statement. Neither side of the iff is proved; no strip is claimed.
**Lean.** `BezoutValuationIncidence/ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis.lean`
(`moebiusPowerWindowSaving_iff`); standard axioms; wired.

### C13 — the centred prime block beats the large sieve (DONE, Lean)
**Statement.** For `7/12 < α < 1`, `ε > 0`, all large `Q`, `H = ⌈(2Q)^α⌉`: every row `c` on primes
`p ≤ Q₀` with `8H(log 2Q + 1)² ≤ ε²p` has, against `c' = (Λ - 1)·𝟙_{(Q,2Q]}`,
`|B + mR' + βH'| ≤ ε√(Σc²p²)√(Q+2Q₀²)Q^{-3/2} + |Σ_{Q<n≤2Q}(Λ(n)-1)/n²|Σ|c|/(6p) + cubic`.
The threshold is `p ≥ Q^{α+o(1)}`; at `α < 3/5` it covers the whole balanced regime.
**Proof.** Generic `sum_sq_shortWindowAverage_le_of_window` (`Σ x̄² ≤ Q(G/H)² + 2HB²`); Huxley in
all windows via the sibling module's `abs_sum_block_le_of_window` (`G = 2εH/Q²`), `B = (log 2Q+1)/Q²`;
`⌈(2Q)^α⌉(log 2Q+1)² ≤ 16δ²Q` from corpus `tendsto_one_add_log_div_rpow_atTop_zero`; C11 transfer law.
**Meaning.** The prime-row counterpart of C11, stronger than the sibling's rank-two result
(`exists_abs_rowBilinear_centredPrimeRow_le`) by the large-sieve factor `(P/Q)^{1/2}`. The omitted
class (C8) is inside the bound: its dual-norm size `P/Q` is `o(P^{5/2}Q^{-3/2})` for `P ≥ Q^{1/3+δ}`.
Input strength: Huxley (zero density); a power gain needs power-saving short-interval PNT, again a
zero-free strip (cf. C12).
**Lean.** `BezoutValuationIncidence/CentredPrimeBlockBeatsTheLargeSieve.lean`
(`eventually_abs_rowBilinear_centredPrimeBlock_le`); standard axioms; wired.

### C14 — short-window prime saving is the quasi-Riemann hypothesis (DONE, Lean)
**Statement.** With `R = ψ - id`, `F_α(Q) = Σ_{Q≤t<2Q}(Σ_{t<n≤t+⌈Q^α⌉}Λ(n) - ⌈Q^α⌉)²`:
`(∃ α ∈ (0,1), δ > 0, C, ∀ Q ≥ 1, F_α(Q) ≤ C Q^{1+2α-δ}) ↔ Θ < 1`. A saving `(α, δ)` forces
`Θ ≤ max(1 - δ/2, (1+α)/2, 1/2)`; `Θ < 1` gives the saving at `α = (1+Θ)/2`, `δ = (1-Θ)/2`.
**Proof.** `⇐` `exists_psiRemainder_le_rpow_zetaZeroAbscissa`. `⇒` generic window telescoping
(`sum_Ico_window_telescope`), `|R(a+i) - R(a)| ≤ i(log(a+i)+1)`, doubling
`|R(2Q)-R(Q)| ≤ √Q√F/H + 2H(log(2Q+H)+1)`, `log 4Q + 1 ≤ (4/η+1)Q^η` (`Real.log_le_rpow_div`), halving
induction, square-sample law `zetaZeroAbscissa_eq_half_add_sInf_psiRemainder_squareSum_upper`.
**Meaning.** Prime-row counterpart of C12: with C13 the centred prime row gains `o(1)` over the large
sieve unconditionally (Huxley) and a power exactly when `Θ < 1`. Both actual rows now have the same
profile as the receiver: the missing cancellation is a zero-free strip.
**Lean.** `BezoutValuationIncidence/ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis.lean`
(`primePowerWindowSaving_iff`); standard axioms; wired.

### C15 — the dual norm of the actual rows beats the large sieve (DONE, Lean)
**Statement.** README tool 3 in its own terms. For every `ε > 0`, all large `Q`, every prime set `S`
above the row's threshold (`8 log₂Q ≤ ε²p` for `μ`, `8⌈(2Q)^α⌉(log 2Q+1)² ≤ ε²p` for `Λ - 1`):
`Σ_{p∈S}|Λ_p(c')|/p ≤ ε√(Σp²)√(Q+2Q₀²)Q^{-3/2} + (1/6+π²/72)|S'|Σ1/p + ¾(Σp²)Σ|c'|/n³ + 6(Σp³)Σ|c'|/n⁴`
for the actual Möbius block and the centred prime block, `S'` the block mass.
**Proof.** Generic `sum_abs_kernelStatistic_le_of_remainder`: the corpus sign pattern
(`exists_rowBilinear_sub_main_ge`) turns a remainder bound for all bounded rows on `S` into a
dual-norm bound; the main term `|main(c)| ≤ (π²/72)|S'|Σ1/p`; then C11, C13.
**Meaning.** The single-modulus statistics of the actual rows at moduli `p ∼ P` growing with `Q`, in
the balanced regime, bounded by `ε` times the large-sieve size that coherent rows attain, with no
character or modulus average: the bound README tool 3 names as missing, at `o(1)` strength. Its
power-saving form is `Θ < 1` (C12, C14).
**Lean.** `BezoutValuationIncidence/DualNormOfTheActualRowsBeatsTheLargeSieve.lean`
(`eventually_sum_abs_kernelStatistic_moebiusWindowRow_le`,
`eventually_sum_abs_kernelStatistic_centredPrimeBlock_le`); standard axioms; wired.

## Synthesis after C1–C10 (what the research says about the missing cancellation)

1. **Receiver = zero-free region, both directions.** Any Mertens rate becomes a receiver band through
   `abs_weightCenteredPrefix_dampedSign_le_of_linear`; conversely a horizon-uniform bound at damping
   `ε` forces the zero-translation law (`RHTower.pmPowerDamped_zero_translation`). Unconditionally the
   band is exactly VK-wide (C2). The cancellation is sign-reading (C3) and decided at the primes for every
   multiplicative weight (C7). There is no BVI-internal cancellation in the receiver beyond the zero-free
   region: a single zero just past the region kills every wider band (zero-density does not help, the
   Möbius explicit formula carries `1/ζ'(ρ)`).
2. **Single-modulus statistics at fixed moduli are Dirichlet-strength and exact.** The prime row carries
   the omitted-class sieve term (C8), which reverses the sign of the cross-scale coupling (C9); the Möbius
   row cancels in every class including `0` (C10). This is the actual arithmetic cancellation at one
   modulus, from `L(1+it, χ) ≠ 0` for the characters of that modulus.
3. **The balanced regime needs moduli growing with `Q`.** Per modulus even GRH gives `√(pQ)` and stalls at
   `θ = 6/5` (the large-sieve value); class-wise square-root cancellation with absolute values over
   classes also stalls at `6/5`; the kernel-weighted class sums reduce to short-interval mean squares of
   μ at scale `P`, where unconditional savings are sub-power (VK, Matomäki–Radziwiłł). The random model
   gives `θ = 3/2` for the dual norm; the receiver's `θ = 2` needs the Möbius signs of the small-scale
   coefficients, i.e. cancellation across moduli. No unconditional input in the corpus or classical
   literature provides power savings there.

## Log
- 2026-10-21 — card created; C1 paper proof written; Lean module
  `BezoutValuationIncidence/ReceiverBoundedInTheZeroFreeBandBelowHalfDamping.lean` started.
- 2026-10-21 — C1 formalized and wired; C2 (VK band) formalized and wired.
- 2026-10-21 — C3 (parity pair on the band) formalized and wired.
- 2026-10-21 — C4 killed (duplicate), C5 killed (dominated), C6 formalized and wired.
- 2026-10-21 — C7 formalized and wired.
- 2026-10-21 — C8 formalized and wired.
- 2026-10-21 — C9 formalized and wired.
- 2026-10-21 — C10 formalized and wired (Möbius in progressions mod p; Möbius/prime pair).
- 2026-10-21 — C11 formalized and wired (transfer law; linear-window MR; Möbius block beats the Type-II barrier).
- 2026-10-21 — C12 formalized and wired (short-window Möbius saving ⟺ Θ < 1).
- 2026-10-21 — C13 formalized and wired (centred prime block o(large sieve) via Huxley).
- 2026-10-21 — C14 formalized and wired (short-window prime saving ⟺ Θ < 1).
- 2026-10-21 — C15 formalized and wired (dual norm of actual rows o(large sieve)).
