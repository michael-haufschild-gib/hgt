# THIM contribution loop (goal: 100 field-native contributions)

- **ID:** thim-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md (read-only)
- **Statement:** Develop Trans-Horizon Incidence Mechanics by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field (sieve responses, horizon
  states, Dirichlet polarization, Buchstab steps, Fermi traces, valuation clocks, prime chains)
  that expands what the field can explain or solve.

## Contract
- Native: stated in the field's objects and proved by its mechanisms; not a classical fact renamed.
- Significant: answers or sharpens a README frontier item, classifies a failure with its positive
  survivor, or discharges a premise elsewhere in the corpus.
- Lean: unconditional, standard axioms only, no heartbeat raises, wired into the umbrella
  `GaloisForLFunctions/TransHorizonIncidenceMechanics.lean`; final check
  `lake --old env lean -j 1 -o … <module>` from `formal/`, one Lean process at a time.
- Search first: 3–4 `scripts/formal_tools.py research` queries per conjecture (statement,
  mechanism, helper tools) before Mathlib name checks.
- Prior programme `thim-100-contribution-programme-2026-10-18` (paused) is prior art; its modules
  are not counted here.

## Conjecture queue
1. (C2 settled large N.) Small horizons: make the polynomial window explicit (squarefree density
   0.51 + explicit divisor bound) and lower the long-window threshold from `11N⁵` toward
   `S_N ≍ N² log N`; goal: global sign for all `N ≥ N₀` with explicit `N₀`.
2. Full Fermi boundary trace (adding `2∥n` cells): does `K_N^full ~ (4/π²)(log₂N)²`? Upper
   bound inherited from `Q_full ≥ Q_sel`; need the cosine family's `2∥n` energy.
3. Linear (not `N/log N`) damped dissipation via odd/even mean split of `τ_ε`.
4. Exact Möbius envelope ladder: `|s| ≤ 2` before `11(N+1)` (family `1155p`, `N=105p−1`),
   `|s| ≤ 3` before `13(N+1)`; Bertrand alternation energy `E ≥ 5+|s|` for `M+1 > 8N`.

## Log
- 2026-10-19 — loop started; README read in full; prior programme card read.
- 2026-10-19 — first idea (Möbius first-octave dissipation ⇒ `N^{3/2}` range) REDISCOVERED:
  corpus BVI `eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound` already gives
  every polynomial window. README frontier text lags the corpus here. C1 done (damped).

## Contribution ledger (append-only)
- **C1 · Prime-boundary dissipation and the cofinal sign of the damped defect** —
  `DampedPrimeBoundaryDissipationAndCofinalDefectSign`.
  `sum_prime_boundary_le_pmPowerDamped_gradient`: for every `ε ≥ 0`, `N ≤ M+1`, the prefix jump
  energy of `s_N(c_ε,·)` is at least `Σ_{3≤p≤N−1 prime} (2^(−ε) − p^(−ε))²` (sub-horizon step
  `τ_ε(p) = 1 − p^(−ε)` → even `τ_ε ≤ 1 − 2^(−ε)`). `two_mul_pmPowerDamped_defect_add_prime_boundary_le`:
  `2D̃ + dissipation ≤ τ(M+1)² − 1`. `eventually_pmPowerDamped_renormalizedDefect_polynomial_cofinal_bound`:
  for every fixed `ε > 0` and `r`, eventually `D̃_N(M;c_ε) ≤ −(2^(−ε)/2)² N/(16 log N)` on
  `N ≤ M+1, M ≤ N^(r+2)`. `eventually_pmPowerDamped_defect_nonpos_of_radicalState_le` and
  `eventually_moebius_defect_nonpos_of_radicalState_le`: eventually nonpositive at every prefix
  (any size) whose horizon radical state is `≤ N^(r+2)`, for `c_ε` and for `μ`.
  New insight: README frontier "for fixed positive ε the known radii shrink with N" — at fixed
  damping no radius is needed on polynomial windows; damped weights dissipate *below* the horizon
  at prime boundaries, a mechanism absent at `ε = 0` (Möbius must wait for the first octave,
  corpus BVI `CofinalMobiusGradientCoercivity…`). Prior-work check: corpus has the Möbius
  polynomial-window result only; no damped cofinal sign. Standard axioms (12 audited); wired;
  lint clean for THIM.
- **C2 · Global sign of the renormalized defect at large horizons** —
  `GlobalRenormalizedDefectSignAtLargeHorizons`. `eventually_moebius_renormalizedDefect_nonpos_all`:
  eventually in `N`, `D̃_N(M; μ) ≤ 0` for **every** `M`. `eventually_pmPowerDamped_renormalizedDefect_nonpos_all`:
  the same for every fixed `ε > 0`. Explicit at every `N ≥ 2`:
  `two_mul_moebius_defect_le_linear_dissipation` (`2D̃ ≤ 4N² − (M − 11N⁵)/(2N)` for `M ≥ 11N⁵`),
  `moebius_defect_nonpos_of_long_window` (`M ≥ 11N⁵+8N³`), damped analogue with `N^(2⌈ε⌉+3)`.
  Ingredients: `S_N ≤ N⁵`, `|H| ≤ N`, Bertrand terminal prime `p ∈ (N/2,N]` whose Selberg coordinate
  is `c(p)/p`, so `V ≥ (p−1)c(p)²/p²` (`primeTail_mode_le_sieveVariance`); then BVI long-window law
  `2D̃_W ≤ 4H² − (K − 11S_N)V` and the polynomial windows (BVI for μ, C1 for `c_ε`) overlap.
  New insight: the README frontier "Möbius defect nonpositive before 6(N+1); for fixed ε radii
  shrink" is settled for large horizons — the two dissipation regimes (first-octave/prime-boundary
  edges vs. long-window Poincaré) overlap polynomially, so no prefix escapes. What remains is only
  the finite range of small horizons (each with an explicit polynomial tail). Corpus had both regimes
  separately (BVI) but never combined them nor bounded `V` below. Built missing olean
  `BVI.PhaseUniformWindowPoincareAndLongWindowDissipation`. Standard axioms (11 audited); wired.
- **C3 · Rough-prime boundaries and the defect sign uniformly in the damping** —
  `RoughPrimeBoundaryUniformDampingDefectSign`. `eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform`:
  eventually in `N`, for **every** `0 ≤ ε ≤ 1` and every `M`, `D̃_N(M; c_ε) ≤ 0` — one threshold for
  all dampings (ε = 0 included). Mechanism `roughPrime_count_le_pmPowerDamped_gradient`: each prime
  `p ∈ (N,2N]` is rough (`s(p) = 1` exactly at every damping) and its four-divisible neighbour has
  `s = τ_ε ≤ 1 − 2^(−ε)` (`sieveSeq_pmPowerDampedRealWeight_le_of_four_dvd`: the only omitted divisor
  is the non-squarefree argument), so `E ≥ 4^(−ε)·#primes(N,2N]`; boundaries `roughPrimeBoundary`
  injective. PNT count (`eventually_card_primes_first_octave_ge`, ≥ `N/(2 log N)`) + unit envelope
  below `5(N+1)` + C2 long window with `k = 1`.
  New insight: the two dissipation mechanisms (Möbius first-octave edges, damped sub-horizon prime
  boundaries) are one mechanism — rough-prime boundaries — which does not degenerate as `ε → 0`.
  This removes the README trap "damping radii shrink with N" for the sign question: no radius at
  all is needed on `[0,1]`. Standard axioms (8 audited); wired.
- **C4 · The all-boundary Fermi trace is exactly four times better conditioned** — five modules:
  `DirichletChainDoubledPrefixAndRobinRamp`, `FermiAllBoundaryTraceDirichletRayBound`,
  `FermiAllBoundaryTraceConditioningBound`, `FermiAllBoundaryTraceRisingSinePackets`,
  `FermiAllBoundaryTraceFourfoldConditioningGain`. Headline:
  `fermiAllBoundaryInverseConstant_logb_limit` (`K^all_N/(log₂N)² → 1/π²`, signed and nonnegative)
  and `fermiSelected_div_allBoundary_inverseConstant_limit` (`K_N/K^all_N → 4`, both cones).
  Answers README §5 "Observation: whether adding the cells 2∥n to the schedule changes the sharp
  loss": yes — by exactly a factor four; the loss stays `(log₂N)²`. Mechanism: per dyadic ray the
  selected trace leaves the step base→first double unobserved (free bottom, mixed boundary,
  ground mode `cos((k+½)π/(2L+3))`, constant `(2L/π)²`); the `n ≡ 2 (4)` cells observe it, so the
  ray is Dirichlet at both ends (saturation tail = 3-step ramp; low-level weight deficit = half-step
  split, `dirichlet_chain_soft_prefix_bound`), ground mode `sin((k+1)π/(L+2))`, constant `(L/π)²`.
  Explicit: `(1−4/(L+2))(L+2)²/π² ≤ K^all_N` (`fermiAllBoundaryInverseConstant_ge`, N ≥ 4) and
  `K^all_N ≤ ((L+m+6)²/(π²(1−5π²/(48(L+m+6)²)))+1)(1+2^−(m+1))` (`…_le_explicit`). Packets are
  nonnegative (`fermiDyadicSinePacket_nonneg`, reflection `2 sin((k+1)θ) ≥ sin(kθ)`); exact mass
  `(L+2)/2` and Dirichlet energy identity. Reuses corpus `RHTower.autocorrelation_chain_sine_bound`,
  BVI/THIM ray decompositions and `fermiPhysicalInverseConstant_logb_limit`. Standard axioms
  (20 audited); five modules wired; THIM lint-clean.
- **C5 · The Buchstab slope law and dissipation at prime horizons** —
  `BuchstabSlopeLawAndPrimeHorizonDissipation`. `sum_sieveSeq_mul_eq_sum_floor_gcd` (any weight):
  `Σ_{j≤B} s_{N,c}(mj) = Σ_{d≤N} c(d)⌊B/(d/gcd(d,m))⌋`. `sieveL2PrefixEnergy_moebius_horizon_step_eq`:
  exact Möbius horizon step `E_m − E_{m−1} = μ(m)²B + 2μ(m)Σ_{d<m}μ(d)⌊B gcd(d,m)/d⌋`, `B = ⌊M/m⌋`.
  `abs_horizon_step_sub_slope_le`: at squarefree `m` the step is `B·λ(m) ± 2(m−1)`, Buchstab slope
  `λ(m) = 1 + 2μ(m)Σ_{d<m}μ(d)gcd(d,m)/d` (`buchstabSlope_prime`: `1 − 2m(p−1)`).
  `sieveL2PrefixEnergy_moebius_six_step`: horizon 6 step is exactly `−B − 2⌊B/5⌋` (negative slope).
  `eventually_prime_horizon_step_nonneg`: for all large primes `p` and every `M ≥ 2p`,
  `E_{p−1}(M;μ) ≤ E_p(M;μ)` (three ratio regimes: quadratic window floor identity = 1; middle
  `p ≤ B < 4p` via three Mertens values and `M(x)=o(x)`; large `B ≥ 4p` via `m(p−1) ≤ 1/4`).
  New insight: README frontier "half-band criterion |S₂| ≤ (B−2)/2 would make every downward
  Buchstab step dissipative at large ratios" — at prime horizons the criterion is exactly the
  Möbius-mean bound and holds by PNT at every ratio `B ≥ 2` (B = 1 is the −1 first-octave step);
  at composite horizons the slope can be negative (m = 6), so step dissipation is a prime
  phenomenon governed by the arithmetic slope `λ(m)`. Built missing olean
  `THIM.BuchstabFermiCovarianceAndQuotientChainBridge`. Standard axioms (8 audited); wired.
- **C6 · Buchstab slopes: horizon derivative of the Selberg form, and inheritance under large
  primes** — `BuchstabSlopeInheritanceAndSelbergDerivative`.
  `selbergTotientDiagonalForm_moebius_step(_squarefree)`: `Q_Sel(m) − Q_Sel(m−1) = μ(m)²λ(m)/m`
  exactly — the large-ratio Buchstab slope of C5 is the horizon derivative of the period mean square.
  `buchstabSlope_mul_prime`: exact identity `λ(aq) = λ(a) − 2μ(a)(G_a(aq−1) + A(a)/q)` for squarefree
  `a ≥ 1`, prime `q > a`, `G_a(x) = Σ_{d≤x} μ(d)gcd(d,a)/d`. `tendsto_gcdTwistedHarmonicMoebius`:
  `G_a → 0` (decomposition over `f | a` into coprime harmonic Möbius sums, `gcdTwistedHarmonicMoebius_eq`;
  each `→ 0` from `m(x) → 0` by the contracting recursion `m_{fp}(n) = m_f(n) + m_{fp}(n/p)/p`,
  `tendsto_coprimeHarmonicMoebius_prod`). `tendsto_buchstabSlope_mul_prime`: `λ(aq) → λ(a)`.
  `eventually_two_mul_prime_horizon_step_neg`: for all large primes `q`, adding horizon `2q`
  strictly lowers `E(M;μ)` at every `M ≥ 2q(8q+1)` (`λ(2) = −1`).
  New insight: rough absorption lifts from responses to horizon steps — large prime factors are
  invisible to the Buchstab slope, which is a function of the small-prime part of the horizon
  (`λ(q)→1`, `λ(2q)→−1`, `λ(3q)→0`, `λ(pq)→1−2m(p−1)`). Standard axioms (11 audited); wired.
- **C7 · Damped prime horizons reverse the Möbius slope; the crossover diverges as ε → 0** —
  `DampedPrimeHorizonSlopeReversalAndCrossover`.
  `eventually_pmPowerDamped_prime_horizon_step_neg`: for every `ε > 0`, all large primes `p`, every
  `M ≥ p`: `E_p(M; c_ε) < E_{p−1}(M; c_ε)` (opposite of C5 at `ε = 0`). Mechanism: floor form
  `pmPowerDamped_prime_horizon_step_eq_floor` (step `= r²B − 2rΣ_{d<p}c_ε(d)⌊B/d⌋`, `r = p^{−ε}`);
  completing the floor sum to horizon `B` gives `Σ_{j≤B}τ_ε(j) ≥ κ_ε B`
  (`exists_pos_linear_le_pmPowerDampedDivisorSum`, mean `1/ζ(1+ε) > 0`), omitted divisors `d ≥ p`
  cost `≤ B(1+ε)/ε·p^{−ε}` (`abs_sum_floor_pmPowerDamped_tail_le`, corpus p-series tail) — all uniform
  in `B`, so `step ≤ rB((1+2C)r − 2κ) < 0`. Damped prime slope `dampedPrimeSlope ε p =
  p^{−ε} − 2Σ_{d<p}μ(d)d^{−1−ε}` (`= λ(p)` at ε = 0, `dampedPrimeSlope_zero`); slope law
  `abs_pmPowerDamped_prime_step_sub_slope_le` (error `2p^{−ε}(p−1)`); explicit continuity
  `buchstabSlope_sub_le_dampedPrimeSlope` (`λ_ε(p) ≥ λ(p) − ε log p (2p−1)`);
  `pmPowerDamped_prime_horizon_step_pos` (injection for `ε log p(2p−1) ≤ λ(p)/2`, `⌊M/p⌋λ(p) > 4(p−1)`);
  `exists_injecting_prime_horizon_of_small_damping` and
  `not_exists_uniform_pmPowerDamped_dissipation_threshold` (no damping-uniform threshold).
  New insight: the horizon mechanics of the PM family are discontinuous at ε = 0 in the cofinal
  sense — Möbius prime horizons inject energy, every damped one beyond a crossover `P(ε)` dissipates,
  and `P(ε) → ∞`. The Möbius picture is the ε → 0 limit only on bounded horizon ranges; the PM
  receiver (fixed small ε, T → ∞) lives entirely in the dissipative regime. Corpus had only the
  first-band/quadratic-window values (`…BuchstabFermiCovarianceAndQuotientChainBridge`). Standard
  axioms (10 audited); wired.
- **C8 · The crossover scale of damped prime horizons: `log p*(ε) = (log(1/(2ε)) + o(1))/ε`** —
  `DampedPrimeHorizonCrossoverScale`. `abs_finiteHarmonicSum_pmPowerDamped_sub_le` /
  `abs_pmPowerDampedDivisorDensity_re_sub_le`: Abel summation against `m(t)` gives
  `|ρ_ε − H_ε(n)| ≤ 2 sup_{t≥n}|m(t)|·(n+1)^{−ε}` uniformly in `ε` (real series
  `hasSum_pmPowerDampedRealWeight_div`, `ρ_ε = 1/ζ(1+ε)`). `dampedPrimeSlope_bounds`:
  `p^{−ε}/2 − 2ρ_ε ≤ λ_ε(p) ≤ (3/2)p^{−ε} − 2ρ_ε` past an absolute `P₀`.
  `dampedPrimeSlope_crossover`: ∀δ>0 ∃ absolute `P₀`, for all small `ε > 0`, primes `p ≥ P₀`:
  `log p ≤ (1−δ)Λ(ε)` ⇒ `λ_ε(p) > 0`; `log p ≥ (1+δ)Λ(ε)` ⇒ `λ_ε(p) < 0`, `Λ(ε) = log(1/(2ρ_ε))/ε`
  (`dampedCrossoverScale`). `tendsto_mul_dampedCrossoverScale_sub_log`: `εΛ(ε) − log(1/(2ε)) → 0`
  (corpus `ρ_ε/ε → 1`). `pmPowerDamped_prime_step_crossover`: same dichotomy for the energy steps at
  all large prefixes (`pmPowerDamped_prime_step_{pos,neg}_of_slope`).
  New insight: sharpens C7 from "the crossover diverges" to its exact location — the damped observer
  is Möbius-like (prime horizons inject) up to horizons `exp((1+o(1))log(1/(2ε))/ε)` and dissipative
  beyond; the threshold `P₀` is absolute (only `m(t) → 0` enters), the damping enters only through
  `ρ_ε`. Standard axioms (7 audited); wired.
- **C9 · The Möbius envelope ladder: exact rungs 11 and 13, defect sign to ratio 11, prime-shell
  growth** — `MobiusEnvelopeLadderAndPrimeShellResponses`.
  `sieveSeq_moebiusReal_squarefree_eq`: for squarefree `r ≥ 2`, `s_{N,μ}(r) = −μ(r)Σ_{q|r,q(N+1)≤r}μ(q)`
  (beyond the horizon a response is a truncated Möbius divisor sum at the radical ratio);
  `abs_sieveSeq_moebiusReal_squarefree_le_ratio` (`|s| ≤ r/(N+1)`).
  `abs_truncated_moebius_divisor_sum_le_two/three` ⇒ `abs_sieveSeq_moebiusReal_le_two_of_radical_lt_eleven_succ`
  and `…_le_three_of_radical_lt_thirteen_succ` (every horizon). Exact: `sieveSeq_moebiusReal_rung_two_family`
  (`N = 105p−1`, `k = 1155p = 11(N+1)`, `s = −3`), `…_rung_three_family` (`N = 1155p−1`, `k = 15015p`,
  `s = 4`). `moebius_prefix_defect_nonpos_of_radical_lt_eleven_succ` and
  `moebius_positive_defect_requires_radical_ratio_eleven` (corpus had ratio 6). General
  `sieveSeq_moebiusReal_prime_shell`: primes `P` with max `Q` and pair products `> Q`, prime `ℓ > Q`:
  `n = ℓ∏P = Q(N+1)` has `s = −(−1)^{|P|}(|P|−1)`; `primeShell Q` (primes `p ≤ Q`, `p² > Q`) gives
  `abs_sieveSeq_moebiusReal_primeShell` and `eventually_card_primeShell_ge` (`≥ ⌊Q/2⌋/(2log⌊Q/2⌋)`).
  New insight: the response envelope is a ladder indexed by the radical ratio with exact rungs
  `5, 11, 13` (|s| ≤ 1, 2, 3), driven by which Möbius channels `q ≤ ratio` can open; the integer
  energy method certifies the defect sign exactly up to rung two (ratio 11, every horizon). The
  ladder grows almost linearly — `Q/log Q ≲ max|s| ≤ Q` at ratio `Q` — so endpoint-square methods
  necessarily fail at ratios `≍ (log N)^{O(1)}`, which is where C2's polynomial windows take over.
  Standard axioms (13 audited); wired.
- **C10 · Exact classification of injective dyadic Fermi schedules** —
  `FermiDyadicScheduleInjectivityClassification`. A schedule `S` reads `J(n)` at levels `v₂(n) ∈ S`
  (`FermiScheduleInjective`). Along a ray `z_k = s(2^k b)`: level 0 reads `−z_0`, level `k` reads
  `2z_{k−1} − z_k`, and the ray saturates (`sieveSeq_two_pow_mul_saturate`, `z_k = z_L` for
  `k ≥ L = ⌊log₂N⌋`) so all levels `> L` read `z_L`: `L+2` slots (`FermiSlotObserved`).
  `fermiScheduleInjective_iff` (N ≥ 1): injective ⇔ at most one slot missing (pinned-chain argument
  both ways; two missing slots `a < b` ⇒ invisible profile `z_k = 2^k` on `[a,b)` realized by a
  powers-of-two row). Corollaries: `fermiScheduleInjective_selected` (odd + four-divisible),
  `fermiScheduleInjective_univ`, `fermiScheduleInjective_odd_iff` (odd alone ⇔ `N = 1`),
  `not_fermiScheduleInjective_of_two_missing_levels`.
  New insight: README §3.9 knew two schedules; this is the complete answer to "which observation
  schedules see the horizon-N sieve": the dyadic levels form a chain pinned at both ends (odd
  boundaries pin the bottom, saturation pins the top), observation depth must equal the dyadic depth
  `⌊log₂N⌋+1`, and exactly one gap is tolerated — C4's conditioning factor 4 is the price of the
  gap at slot 1. Standard axioms (6 audited); wired.
- **C11 · Horizon law of the dissipation rate: `R_p − R_{p−1} = c(p)²/p` for every weight** —
  `SuccessorReserveHorizonLawAndPrimeDissipation`. `sieveSuccessorReserve_eq_sum_nonCoprimeLcmKernel`:
  `R_N(c) = Q_Sel − Q_Bez = Σ_{d,e≤N, gcd(d,e)>1} c(d)c(e)gcd(d,e)/(de)` (the dissipation rate of the
  renormalized defect is the non-coprime part of the lcm kernel). `sieveSuccessorReserve_succ_sub`:
  `R_m − R_{m−1} = (c(m)² + 2c(m)Σ_{d<m,(d,m)>1}c(d)gcd(d,m)/d)/m`. `sieveSuccessorReserve_prime_step`:
  `= c(p)²/p` at every prime, any weight (`…_prime_mono`). `sieveSuccessorReserve_of_prime_support`:
  weights vanishing on composites dissipate at exactly `Σ_{p≤N}c(p)²/p`. Möbius:
  `sieveSuccessorReserve_moebius_step` (`μ(m)²ϑ(m)/m`), `reserveSlope_prime` (`ϑ(p) = 1`),
  `reserveSlope_eq_buchstabSlope_sub` (`ϑ = λ − 2μ m_m(m−1)`), `coprimeHarmonicMoebius_mul_prime`,
  `tendsto_reserveSlope_mul_prime` (`ϑ(aq) → λ(a)`).
  New insight: the Möbius-mean dependence of the Selberg step (C5/C6 slope `1 − 2m(p−1)`) and of the
  Bézout step cancel exactly in their difference: the period dissipation rate jumps by the pure
  square `c(p)²/p` at every prime horizon, independently of any cancellation in the weight, and only
  non-coprime predecessors of a composite horizon move it otherwise. Standard axioms (10 audited);
  wired.
- **C12 · One-gap Fermi schedules: a middle gap is free, an edge gap costs four** — three modules:
  `FermiGapScheduleMixedChains` (`mixed_chain_energy_bound`: pinned/free chain of length `M` has
  constant `2−2cos(π/(2M+1))` by reflection; `mixed_chain_soft_prefix_bound` with half-weighted
  prefix), `FermiGapScheduleTwoChainRayBound` (`fermiGapPronicEnergy N c g` = all boundaries except
  dyadic level `g`; `fermiGapPronicEnergy_one` = selected trace; ray form; `gap_bottom_chain_bound`,
  `gap_top_chain_bound`; `fermiRaySieveEnergy_le_gap`; `one_div_mixedChainConstant_le`
  `1/λ_n ≤ ((2n+1)²+2)/π²`), `FermiGapScheduleMiddleGapLimit` (`sieveTotalPronicEnergy_le_gap`,
  `fermiGapInverseConstant`, `fermiAllBoundaryInverseConstant_le_gap` (`K^all ≤ K_g`),
  `fermiGapInverseConstant_one` (`K_1 = K_N` selected), `fermiGapInverseConstant_le_explicit`
  (`K_{h+1} ≤ (1+2^{−(m+1)})(max(2h+2m+5, 2(L−h)+7)²+2)/π²`), headline
  `fermiMiddleGapInverseConstant_logb_limit` (`K_{⌊L/2⌋+1}(N)/(log₂N)² → 1/π²`) and
  `fermiEdgeGap_div_middleGap_limit` (`K_1/K_mid → 4`)). C4 helpers made public
  (`fermiRay_sq_summable`, `fermiRay_value_tail`, `fermiRay_jump_tail`, weight floors).
  New insight: with C10 (exactly one gap is tolerated) this settles the price of the gap: a missing
  dyadic level splits each ray into two mixed chains, so the conditioning is governed by the longer
  piece, `≲ 4max(α,1−α)²/π²·L²` at relative depth `α`; the edge gap (selected trace) attains `4/π²`
  and the half-depth gap costs nothing — same `1/π²` as reading every boundary. Standard axioms
  (14 audited); wired.
- **C13 · The position law of a one-gap Fermi schedule: `K_g/(log₂N)² → 4max(α,1−α)²/π²`** —
  three modules: `FermiGapScheduleQuarterWavePackets` (general `fermiDyadicProfilePacket L y`,
  `sieveSeq_fermiDyadicProfilePacket_ray`, ray bounds `fermiRaySieveEnergy_profilePacket_ge`
  (`≥ (S−2)/b²`), `fermiRayGapEnergy_profilePacket_le` (`≤ E/b²`), `fermiGapInverseConstant_ge_profilePacket`
  (`K ≥ (S−2)/E`); `quarterWave_mass` (`Σ_{j≤n} sin²(jθ) = (2n+1)/4`, `θ = π/(2n+1)`) and
  `quarterWave_energy` (jump energy `= (2−2cosθ)·mass` via the free-end reflection `v_{n+1} = v_n`)),
  `FermiGapSchedulePositionLaw` (`gapBottomWave`, `gapTopWave`; `fermiGapInverseConstant_ge_bottom`
  `K_{h+1} ≥ ((2h+3)²−8(2h+3))/π²`, `fermiGapInverseConstant_ge_top` `≥ ((2(L−h)+1)²−8(2(L−h)+1))/π²`),
  `FermiGapSchedulePositionLimit` (`fermiGapInverseConstant_position_law_natLog`,
  `fermiGapInverseConstant_position_law`: if `h(N)/⌊log₂N⌋ → α`, `h → ∞`, then
  `K_{h(N)+1}(N)/(log₂N)² → 4max(α,1−α)²/π²`; `fermiQuarterGapInverseConstant_logb_limit` (`9/(4π²)`)).
  New insight: with C10 and C12 this completes the observation theory of dyadic schedules: injective
  iff ≤ 1 missing slot, and then the conditioning is *exactly* the square of the longer of the two
  half-observed mixed chains the gap creates — a continuous position law from `1/π²` (half depth,
  free) to `4/π²` (edges; the selected trace is the case α = 0). Matching quarter-wave packets attain
  it on each side. Standard axioms (11 audited); wired.
- **C14 · The actual PM receiver row has a global defect sign** — `PMCofactorRowRamanujanTruncation`,
  `PMCofactorRowGlobalDefectSign`. The cofactor row `c_Q` lives on `[1,Q]`
  (`pmCofactorRealWeight_eq_zero_of_gt`), so its horizon-`Q` response is its complete divisor sum
  at every integer: `sieveSeq_pmCofactorRealWeight_eq` (`s_Q(n) = Re Σ_{q≤Q} w(q)c_q(n)`).
  `norm_ramanujan_le_common_divisor_mass` (`|c_q(n)| ≤ Σ_{d|(n,q)} d`), `multiples_rpow_tail_le`,
  `abs_sieveSeq_pmCofactor_sub_divisorCoeff_le`: `|s_Q(n) − τ_ε(n)| ≤ (1+ε)/ε·τ(n)·Q^{−ε}` for all
  `n ≥ 1`; `eventually_abs_sieveSeq_pmCofactor_sub_divisorCoeff_le` (uniform `≤ η` on `n ≤ Q^r+1`).
  `eventually_pmCofactor_defect_nonpos_polynomial`: all `M ≤ Q^r` via just the first jump
  `τ_ε(1) − τ_ε(2) = 2^{−ε}` and the global unit envelope `0 ≤ τ_ε ≤ 1`;
  `pmCofactor_primeTail_mode_ge` (terminal mode `≥ ρ_ε²/(4Q^{2k+1})`, Euler form of `w(p)`);
  headline `eventually_pmCofactor_renormalizedDefect_nonpos_all`: for every `ε > 0`, eventually in
  `Q`, `D̃_Q(M; c_Q) ≤ 0` for every prefix `M`.
  New insight: README frontier lists only certified checkpoints for the cofactor row. The row is
  built to have the Selberg coordinates of `τ_ε`, so far beyond its horizon it *observes the complete
  damped divisor function* (error `τ(n)Q^{−ε} = Q^{−ε+o(1)}` on polynomial ranges); `τ_ε` never exceeds
  its initial value, so the trans-horizon envelope problem (ratio five, ladders, C9) does not arise for
  the receiver's actual row — its sign is controlled by one jump. Standard axioms (10 audited); wired
  (rebuilt the missing olean of `CofactorSquarefreeFermiSamplingAndPronicObservability`).
- **C15 · Bézout decorrelation of the Möbius observer** — `MoebiusBezoutDecorrelation`.
  `abs_coprimeHarmonicMoebius_one_le`, `abs_coprimeHarmonicMoebius_prod_le` (each prime of a
  squarefree modulus at most doubles `m_f`, via `m_{fp}(n) = m_f(n) + m_{fp}(n/p)/p` and strong
  induction along `n ↦ n/p`), `abs_coprimeHarmonicMoebius_le_card_divisors` (`|m_f(n)| ≤ τ(f)`),
  `selbergMultiplesCoord_moebiusReal` (`Y_N(f) = μ(f)/f · m_f(N/f)`),
  `bezoutCoprimeQuadraticForm_moebius_eq` (`Q_Bez(N;μ) = Σ_{f≤N} μ(f)/f²·m_f(N/f)²`); headline
  `tendsto_bezoutCoprimeQuadraticForm_moebius` (`Q_Bez(N;μ) → 0`, dominated convergence with
  `C² f^{−3/2}` and C6's `tendsto_coprimeHarmonicMoebius_prod`);
  `tendsto_sieveSuccessorReserve_sub_selberg_moebius` (`R_N(μ) − Q_Sel(N;μ) → 0`);
  `eventually_abs_period_correlation_moebius_le` (every full period of the Möbius response has
  unit-shift correlation `≤ ηL`, eventually in the horizon).
  New insight: the Bézout form is the period lag-one correlation; for the Möbius observer it is
  diagonal with the *summable* weights `μ(f)/f²` against coprime harmonic sums that are both
  τ-bounded and null, so successive Möbius observations decorrelate completely over a period, and the
  dissipation rate of the Möbius defect becomes the full period mean square of its response.
  Open: positivity of `liminf Q_Sel(N;μ)` (squarefree-weighted `φ(f)/f²` mass on `(N/2,N]`).
  Standard axioms (4 audited); wired.
- **C16 · The smooth-core law of Möbius Buchstab steps** — `MoebiusBuchstabStepSmoothCoreLaw`.
  `moebiusBandStep m B = μ(m)²B + 2μ(m)Σ_{j≤B} s_{m−1}(mj)`;
  `sieveL2PrefixEnergy_moebius_step_eq_bandStep` (`E_{n+1}(M;μ) − E_n(M;μ) = Δ(n+1, ⌊M/(n+1)⌋)`).
  `sieveSeq_moebius_mul_eq_neg_quotients` (`s_{m−1}(mj) = −Σ_{q|mj, q≤j} μ(mj/q)`),
  `sum_quotients_rough_cofactor` (quotients `q ≤ j ≤ B` do not see a cofactor with all primes `> B`),
  `moebiusBandStep_mul_rough` (`Δ(rm', B) = Δ(r, B)`, `r ≥ 2`, `m'` squarefree `B`-rough coprime),
  `moebiusBandStep_rough` (`Δ(m, B) = B − 2` for squarefree `B`-rough `m ≥ 2`), headline
  `moebiusBandStep_eq_smoothCore` (step depends only on the `B`-smooth core `gcd(m, B#)`),
  `moebiusBandStep_mem_finite_values` (in band `B` the step lies in `{0, B−2} ∪ {Δ(r,B) : r | B#}`),
  classes `moebiusBandStep_two` (`−B`), `moebiusBandStep_three` (`2⌊B/2⌋ − B`), `moebiusBandStep_six`
  (`−B − 2⌊B/5⌋`), energy forms `sieveL2PrefixEnergy_moebius_step_smoothCore`,
  `sieveL2PrefixEnergy_moebius_step_even_rough` (`n+1 = 2m'`, `m'` odd squarefree `B`-rough: step `−B`).
  New insight: README §3.6 classifies Möbius horizon steps in bands 1–3 (first-octave −1, parity
  dichotomy, `(2,3)`-adic law); these are the cases `B ≤ 3` of one exact law valid in every band —
  rough absorption acts on horizon steps through complementary quotients, so in band `B` the step is a
  function of the `B#`-core alone (finitely many classes; C6's slope inheritance `λ(aq) → λ(a)` is its
  `B → ∞` shadow, exact here at finite `B`). Standard axioms (9 audited); wired. Repaired the missing
  upstream olean `RHTower.CHMDSpectralGraphCompletion` (left by another agent's interrupted build).
- **C17 · The Möbius response is asymptotically white noise** — `MoebiusResponseWhiteNoiseLaw`.
  `tendsto_sum_bounded_mul_moebiusCoord_sq` (any bounded multiplier `w`: `Σ_{e≤N} w(e)Y_N(e;μ)² → 0`),
  `abs_ramanujanLagWeight_le_sigma` (`|c_e(h)| ≤ σ(h)`), `tendsto_periodCovariance_moebius`
  (`Cov_N(h; μ) → 0` for every lag `h ≥ 1`, via BSU's diagonalization
  `periodCovariance_eq_ramanujanLagWeight_diagonal`); `sum_totientRatio_le` (`Σ_{e≤X} e/φ(e) ≤ 4X`),
  `sum_window_le_periodCovariance_zero` (variance ≥ `Σ φ(e)/e²` over the odd squarefree top octave,
  where `m_e(1) = 1`), `sq_sum_inv_window_le` (Cauchy–Schwarz, `(Σ1/e)² ≤ 8Σφ(e)/e²`),
  `eventually_periodCovariance_moebius_zero_ge` (variance `≥ 1/288` at large horizons, density `4/π²`
  of odd squarefree integers); `tendsto_periodCorrelation_moebius` (`Cov_N(h)/Cov_N(0) → 0`),
  `tendsto_periodShiftDifferenceEnergy_div_variance_moebius` (every translation dissipates twice the
  variance), `eventually_sieveSuccessorReserve_moebius_ge` (`R_N(μ) ≥ 1/576`: by the period law the
  Möbius renormalized defect drops by `≥ L/576` per complete period).
  New insight: closes C15's open item. On the period torus the Möbius response is white noise: lag
  multipliers are bounded clock weights against summable `τ²/e²` masses and null coprime harmonic
  sums, while the variance is held up by the top octave `N/2 < e ≤ N` where the harmonic sum is
  frozen at `1`. The dissipation rate of the Möbius defect therefore has a horizon-uniform floor.
  Standard axioms (7 audited); wired. C15 olean rebuilt after its docstring edit.
- **C18 · Band averages of Möbius horizon steps and the energy profile** —
  `MoebiusBandAverageStepAndEnergyProfile`. `bandClassValue` (`v_B(1) = B−2`, `v_B(r) = Δ(r,B)`),
  `bandRoughDensity` (`δ_B = (6/π²)∏_{p≤B} p/(p+1)`), `bandAverageStep` (`A(B) = δ_B Σ_{r|B#} v_B(r)/r`).
  `moebiusBandStep_eq_sum_classes`; `bandCoreCount_eq` (core class `r` up to `X` ↔ squarefree
  `B`-rough integers up to `X/r`, bijection `m ↦ m/r`); `sum_moebiusBandStep_eq_classes`
  (exact class-count formula); headline `tendsto_sum_moebiusBandStep_div` (band-average law:
  `(1/X)Σ_{2≤m≤X} Δ(m,B) → A(B)`, via corpus RHTower `tendsto_fixedCoreSquarefreeCount_div`).
  `sieveL2PrefixEnergy_moebius_eq_one_sub_bandSteps`, `sum_Ioc_band_split` (horizons in
  `(M/(b+1), M/b]` lie in band `b`), `sieveL2PrefixEnergy_moebius_linear_horizon_eq_bands`,
  `tendsto_sieveL2PrefixEnergy_moebius_linear_horizon_bands` (`E_N((B+1)N;μ)/N →
  −Σ_b A(b)((B+1)/b − (B+1)/(b+1))`); `cofinalMobiusQuadraticProfile_eq_band_integral` (identity with
  BVI's quotient profile: `P(B) = −(B+1)Σ_{b≤B} A(b)/(b(b+1))`), `bandAverageStep_eq_profile`
  (`A(B) = (B+1)P(B−1) − B P(B)`), `bandAverageStep_one` (`−6/π²`), `bandAverageStep_two`
  (`−4/π²`), `cofinalMobiusQuadraticProfile_two` (`P(2) = 11/π²`, new value).
  New insight: the smooth-core law turns the Buchstab calculus into a density calculus — each band
  has a finite set of core classes with explicit Euler densities, so the mean horizon step exists
  and is a finite class average; integrating it across bands reproduces the BVI energy profile (built
  from Möbius dilation-pair densities) by a completely different finite formula, and conversely the
  mean step of every band is a second difference of the profile. Standard axioms (10 audited); wired.
- **C19 · The damped period variance and the non-commuting limits** —
  `DampedPeriodVarianceAndNonCommutingLimits`. `dampedGcdKernel` (`G(d,e) = (de)^{−ε}/lcm(d,e)`),
  `sum_box_dampedGcdKernel_le` (boxes are Selberg forms of `d^{−ε}`, `≤ ζ(1+ε)²ζ(1+2ε)`),
  `summable_dampedGcdKernel`; `pmPowerDampedDivisorCoeff_sub_sieveSeq` (`τ_ε − s_N` = divisors above
  the horizon), `sum_sq_divisorCoeff_sub_sieveSeq_le` (mean square of the trans-horizon tail ≤ gcd
  series on `(N,X]²`), `dampedGcdTail`, `tendsto_dampedGcdTail`; headline
  `tendsto_selbergTotientDiagonalForm_pmPowerDamped` (`Q_Sel(N; c_ε) → E[τ_ε²]` = RHTower
  `pmPowerDampedSecondDensity`, via complete periods `qN!` vs Cesàro means and
  `(a+b)² ≤ (1+η)a² + (1+1/η)b²` with adapted `η_N = √T_N + 1/(N+1)`),
  `tendsto_periodCovariance_pmPowerDamped_zero` (`Cov_N(0; c_ε) → V(ε)` = RHTower
  `pmPowerDampedDivisorVariance`), `tendsto_pmPowerDampedDivisorVariance_zero` (`V(ε) → 0`, from corpus
  `V(ε)/ε → 1/2`), `eventually_periodCovariance_pmPowerDamped_lt_moebius` (for all small `ε`, eventually
  in `N`: `Cov_N(0; c_ε) < Cov_N(0; μ)`).
  New insight: `lim_{ε→0} lim_N Var_N(c_ε) = 0 < 1/288 ≤ liminf_N Var_N(μ)` — the cofinal and damping
  limits do not commute. The Möbius variance floor (C17) lives entirely in the trans-horizon divisors,
  which every fixed damping suppresses (their mean square is a convergent gcd-series tail); the damped
  response freezes into the complete damped divisor function. Bridges THIM period forms to the RHTower
  PM-lane Haar moments of `τ_ε`. Standard axioms (8 audited); wired.
- **C20 · Prime pairing collapse and the prime-factor step law** —
  `PrimePairingCollapseAndPrimeFactorStepLaw`. Headline `sieveSeq_moebius_prime_pairing`: for a prime
  `p | k` and every truncation `X`, `s_X(k; μ) = Σ_{d ≤ X, d | k, p ∤ d, X/p < d} μ(d)` (pairs `d ↔ pd`
  cancel inside the horizon; `p² | d` is silent). `sieveSeq_moebius_even_collapse` (even `k`: odd
  divisors of the top octave). `primeFactorWindowCorrection`, `moebiusBandStep_prime_mul`
  (`Δ(pa, B) = −B − 2μ(a) Σ_{a<d<pa, p∤d} μ(d)⌊B gcd(d,a)/d⌋` for squarefree `pa`; `a = 1` is C5's
  prime step), `moebiusBandStep_two_mul_prime` (odd prime `q`: `Δ(2q, B) = −B` for every `B ≤ q+1`),
  `sieveL2PrefixEnergy_moebius_step_two_mul_prime` (`E_{2q}(M;μ) = E_{2q−1}(M;μ) − ⌊M/(2q)⌋` for
  `M < 2q(q+2)`).
  New insight: every prime factor of the observed integer folds the truncated Möbius sum onto a single
  top `p`-adic window of `p`-free divisors — a second exact normal form beside the complementary
  quotients, now on the divisor side. It splits every squarefree horizon step into the universal
  dissipation `−B` and a window correction, explains the even-step laws of README §3.6 in all bands,
  and upgrades C6's asymptotic slope `λ(2q) → −1` to the exact step `−B` for all `B ≤ q+1`.
  Standard axioms (5 audited); wired.
  Note on C20 (prior-art audit): for Möbius the pairing collapse is equivalent to the corpus chain law
  `sieveSeq_prime_mul_sub_eq_sieveSeq_div` (`s_H(pb) − s_H(b) = s_{H/p}(c(p·), b)`) plus squarefree
  saturation `sieveSeq_prime_pow_mul_eq_prime_mul_of_squarefree_support`; the identity was re-derived
  directly by pairing. C20's new content is the step side: `moebiusBandStep_prime_mul` and the exact
  even-prime horizon law.
- **C21 · The receiver row's Parseval spectrum and horizon-uniform variance** —
  `ReceiverRowParsevalSpectrumAndHorizonUniformVariance`. `dampedRamanujanCoeff` (`w_ε(e)` = Re of
  RHTower `pmPowerDampedRamanujanWeight`), `hasSum_dampedRamanujanCoeff` (`w_ε(e) = Σ_m c_ε(em)/(em)`),
  `tendsto_selbergMultiplesCoord_pmPowerDamped` (`Y_N(e; c_ε) → w_ε(e)`: Selberg coordinates converge
  to Ramanujan coefficients), `tendsto_selbergTotientDiagonalForm_pmPowerDamped_parseval` (dominated
  convergence with `ζ(1+ε)² e^{−1−2ε}`), `summable_totient_mul_dampedRamanujanCoeff_sq`,
  `pmPowerDampedSecondDensity_eq_parseval` (**Parseval**: `E[τ_ε²] = Σ_e φ(e) w_ε(e)²`, by uniqueness
  against C19), `pmPowerDampedDivisorVariance_eq_parseval` (`V(ε) = Σ_{e≥2} φ(e)w_ε(e)²`);
  `periodCovariance_cofactor_eq` (receiver row at horizon `Q+1`: variance = partial Parseval sum,
  via BVI `selbergMultiplesCoord_pmCofactorDivisorWeight`), `periodCovariance_cofactor_le_variance`
  (`≤ V(ε)` for **every** `Q`), `tendsto_periodCovariance_cofactor` (`→ V(ε)`),
  `sieveSuccessorReserve_cofactor_le` (receiver dissipation `≤ 2V(ε)` for every `Q`), headline
  `eventually_cofactor_below_moebius_floors` (for all small `ε`: variance `< 1/288` and dissipation
  `< 1/576` at every cutoff).
  New insight: the PM receiver row is the Ramanujan spectrum of `τ_ε` truncated at the horizon — its
  period variance is a monotone partial Parseval sum with limit `V(ε) ~ ε/2` — so its period statistics
  are bounded **uniformly in the horizon** at each fixed damping (the uniformity README §4 demands of
  the PM receiver), and at small damping they sit strictly below the Möbius floors (C17) at every
  horizon. A Parseval identity for `τ_ε` falls out of THIM period forms. Standard axioms (10 audited);
  wired. C19's `sum_multiples_rpow_le` made public.
- **C22 · Damped autocorrelation, small-damping whiteness, clock invisibility** —
  `DampedAutocorrelationAndClockInvisibility`. `periodCovariance_eq_of_primeFactors_eq` (**clock
  invisibility**: for every squarefree-supported weight and horizon, lags with the same primes have the
  same period covariance — the visibility clock `h/rad(h)` is invisible; via
  `selbergMultiplesCoord_eq_zero_of_not_squarefree` and BSU `ramanujanLagWeight_eq_of_gcd_eq`).
  `dampedRamanujanCoeff_sq_le` (`w_ε(e)² ≤ E[τ_ε]² μ²/φ²`, from `D_ε(e) ≥ φ(e)`),
  `summable_sqfreeTotientInv_div_totient` (`Σ μ²/φ² ≤ 16`, corpus Levinson bound), `dampedAutocorrelation`
  (`A_ε(h) = Σ_{e≥2} c_e(h) w_ε(e)²`), `abs_dampedAutocorrelation_le` (`|A_ε(h)| ≤ 16σ(h)E[τ_ε]²`),
  `tendsto_periodCovariance_pmPowerDamped_lag` (`Cov_N(h; c_ε) → A_ε(h)`), `periodCovariance_cofactor_lag_eq`
  and `abs_periodCovariance_cofactor_lag_le` (receiver row: same bound at every cutoff),
  `tendsto_dampedAutocorrelation_div_variance` (**small-damping whiteness**: `A_ε(h)/V(ε) → 0`).
  New insight: the damped response is not white at fixed ε (`A_ε(h) ≠ 0`), but its correlations are
  `O(ε²)` against a variance `~ε/2`, so the correlation structure commutes with the damping limit
  (`ε → 0` gives white, as Möbius) while the variance does not (C19). Clock invisibility: translation
  statistics of every squarefree-supported response (Möbius, damped, receiver) see only `rad(h)`.
  Standard axioms (9 audited); wired. C21's `abs_pmPowerDampedRealWeight_div_le` made public.
- **C23 · The damped prefix energy is linear: band structure dissolves under damping** —
  `DampedPrefixEnergyLinearityAndBandNonCommutation`. `card_divisors_gt_le` (on `k ≤ (B+1)N` at most
  `B` divisors exceed the horizon), `abs_divisorCoeff_sub_sieveSeq_le` (`|τ_ε(k) − s_N(k; c_ε)| ≤
  B(N+1)^{−ε}` uniformly on the window), `abs_sieveL2PrefixEnergy_pmPowerDamped_sub_le`, headline
  `tendsto_sieveL2PrefixEnergy_pmPowerDamped_linear_horizon` (`E_N((B+1)N; c_ε)/N → (B+1)E[τ_ε²]`),
  `tendsto_pmPowerDampedSecondDensity_zero`, `eventually_sieveL2PrefixEnergy_pmPowerDamped_lt_moebius`
  (every band `B ≥ 1`: for all small `ε`, eventually `E_N((B+1)N; c_ε) < E_N((B+1)N; μ)`).
  New insight: at fixed damping the trans-horizon energy profile is exactly linear in the band
  index (slope `E[τ_ε²] ~ ε/2`) — the Möbius band calculus (C16 classes, C18 band averages, BVI
  profile `P(B)` with `P(1) = 6/π²`, `P(2) = 11/π²`) is a pure `ε = 0` phenomenon, invisible to every
  fixed damping; third non-commuting limit after the period variance (C19) and dissipation (C21).
  Standard axioms (6 audited); wired.
- **C24 · Linear dissipation of the damped defect at an exact rate** (queue item 3) —
  `DampedLinearDissipationExactRate`. `dampedBezoutLimit`, `dampedDissipationRate` (`R(ε) = E[τ_ε²] −
  Σ_e μ(e)w_ε(e)²`), `tendsto_bezoutCoprimeQuadraticForm_pmPowerDamped` (`Q_Bez(N; c_ε) → Σ μ w²`),
  `tendsto_sieveSuccessorReserve_pmPowerDamped` (`R_N(c_ε) → R(ε)`), `dampedDissipationRate_pos`
  (`R(ε) ≥ 2w_ε(2)² > 0`), `tendsto_mean_successor_energy` (every horizon, every weight: Cesàro mean
  of `(Δs_N)²` → `2R_N`), `tendsto_mean_divisorCoeff_successor_energy` (**Cesàro law for `τ_ε`**:
  `(1/X)Σ(τ_ε(k+1) − τ_ε(k))² → 2R(ε)`, transferred from periodic responses through the gcd tail with an
  abstract uniform-approximation principle), headline
  `tendsto_sieveRenormalizedPrefixDefect_pmPowerDamped_linear` (`D̃_N((B+1)N; c_ε)/N → −(B+1)R(ε)`).
  New insight: queue item 3 (and C1's `N/log N`) resolved with an exact rate — the damped defect on
  linear windows dissipates linearly, the rate being the Haar dissipation of the complete damped
  divisor function, `R(ε) = Σ_{e≥2}(φ(e) − μ(e))w_ε(e)² ∈ (0, 2V(ε)]`. The prime-boundary mechanism of C1
  was only the visible part of a positive-density dissipation. C19's `sq_add_le_weighted` made public.
  Standard axioms (6 audited); wired.
- **C25 · The primitive (discrepancy) energy of the damped response: threshold at ε = 1/2** —
  `DampedPrimitiveEnergyHalfThreshold`. Uses BVI `twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal`
  (`12 E_prim(N;c) = Σ_{2≤q≤N} J₂(q) Y_N(q)²`, `E_prim` = period mean square of the zero-mean primitive,
  i.e. of the centered discrepancy `Σ_{j≤n} s_N(j) − nH_N`). `jordanTotient2_le_sq` (`J₂(n) ≤ n²`),
  `abs_selbergMultiplesCoord_pmPowerDamped_le`, `sievePrimitiveEnergy_pmPowerDamped_le` (ε > 1/2: bound
  `ζ(1+ε)²Σ q^{−2ε}` uniform in `N`), `tendsto_sievePrimitiveEnergy_pmPowerDamped` (ε > 1/2: `12E_prim →
  Σ_{q≥2} J₂(q)w_ε(q)²`), `tendsto_sievePrimitiveEnergy_pmPowerDamped_atTop` (**0 < ε ≤ 1/2: divergence**,
  prime modes `J₂(p)w_ε(p)² ≥ (3/4)E[τ_ε]²/p` and Mathlib `not_summable_one_div_on_primes`),
  `eventually_sievePrimitiveEnergy_moebius_ge` (Möbius: `⌊N/2⌋ ≤ 3456 E_prim(N; μ)`, linear growth from
  the top octave, C17 window lemmas).
  New insight: README §1.2/§5 say the PM receiver bound is known for ε ≥ 1/2 and open below. On the
  period torus the same threshold is exact: the damped discrepancy energy is horizon-uniformly bounded
  iff ε > 1/2 (mode masses `J₂ w_ε² ≍ q^{−2ε}`), diverges for ε ≤ 1/2, and grows linearly for Möbius.
  So no receiver estimate below one half can come from complete-period averages of the discrepancy;
  it must exploit the pronic weighting of small arguments. Standard axioms (5 audited); wired.
- **C26 · The half-damping law** — `HalfDampingDissipationLaw`.
  `dampedDissipationRate_eq_variance_sub_autocorrelation` (`R(ε) = V(ε) − A_ε(1)`, splitting the modes
  `e ≤ 1` off the Bézout limit), `tendsto_dampedDissipationRate_div_parameter` (`R(ε)/ε → 1/2`, since
  `|A_ε(1)| ≤ 16E[τ_ε]² = O(ε²)` by C22), `tendsto_dampedDissipationRate_div_variance` (`R(ε)/V(ε) → 1`),
  `tendsto_linear_defect_rate_div_parameter` (`−(B+1)R(ε)/ε → −(B+1)/2`).
  New insight: combined with C24 the trans-horizon defect has an explicit small-damping slope,
  `lim_{ε→0} (1/ε) lim_N D̃_N((B+1)N; c_ε)/N = −(B+1)/2`: at small damping every unit of window
  dissipates half the damping parameter, and dissipation and variance coincide to first order (the
  damped response is asymptotically white, C22). Standard axioms (4 audited); wired.
- **C27 · The Möbius energy profile through the fourth band** — `MoebiusEnergyProfileThroughFourthBand`.
  `bandAverageStep_three` (`A(3) = −4/π²`), `bandAverageStep_four` (`A(4) = −2/π²`), via the four core
  classes `1, 2, 3, 6` of bands 3–4 (density `3/π²·1/r`, class steps from C16);
  `cofinalMobiusQuadraticProfile_three` (`P(3) = 16/π²`: `E_N(4N; μ)/N → 16/π²`),
  `cofinalMobiusQuadraticProfile_four` (`P(4) = 41/(2π²)`: `E_N(5N; μ)/N → 41/(2π²)`),
  `bandAverageStep_neg_of_le_four` (the first four bands dissipate on average).
  New insight: README §3.6 gives only linear bounds `E_N(M;μ) ≤ 1 + B(M − N)` through the fourth band;
  the class calculus (C16+C18) gives the exact asymptotic energy through the fifth multiple of the
  horizon, with band means of `s²` equal to `6, 5, 5, 9/2` (units `1/π²`) — the squared response thins
  out band by band while each band still dissipates on average. Standard axioms (5 audited); wired.
- **C28 · The PM receiver row dissipates linearly at the Haar rate** — `ReceiverRowLinearDissipationRate`.
  Headline `tendsto_sieveRenormalizedPrefixDefect_cofactor_linear`: for every `ε > 0` and band `B`,
  `D̃_Q((B+1)Q; c_Q)/Q → −(B+1)R(ε)` for the actual PM cofactor row `c_Q = pmCofactorRealWeight ε Q`
  at horizon `Q`. Mechanism: C14's pointwise approximation `|s_Q − τ_ε| ≤ ((1+ε)/ε)τ(n)Q^{−ε}`, the
  divisor moments `Σ τ ≤ X(1+log X)` (BVI) and `Σ τ² ≤ X·invSum³` (RHTower), the bound
  `Q^{−ε}(1+log((B+2)Q))³ → 0` (`isLittleO_log_rpow_rpow_atTop`), bounded boundary values via
  `τ(k) ≪ k^{ε/2}`, and C24's Cesàro law for `τ_ε`; helpers `abs_gradient_receiver_sub_le`,
  `receiver_boundary_bounded`.
  New insight: the receiver's own row — the object of README §1.2's first receiver — carries the exact
  Haar dissipation of `τ_ε`: on every linear trans-horizon window its renormalized defect falls
  linearly at rate `R(ε) ~ ε/2` (C26). Its defect sign (C14) is thus a quantitative linear law, not
  only a sign. Standard axioms (1 audited); wired.
- **C29 · The pronic observable commutes with the damping limit** — `PronicEnergyCommutesWithDamping`.
  `abs_sieveSeq_le_card_divisors` (`|c| ≤ 1 ⇒ |s_N(n)| ≤ τ(n)`), `tendsto_sieveTotalPronicEnergy_of_pointwise`
  (pronic energy follows pointwise response limits; domination `τ(n)²/(n(n+1)) ≪ n^{−3/2}`),
  `tendsto_sieveTotalPronicEnergy_moebius` (`P(N; μ) → 1/2`), `tendsto_sieveTotalPronicEnergy_pmPowerDamped`
  (`P(N; c_ε) → Σ_n τ_ε(n)²/(n(n+1))`), `tendsto_dampedPronicLimit_zero` (that limit → 1/2 as ε → 0⁺).
  New insight: `lim_{ε→0} lim_N P(N; c_ε) = 1/2 = lim_N P(N; μ)` — the README §2.3 sieve pronic energy
  (the physical energy of the Fermi receiver) commutes with the damping limit, whereas the period
  variance (C19), dissipation (C21/C24) and trans-horizon profile (C23) do not. This locates the
  non-commutation precisely: it lives in the trans-horizon bulk that pronic weights suppress, so any
  receiver argument passing through pronic energies cannot see the Möbius horizon floor. Standard
  axioms (5 audited); wired.
- **C30 · The growth law of the discrepancy energy below one half** —
  `DampedDiscrepancyEnergyGrowthLaw`. `selbergMultiplesCoord_of_top_octave` (`Y_N(q) = c(q)/q` for
  `N < 2q`), `sievePrimitiveEnergy_pmPowerDamped_le_rpow` (`0 < ε < 1/2`: `12E_prim ≤ ζ(1+ε)²
  N^{1−2ε}/(1−2ε)` via HTGeometry `sum_rpow_sub_one_le`), `eventually_sievePrimitiveEnergy_pmPowerDamped_ge`
  (every `ε ≥ 0`: `⌊N/2⌋N^{−2ε} ≤ 3456 E_prim`, top-octave Jordan modes), headline
  `eventually_sievePrimitiveEnergy_pmPowerDamped_growth` (**`E_prim(N; c_ε) ≍ N^{1−2ε}`** for
  `0 < ε < 1/2`), `abs_coprimeHarmonicMoebius_le_ratio` (`|m_f(x)| ≤ f/φ(f)` for squarefree `f`,
  sharpening C15's `τ(f)`), `sievePrimitiveEnergy_moebius_le` (Möbius: `12E_prim ≤ 64N(1 + log N)`, with
  RHTower `sum_totientRatio_sq_div_le`; with C25 the Möbius discrepancy energy lies between `N/6912` and
  `(16/3)N(1 + log N)`).
  New insight: C25's threshold resolved into an exact power law — the damped discrepancy is a walk
  with `N^{1−2ε}` effective steps, interpolating continuously between the Möbius row (linear, up to
  log) and the bounded regime above one half. The exponent `1 − 2ε` is the period-torus shadow of the
  `1/2 − ε` loss in the PM receiver. Standard axioms (6 audited); wired. C25's `jordan_mode_le` made
  public.
- **C31 · Spectral escape of the Möbius response, tightness of the damped one** —
  `MoebiusSpectralEscapeAndDampedTightness`. `tendsto_moebius_low_spectral_mass` (for every `E`, the
  Möbius Ramanujan mode mass `Σ_{e ≤ E} φ(e) Y_N(e)²` → 0), `eventually_moebius_high_spectral_mass_ge`
  (for every `E`, eventually `Σ_{E < e ≤ N} φ(e) Y_N(e)² ≥ 1/300`), `damped_high_spectral_mass_le`
  (damped mass above `E` ≤ `ζ(1+ε)² ((1+2ε)/(2ε)) E^{−2ε}` uniformly in `N`), `tendsto_damped_tail_bound`.
  New insight: the C17/C19 non-commutation of the period variance is now a statement about *where*
  the spectrum lives. The Möbius variance floor escapes to moduli comparable with the horizon (no
  fixed modulus retains mass), while the damped spectrum is uniformly tight around the Parseval
  spectrum of `τ_ε` (C21). The non-commuting limits are a loss of tightness, i.e. spectral escape to
  the horizon — the period-torus form of the README's trans-horizon mechanism. Standard axioms (4
  audited); wired.
- **C32 · Second-order law of the damped variance and dissipation** (README §5 frontier item
  "second-order terms of V(ε) and R(ε)" — resolved) — `DampedVarianceAndDissipationSecondOrderLaw`.
  `tendsto_pmPowerDampedSecondDensity_second_order` (**`E[τ_ε²] = ε/2 + o(ε²)`**: γ cancels between
  `ζ(1+2ε)` and `ζ(1+ε)^{-2}`; Euler correction `1 − H(ε) ≤ 64ε²Σ_p p^{−3/2}`; Mathlib
  `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right`), `tendsto_pmPowerDampedDivisorVariance_second_order`
  (**`V(ε) = ε/2 − ε² + o(ε²)`**), `dampedBezoutLimit_eq_parity` (exact: `Σ_e μ(e)w_ε(e)² =
  (1 − (2^{1+ε}−1)^{−2})·Σ_{e odd} μ(e)w_ε(e)²`), `abs_dampedBezoutLimit_le` (`|Σ_e μ(e)w_ε(e)²| ≤
  128ε E[τ_ε]²` for `ε ≤ 1`, i.e. `O(ε³)`), `tendsto_dampedDissipationRate_second_order` (**`R(ε) = ε/2 +
  o(ε²)`**), `tendsto_dampedAutocorrelation_one_second_order` (`A_ε(1) = −ε² + o(ε²)`),
  `tendsto_dampedDissipationRate_sub_variance` (`(R − V)/ε² → 1`).
  New insight: V and R separate at second order by exactly the squared mean. The dissipation follows
  the full second moment, because the uncentred lag-one Bézout mean is cubic: parity (one of `n, n+1`
  is even, and `τ_ε(2m)` carries `1 − 2^{−ε}`) factors out an `O(ε)` prime-2 term. Neighbours are
  anti-correlated at exactly the scale `E[τ_ε]²`. Standard axioms (8 audited); wired.
- **C33 · The damped crossover: Euler's constant and an additive window** (README §5 frontier items
  "second-order term of εΛ(ε)" and "prime horizons with log p = Λ(ε) + O(1)" — both resolved) —
  `DampedCrossoverEulerConstantAndAdditiveWindow`. `tendsto_pmPowerDampedDivisorDensity_re_second_order`
  (`ρ_ε = ε − γε² + o(ε²)`), `tendsto_dampedCrossoverScale_sub_main` (**`Λ(ε) = log(1/(2ε))/ε + γ +
  o(1)`**, i.e. `εΛ(ε) = log(1/(2ε)) + γε + o(ε)`; squeeze `(ρ−ε)/(ερ) ≤ log(ρ/ε)/ε ≤ (ρ−ε)/ε²`),
  `tendsto_exp_dampedCrossoverScale_mul` (crossover prime `e^{Λ(ε)}(2ε)^{1/ε} → e^γ`),
  `dampedPrimeSlope_additive_crossover` (**past one absolute `P₀`, for all small ε: `λ_ε(p) > 0` when
  `log p ≤ Λ(ε) − ε`, `< 0` when `log p ≥ Λ(ε) + ε`**; uses RHTower `exists_abs_deningerHarmonicPartial_log_rate`
  `|m(t)| ≪ (log t)^{−3}` against the gap `ε²·2ρ_ε`), `dampedPrimeSlope_explicit_crossover`
  (inject for `p ≤ e^{γ−δ}(2ε)^{−1/ε}`, dissipate for `p ≥ e^{γ+δ}(2ε)^{−1/ε}`),
  `pmPowerDamped_prime_step_additive_crossover` (energy-step form).
  New insight: the multiplicative window `(1±δ)Λ(ε)` of the earlier crossover shrinks to an additive
  window `Λ(ε) ± ε` (relative width `ε²/log(1/ε)`). The crossover prime is a Mertens-type constant
  `e^γ` times `(2ε)^{−1/ε}`: Euler's constant enters through `ζ(1+ε) = 1/ε + γ + o(1)`. A horizon at
  `log p = Λ(ε) + c` with fixed `c ≠ 0` has slope of sign `−sign c` for all small ε. Standard axioms
  (6 audited); wired. C32's `tendsto_riemannZeta_one_add_sub_inv` made public.
- **C34 · The long-window regime starts at the quadratic scale** (README §5 "least long-window
  threshold" — explicit threshold lowered from `11N⁵ + 8N³` to `10N² + 8N`) —
  `QuadraticLongWindowThreshold`. `abs_finiteHarmonicSum_moebiusReal_le_one` (`|m(N)| ≤ 1` via RHTower
  `abs_sum_moebius_div_le_one`), `two_mul_moebius_defect_le_quadratic_window` (every `N ≥ 2`,
  `M ≥ 10N²`: `2D̃_N(M;μ) ≤ 4 − (M − 10N²)/(2N)`; BVI quadratic window law
  `two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq` + Bertrand terminal mode),
  `moebius_defect_nonpos_of_quadratic_window` (**`D̃_N(M;μ) ≤ 0` for `M ≥ 10N² + 8N`, every `N ≥ 2`**),
  `eventually_two_mul_moebius_defect_le_uniform_slope` (eventually: slope `1/288` uniform in `N`, via
  C17's white-noise floor), `eventually_moebius_defect_neg_all` (**eventually `D̃_N(M;μ) < 0` strictly at
  every `M ≥ 2N`**; polynomial window only up to `N³`), `abs_finiteHarmonicSum_pmPowerDamped_le_three`,
  `two_mul_pmPowerDamped_defect_le_quadratic_window`, `pmPowerDamped_defect_nonpos_of_quadratic_window`
  (damped: `D̃_N(M;c_ε) ≤ 0` for `M ≥ 10N² + 72N^{1+2ε}` at every `N ≥ 2`).
  New insight: the README's quintic threshold (from `S_N ≤ N⁵`) is three powers too pessimistic.
  Bounded Möbius harmonic sum + quadratic observability put the explicit threshold at the natural
  scale `S_N ≍ N²`. The global sign at large horizons becomes strict on `M ≥ 2N`, and the polynomial
  window is only needed up to `N³`. Standard axioms (8 audited); wired.
- ~~C35 · damped autocorrelation and the singular series~~ — **WITHDRAWN, not counted.** A parallel
  BVI agent proved the same law 90 s earlier: BVI `HardyLittlewoodSingularSeriesOfTheDampedSource`
  (`tendsto_dampedAutocorrelation_div_density_sq`: `A_ε(h)/ρ_ε² → 𝔖(h) − 1`, Euler product, `𝔖(odd) = 0`,
  `𝔖(even) > 0`, plus the joint `(ε, Q)` receiver-row limit). The duplicate THIM module was deleted and
  unwired; C36 now builds on the BVI series. C32's `moebiusReal_two_mul_odd`/`moebiusReal_four_mul`
  remain public.
- **C36 · Period correlations of the Selberg row are the singular series** —
  `SelbergRowPeriodCorrelationsSingularSeries`. Row `ℓ_N = barbanVehovWeight N` (`μ(d)log(N/d)`, response
  = Selberg's truncated `Λ_N`). `selbergMultiplesCoord_barbanVehov_eq` (`Y_N(e) = μ(e)T_e(N/e)/e`, RHTower
  `barbanVehov_inner_eq`), `tendsto_selbergMultiplesCoord_barbanVehov` (`Y_N(e) → μ(e)/φ(e)`, RHTower
  `tendsto_coprimeLogMoebius_squarefree`), `tendsto_finiteHarmonicSum_barbanVehov` (`H_N → 1`),
  **`tendsto_periodCovariance_barbanVehov` (`Cov_N(h;ℓ_N) → 𝔖(h) − 1` for every `h ≥ 1`;** dominated by
  `σ(h)A²μ²/φ²` via BVI `abs_selbergMultiplesCoord_barbanVehovWeight_le`), `tendsto_periodCorrelation_barbanVehov`
  (`H² + Cov → 𝔖(h)`: complete-period Goldston–Yıldırım law), `tendsto_periodCovariance_barbanVehov_odd`
  (`→ −1`), `tendsto_periodCovariance_barbanVehov_zero` (variance `→ ∞`, modes `→ μ²/φ`, RHTower
  `tendsto_sum_sqfreeTotientInv_div_log_one`), `tendsto_periodCorrelation_barbanVehov_normalised` (normalised
  correlations `→ 0`), `selberg_and_damped_tangent_correlations_agree` (Selberg horizon limit =
  `lim A_ε(h)/ε²`, the latter derived from BVI's `ρ_ε²`-normalised law with `ρ_ε/ε → 1`). Uses BVI
  `hardyLittlewoodSingularSeries`, `hasSum_singularSeriesTerm_ge_two`, `hardyLittlewoodSingularSeries_eq_zero_of_odd`.
  New insight: the literal Möbius row is white on the period torus (C17, all lag covariances → 0).
  Its Selberg log-tangent carries the prime-pair singular series at every lag, with divergent variance.
  The horizon limit of the Selberg tangent and the Haar second-order limit of the damped row
  (BVI) coincide: at the level of lag correlations, the order of the horizon and damping limits
  does not matter, in contrast to the variance (C19). Standard axioms (9 audited); wired.
  **Count after C36: 35 counted contributions (C35 withdrawn).**
