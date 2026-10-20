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
