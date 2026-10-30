# Walls ledger

Status: 30 October 2026, corpus `12ba3d87c6` plus working tree. **No core wall is crossed.**

**Three families of walls**, one for each property a crossing input must supply:

- **Σ — the critical sign.** A positivity statement that must hold with zero margin.
- **Π — square-root precision.** A count or cancellation that must be exact at x^{1/2}.
- **Γ — selection.** The statement must hold for ζ and fail for its gauge twins, at the trivial gauge point.

Each family is forced by theorems (§1). §5 reads all three off one object and names the single channel through which every crossing input has to pass: the archimedean place.

**Solved faces:**

- the sub-spacing Hodge index, and Weil positivity on every C² test supported within a fixed fraction of the spacing to the right of the logarithms log n, n ≤ N;
- complete Weil positivity at every fixed overlap, with its full conductor spectrum;
- twin resolution at bounded overlap;
- the rank-eight theta Hankel section;
- fixed conductor packets up to overlap (log N)^{1/19}.

**Sharpest open faces:**

- **Σ1b** — the edge payment: successor shells, Euler heads and the pole paid jointly at the cutoff edges.
- **Σ7** — a source law that makes the two reconstructed orientations of the Ξ resolvent agree.
- **Σ5** — finite Krein index, in its graded form: the growth of the de Bruijn–Newman nonreal count N(t) as t ↓ 0.

Links: [route report](route-obstacles.md) · [summary and next questions](obstacles-summary.md) · [route unification](route-unification-ledger.md) · [scoped no-gos](../rh-killed-routes.md) · [working log](../../../logs/review-3010-rev5-facts-2026-10-30.md).

- No builds were run.
- Evidence labels [L]/[K]/[S]/[P] follow the frontier map. [S] on a recent module means: statement and proof read in source, integration not checked.
- (inference) marks this review's interpretation.

| Strength tag | Meaning |
|---|---|
| [RH] | Equivalent to RH |
| [FS] | Finitely many off-line zeros; implies Lindelöf |
| [LH] / [QRH] | Lindelöf; zero-free strip Re s > Θ, Θ < 1 |
| [C%] | Critical-line proportion |
| [sub] | Open, implies no classical conjecture by itself |

## 1. Why there are exactly three families

| Family | Forcing theorems | What any crossing input must do |
|---|---|---|
| **Σ** | Extension no-go (`extension_forces_positivity`). E₁(c) → 0. At the critical overlap c*_N the margin of the complete form equals its synthesis error, 1/log N (`riemannHypothesis_iff_forall_critical_multiple`) [S]. The odd Markov form is never subcritical. The Hecke state is PD exactly from s = 1/2. The zero side of the explicit formula is a positive measure exactly under RH (`positive_duality_of_the_explicit_formula`) [S]. | Hold at the boundary of a positivity cone: there is no gap to spend and no monotone continuation from a positive range. |
| **Π** | `deciding_input_necessary_properties`. Producers are precision-blind. κ = 0 ⟺ one-sided √x log²x count. Syndetic Kronecker alignment excludes every eventual single-height power saving (`not_exists_eventually_atTop_PX_power_saving`) [S]. | Separate a from a + εn^{−η} for every η < 1/2; no known producer law does. |
| **Γ** | Gauge-invariant majorants are ≥ 3/4 at the trivial point (`threeQuarters_le_of_gaugeInvariant_bound`). Pointwise-closed statements are twin-blind. The sub-spacing Hodge index (one positive square) holds for every completely multiplicative sign twin (`twinAtomicIntersectionGram_isHyperbolic`, `liouville_isHyperbolic_and_not_metzler`) [S]. Nonnegative statistics are maximal at the trivial point and attain the same size at the Liouville antipode (`norm_twistSum_le_trivial`, `primeGaugeSum_liouville_add_trivial`) [S]. Λ ≥ 0 + FE + an entire completion admits off-line zeros. | Break the gauge symmetry at the trivial point through the discreteness of the prime support, the simple pole and the sign of the boundary term. Size statements cannot do it. |

(inference) Away from the endpoint the three are independent:

- Bounded-overlap complete positivity is selective and has fixed resolution, but is not critical.
- The Krein index is critical and precise by construction, but has no producer.
- Integrality producers are selective through Λ∗1 = log, but reach only Chebyshev precision.

## 2. Family Σ — the critical sign

| Wall | Content | Status |
|---|---|---|
| **Σ1 Growing-overlap complete positivity** | Positive at every fixed c, for the tilted spline and for every C² profile without real Fourier zeros; the low spectrum consists of conductor modes with energies E_m(c) ≥ 0 [K/L]. Fixed conductor packets are positive at c = (log N)^α for α < 1/19 [L]. RH ⟺ positivity whenever c⁴/log N → ∞, for every C² profile with ∫φ ≠ 0 [L]. For logarithmic Denjoy–Carleman profiles, RH ⟺ positivity at every bounded multiple of c*_N ≍ L(log L)², L = log log N [S]. The profiles with the smallest RH-complete overlap have real Fourier zeros, and fixed-overlap positivity is not proved for them. | Fixed c: **solved**. RH-complete overlap: **open [RH]**. |
| **Σ1a Defect-only confinement** | Unit vectors with defect ≤ γ + (k+1)log 2 + log 4 + 5 escape every conductor set below 2^k (`eventually_exists_unit_vector_escaping_conductors`) [L]. | **Exact boundary:** capture from the defect alone needs exponential conductor cutoffs. |
| **Σ1b Edge payment** | **Shells.** Any separate one-sided payment of the non-ratio shells costs C ≥ A²/(2ε), hence c⁹ at the reserve fraction (`TheShellsAloneCostTheSquareOfTheOverlap`) [L]. On conductor modes the shells repay log(2πc) [L]. On the top-band witness the two pole moments are computed exactly (`poleMoments_topWitnessVector`) [S]; the joint shell–pole cancellation theorem is absent from source. **Twins.** A twin's prime-form defect is exactly the sum of successor-disagreement shells (`twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`) [S]. **Euler heads.** The sharp head edge at m = Y couples details to far windows with strength √Y·L[a,b], L lower triangular with negative diagonal (`tendsto_headCoupling`, `headCouplingLimit_self_neg`) [S]; the capstone "Γ − head(p ≤ Y) has unbounded index" is absent from source. | Separate payment: **exact boundary**. Joint signed payment at the edges: **open [sub]**. |
| **Σ2 Extension** | A nondecreasing minorant of λ(L) that is nonnegative from some L₀ forces λ ≥ 0 everywhere. Soft tools move positivity only downward in L. | **Exact no-go.** |
| **Σ3 Criticality of the arithmetic Markov form** | The odd form is never subcritical. A folded supersolution of the full generator gives RH, given a factorization of every odd test through it (`riemannHypothesis_of_foldedSupersolution`) [S]. The archimedean place is Z-type; every obstruction is prime. μ(A) ≤ K exp((11/2)A − πe^{2(A−2)}) [L]. | **Open [RH]:** a positive supersolution of the full nonlocal generator. |
| **Σ4 Rank and order uniformity** | Rank-eight theta Hankel PSD for 0 < a < 1/2 [L]. Finite native tail = 2·(Gram-square mass) − 2·(local flux) [L]. No rank-uniform fraction of the new diagonal survives [K]. All-rank signed-center positivity ⟺ RH. | Each finite rank: **A**. All ranks: **open [RH]**. |
| **Σ5 Infinite genus / finite index** | κ = 2·#sector zeros. κ < ∞ ⟺ finite off-line support ⟺ bounded heat counts ⟺ eventual criticality [S]; κ < ∞ ⇒ LH. **Heat depth law** [S]: with D(y) = #zeros of depth > y, every t-uniform bound B on the zeros of H_t of height ≥ h satisfies D(2h) ≤ B, and D(h/2)/(2h²) is one such bound; t-uniform high counts at every h ⟺ the zeros approach the line ⇒ LH (`zerosApproachLine_iff_highCount`). Deep zeros: #{depth ≥ δ, ordinate in [X, 2X]} ≤ C log X·N(t) for t ≤ δ²/(C log⁴X) (`exists_card_deep_le_mul_nonrealZeroCount`) [S]. Known bound: N(t) ≤ C R log R, R = 2π exp((2/3+ε)/t) [L]. | **Open [FS].** Graded targets for N(t) in §6. |
| **Σ6 Realization** | Weil distribution = CCM operator trace. Complete Deninger carriers have bounded generators. Finite even and virtual graph realizations are impossible, additive prime-length realizations are commutative, and a Hölder mixing realization would give only a zero-free strip [L]. | **Open [RH]**; a Hölder mixing realization would give [QRH]. |
| **Σ7 Explicit image and orientation** | Every line-calibrated explicit statistic is the Weil form W; holomorphic clocks have Cesàro excess 0 or ∞; strip-holomorphic carriers vanishing on critical configurations vanish on all reflection-invariant ones [L]. On the Ξ divisor: RH ⟺ the resolvent vector equals its line reflection ⟺ the two source polarizations agree (`riemannHypothesis_iff_xiResolventLp_lineConj_fixed`, `riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`) [S]. Both orientations lie in one closed continued-Cauchy source carrier. | **Exact boundary:** same-point information needs a non-holomorphic operation. **Open [RH]:** a source law that forces the two orientations to agree. |
| **Σ8 Quantum** | **Configurations.** Collision charge O ∈ 2ℕ; O = 0 ⟺ critical; N ≤ N₀ + O [L]. **Actual Ξ.** Charge < 2 on every natural-height window ⟺ RH [S]. **𝔽_q.** Unitary ⟺ O < 2; the golden datum has O = 2 [L]. **Scalar model.** In the de la Vallée Poussin coupling the admissible order budget at distance 1/2 exceeds the first quantum once the growth factor is ≥ 2 (`one_le_quantumBudget_half`) [S]. | RH has integer margin 2 here. **Open [RH]:** a source bound O < 2. **Open [C%]:** O ≤ cN, c < 1/4. |
| **Σ9 Local-to-global signature** | Each local prime constituent log p·δ₀ − L_p lives on its tower. On ℤ^S, \|S\| ≥ 2, axis-supported kernels have index 0 or ∞, and every positive local assembly has infinite index (`negIndex_localAssembly_eq_top`) [S]. Matched against log M − γ, the prime form on the p-adic class pole vectors has one positive square (the pole) and a gap → p log p/(p − 1) below it (`eventually_isHyperbolic_classHodgeGram`) [S]. Coupling a full-rank prime block to a partner of counterterm rank r lets at most r prime directions survive (`finrank_primeSurvival_le_rank`) [S]. | Single prime: **solved**. Finite sieve: **open [sub]**. All primes with the archimedean glue: **open [RH]**. |

**Σ1 phase diagram (overlap axis).**

| Overlap c | State | Selective? |
|---|---|---|
| ≤ c★ (fixed fraction of spacing) | Hodge index proved for every N [L]; Weil ≥ 0 on all C² tests near the logarithms [S] | Hyperbolicity: no, it holds for every sign twin. Metzler sign: yes, Liouville fails it [S] |
| Fixed | Positive definite, attained bottom E₁(c) [K/L] | Yes for Liouville and cofinite flips. Single flips need c₀(p) ≍ p^{1/7}; every fixed c misses all large primes (`eventually_flip_posDef_of_large_prime`) [S] |
| (log N)^α, packets | α < 1/48 uniformly, α < 1/40 along schedules, α < 1/19 [L] | Packets only, not all vectors |
| Reserve | Gamma survives while c⁸ = o(log N); negative vectors have D ≤ C′c¹⁶ [L] | — |
| c*_N ≍ L(log L)² (DC profiles) | RH-equivalent at every bounded multiple; margin = synthesis error = 1/log N [S] | — |
| c⁴/log N → ∞ (every C² profile, ∫φ ≠ 0) | RH-equivalent [L] | — |

## 3. Family Π — square-root precision

| Wall | Content | Status |
|---|---|---|
| **Π1 Global law** | κ = 0 ⟺ ψ(x) − x ≤ C√x log²x ⟺ odd Liouville upper count [L/S]. | **Open [RH].** |
| **Π2 Deciding input** | A Count-sufficient criterion must reject Liouville, separate a from a + εn^{−η} (η < 1/2) and use unbounded aperture. Λ + εn^{−η} satisfies PNT and every short-interval law past 17/30 [S]. Count(a) ⟺ a − 1 ∈ 𝒬 [K]. | **Exact boundary.** |
| **Π3 Producer cost** | Adams mixed-jet multiplicity r on the q-torsion locus costs support 2^{qr}, sharply. Balanced factorial ratios cost (2 log 2 − ε)mn. Bézout and Riemann–Roch on 𝔾_m are linear; approximate integer vanishing is divisibility; twist towers collapse to proper prime powers [L]. On the gauge torus the Adams operations ψ^k form a Λ-ring, and ψ² fixes only the trivial point (`isAdamsFixed_two_iff`) [S]; they act on characters, not on integers. Over 𝔽_q Stepanov reaches √q. | Boundaries **exact**; a square-root producer over ℤ: **open [RH]**. |
| **Π4 Gamma reach** | The Gamma reserve pays Euler heads p ≤ Y while 32√Y log Y ≤ log A, i.e. up to Y ≈ (log A)² [L]. Euler costs are not summable, and the remainder needs prime cancellation. Beyond that range the head edge couples details to far windows at strength √Y (Σ1b) [S]. | **Exact boundary** below (log A)²; index divergence for growing heads in progress. |
| **Π5 Dispersion / parity** | No Type-II dispersion below the quadratic horizon for coherent prime blocks. Every short-window or balanced saving is a zero-free strip; the 5/6 strip ⟺ R = O(N^{5/3+ε}) [K]. Prime phases align syndetically at every fixed length, so single-height positivity reaches only X ≲ (log ξ)² [S]. | **Open [QRH]** and up. |
| **Π6 Depth visibility** | The single-horizon pole charge is depth-blind. Windowed modes see depth through N^{κ−Re z}M^{κ+Re z} [L]. Orbit correlation ≤ Ke^{σt} ⟺ zero width ≤ σ [L]. Refutation is finite, confirmation is not. | **Exact boundary**; the amplifier exists, a subexponential bound does not. |
| **Π7 Amplifier rank** | Orthogonal families on π(x) phases have ≥ binom(π(x)+k−1, k) members, cancelling the moment gain (`OrthogonalityAmplifiersAreTrivial`) [L]. | **Exact boundary**; a non-envelope amplifier over ℤ: **open [RH]**. |
| **Π8 Classical density layer and census** | Guth–Maynard; the density hypothesis on σ ≥ 5/6; VK; ≥ 0.6725 simple critical; 3/4-or-near-line dichotomy; 0 ≤ Λ_dBN < 1/8 [L]. Higher odd moments of a Gram bound its inertia (`sq_trace_pow_le_negIndex_mul`) [S]. Census past 3/4 needs the signed coalescent prime surplus ≤ N/18 at bandwidth 4/3 [L]. | **Formalized.** LH, DH below 5/6, 70%/75%: open. |
| **Π9 Exceptional zeros** | Uniform Dirichlet zero-free region except real zeros of real characters [L]; conductor-uniform log-derivative and Perron contours [S]. | **Open [Siegel].** |

## 4. Family Γ — selection

| Wall | Content | Status |
|---|---|---|
| **Γ1 Trivial gauge point** | θ_μ(0) = Θ; the typical exponent is 1/2; RH ⟺ the trivial point is typical. Gauge-invariant majorants are ≥ 3/4. Quadratic Dirichlet twins have exponent ≤ (2 + Θ)/6. A universal gauge floor 1/2 would force Θ = 1 [L]. | **Open [RH].** |
| **Γ2 Twin resolution** | Bounded overlap rejects Liouville and every cofinite flip [L]. Single flips need c₀(p) ≍ p^{1/7} [L]. Every nonempty finite flip set has sup over tests of the Weil-kernel index = ∞, while for ζ the supremum is κ(K_ζ), attained by the cubic spline (`iSup_negIndex_weightKernel_finiteFlip_eq_top`, `iSup_negIndex_weightKernel_vonMangoldt`) [S]. Unconditionally, ζ or the p-flip has infinite index [L]. | Bounded overlap: **solved**. Uniform in p at growing overlap: **open [RH]**. |
| **Γ3 Twin-blindness of soft structure** | Locality and pointwise-closed statements are twin-blind: twins are Bohr limits of vertical shifts [L]. The sub-spacing Hodge index holds for every sign twin [L/S]. Multiplicativity + polar matching + maximal gap 2 log 2 does not select ζ [L]. | **Exact boundary.** |
| **Γ4 Hecke invariance** | RH ⟺ the collided form is Hecke invariant ⟺ Hecke similitude ⟺ W = collided [L]. | **Open [RH].** |
| **Γ5 Source identification** | Λ ≥ 0, Euler product, exact FE and an entire order-one completion admit off-line zeros, with a continuous Λ-measure and a triple pole [L]. The simple-pole class is ζ; a positive measure with the FE is Riemann's prime measure [L]. | **Exact boundary:** selection must use the discreteness of the prime support and the simple pole. |
| **Γ6 Coherence and the boundary sign** | Nonnegative twisted statistics satisfy ‖S(x)‖ ≤ S(0) at every gauge point; the prime source sits ≥ √(ψ(N)/log N) gauge deviations above its mean, and that excess is the pole [S]. The divisor fibre Σ_{k\|ℓ}Λ(k)χ_x(k) is maximal exactly at the trivial point (Λ∗1 = log) [S]. The Liouville point has the same size with the opposite sign: S_N(ℓ) + S_N(0) = 2ψ(√N) [S]. The Möbius escape state on the torus has coefficient −(6/π²)/(p+1) at every prime: it leans toward the Liouville point (`tendsto_escapeCoefficient_prime`) [S]. | **Exact boundary:** no size statement selects ζ. Selection is the sign of the pole boundary term, read on signed nonpolar directions. |
| **Γ7 Affine extension** | A PD function on Aff(ℚ) whose dilation part is Weil's correlation has constant translation part on ℚ ∖ {0} (`weil_successor_blind`) [S]. Its extensions form one parameter box indexed by the critical zeros [S]. A dilation part forced by the integer successor dominates no nonzero archimedean PD function (`eq_zero_of_archimedean_le_integer_successor`) [S]. A ℤ-periodic successor with a dilation part continuous at 1 is constant on ℚ (`translation_eq_of_continuousAt_dilation`) [S]. | **Exact boundary:** Weil's correlation and the integer successor meet in no positive-definite component on Aff(ℚ). A successor-carrying carrier must be adelic or indefinite. |
| **Γ8 Poisson rigidity on the Weil pair** | A positive tent-self-dual measure with gap (−1, 1) ∖ {0} is a Dirac comb, and a one-sided gap gives only the local mass bound μ[s−½, s+½] ≤ (π²/4)ν{0} (`tentSelfDual_iff_eq_smul_diracComb`, `measure_Icc_le_of_poissonPair`) [S]. On the Weil pair the prime side carries both the positivity and the prime-free gap below log 2 (`weilFullFunctional_of_prime_free`) [S]. The zero side is a positive measure exactly under RH [S]. | **Exact boundary:** comb-type rigidity of the zero divisor needs zero-side positivity, which is RH. Unconditionally only density statements follow. |

## 5. How the walls interlock

| Bridge | Joins | Consequence (inference) |
|---|---|---|
| κ = #right zeros = Hodge defect; κ = 0 ⟺ one-sided count | Σ5 = Π1 | At the endpoint a critical sign and a precise count are one statement. |
| Uniform high heat count ⟺ zeros approach the line; deep count ≤ C log X·N(t) | Σ5 → Π8 | The heat flow turns the index into a depth-counting function of Ξ. Its growth as t ↓ 0 grades the distance between density theorems and finite support. |
| Finite ζ index ⇒ every p-flip has infinite index; sup_g κ = ∞ for flips | Σ5 = Γ2 | Finite index is selective by itself. |
| Twin defect = successor-disagreement shells; shells repay log c only jointly | Σ1b = Γ6 | The shells carry both the missing sign and the selection. Repayment can happen only on signed nonpolar directions, where coherence fails. |
| Gamma pays heads to (log A)²; the head edge couples at √Y | Σ1b → Π4 | Beyond square-logarithmic depth, absolute payment fails at the head's edge, and positivity needs PNT-level cancellation. |
| Hecke state PD ⟺ s ≥ 1/2; prime Poisson measure ≪ Haar ⟺ s > 1/2 | Σ = Γ = Π | The critical line is the Kakutani threshold of a product measure on the gauge torus. |
| RH ⟺ W = collided; the collided form is read from theta prefixes | Σ7 = Γ4 | The multiplicative reading (primes) and the additive reading (theta) of one divisor must agree. |
| Local towers assemble to index 0 or ∞; the archimedean factor is the only off-tower constituent | Σ9 = Γ7 | The archimedean place is the only glue between primes, and its counterterm has rank one. |
| Gauge-invariant data ≥ 3/4; typical exponent 1/2 | Γ1 → Π | Precision must be spent at one point of the gauge torus, not on average. |

**The common object** (inference, from the bridges above).

- Weil's correlation lives on the dilation group ℚ^×_{>0} = ⊕_p ℤ, whose dual is the prime (gauge) torus.
- **Σ** is its Bochner positivity.
- **Γ** is the location of the trivial character on that torus.
- **Π** is the Kakutani threshold s = 1/2 of the prime Poisson measure, where square-root precision sits.
- The same divisor has an additive reading (theta, successor) and a multiplicative reading (primes, dilation), and every wall is a form of their comparison.

**The single channel** (inference). The prime part of Weil's kernel is supported on the prime-power towers of ⊕_p ℤ. Everything that is not on a tower enters only through the archimedean kernel:

| What crosses | Where the corpus proves it passes through the archimedean place |
|---|---|
| Between two primes | Positive local assemblies have infinite index; finite nonzero index needs the off-tower constituent [S] |
| Between + and × | Consecutive integers share no prime incidence; their only coupling is the collar ω(log(1 + 1/k)) ≍ k/2 (`successor_localPair_bounds`) [S]. In the Euler gauge the archimedean kernel carries the successor connection (`gaugedArch_succ_nonneg_iff`) [S] |
| Through renormalization | The archimedean germ has rank-one counterterm and pays one prime direction [S] |
| Selection | The pole (archimedean polar term) is the coherent excess at the trivial point and flips sign at the Liouville antipode [S] |

A crossing input must therefore pay an infinite-rank prime debt through a rank-one channel. Absolute bounds cannot do this, only signed cancellation can. Over 𝔽_q all data lie on one Frobenius tower and the channel is not needed.

## 6. Status by face

"Solved" means the stated face is answered; it never means a route is closed.

| Face | Wall | Status |
|---|---|---|
| Sub-spacing Hodge index, ζ and twins | Σ1, Γ3 | **Solved [L]**, hyperbolicity not selective |
| Weil positivity on all C² tests near the logarithms | Σ1 | **Solved [S]** at width ≤ K★δ_N |
| Uniform margin at a fixed overlap ratio | Σ1 | **Exact boundary [S]**: the gap grows like K√(log N) |
| Complete positivity at fixed overlap, conductor spectrum | Σ1 | **Solved [K/L]** |
| Fixed packets at growing overlap | Σ1 | **Solved to (log N)^{1/19} [L]** |
| Defect-only capture | Σ1a | **Exact boundary [L]** |
| Separate shell payment | Σ1b | **Exact boundary [L]** |
| Twin defect as disagreement shells | Σ1b, Γ6 | **Solved [S]** |
| Top-band joint shell–pole cancellation | Σ1b | **In progress [S]**: pole moments proved, cancellation absent |
| Growing Euler-head index | Σ1b, Π4 | **In progress [S]**: coupling limit proved, capstone absent |
| Signed joint edge payment off the conductor span | Σ1b | **Open [sub]** |
| Positivity at the RH-complete overlap | Σ1 | **Open [RH]** |
| Extension of positivity ranges | Σ2 | **Exact no-go** |
| Ground state of the full nonlocal generator | Σ3 | **Open [RH]** |
| Rank-eight theta section | Σ4 | **Solved [L]**; rank nine: A |
| All-rank flux domination | Σ4 | **Open [RH]** |
| Heat depth law | Σ5 | **Solved [S]** |
| t-uniform heat count (finite index) | Σ5 | **Open [FS]** |
| Polynomial growth of N(t) | Σ5 | **Open [sub]**; gives O((log X)^{4a+1}) deep zeros [S] |
| Growth N(t) ≤ exp(Ct^{−α}), α < 1/4 | Σ5 | **Open [sub]**; gives X^{o(1)} deep zeros in [X, 2X] (inference from `exists_card_deep_le_mul_nonrealZeroCount`) |
| Realization without zero indexing | Σ6 | **Open [RH]** |
| Explicit image of same-point sums | Σ7 | **Exact boundary [L]** |
| Ξ-resolvent orientation receiver | Σ7 | **Solved [S]** (receiver) |
| Source law forcing the two orientations to agree | Σ7 | **Open [RH]** |
| Collision quantum O < 2 | Σ8 | **Open [RH]**; O ≤ N/4 **open [C%]** |
| Local Hodge index at one prime | Σ9 | **Solved [S]** |
| Hodge index on a finite sieve | Σ9 | **Open [sub]** |
| Producer cost (Adams, factorial, Bézout) | Π3 | **Exact boundary [L]** |
| Gamma reach for Euler heads | Π4 | **Exact boundary [L]** |
| Type-II horizon; single-height saving | Π5 | **Exact boundary [K/S]**; strips open [QRH] |
| Amplifier rank | Π7 | **Exact boundary [L]** |
| Classical density layer | Π8 | **Formalized [L]** |
| Bounded-overlap twin resolution | Γ2 | **Solved [L]** |
| Uniform selection at growing resolution | Γ2 | **Open [RH]** |
| Exponent at the trivial gauge point | Γ1 | **Open [RH]** |
| Coherence and antipode | Γ6 | **Exact boundary [S]** |
| Hecke invariance | Γ4 | **Open [RH]** |
| Source identification by Λ ≥ 0 + FE | Γ5 | **Exact boundary [L]** |
| Positive affine extension with integer successor | Γ7 | **Exact boundary [S]** |
| Poisson rigidity of the zero divisor | Γ8 | **Exact boundary [S]** |
