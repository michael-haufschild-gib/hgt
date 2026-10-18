import GaloisForLFunctions.BezoutValuationIncidence.DilationProfileIntegerJumpCoupling
import GaloisForLFunctions.BezoutValuationIncidence.DilationSuccessorLeastSeedResonance
import GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge
import GaloisForLFunctions.RHTower.BeurlingSystemDecomposition
import GaloisForLFunctions.RHTower.ArithmeticCotangentPhaseTransport
import GaloisForLFunctions.RHTower.ArithmeticLogarithmicCotangent
import GaloisForLFunctions.TransHorizonIncidenceMechanics.UnconditionalSchurRatioAndGlobalLowPrimeBudget
import GaloisForLFunctions.TransHorizonIncidenceMechanics.StrictMobiusMarginAndUniformDampingStability

/-!
# Beurling Gibbs Geometry vs. Bézout Successor Seeds, Logarithmic Cotangent Transport, and Unconditional Schur Collar / Radical-Fiber Margins for Wall 1

This module bridges three major families of existing corpus theorems into
`GaloisForLFunctions.BezoutValuationIncidence` to target Tools 2, 3, and 4 of the Wall 1
programme (`docs/reports/walls/bezout-wall1-programme.md`):

1. **Tool 2 — Beurling Generalized Prime Invariance vs. $\mathbb{Z}$-Lattice Bézout Successor Seeds (§1):**
   - `RHTower.BeurlingSystemGibbsGauge` and `RHTower.BeurlingSystemDecomposition` prove that on
     **every** abstract Beurling generalized prime system `B : BeurlingSystem` (the free commutative
     monoid `Multiset B.Label` with `1 < B.labelNorm p`), five foundational multiplicative structures
     hold without any additive integer-lattice input:
     (i) exact Möbius divisor inversion `B.sum_moebius_divisors`,
     (ii) strict transverse log-submodularity of the squarefree exponential-Gibbs table
     `B.gibbsWeight_mul_lt`,
     (iii) divided-log prime-power completion `B.log_labelNorm_div_log_intNorm_replicate`,
     (iv) uniform depth-zero Gamma gauge enclosure `(B.truncate 2).gammaGauge_mem_Icc_of_truncate`,
     and
     (v) the exact three-sector zero/one/higher large-prime decomposition
     `B.phi_eq_apertureSum_sub_tsum_add`.
   - Because all five hold for arbitrary Beurling systems (including Diamond–Montgomery–Voronin
     systems violating RH), any proof route relying solely on multiplicative divisor lattices or
     one-large-prime Buchstab splits is blocked by the Beurling invariance obstruction.
   - By contrast, `DilationProfileIntegerJumpCoupling` and `DilationSuccessorLeastSeedResonance`
     couple the continuous Hilbert profile `pmRamanujanDilationProfile r hr (p / q)` directly to
     the $\mathbb{Z}$-specific pronic integer-cell series `ramanujanIntegerDilationGram r p q`,
     resolve all additive lags $h = pa - qb$ at quadratic horizon $Q^2$ with error $\le B_r^2 / Q$,
     and isolate the least positive Bézout successor seed $pa = qb + 1$
     (`leastSuccessorSeed p q`, `successorLeastSeedResonance R p q`) with uniform inverse-scale
     error (`beurling_invariance_vs_bezout_successor_seed_wall1_bridge`).

2. **Tool 3 — Kuzmin–Landau Cotangent Transport on the Logarithmic Lattice (§2):**
   - Bridges `RHTower.PhaseCotangent` (`ArithmeticCotangentPhaseTransport`) and
     `RHTower.LogarithmicCotangent` (`ArithmeticLogarithmicCotangent`) into
     `BezoutValuationIncidence`:
     - Exact non-resonant and resonant chronological phase transport (`phaseUnit_step_with_resonance`,
       `weightedPhaseDefect_eq`) and strict negativity of unweighted first-band prefixes with
       strictly decreasing increments (`phaseDefect_neg`).
     - For the literal logarithmic lattice phase
       `logarithmicPhase n t j = t / (2π) * (log(n + j) - log n)`, increments are positive, strictly
       decreasing (`logarithmicPhase_increment_strictAnti`), and bounded above by the harmonic step
       $t / (2\pi(n + j))$ (`logarithmicPhase_increment_lt`); the unweighted defect is strictly
       negative below $2\pi n$ (`logarithmicPhase_defect_neg`) and non-increasing beyond any
       sub-resonant head (`logarithmicPhase_defect_le_head`), while the weighted defect equals the
       exact Riemann zeta / power-sum remainder source functional `sourcePhaseDefect σ t M`
       (`logarithmic_cotangent_transport_and_zeta_source_wall1_bridge`).

3. **Tool 4 — Unconditional Horizon-Uniform Schur Collar Ratio & Damped Möbius Radical-Fiber Stability (§3):**
   - Bridges `TransHorizonIncidenceMechanics.UnconditionalSchurRatioAndGlobalLowPrimeBudget` and
     `TransHorizonIncidenceMechanics.StrictMobiusMarginAndUniformDampingStability`:
     - The horizon-independent Schur ratio bound
       $m_a(x) \le 4 e^{4t}(m_a(t+x) - m_a(t-x))$ (`oddProfile_le_four_exp_four_mul_sub`), its
       super-exponentially damped refinement (`oddProfile_le_damped_four_exp_four_mul_sub`), the
       unconditional 1-for-1 collar-minus-direct excess bound via `absorbedArchSlice`, and the
       summed low-prime von Mangoldt collar budget (`unconditional_schur_collar_and_low_prime_budget_wall1_bridge`).
     - The strict unit defect margin $D_N(M; \mu) \le -1$ on six-horizon prefixes
       (`moebius_prefix_defect_le_neg_one_of_lt_six_succ`), uniform positive-damping stability
       $D_N(M; c_\varepsilon) < -1/2$ across infinite radical fibers and arbitrary prime powers
       (`exists_uniform_damping_radius_all_certified_margin`,
       `exists_uniform_damping_radius_power_margin`,
       `exists_damping_radius_counterfamily_power_separation`), and the sharp universal ratio $C \le 5$
       and additive buffer $b < 5$ characterizations under strictly positive damping
       (`strict_mobius_margin_and_damping_stability_wall1_bridge`).
-/

set_option autoImplicit false

open scoped BigOperators Topology ArithmeticFunction.Moebius
open Finset Real Complex MeasureTheory Set
open RHTower RHTower.PhaseCotangent RHTower.LogarithmicCotangent
open RHTower.CHMDPolar RHTower.CHMDDoobGraph RHTower.ThetaSourceWard RHTower.PhiDivisorEnergy
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-! ## Section 1: Beurling Generalized Prime Invariance vs. $\mathbb{Z}$-Lattice Bézout Successor Seeds (Tool 2) -/

/-- **Universal Beurling Multiplicative Package (`BeurlingSystemGibbsGauge` & `BeurlingSystemDecomposition`):**
On any abstract Beurling system `B : BeurlingSystem`, generalized Möbius divisor inversion,
strict transverse log-submodularity of `B.gibbsWeight`, divided-log prime-power completion, and
depth-zero Gamma gauge enclosure in $[1, 2]$ after truncating labels below $2$ all hold purely from
free-monoid label geometry. -/
theorem beurling_universal_gibbs_and_gauge_package
    (B : BeurlingSystem) [DecidableEq B.Label]
    (g : Multiset B.Label) {x : ℝ} (hx : 0 < x)
    {A C : Finset B.Label} (hAC : (A \ C).Nonempty) (hCA : (C \ A).Nonempty)
    (p : B.Label) {k : ℕ} (hk : k ≠ 0) (q : (B.truncate 2).Label) :
    (∑ d ∈ g.powerset.toFinset, B.moebius d = if g = 0 then 1 else 0) ∧
    (B.gibbsWeight x (A ∪ C) * B.gibbsWeight x (A ∩ C) <
      B.gibbsWeight x A * B.gibbsWeight x C) ∧
    (Real.log (B.labelNorm p) / Real.log (B.intNorm (Multiset.replicate k p)) = 1 / (k : ℝ)) ∧
    ((B.truncate 2).gammaGauge q ∈ Set.Icc (1 : ℝ) 2) :=
  ⟨B.sum_moebius_divisors g,
   B.gibbsWeight_mul_lt hx hAC hCA,
   B.log_labelNorm_div_log_intNorm_replicate p hk,
   B.gammaGauge_mem_Icc_of_truncate q⟩

/-- **Beurling Three-Sector Zero/One/Higher Large-Label Decomposition (`BeurlingSystemDecomposition`):**
For any discrete Beurling system `B` with linear counting constant `C`, the full Möbius-Gibbs sum
`B.phi x` splits into the zero-large-label aperture sum `B.apertureSum z x`, the negative sum of
large-label dilated aperture sums `-∑' p : {p // z < B.labelNorm p}, B.apertureSum z (B.labelNorm p * x)`,
and the higher-large-label remainder `B.higherLargeSum z x`. -/
theorem beurling_zero_one_higher_large_label_decomposition
    (B : BeurlingSystem) (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) (z : ℝ) :
    B.phi x = B.apertureSum z x + B.oneLargeSum z x + B.higherLargeSum z x ∧
    B.oneLargeSum z x =
      -∑' p : {p : B.Label // z < B.labelNorm p},
        B.apertureSum z (B.labelNorm (p : B.Label) * x) ∧
    B.phi x =
      B.apertureSum z x -
        (∑' p : {p : B.Label // z < B.labelNorm p},
          B.apertureSum z (B.labelNorm (p : B.Label) * x)) +
        B.higherLargeSum z x :=
  ⟨B.phi_eq_apertureSum_add hdisc hC hx z,
   B.oneLargeSum_eq_neg_tsum hdisc hC hx z,
   B.phi_eq_apertureSum_sub_tsum_add hdisc hC hx z⟩

/-- **Tool 2 Bridge — Abstract Beurling Invariance vs. $\mathbb{Z}$-Lattice Bézout Successor-Seed Coupling:**
Contrasts the universal multiplicative Beurling identities (which hold on every abstract
`BeurlingSystem`) against the $\mathbb{Z}$-specific integer-jump coupling of
`pmRamanujanDilationProfile`:
1. Every rational scale pair $(p+1)/(q+1)$ equals its pronic integer-cell Gram series
   $\sqrt{p+1}\sqrt{q+1} \sum_n \operatorname{re}\widetilde c_r(\lfloor n/(p+1)\rfloor)\operatorname{re}\widetilde c_r(\lfloor n/(q+1)\rfloor)/\operatorname{pronicSeq}(n)$
   and is resolved by finite additive lag sectors $h = (p+1)a - (q+1)b$ at quadratic horizon
   $Q^2 = \max(p+1, q+1)^2$ with error $\le B_{r+2}^2 / Q$.
2. For coprime scales $p, q > 1$, the least positive successor seed `(a, b) = leastSuccessorSeed p q`
   satisfies $p a = q b + 1$ ($1 \le a \le q$, $1 \le b$).
3. Replacing the $h = 1$ successor sector inside `pmRamanujanDilationProfile (r+2) _ ((k+n+2)/(k+m+2))`
   by $(\sqrt{q}/\sqrt{p}) \cdot \operatorname{successorLeastSeedResonance}(r+2, p, q)$ leaves a
   uniform error of at most $(B_{r+2}^2/(r+2) + (r+2)\varphi(r+2)^2)/(k+2)$. -/
theorem beurling_invariance_vs_bezout_successor_seed_wall1_bridge
    (r k n m : ℕ) {pCop qCop : ℕ} (hpCop : 1 < pCop) (hqCop : 1 < qCop)
    (hcop : Nat.Coprime pCop qCop) :
    let R := r + 2
    let p := k + n + 2
    let q := k + m + 2
    let Q := max (p + 1) (q + 1)
    let H := p * q * R
    (pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) =
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * ramanujanIntegerDilationGram R p q) ∧
    (|pmRamanujanDilationProfile R (by dsimp [R]; omega)
        (((p + 1 : ℕ) : ℝ) / (q + 1 : ℕ)) -
      Real.sqrt (p + 1 : ℕ) * Real.sqrt (q + 1 : ℕ) *
        (∑ h ∈ (dilationJumpPairs (Q * Q) (p + 1) (q + 1)).image
          (dilationJumpGap (p + 1) (q + 1)),
          ramanujanDilationLagSector R (p + 1) (q + 1) (Q * Q) h)| ≤
      pmRamanujanPrimitiveBound R ^ 2 / (Q : ℝ)) ∧
    (1 ≤ (leastSuccessorSeed pCop qCop).1 ∧ (leastSuccessorSeed pCop qCop).1 ≤ qCop ∧
      1 ≤ (leastSuccessorSeed pCop qCop).2 ∧
      pCop * (leastSuccessorSeed pCop qCop).1 = qCop * (leastSuccessorSeed pCop qCop).2 + 1) ∧
    (|pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector R p q H h) - ramanujanDilationLagSector R p q H 1) -
        (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) * successorLeastSeedResonance R p q| ≤
      (pmRamanujanPrimitiveBound R ^ 2 / (R : ℝ) + (R : ℝ) * (R.totient : ℝ) ^ 2) /
        ((k + 2 : ℕ) : ℝ)) := by
  dsimp only
  refine ⟨pmRamanujanDilationProfile_eq_integerDilationGram (by omega) (by omega) (by omega),
    dilationProfile_quadratic_horizon_coupling r (k + n + 2) (k + m + 2),
    leastSuccessorSeed_spec hpCop hqCop hcop,
    dilation_profile_least_successor_seed_uniform r k n m⟩

/-! ## Section 2: Kuzmin–Landau Cotangent Transport on the Logarithmic Lattice (Tool 3) -/

/-- **Tool 3 Bridge — Logarithmic-Lattice Cotangent Transport & Zeta Source Remainder Identity:**
Unifies `ArithmeticCotangentPhaseTransport` and `ArithmeticLogarithmicCotangent` inside
`BezoutValuationIncidence`:
1. Every logarithmic phase increment `logarithmicPhase n t (j+1) - logarithmicPhase n t j` at
   positive anchor $n > 0$ and height $t > 0$ is strictly positive, strictly decreasing in $j$, and
   bounded above by $t / (2\pi(n + j))$.
2. Below the first-band threshold $t < 2\pi n$, every corrected unweighted phase prefix with
   $M \ge 1$ is strictly negative (`phaseDefect (logarithmicPhase n t) M < 0`), and at any Exact
   closing phase $t \log((n + M + 1)/n) = 2\pi K$ the raw sine sum is strictly negative.
3. For arbitrary positive height $t > 0$, once $t < 2\pi(n + J)$, `phaseDefect (logarithmicPhase n t)`
   is non-increasing for all $M \ge J$.
4. For all real $\sigma, t \in \mathbb{R}$ and $M \in \mathbb{N}$ (including resonances), the actual
   Riemann zeta / Euler–Maclaurin source remainder functional `sourcePhaseDefect σ t M` equals the
   weighted Kuzmin–Landau cotangent drift sum plus `resonantPhasePrefix`. -/
theorem logarithmic_cotangent_transport_and_zeta_source_wall1_bridge
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (σ : ℝ)
    {J M : ℕ} (hbandJ : t < 2 * Real.pi * ((n : ℝ) + J)) (hJM : J ≤ M) :
    (0 < logarithmicPhase n t (J + 1) - logarithmicPhase n t J ∧
      logarithmicPhase n t (J + 2) - logarithmicPhase n t (J + 1) <
        logarithmicPhase n t (J + 1) - logarithmicPhase n t J ∧
      logarithmicPhase n t (J + 1) - logarithmicPhase n t J <
        t / (2 * Real.pi * ((n : ℝ) + J))) ∧
    (0 < chordCotangent (logarithmicPhase n t) (J + 1) -
      chordCotangent (logarithmicPhase n t) J) ∧
    (phaseDefect (logarithmicPhase n t) M ≤ phaseDefect (logarithmicPhase n t) J) ∧
    (sourcePhaseDefect σ t M =
      weightedPhaseDefect (logarithmicPhase 1 t) (powerWeight 1 σ) M) ∧
    (sourcePhaseDefect σ t M =
      (∑ j ∈ Finset.range M,
        ((powerWeight 1 σ (j + 1) - powerWeight 1 σ j) *
          Real.sin (2 * Real.pi * logarithmicPhase 1 t (j + 1)) / 2 -
        (powerWeight 1 σ (j + 1) * chordCotangent (logarithmicPhase 1 t) (j + 1) -
          powerWeight 1 σ j * chordCotangent (logarithmicPhase 1 t) j) *
          (1 - Real.cos (2 * Real.pi * logarithmicPhase 1 t (j + 1))) / 2)) +
      resonantPhasePrefix (logarithmicPhase 1 t) (powerWeight 1 σ) M) :=
  ⟨⟨logarithmicPhase_increment_pos hn ht J,
    logarithmicPhase_increment_strictAnti hn ht J,
    logarithmicPhase_increment_lt hn ht J⟩,
   logarithmicPhase_cotangent_step_pos hn ht J hbandJ,
   logarithmicPhase_defect_le_head hn ht hbandJ hJM,
   sourcePhaseDefect_eq_weighted σ t M,
   sourcePhaseDefect_eq σ t M⟩

/-- **First-Band Strict Negativity & Closed-Cycle Sine Sum Negativity on the Logarithmic Lattice:** -/
theorem logarithmic_cotangent_first_band_strict_neg_bridge
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (hband : t < 2 * Real.pi * n)
    {M : ℕ} (hM : 0 < M) :
    phaseDefect (logarithmicPhase n t) M < 0 ∧
    (∀ K : ℤ, t * Real.log (((n : ℝ) + (M + 1 : ℕ)) / n) = (K : ℝ) * (2 * Real.pi) →
      (∑ j ∈ Finset.range (M + 1), Real.sin (t * Real.log (((n : ℝ) + j) / n))) < 0) :=
  ⟨logarithmicPhase_defect_neg hn ht hband hM,
   fun K hclosed => logarithmicPhase_closed_prefix_neg hn ht hband hM K hclosed⟩

/-! ## Section 3: Unconditional Horizon-Uniform Schur Collar Ratio & Damped Möbius Radical-Fiber Margin (Tool 4) -/

/-- **Tool 4 Bridge (Part A) — Unconditional Horizon-Uniform Schur Collar Ratio & Summed Low-Prime Budget:**
Packages the unconditional resolution of Obstacle B from
`UnconditionalSchurRatioAndGlobalLowPrimeBudget`:
1. For $0 \le t$, $\frac{3}{2}t + \frac{1}{2}\log 2 \le a$, and $x \in [0, t/2]$, the odd profile
   satisfies both the super-exponentially damped Schur ratio bound
   $m_a(x) \le 4 e^{4t}\exp(-\pi e^{2(a-t+x)}(t-2x))(m_a(t+x) - m_a(t-x))$ and the horizon-uniform
   bound $m_a(x) \le 4 e^{4t}(m_a(t+x) - m_a(t-x))$.
2. For any finite set $S$ of low prime powers ($\frac{3}{2}\log d + \delta + L \le a$) and any even
   continuous compactly supported test profile $w$, the unweighted von Mangoldt sum of discrete
   prime-collar line integrals is bounded above by twice the half-line prime shift jumps plus the
   single global 2D absorbed archimedean integral over $(0, a) \times (\delta, a)$, and the
   full-line prime shift-jump sum plus the global 2D absorbed archimedean integral dominates twice
   the tail prime jump sum. -/
theorem unconditional_schur_collar_and_low_prime_budget_wall1_bridge
    {a t x δ L : ℝ} (ht : 0 ≤ t) (ha : 3 * t / 2 + Real.log 2 / 2 ≤ a)
    (hx : x ∈ Icc (0 : ℝ) (t / 2)) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : Real.log 2 / 2 ≤ δ + L) (S : Finset ℕ)
    (hS : ∀ d ∈ S, 3 * Real.log d / 2 + δ + L ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (heven : ∀ u, w (-u) = w u) :
    (oddProfile a x ≤
      4 * Real.exp (4 * t) *
        Real.exp (-(Real.pi * Real.exp (2 * (a - t + x)) * (t - 2 * x))) *
        (oddProfile a (t + x) - oddProfile a (t - x))) ∧
    (oddProfile a x ≤
      4 * Real.exp (4 * t) * (oddProfile a (t + x) - oddProfile a (t - x))) ∧
    ((∑ d ∈ S, vonMangoldtAtom d *
        (∫ u in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) u)) ≤
      2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ u in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) u)) +
      (∑ d ∈ S, vonMangoldtAtom d * primeCollarArchRatio δ L d) *
        ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) ∧
    (2 * (∑ d ∈ S, vonMangoldtAtom d *
        (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ u in Ioi (Real.log d / 2), oddProfileShiftJump a w (Real.log d) u))) ≤
      (∑ d ∈ S, vonMangoldtAtom d *
        (L * ((1 - Real.exp (-(Real.log d / 2))) * archLevyDensity (Real.log d + δ + L)) *
          (∫ u : ℝ, oddProfileShiftJump a w (Real.log d) u))) +
        (∑ d ∈ S, 16 * vonMangoldtAtom d * Real.exp (4 * Real.log d)) *
          ∫ y in Ioo (0 : ℝ) a, absorbedArchSlice a w δ a y) :=
  ⟨oddProfile_le_damped_four_exp_four_mul_sub ht ha hx,
   oddProfile_le_four_exp_four_mul_sub ht ha hx,
   sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_global_absorbedArchSlice
     hδ hL hδL S hS hw hwc,
   sum_vonMangoldt_fullLine_add_global_absorbedArchSlice_ge_tail
     hδ hL hδL S hS hw hwc heven⟩

/-- **Tool 4 Bridge (Part B) — Strict Möbius Defect Margin & Uniform Damping Stability on Infinite Radical Fibers:**
Packages the main theorems of `StrictMobiusMarginAndUniformDampingStability` inside
`BezoutValuationIncidence`:
1. Every nonempty Möbius prefix at $N \ge 2$ with $|s_N(M+1)| \le 2$ (and in particular every
   six-horizon prefix $M + 1 < 6(N + 1)$) has strict unit renormalized defect margin
   $D_N(M; \mu) \le -1$.
2. For every $N \ge 2$, there is a uniform positive damping radius $\delta_N > 0$ such that for all
   $|\varepsilon| < \delta_N$, every $M \ge 1$ with radical state $R_N(M+1) < 6(N+1)$ and every
   prime power $k^m$ ($2 \le k < 6(N+1)$, $m \ge 1$) satisfies
   $D_N(\cdot; c_\varepsilon) < -1/2$.
3. Requiring the unit pointwise envelope $|s_N(k; c_\varepsilon)| \le 1$ uniformly for all
   strictly positive $\varepsilon > 0$ on $2 \le k \le C N$ (or $k \le 5N + b$) is equivalent to
   the sharp undamped thresholds $C \le 5$ and $b < 5$. -/
theorem strict_mobius_margin_and_damping_stability_wall1_bridge
    {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M) (hhi : M + 1 < 6 * (N + 1)) (C b : ℝ) :
    (sieveRenormalizedPrefixDefect N M moebiusReal ≤ -1) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ L : ℕ, 1 ≤ L →
      horizonRadicalState N (L + 1) < 6 * (N + 1) →
      sieveRenormalizedPrefixDefect N L (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ)) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ k m : ℕ,
      2 ≤ k → k < 6 * (N + 1) → 1 ≤ m →
      sieveRenormalizedPrefixDefect N (k ^ m - 1) (pmPowerDampedRealWeight ε) < -(1 / 2 : ℝ)) ∧
    ((∀ (ε : ℝ) (N₀ k : ℕ), 0 < ε → 2 ≤ k → (k : ℝ) ≤ C * N₀ →
      |sieveSeq N₀ (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ C ≤ 5) ∧
    ((∀ ε : ℝ, 0 < ε → ∀ N₀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ 5 * N₀ + b →
      |sieveSeq N₀ (pmPowerDampedRealWeight ε) k| ≤ 1) ↔ b < 5) :=
  ⟨moebius_prefix_defect_le_neg_one_of_lt_six_succ hN hM hhi,
   exists_uniform_damping_radius_all_certified_margin hN,
   exists_uniform_damping_radius_power_margin hN,
   forall_positive_pmPowerDamped_unit_envelope_iff_ratio_le_five C,
   forall_positive_pmPowerDamped_unit_envelope_iff_additive_lt_five b⟩

end GaloisForLFunctions.BezoutValuationIncidence
