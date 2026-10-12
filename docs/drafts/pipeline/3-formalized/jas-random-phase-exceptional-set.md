# JAS random-phase exceptional set

- **ID:** jas-rp-exc
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** jas-goal-loop-2026-10-09 rows 136–137, 148, 150–154
- **Statement:** On every set P of primes in (y, 2y], level-one JAS positivity fails on at most C·N^{|P|}·Σ_ρ|w_ρ| exp(−c y^{2ω_ρ} log y) of the phase vectors z_p = rω^{k_p}, where ω_ρ = ½ − |Re ρ − ½|. Hence the count is at most C·N^{|P|}·exp(−c y^{1−2α} log y) under Re ρ ≤ ½ + α, and C·N^{|P|}·exp(−(log y)^α) unconditionally for every α < 3/2.

## Goal
Find the largest set of JAS test vectors on which positivity is unconditional, and measure how far
it is from the constant vectors. RH is equivalent to positivity at the constant vectors on every
dyadic set (R:JointAncestryDyadicPhaseCapstone).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `RHTower.card_jasPhaseAggregate_re_neg_le_tsum`,
  `exists_card_jasPhaseAggregate_re_neg_le_dyadic_width`,
  `exists_card_jasPhaseAggregate_re_neg_le_dyadic_halfPlane`,
  `exists_card_jasPhaseAggregate_re_neg_le_dyadic_superpoly`
  (R:JointAncestryRandomPhaseWidthGraded). `lake build --old` green; axioms propext,
  Classical.choice, Quot.sound.
- [ ] 3 → 4  publication-ready

## Results (Lean)
1. Second moment, O(1/log y) (R:JointAncestryRandomPhasePositivity, R:JointAncestryDyadicPhaseCapstone; MUST-1312, MUST-1314).
2. Hoeffding/Chernoff, y^{−c} (R:JointAncestryRandomPhaseLargeDeviation; MUST-1316).
3. Width-graded count (this card; MUST-1320). For each zero, the linear phase terms satisfy
   |u_p| ≤ 2a·p^{−(1−|Re ρ−½|)}, so the variance is U_ρ = y^{−2ω_ρ}·Σ_P 4a²/p. Each zero gets its
   own tilt λ_ρ = t₀/(16U_ρ), and Markov's inequality over the phases gives
   #bad ≤ N^{|P|}(4/Φ(0))Σ_ρ|w_ρ|e^{1 − t₀²/(32U_ρ)}.
   - Half-plane α: exp(−c y^{1−2α} log y).
   - Unconditional: split the zeros at T = exp((log y)^{α'}). Below T use the VK width
     (log T)^{−θ}, θ > 2/3. Above T use the weight tail O(log T/T)
     (R:JointAncestryZeroTailBound). This gives exp(−(log y)^α) for every α < 3/2.

## Reading
- **Exponent duality.** A zero-free width (log T)^{−θ} gives exceptional exponent (log y)^{1/θ}.
  A half-plane α gives y^{1−2α} log y. RH gives y log y.
- **Constant vectors.** They form a proportion N^{1−|P|} ≈ exp(−y log N / log y) of the phase
  vectors. Counting excludes them only when y^{1−2α}(log y)² ≳ y log N, i.e. as α → 0. So the
  measure route reaches the receiver exactly at the RH point, and never before.
- Refinement available on paper: a per-zero threshold t_ρ ≍ log|γ_ρ| for high zeros improves the
  unconditional exponent to (log y)^{1+2/θ} = (log y)^{4−ε}. It is not formalized, because the
  conclusion is unchanged.

## Parseval identity and variance law (MUST-1324)
- **Statement (Lean, R:JointAncestryRandomPhaseParseval):**
  Σ_k |agg(k) − (1+r²)^{|P|}Φ(0)|² = (1+r²)^{2|P|} N^{|P|} Σ_{e≠0} κ_e² Φ(L_e)²
  (`sum_normSq_jasPhaseAggregate_sub_mean`).
- **Proof:** each factor is expanded as Σ_{e∈{0,+,−}} χ_e(k)h_e. The characters χ_e of (ℤ/N)^P
  are orthonormal for N ≥ 3, so Parseval applies. The coefficient of χ_e is κ_e Φ(L_e), because
  A_p = p^{−ρ−½} and B_p = p^{ρ−3/2}.
- **Corollaries:**
  - Single-prime patterns give the lower bound a²Σ_P Φ(log p)²/p².
  - Under a half-plane α: Σ_e κ_e²Φ(L_e)² ≤ M²(Π_P(1 + 2a²p^{2α−2}) − 1).
  - Variance receiver through Cauchy–Schwarz and the window-mean receiver
    (`abs_re_sub_half_le_of_phaseVariance`).
  - Exact equivalences: `exists_halfPlane_lt_half_iff_exists_phaseVariance` and
    `riemannHypothesis_iff_forall_phaseVariance`.
- **Reading:** the phase average sees only Φ², at signed prime-product lags. Even so, a subpower
  phase variance is a full RH receiver. It is equivalent to constant-vector positivity on dyadic
  sets, because both are equivalent to the half-plane bound through the window-mean receiver. The
  row-142 no-go is about direct counting, which compares the exceptional set with the proportion
  N^{1−|P|} without passing through the zeros.

## No-go closure (measure paradigm)
- **Exact killing mechanism:** a measure bound of exp(−F(y)) excludes the N constant vectors only
  if F(y) ≳ y log N/log y. The width-graded bound gives F ≍ y^{1−2Θ} log y, so this needs Θ = ½.
- **Strongest positive survivor:** the width-graded count and its exponent duality (formalized).
- **New insight:** the exceptional set is controlled zero by zero through y^{2ω_ρ}. The measure
  paradigm is a faithful transcription of the zero-free region and contains no extra positivity.
- **Status:** dependency-closed and formalized.

## Log
- 2026-10-12 — created directly in 3-formalized (module built and audited)
