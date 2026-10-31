import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilResidualIsTheUpwardDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheConductorEnergyKeepsALogarithmicReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NearGammaDownwardCancellationHasPolynomialGrowth
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights

/-!
# Conductor-band bounds for the overlap and non-ratio prime operators

This module establishes operator-norm and quadratic-form bounds for `overlapMatrix`,
`downwardPrimeVector`, `upwardPrimeVector`, and `fullWeilNonRatioMatrix` on finite Ramanujan
conductor subspaces `conductorSubspace R N`:

* **Exact non-ratio transpose symmetry.** Swapping `(n, j)` on `Icc 1 N × Icc 1 N` identifies
  `⟪upwardPrimeVector φ c N x, x⟫ = ⟪downwardPrimeVector φ c N x, x⟫` for every vector `x`,
  reducing `⟪(overlapMatrix - fullWeilNonRatioMatrix) x, x⟫` identically to
  `-⟪overlapMatrix x, x⟫ + 2 ⟪overlapMatrix x - downwardPrimeVector x, x⟫`.
* **Collective downward-archimedean cancellation on `conductorSubspace R N`.** Assembling the
  modewise identity `overlapMatrix v_m - downwardPrimeVector v_m` across `1 ≤ m ≤ R` contracts the
  shared near kernels directly into `u` and the logarithmic divisor-jet packet
  `divisorJetHorizonVector R N a ∈ conductorSubspace R N`, while retaining `1 / √N` on the
  exterior strip `(N, exteriorPrimeCutoff c N]`.
* **Conductor-independent upward operator norm on `conductorSubspace R N`.** Integer separation
  restricts active upward inputs to `(N : ℝ) ≤ c e j`; combining the weighted Schur bound from
  `up_row_le` and `down_row_le` with the `log R`-free sub-horizon quotient tail cancels `√(log N)`
  identically.
* **Bilinear and intermediate-band overlap bounds.** Top-strip confinement on both factors bounds
  `|⟪overlapMatrix v_A, v_B⟫|` by `O(c (1 + log c)) ‖v_A‖ ‖v_B‖`. On packets supported on
  `(Q_1, R_2]`, log-kernel linearization and telescoping summation by parts over `m * l`-periodic
  autocorrelations suppress `|⟪overlapMatrix u, u⟫|` to
  `O(c^2 (1 + log c) / log N + c^5 log N / N + c^4 / √Q_1 + c^3 R_2^4 / N) ‖u‖^2`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Classical

namespace GaloisForLFunctions.CompletedArithmeticForms

open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory ArithmeticEffectivityTheory ArithmeticElectrostatics
  BezoutValuationIncidence HTGeometry
  RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis

/-! ### 1. Exact non-ratio transpose symmetry and completed energy upper bound -/

/-- Operator decomposition of `fullWeilNonRatioMatrix` into downward and upward prime vectors. -/
theorem fullWeilNonRatioMatrix_eq_downward_add_upward {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x =
      downwardPrimeVector φ c N x + upwardPrimeVector φ c N x := by
  ext n
  rw [fullWeilNonRatioMatrix_row_eq hφ hsupp hM hc hN, add_div]
  rfl

/-- Exact transpose symmetry between upward and downward non-ratio prime quadratic forms on all
horizon vectors. -/
theorem upwardPrimeVector_self_inner_eq_downward {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪upwardPrimeVector φ c N x, x⟫ = ⟪downwardPrimeVector φ c N x, x⟫ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c / N)
  let G0 := ∫ u, g u ^ 2
  let K := lagRange (Real.log N + c / N + 1)
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, x n * (upwardPrimeRow g N (primeHorizonExtension x) n / G0)) =
    ∑ n : PrimeHorizonIndex N, x n * (downwardPrimeRow g N (primeHorizonExtension x) n / G0)
  have hlhs :
      (∑ n : PrimeHorizonIndex N, x n * (upwardPrimeRow g N (primeHorizonExtension x) n / G0)) =
        ∑ n ∈ Icc 1 N,
          primeHorizonExtension x n * (upwardPrimeRow g N (primeHorizonExtension x) n / G0) := by
    rw [← sum_coe_sort (Icc 1 N)]
    exact sum_congr rfl fun n _ => by rw [primeHorizonExtension_coe]
  have hrhs :
      (∑ n : PrimeHorizonIndex N, x n * (downwardPrimeRow g N (primeHorizonExtension x) n / G0)) =
        ∑ n ∈ Icc 1 N,
          primeHorizonExtension x n * (downwardPrimeRow g N (primeHorizonExtension x) n / G0) := by
    rw [← sum_coe_sort (Icc 1 N)]
    exact sum_congr rfl fun n _ => by rw [primeHorizonExtension_coe]
  rw [hlhs, hrhs]
  simp_rw [← mul_div_assoc, ← sum_div]
  congr 1
  have hup : ∀ n ∈ Icc 1 N,
      primeHorizonExtension x n * upwardPrimeRow g N (primeHorizonExtension x) n =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) := by
    intro n hn
    rw [upwardPrimeRow_eq_sum hgsupp hw.le hn (primeHorizonExtension x), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (primeHorizonExtension x n), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by dsimp only [g]; ring
  have hdown : ∀ n ∈ Icc 1 N,
      primeHorizonExtension x n * downwardPrimeRow g N (primeHorizonExtension x) n =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
            (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) := by
    intro n hn
    rw [downwardPrimeRow_eq_sum hgsupp hw.le hn (primeHorizonExtension x), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (primeHorizonExtension x n), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by dsimp only [g]; ring
  rw [sum_congr rfl hup, sum_congr rfl hdown, sum_comm,
    sum_comm (s := Icc 1 N) (t := range K)]
  refine sum_congr rfl fun k _ => ?_
  simp_rw [← mul_sum]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by
    rw [mul_comm (primeHorizonExtension x j) (primeHorizonExtension x n)]

/-- Exact quadratic-form reduction eliminating `upwardPrimeVector` from
`overlapMatrix - fullWeilNonRatioMatrix`. -/
theorem overlap_sub_nonRatio_inner_eq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, x⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫ =
      -⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, x⟫ +
        2 * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x - downwardPrimeVector φ c N x, x⟫ := by
  rw [fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM hc hN x, inner_add_left,
    upwardPrimeVector_self_inner_eq_downward hφ hsupp hc hN x, inner_sub_left]
  ring

/-- Polynomial-in-overlap and logarithmic-in-conductor upper bound for `completedConductorEnergy`. -/
theorem completedConductorEnergy_le_of_one_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc1 : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m ≤
      |completeWeilSelfFinitePart φ 1| + 2 * Real.log m + 3 * c ^ 4 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hself : completeWeilSelfFinitePart φ c ≤ |completeWeilSelfFinitePart φ 1| := by
    have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
    have heq : completeWeilSelfFinitePart φ c = completeWeilSelfFinitePart φ 1 - Real.log c := by
      unfold completeWeilSelfFinitePart
      rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
        Real.log_div one_ne_zero (by positivity), Real.log_one]
      ring
    linarith only [heq, hlogc, le_abs_self (completeWeilSelfFinitePart φ 1)]
  have hadj : ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant ≤ 2 * Real.log m := by
    unfold ramanujanAdjunctionEnergy
    linarith only [tameDifferent_le_log hm]
  have hpole : (if m = 1 then completeWeilPoleShift φ c else 0) ≤ c ^ 4 := by
    have hc4 : c ≤ c ^ 4 := by
      have := pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 4)
      simpa only [pow_one] using this
    split_ifs
    · exact (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le).trans hc4
    · positivity
  have hshell : -shellCorrection φ c m ≤ 2 * c ^ 4 := by
    have ht1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
    have habs := (abs_shellCorrection_le_polynomial_div_totient hφ hsupp hM hc1 hm).trans
      (div_le_self (by positivity) ht1)
    linarith only [(abs_le.mp habs).1]
  rw [completedConductorEnergy_eq_sub_shellCorrection hc0 hm, completeWeilAdjunctionEnergy]
  linarith only [hself, hadj, hpole, hshell]

/-! ### 2. Shared near-band Schur helper and collective `overlap - downward` bound -/

private theorem mem_nearRowIndices_symm {c : ℝ} {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) :
    n ∈ nearRowIndices c N j := by
  obtain ⟨_, hjn, hlog⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hn, Ne.symm hjn, by rwa [abs_sub_comm]⟩

private theorem log_two_mul_linearNearRowRadius_le {c : ℝ} (hc1 : 1 ≤ c) :
    Real.log (2 * (linearNearRowRadius c + 1)) + 3 ≤ 10 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, h2, Real.exp_pos 1]
  have hlin : 2 * (linearNearRowRadius c + 1) ≤ 34 * c := by
    unfold linearNearRowRadius
    nlinarith only [hc1, he2]
  have hlog34 : Real.log 34 ≤ 6 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he6 : (34 : ℝ) ≤ Real.exp 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      linarith only [hpow]
    exact (Real.log_le_log (by norm_num) he6).trans_eq (Real.log_exp 6)
  have hlog_le : Real.log (2 * (linearNearRowRadius c + 1)) ≤ 6 + Real.log c := by
    calc
      Real.log (2 * (linearNearRowRadius c + 1)) ≤ Real.log (34 * c) :=
        Real.log_le_log (by unfold linearNearRowRadius; positivity) hlin
      _ = Real.log 34 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
      _ ≤ 6 + Real.log c := by linarith only [hlog34]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  linarith only [hlog_le, hlc0]

/-- Shared `L²` row-sum bound for any kernel supported on `nearRowIndices c N n` acting on a
vector in `conductorSubspace R N`. -/
private theorem sum_nearBand_sq_le_of_mem_conductorSubspace
    {R N : ℕ} {c M : ℝ} (hR : 2 ≤ R) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    (hc1 : 1 ≤ c) (hw : c / N ≤ 1) (hM0 : 0 ≤ M)
    (hRNT : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    (K : ℕ → ℕ → ℝ)
    (hK : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K n j| ≤ M)
    {v : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hv : v ∈ conductorSubspace R N) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K n j * primeHorizonExtension v j) ^ 2) ≤
      (80 * (2 * Real.exp 2) ^ 2) * c ^ 2 * M ^ 2 *
        ((1 + Real.log c) / Real.log N) * ‖v‖ ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL : 0 < Real.log N := by
    have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  let T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    dsimp only [T]; linarith only [h0]
  let vTop : ℕ → ℝ := fun j => if (N : ℝ) / j < T then primeHorizonExtension v j else 0
  let K' : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then K n j else 0
  let U : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then M else 0
  have hrow_eq : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, K n j * primeHorizonExtension v j) =
        ∑ j ∈ Icc 1 N, K' n j * vTop j := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (hsub hj)).1
      have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.2
      have hlt : (N : ℝ) / j < T := by
        have hle : (N : ℝ) / j ≤ linearNearRowRadius c := (div_le_iff₀ hj0).mpr hgeom
        dsimp only [T]; linarith only [hle]
      dsimp only [K', vTop]
      rw [if_pos hj, if_pos hlt]
    · intro j _ hj; dsimp only [K']; rw [if_neg hj, zero_mul]
  let B_row := 2 * linearNearRowRadius c * M
  have hB_row0 : 0 ≤ B_row := by dsimp only [B_row, linearNearRowRadius]; positivity
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * 1) ≤ B_row := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    have heq : (∑ j ∈ Icc 1 N, U n j * 1) = ((nearRowIndices c N n).card : ℝ) * M := by
      simp only [U, mul_one, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hsub,
        sum_const, nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (card_nearRowIndices_le_small_width hc0 hn hw) hM0
  have hU_col : ∀ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (B_row / 1)) ≤ B_row ^ 2 := by
    intro j hj
    have hsym : ∀ n ∈ Icc 1 N, U n j * (B_row / 1) = B_row * (U j n * 1) := by
      intro n hn
      dsimp only [U]
      by_cases hjn : j ∈ nearRowIndices c N n
      · rw [if_pos hjn, if_pos (mem_nearRowIndices_symm hn hjn)]; ring
      · have hnj : n ∉ nearRowIndices c N j := fun h => hjn (mem_nearRowIndices_symm hj h)
        rw [if_neg hjn, if_neg hnj]; ring
    rw [sum_congr rfl hsym, ← mul_sum, sq]
    exact mul_le_mul_of_nonneg_left (hU_row j hj) hB_row0
  have hschur := sum_sq_abs_majorized_kernel_le' K' U vTop
    (fun _ => 1) (fun _ => B_row) (fun _ => B_row ^ 2)
    (fun _ _ _ _ => by dsimp only [U]; split_ifs <;> positivity)
    (fun n hn j _ => by
      dsimp only [K', U]
      split_ifs with hj
      · exact hK n hn j hj
      · rw [abs_zero])
    (fun _ _ => zero_lt_one) hU_row hU_col
  have hvTop_sq : (∑ j ∈ Icc 1 N, vTop j ^ 2) ≤
      20 * (1 + Real.log c) / Real.log N * ‖v‖ ^ 2 := by
    have hfilt : (∑ j ∈ Icc 1 N, vTop j ^ 2) =
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (N : ℝ) / j < T), primeHorizonExtension v j ^ 2 := by
      rw [sum_filter]
      exact sum_congr rfl fun j _ => by dsimp only [vTop]; split_ifs <;> simp
    rw [hfilt, div_mul_eq_mul_div, le_div_iff₀' hL]
    have hq := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hRNT hlog hv
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _))
  rw [sum_congr rfl fun n hn => by rw [hrow_eq n hn]]
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K' n j * vTop j) ^ 2) ≤
        ∑ j ∈ Icc 1 N, B_row ^ 2 * vTop j ^ 2 := hschur
    _ = B_row ^ 2 * ∑ j ∈ Icc 1 N, vTop j ^ 2 := (mul_sum ..).symm
    _ ≤ B_row ^ 2 * (20 * (1 + Real.log c) / Real.log N * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hvTop_sq (sq_nonneg _)
    _ = (80 * (2 * Real.exp 2) ^ 2) * c ^ 2 * M ^ 2 *
          ((1 + Real.log c) / Real.log N) * ‖v‖ ^ 2 := by
      dsimp only [B_row, linearNearRowRadius]; ring

private theorem downwardPrimeVector_packet_apply (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {M N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ) (n : PrimeHorizonIndex N) :
    downwardPrimeVector φ c N
        (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) n =
      ∑ m ∈ Icc 1 M,
        a m * downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c / N)
  let G0 := ∫ u, g u ^ 2
  let K := lagRange (Real.log N + c / N + 1)
  let u := ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N
  change downwardPrimeRow g N (primeHorizonExtension u) n / G0 =
    ∑ m ∈ Icc 1 M, a m *
      (downwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n / G0)
  have hext : ∀ j ∈ Icc 1 N, primeHorizonExtension u j =
      ∑ m ∈ Icc 1 M, a m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) j := by
    intro j hj
    rw [primeHorizonExtension_coe u ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) u = _
    dsimp only [u]
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    rfl
  simp_rw [← mul_div_assoc, ← sum_div]
  congr 1
  rw [downwardPrimeRow_eq_sum hgsupp hw.le n.property (primeHorizonExtension u)]
  have hterm : ∀ m ∈ Icc 1 M,
      a m * downwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, a m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
            (if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) := by
    intro m _
    rw [downwardPrimeRow_eq_sum hgsupp hw.le n.property, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (a m), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by dsimp only [g]; ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [hext j hj, sum_mul]

private theorem sum_exterior_packet_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {R N : ℕ} {c : ℝ}
    (hR : 2 ≤ R) (hRN : R * R ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    (hc1 : 1 ≤ c) (hw1 : c / N ≤ 1 / 3) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
      (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
        (actualExteriorDownwardRow (atomDilate φ (c / N)) N m n / Real.sqrt (Real.log N)))) ^ 2) ≤
      (36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2) *
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  let g := atomDilate φ (c / N)
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hmode_row : ∀ m ∈ Icc 1 R, ∀ n ∈ Icc 1 N,
      |(Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))| ≤
        3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N) := by
    intro m hm n hn
    obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
    rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
    have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤
          3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      intro ℓ hℓ
      have hNℓ : (N : ℝ) ≤ ℓ := by exact_mod_cast (mem_Ioc.mp hℓ).1.le
      have hℓ0 : (0 : ℝ) < ℓ := hN0.trans_le hNℓ
      have hsℓ : Real.sqrt N ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hNℓ
      have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos hG, div_le_one hG]
        exact abs_bumpCorr_le hg.continuous hgc _
      have hℓ_le : (ℓ : ℝ) ≤ 3 * N := by
        have hcut := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
        have hℓ_nat : ℓ ≤ N + linearPrimeStrip c := (mem_Ioc.mp hℓ).2.trans hcut
        have hB := linearPrimeStrip_le hc1
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        have hcN : 3 * c ≤ N := by
          have := (div_le_iff₀ hN0).mp hw1; linarith only [this]
        have hcast : (ℓ : ℝ) ≤ N + linearPrimeStrip c := by exact_mod_cast hℓ_nat
        nlinarith only [hcast, hB, he1, hcN, hc0]
      have hlogℓ : Real.log ℓ ≤ 3 * Real.log N := by
        have hlog3 : Real.log 3 ≤ 2 := by
          linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
        calc
          Real.log ℓ ≤ Real.log (3 * N) := Real.log_le_log hℓ0 hℓ_le
          _ = Real.log 3 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
          _ ≤ 3 * Real.log N := by linarith only [hlog3, hL1]
      have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
          3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
        rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hℓ0)]
        calc
          |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ ≤
              (m.totient : ℝ) * Real.log ℓ / Real.sqrt ℓ :=
            div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) (Real.sqrt_nonneg _)
          _ ≤ (m.totient : ℝ) * (3 * Real.log N) / Real.sqrt ℓ :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
          _ ≤ (m.totient : ℝ) * (3 * Real.log N) / Real.sqrt N :=
            div_le_div_of_nonneg_left (by positivity) hsN hsℓ
          _ = 3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
    have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ (Real.exp 1 + 1) * c := by
      have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
      have hc_strip : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
        rw [Nat.card_Ioc]
        exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
      exact hc_strip.trans (linearPrimeStrip_le hc1)
    have hreg : |regroupedExteriorDownwardPrimeRow g c N m n| ≤
        3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      unfold regroupedExteriorDownwardPrimeRow
      calc
        _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
              |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
                (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
              (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := sum_le_sum hterm
        _ = ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) *
              (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ ((Real.exp 1 + 1) * c) * (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
    have hsφm : 0 < Real.sqrt (m.totient : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm1)
    have hsφR : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt (by exact_mod_cast (Nat.totient_le m).trans hmR)
    rw [abs_mul, abs_inv, abs_of_pos hsφm, abs_div, abs_of_pos hsL]
    calc
      (Real.sqrt (m.totient : ℝ))⁻¹ * (|regroupedExteriorDownwardPrimeRow g c N m n| /
          Real.sqrt (Real.log N)) ≤
          (Real.sqrt (m.totient : ℝ))⁻¹ *
            ((3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N) /
              Real.sqrt (Real.log N)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hreg hsL.le) (by positivity)
      _ = 3 * (Real.exp 1 + 1) * c * Real.sqrt (m.totient : ℝ) *
            (Real.sqrt (Real.log N) / Real.sqrt N) := by
        calc
          (Real.sqrt (m.totient : ℝ))⁻¹ *
              ((3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N) /
                Real.sqrt (Real.log N)) =
              (Real.sqrt (m.totient : ℝ))⁻¹ *
                ((3 * (Real.exp 1 + 1) * c * (Real.sqrt (m.totient : ℝ) ^ 2) *
                  (Real.sqrt (Real.log N) ^ 2) / Real.sqrt N) / Real.sqrt (Real.log N)) := by
            rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hL0.le]
          _ = 3 * (Real.exp 1 + 1) * c * Real.sqrt (m.totient : ℝ) *
                (Real.sqrt (Real.log N) / Real.sqrt N) := by
            field_simp [hsφm.ne', hsL.ne', hsN.ne']
      _ ≤ 3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N) := by
        rw [Real.sqrt_div hL0.le]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsφR (by positivity)) (by positivity)
  let S_ext := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hrestrict :
      (∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) =
      ∑ n ∈ S_ext,
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2 := by
    symm
    refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
    have hout : n < N - linearPrimeStrip c :=
      lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    have hzero : ∀ m ∈ Icc 1 R, actualExteriorDownwardRow g N m n = 0 := fun m _ => by
      rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
      exact regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw hout m
    rw [sum_eq_zero fun m hm => by rw [hzero m hm]; ring, sq, mul_zero]
  have hsum_abs_a_sq : (∑ m ∈ Icc 1 R, |a m|) ^ 2 ≤
      2 * (R : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R) (fun m => |a m|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hcs
    have hriesz := (half_and_three_halves_riesz_of_log_le hR hRN hlog a).1
    nlinarith only [hcs, hriesz, Nat.cast_nonneg (α := ℝ) R]
  have hpt_S : ∀ n ∈ S_ext,
      (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
        (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2 ≤
        18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro n hnS
    have hn := (mem_filter.mp hnS).1
    let M_ext := 3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N)
    have habs :
        |∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))| ≤
          M_ext * ∑ m ∈ Icc 1 R, |a m| := by
      calc
        _ ≤ ∑ m ∈ Icc 1 R, |a m| * |(Real.sqrt (m.totient : ℝ))⁻¹ *
              (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
          rw [abs_mul]
        _ ≤ ∑ m ∈ Icc 1 R, |a m| * M_ext :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hmode_row m hm n hn) (abs_nonneg _)
        _ = M_ext * ∑ m ∈ Icc 1 R, |a m| := by rw [← sum_mul, mul_comm]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs, mul_pow] at hsq
    have hM_sq : M_ext ^ 2 =
        9 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) * (Real.log N / N) := by
      dsimp only [M_ext]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg R),
        Real.sq_sqrt (by positivity)]
      ring
    calc
      _ ≤ M_ext ^ 2 * (∑ m ∈ Icc 1 R, |a m|) ^ 2 := hsq
      _ ≤ M_ext ^ 2 * (2 * (R : ℝ) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_abs_a_sq (sq_nonneg _)
      _ = 18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
        rw [hM_sq]; ring
  have hcard_S : (S_ext.card : ℝ) ≤ 2 * (Real.exp 1 + 2) * c := by
    have hcontain : S_ext ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S_ext.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    have hcast : (S_ext.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
    have hB := linearPrimeStrip_le hc1
    nlinarith only [hcast, hB, hc1, Real.exp_pos 1]
  rw [hrestrict]
  calc
    _ ≤ ∑ _n ∈ S_ext,
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      sum_le_sum hpt_S
    _ = (S_ext.card : ℝ) *
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Real.exp 1 + 2) * c) *
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard_S (by positivity)
    _ = (36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2) *
          c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private theorem quad_four_combine {K_nb K_ext M_nc M_2a C_jet X Y U S1 S2 S3 S4 : ℝ}
    (hK_nb : 0 ≤ K_nb) (hK_ext : 0 ≤ K_ext) (hM_nc : 0 ≤ M_nc) (hM_2a : 0 ≤ M_2a)
    (hC_jet : 0 ≤ C_jet) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hS1 : S1 ≤ K_nb * M_nc ^ 2 * X ^ 2 * U ^ 2)
    (hS2 : S2 ≤ K_nb * M_2a ^ 2 * X ^ 2 * U ^ 2)
    (hS3 : S3 ≤ K_nb * (2 * C_jet) ^ 2 * X ^ 2 * U ^ 2)
    (hS4 : S4 ≤ K_ext * Y ^ 2 * U ^ 2) :
    4 * (S1 + S2 + S3 + S4) ≤
      ((2 * Real.sqrt K_nb * (M_nc + M_2a + 2 * C_jet) + 2 * Real.sqrt K_ext + 1) *
        (X + Y) * U) ^ 2 := by
  let C_od := 2 * Real.sqrt K_nb * (M_nc + M_2a + 2 * C_jet) + 2 * Real.sqrt K_ext + 1
  have hsKnb : Real.sqrt K_nb ^ 2 = K_nb := Real.sq_sqrt hK_nb
  have hsKext : Real.sqrt K_ext ^ 2 = K_ext := Real.sq_sqrt hK_ext
  have hsKnb0 : 0 ≤ Real.sqrt K_nb := Real.sqrt_nonneg _
  have hsKext0 : 0 ≤ Real.sqrt K_ext := Real.sqrt_nonneg _
  have hA_le : 4 * K_nb * (M_nc ^ 2 + M_2a ^ 2 + (2 * C_jet) ^ 2) ≤ C_od ^ 2 := by
    dsimp only [C_od]
    nlinarith only [hsKnb, hM_nc, hM_2a, hC_jet, hsKnb0, hsKext0,
      mul_nonneg hM_nc hM_2a, mul_nonneg hM_nc hC_jet, mul_nonneg hM_2a hC_jet,
      mul_nonneg hsKnb0 hM_nc, mul_nonneg hsKnb0 hM_2a, mul_nonneg hsKnb0 hC_jet]
  have hB_le : 4 * K_ext ≤ C_od ^ 2 := by
    dsimp only [C_od]
    have hsum0 : 0 ≤ 2 * Real.sqrt K_nb * (M_nc + M_2a + 2 * C_jet) + 1 := by positivity
    nlinarith only [hsKext, hsKext0, hsum0]
  have hcoef_le :
      4 * K_nb * (M_nc ^ 2 + M_2a ^ 2 + (2 * C_jet) ^ 2) * X ^ 2 + 4 * K_ext * Y ^ 2 ≤
        C_od ^ 2 * (X + Y) ^ 2 := by
    nlinarith only [hA_le, hB_le, hX, hY, sq_nonneg X, sq_nonneg Y, mul_nonneg hX hY,
      sq_nonneg C_od]
  calc
    4 * (S1 + S2 + S3 + S4) ≤
        4 * (K_nb * M_nc ^ 2 * X ^ 2 * U ^ 2 + K_nb * M_2a ^ 2 * X ^ 2 * U ^ 2 +
          K_nb * (2 * C_jet) ^ 2 * X ^ 2 * U ^ 2 + K_ext * Y ^ 2 * U ^ 2) := by
      linarith only [hS1, hS2, hS3, hS4]
    _ = (4 * K_nb * (M_nc ^ 2 + M_2a ^ 2 + (2 * C_jet) ^ 2) * X ^ 2 + 4 * K_ext * Y ^ 2) *
          U ^ 2 := by ring
    _ ≤ (C_od ^ 2 * (X + Y) ^ 2) * U ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef_le (sq_nonneg U)
    _ = (C_od * (X + Y) * U) ^ 2 := by ring

/-- Collective `L²` norm bound on `overlapMatrix u - downwardPrimeVector u` for any
`u ∈ conductorSubspace R N`. -/
theorem exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_od : ℝ, 0 < C_od ∧
      ∀ {R N : ℕ} {c : ℝ},
        2 ≤ R → R * R ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R N →
        ‖Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u‖ ≤
          C_od * (c ^ 2 * (1 + Real.log R) * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  obtain ⟨C_jet, hC_jet_pos, hC_jet⟩ := exists_divisorJetHorizonVector_norm_le
  let M_nc : ℝ := 1 + Real.exp (1 / 2)
  let M_2a : ℝ := K_pair + 2 * Real.exp 2 + 1
  let K_nb : ℝ := 80 * (2 * Real.exp 2) ^ 2
  let K_ext : ℝ := 36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2
  let C_od : ℝ := 2 * Real.sqrt K_nb * (M_nc + M_2a + 2 * C_jet) + 2 * Real.sqrt K_ext + 1
  have hC_od_pos : 0 < C_od := by dsimp only [C_od, K_nb, K_ext, M_nc, M_2a]; positivity
  refine ⟨C_od, hC_od_pos, ?_⟩
  intro R N c hR hRN hlog hc1 hw1 hRNT u hu
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := u)).mp hu
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN2 : 2 * c ≤ N := by
    have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL : 0 < Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  let g := atomDilate φ (c / N)
  let G0 := ∫ t, g t ^ 2
  let K1 : ℕ → ℕ → ℝ := fun n j =>
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j
  let K2a : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair g n j / G0 -
      Real.log j * (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2))
  let K2b : ℕ → ℕ → ℝ := fun n j =>
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)
  let vJet := divisorJetHorizonVector R N a
  have hu_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension u j =
      (Real.sqrt (Real.log N))⁻¹ *
        ∑ m ∈ Icc 1 R, a m * (normalizedRamanujanMode m j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension_coe u ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) u = _
    rw [hu_eq, map_sum, mul_sum]
    exact sum_congr rfl fun m _ => by
      change a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) = _
      ring
  have hvJet_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension vJet j =
      (Real.sqrt (Real.log N))⁻¹ *
        ∑ m ∈ Icc 1 R, a m * (ramanujanLogDivisorJet m j /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt j)) := by
    intro j hj
    rw [primeHorizonExtension_coe vJet ⟨j, hj⟩, divisorJetHorizonVector_apply R N a ⟨j, hj⟩]
    simp only [poleVector]
    rw [mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun m _ => by ring
  have hrow_decomp : ∀ n ∈ Icc 1 N,
      primeHorizonExtension
          (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u) n =
        (∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) -
        ∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))) := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ -
      downwardPrimeVector φ c N u ⟨n, hn⟩ = _
    have hov_sum : (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ =
        ∑ m ∈ Icc 1 R, a m *
          (Matrix.toEuclideanLin (overlapMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)) ⟨n, hn⟩ := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
        (Matrix.toEuclideanLin (overlapMatrix φ c N) u) = _
      rw [hu_eq, map_sum, map_sum]
      exact sum_congr rfl fun m _ => by rw [map_smul, map_smul]; rfl
    have hdown_sum : downwardPrimeVector φ c N u ⟨n, hn⟩ =
        ∑ m ∈ Icc 1 R, a m *
          downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩ := by
      rw [hu_eq]
      exact downwardPrimeVector_packet_apply φ hc0 hφ hsupp hN1 a ⟨n, hn⟩
    rw [hov_sum, hdown_sum, ← sum_sub_distrib]
    have hmode : ∀ m ∈ Icc 1 R,
        a m * (Matrix.toEuclideanLin (overlapMatrix φ c N)
            (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩ -
          downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩) =
        a m * nearCenterVector φ c N m ⟨n, hn⟩ +
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N))) -
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))) := by
      intro m hm
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      rw [overlapMatrix_ramanujan_row_eq φ c hm0 ⟨n, hn⟩]
      have hfull := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) => v ⟨n, hn⟩)
        (normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0 N m)
      change normalizedFullNearGammaDownwardVector φ c N m ⟨n, hn⟩ =
        nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N) -
          actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N) at hfull
      rw [hfull]
      ring
    rw [sum_congr rfl fun m hm => by rw [← mul_sub, hmode m hm], sum_sub_distrib, sum_add_distrib]
    have hnc_sum : (∑ m ∈ Icc 1 R, a m * nearCenterVector φ c N m ⟨n, hn⟩) =
        ∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j := by
      have h1 : ∀ m ∈ Icc 1 R, a m * nearCenterVector φ c N m ⟨n, hn⟩ =
          ∑ j ∈ nearRowIndices c N n,
            K1 n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (normalizedRamanujanMode m j / Real.sqrt j))) := by
        intro m _
        change a m * ((∑ j ∈ nearRowIndices c N n,
          K1 n j * normalizedRamanujanMode m j / Real.sqrt j) / Real.sqrt (Real.log N)) = _
        rw [sum_div, mul_sum]
        exact sum_congr rfl fun j _ => by ring
      rw [sum_congr rfl h1, sum_comm]
      refine sum_congr rfl fun j hj => ?_
      rw [← mul_sum, ← mul_sum, hu_ext j (mem_filter.mp hj).1]
    have hng_sum :
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N)))) =
        (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) := by
      have hcoeff : ∀ m ∈ Icc 1 R, ∀ j ∈ nearRowIndices c N n,
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j / Real.sqrt (Real.log N))) =
          K2a n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (normalizedRamanujanMode m j / Real.sqrt j))) +
            K2b n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (ramanujanLogDivisorJet m j / (Real.sqrt (m.totient : ℝ) * Real.sqrt j)))) := by
        intro m hm j hj
        have hm0 : 0 < m := (mem_Icc.mp hm).1
        have hj1 : 1 ≤ j := (mem_Icc.mp (mem_filter.mp hj).1).1
        rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hj1,
          normalizedRamanujanMode_eq_coefficient hm0]
        dsimp only [K2a, K2b, g, G0]
        ring
      have hm_eq : ∀ m ∈ Icc 1 R,
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N))) =
          ∑ j ∈ nearRowIndices c N n,
            (K2a n j * ((Real.sqrt (Real.log N))⁻¹ *
                (a m * (normalizedRamanujanMode m j / Real.sqrt j))) +
              K2b n j * ((Real.sqrt (Real.log N))⁻¹ *
                (a m * (ramanujanLogDivisorJet m j /
                  (Real.sqrt (m.totient : ℝ) * Real.sqrt j))))) := by
        intro m hm
        unfold nearGammaDownwardRow
        rw [sum_div, mul_sum, mul_sum]
        exact sum_congr rfl fun j hj => by
          simpa only [mul_assoc] using hcoeff m hm j hj
      rw [sum_congr rfl hm_eq, sum_comm, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjI := (mem_filter.mp hj).1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum,
        hu_ext j hjI, hvJet_ext j hjI]
    rw [hnc_sum, hng_sum, add_assoc]
  have hK1_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K1 n j| ≤ M_nc * c := by
    intro n hn j hj
    have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
    have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
      rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
        Real.sqrt_one, div_one]
    rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
      abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
    have hpole := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
    exact h1.trans (by
      dsimp only [M_nc]
      simpa only [mul_comm c] using mul_le_mul_of_nonneg_right hpole (by positivity))
  have hK2a_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K2a n j| ≤ M_2a * c := by
    intro n hn j hj
    have hjN := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    have hrem : |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j| ≤ K_pair := by
      simpa only [g, G0, K2b, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
    have hq : |K2b n j| ≤ 1 := by
      dsimp only [K2b]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
      (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
    have hloglow : 0 ≤ Real.log N - Real.log j :=
      sub_nonneg.mpr (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
    have hloghigh : Real.log N - Real.log j ≤ linearNearRowRadius c := by
      have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
      rw [Real.log_div hN0.ne' hj0.ne'] at h
      linarith only [h, hquot]
    have hlogc : |Real.log c| ≤ c := by
      rw [abs_of_nonneg (Real.log_nonneg hc1)]
      linarith [Real.log_le_sub_one_of_pos hc0]
    have hlogeq : Real.log (1 / (c / N)) - Real.log j = (Real.log N - Real.log j) - Real.log c := by
      rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
    have hlog_diff : |Real.log (1 / (c / N)) - Real.log j| ≤ linearNearRowRadius c + c := by
      rw [hlogeq]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh, hlogc])
    have hid : K2a n j = (atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j) +
        (Real.log (1 / (c / N)) - Real.log j) * K2b n j := by
      dsimp only [K2a]; ring
    rw [hid]
    calc
      _ ≤ |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j| +
            |(Real.log (1 / (c / N)) - Real.log j) * K2b n j| := abs_add_le _ _
      _ ≤ K_pair + (linearNearRowRadius c + c) * 1 := by
        rw [abs_mul]
        exact add_le_add hrem (mul_le_mul hlog_diff hq (abs_nonneg _)
          (by unfold linearNearRowRadius; positivity))
      _ ≤ M_2a * c := by
        dsimp only [M_2a, linearNearRowRadius]
        nlinarith only [hc1, hK_pair0]
  have hK2b_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K2b n j| ≤ 1 := by
    intro _ _ _ _
    dsimp only [K2b]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
  have hvJet_mem : vJet ∈ conductorSubspace R N :=
    divisorJetHorizonVector_mem_conductorSubspace R N a
  have hvJet_norm : ‖vJet‖ ≤ 2 * C_jet * (1 + Real.log R) * ‖u‖ := by
    have h1 := hC_jet hR hRN hlog a
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN hlog a).1
    rw [← hu_eq] at hr
    have hs : Real.sqrt (∑ m ∈ Icc 1 R, a m ^ 2) ≤ 2 * ‖u‖ := by
      calc
        Real.sqrt (∑ m ∈ Icc 1 R, a m ^ 2) ≤ Real.sqrt (4 * ‖u‖ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [hr, sq_nonneg ‖u‖])
        _ = 2 * ‖u‖ := by
          rw [show (4 : ℝ) * ‖u‖ ^ 2 = (2 * ‖u‖) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc
      ‖vJet‖ ≤ C_jet * (1 + Real.log R) * Real.sqrt (∑ m ∈ Icc 1 R, a m ^ 2) := h1
      _ ≤ C_jet * (1 + Real.log R) * (2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hs (by have := Real.log_natCast_nonneg R; positivity)
      _ = 2 * C_jet * (1 + Real.log R) * ‖u‖ := by ring
  have hsq1 := sum_nearBand_sq_le_of_mem_conductorSubspace hR hlog hc1 hw
    (by dsimp only [M_nc]; positivity) hRNT K1 hK1_le hu
  have hsq2a := sum_nearBand_sq_le_of_mem_conductorSubspace hR hlog hc1 hw
    (by dsimp only [M_2a]; positivity) hRNT K2a hK2a_le hu
  have hsq2b := sum_nearBand_sq_le_of_mem_conductorSubspace hR hlog hc1 hw
    zero_le_one hRNT K2b hK2b_le hvJet_mem
  have hsq3 := sum_exterior_packet_sq_le hφ hsupp hM hR hRN hlog hc1 hw1 a
  rw [← hu_eq] at hsq3
  let X := c ^ 2 * (1 + Real.log R) * Real.sqrt ((1 + Real.log c) / Real.log N)
  let Y := c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)
  have hX0 : 0 ≤ X := by
    dsimp only [X]; have := Real.log_natCast_nonneg R; positivity
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have h1R : 1 ≤ 1 + Real.log R := by have := Real.log_natCast_nonneg R; linarith only [this]
  have h1R_sq : 1 ≤ (1 + Real.log R) ^ 2 := by nlinarith only [h1R]
  have hlc0 : 0 ≤ (1 + Real.log c) / Real.log N :=
    div_nonneg (by linarith [Real.log_nonneg hc1]) hL.le
  have hX_sq : X ^ 2 = c ^ 4 * (1 + Real.log R) ^ 2 * ((1 + Real.log c) / Real.log N) := by
    dsimp only [X]; rw [mul_pow, mul_pow, Real.sq_sqrt hlc0]; ring
  have hY_sq : Y ^ 2 = c ^ 4 * (R : ℝ) ^ 2 * (Real.log N / N) := by
    dsimp only [Y]; rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hKnb0 : 0 ≤ K_nb := by dsimp only [K_nb]; positivity
  have hKext0 : 0 ≤ K_ext := by dsimp only [K_ext]; positivity
  have hMnc0 : 0 ≤ M_nc := by dsimp only [M_nc]; positivity
  have hM2a0 : 0 ≤ M_2a := by dsimp only [M_2a]; positivity
  have hsq1' : (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2) ≤
      K_nb * M_nc ^ 2 * X ^ 2 * ‖u‖ ^ 2 := by
    rw [hX_sq]
    have h1 : K_nb * c ^ 2 * (M_nc * c) ^ 2 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 ≤
        K_nb * M_nc ^ 2 * (c ^ 4 * (1 + Real.log R) ^ 2 * ((1 + Real.log c) / Real.log N)) *
          ‖u‖ ^ 2 := by
      have hbase : 0 ≤ K_nb * M_nc ^ 2 * c ^ 4 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
        positivity
      nlinarith only [h1R_sq, hbase]
    exact hsq1.trans h1
  have hsq2a' : (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2) ≤
      K_nb * M_2a ^ 2 * X ^ 2 * ‖u‖ ^ 2 := by
    rw [hX_sq]
    have h1 : K_nb * c ^ 2 * (M_2a * c) ^ 2 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 ≤
        K_nb * M_2a ^ 2 * (c ^ 4 * (1 + Real.log R) ^ 2 * ((1 + Real.log c) / Real.log N)) *
          ‖u‖ ^ 2 := by
      have hbase : 0 ≤ K_nb * M_2a ^ 2 * c ^ 4 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
        positivity
      nlinarith only [h1R_sq, hbase]
    exact hsq2a.trans h1
  have hsq2b' : (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2) ≤
      K_nb * (2 * C_jet) ^ 2 * X ^ 2 * ‖u‖ ^ 2 := by
    rw [hX_sq]
    have hvj2 : ‖vJet‖ ^ 2 ≤ (2 * C_jet * (1 + Real.log R) * ‖u‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hvJet_norm 2
    have hc24 : c ^ 2 ≤ c ^ 4 := pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 4)
    calc
      _ ≤ K_nb * c ^ 2 * 1 ^ 2 * ((1 + Real.log c) / Real.log N) *
            (2 * C_jet * (1 + Real.log R) * ‖u‖) ^ 2 :=
        hsq2b.trans (mul_le_mul_of_nonneg_left hvj2 (by positivity))
      _ ≤ K_nb * c ^ 4 * 1 ^ 2 * ((1 + Real.log c) / Real.log N) *
            (2 * C_jet * (1 + Real.log R) * ‖u‖) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc24 hKnb0)
              (by norm_num)) hlc0) (sq_nonneg _)
      _ = K_nb * (2 * C_jet) ^ 2 *
            (c ^ 4 * (1 + Real.log R) ^ 2 * ((1 + Real.log c) / Real.log N)) * ‖u‖ ^ 2 := by ring
  have hsq3' :
      (∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) ≤
      K_ext * Y ^ 2 * ‖u‖ ^ 2 := by
    rw [hY_sq]
    have hc34 : c ^ 3 ≤ c ^ 4 := pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 4)
    calc
      _ ≤ K_ext * c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * ‖u‖ ^ 2 := hsq3
      _ ≤ K_ext * c ^ 4 * (R : ℝ) ^ 2 * (Real.log N / N) * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc34 hKext0)
              (sq_nonneg _)) (div_nonneg hL.le hN0.le)) (sq_nonneg _)
      _ = K_ext * (c ^ 4 * (R : ℝ) ^ 2 * (Real.log N / N)) * ‖u‖ ^ 2 := by ring
  have hfour : ∀ x₁ x₂ x₃ x₄ : ℝ,
      (x₁ + x₂ + x₃ - x₄) ^ 2 ≤ 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := fun x₁ x₂ x₃ x₄ => by
    nlinarith only [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ + x₄),
      sq_nonneg (x₂ - x₃), sq_nonneg (x₂ + x₄), sq_nonneg (x₃ + x₄)]
  have hnorm_sq :
      ‖Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u‖ ^ 2 ≤
        (C_od * (X + Y) * ‖u‖) ^ 2 := by
    rw [← sum_primeHorizonExtension_sq
      (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u)]
    have hpt : ∀ n ∈ Icc 1 N,
        primeHorizonExtension
            (Matrix.toEuclideanLin (overlapMatrix φ c N) u -
              downwardPrimeVector φ c N u) n ^ 2 ≤
          4 * ((∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2 +
            (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2 +
            (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2 +
            (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
              (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) := by
      intro n hn
      rw [hrow_decomp n hn]
      exact hfour _ _ _ _
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
            4 * ((∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2 +
              (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2 +
              (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2 +
              (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
                (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) :=
        sum_le_sum hpt
      _ = 4 * ((∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2) +
            (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2) +
            (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2) +
            (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
              (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2)) := by
        rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib]
      _ ≤ (C_od * (X + Y) * ‖u‖) ^ 2 :=
        quad_four_combine hKnb0 hKext0 hMnc0 hM2a0 hC_jet_pos.le hX0 hY0 hsq1' hsq2a' hsq2b' hsq3'
  have hrhs0 : 0 ≤ C_od * (X + Y) * ‖u‖ := by positivity
  nlinarith only [hnorm_sq,
    norm_nonneg (Matrix.toEuclideanLin (overlapMatrix φ c N) u -
      downwardPrimeVector φ c N u), hrhs0]

/-! ### 3. Conductor-independent `L²` norm bound for `upwardPrimeVector` -/

/-- Uniform `O(c √(1 + log c))` `L²` norm bound on `upwardPrimeVector φ c N u` for any
`u ∈ conductorSubspace R N`, completely independent of `R`. -/
theorem exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_up : ℝ, 0 < C_up ∧
      ∀ {R N : ℕ} {c : ℝ},
        2 ≤ R → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R N →
        ‖upwardPrimeVector φ c N u‖ ≤ C_up * c * Real.sqrt (1 + Real.log c) * ‖u‖ := by
  let A_up : ℝ := 2 * (Real.log 4 + 4) * Real.exp (3 / 2) * Real.exp 1
  let B_down : ℝ := 4 * Real.exp (1 / 2) * Real.exp 1
  let C_up : ℝ := 4 * Real.sqrt (A_up * B_down) + 1
  have hlog4_pos : 0 < Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hA_up_pos : 0 < A_up := by dsimp only [A_up]; positivity
  have hB_down_pos : 0 < B_down := by dsimp only [B_down]; positivity
  refine ⟨C_up, by dsimp only [C_up]; positivity, ?_⟩
  intro R N c hR hlog hc1 hw1 hRNT u hu
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw_le1 : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) := by positivity
    linarith only [this, hRNT]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) := by
      have h1 : (0 : ℝ) ≤ c * Real.exp 1 := by positivity
      have h2 : (0 : ℝ) ≤ (R * R : ℕ) := by positivity
      nlinarith only [h1, h2]
    exact_mod_cast this.trans hRNT
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  let w := c / N
  have hw0 : 0 < w := div_pos hc0 hN0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw0
  let g := atomDilate φ w
  let G0 := ∫ t, g t ^ 2
  have hG0 : 0 < G0 := by
    dsimp only [G0, g]; rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  let K := lagRange (Real.log N + w + 1)
  let T := c * Real.exp 1 + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ c * Real.exp 1 := by positivity
    dsimp only [T]; linarith only [h0]
  let uTop : ℕ → ℝ := fun j => if (N : ℝ) / j < T then primeHorizonExtension u j else 0
  let K_up : ℕ → ℕ → ℝ := fun n j =>
    (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
      (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) / G0
  let U : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * upInd w k n j
  have hrow_eq : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (upwardPrimeVector φ c N u) n =
        ∑ j ∈ Icc 1 N, K_up n j * uTop j := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change upwardPrimeRow g N (primeHorizonExtension u) n / G0 = _
    rw [upwardPrimeRow_eq_sum hgsupp hw0.le hn (primeHorizonExtension u)]
    have hcomm :
        (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, primeHorizonExtension u j *
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) / G0 =
        ∑ j ∈ Icc 1 N, K_up n j * primeHorizonExtension u j := by
      simp_rw [mul_sum]
      rw [sum_comm, sum_div]
      refine sum_congr rfl fun j _ => ?_
      dsimp only [K_up]
      rw [div_mul_eq_mul_div, sum_mul]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [hcomm]
    refine sum_congr rfl fun j hj => ?_
    dsimp only [uTop]
    split_ifs with hlt
    · rfl
    · rw [mul_zero]
      have hKup0 : K_up n j = 0 := by
        dsimp only [K_up]
        rw [sum_eq_zero, zero_div]
        intro k _
        rcases lt_or_ge k 2 with hk2 | hk2
        · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
        · split_ifs with hjn
          · rw [mul_zero]
          · by_cases hbc : bumpCorr g (Real.log k - (Real.log j - Real.log n)) = 0
            · rw [hbc, mul_zero]
            · exfalso
              have hk1 : 1 ≤ k := by omega
              have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
              have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
              have hkn1 : 1 ≤ k * n := Nat.mul_pos hk1 hn1
              have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
              have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
              have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
              have hgap : |Real.log k - (Real.log j - Real.log n)| ≤ w := by
                by_contra hgt
                exact hbc (bumpCorr_eq_zero hgsupp (lt_of_not_ge hgt))
              have hlog_eq : Real.log j - Real.log (k * n : ℕ) =
                  -(Real.log k - (Real.log j - Real.log n)) := by
                rw [Nat.cast_mul, Real.log_mul hk0.ne' hn0.ne']; ring
              have hlog_kn : |Real.log j - Real.log (k * n : ℕ)| ≤ c / N := by
                rwa [hlog_eq, abs_neg]
              have hsep := (logWindow_integer_separation_small_width hc0 hN1 hkn1 hj1
                (Ne.symm hjn) hlog_kn hw_le1).2
              have hdiv : (N : ℝ) / j ≤ c * Real.exp 1 := (div_le_iff₀ hj0).mpr hsep
              exact hlt (by dsimp only [T]; linarith only [hdiv])
      rw [hKup0, zero_mul]
  have hKU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, |K_up n j| ≤ U n j := by
    intro n _ j _
    dsimp only [K_up, U]
    rw [abs_div, abs_of_pos hG0, div_le_iff₀ hG0, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((abs_nonRatio_term_le hg.continuous hgc hgsupp k n j).trans_eq (mul_comm G0 _))
      (vonMangoldtAtom_nonneg' k)
  have hew : Real.exp w - 1 ≤ (c / N) * Real.exp 1 := by
    calc
      Real.exp w - 1 ≤ w * Real.exp w := exp_sub_one_le_mul_exp
      _ ≤ (c / N) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw_le1) hw0.le
  have hU_row : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, U n j * (1 / Real.sqrt j)) ≤ A_up * c / Real.sqrt n := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have heq : (∑ j ∈ Icc 1 N, U n j * (1 / Real.sqrt j)) =
        (1 / Real.sqrt n) * ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd w k n j := by
      dsimp only [U]
      simp_rw [sum_mul]
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, mul_comm (1 / Real.sqrt n), mul_assoc, mul_sum, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      rw [Real.sqrt_div hn0.le]
      field_simp [hsn.ne', (Real.sqrt_pos.mpr hj0).ne']
    rw [heq, div_eq_mul_one_div (A_up * c), mul_comm (A_up * c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hup := up_row_le (N := N) hw0.le hn1 K
    have hexp32 : Real.exp (3 * w / 2) ≤ Real.exp (3 / 2) :=
      Real.exp_le_exp.mpr (by dsimp only [w]; linarith only [hw_le1])
    have hewN : (Real.exp w - 1) * N ≤ c * Real.exp 1 := by
      calc
        (Real.exp w - 1) * N ≤ ((c / N) * Real.exp 1) * N :=
          mul_le_mul_of_nonneg_right hew hN0.le
        _ = c * Real.exp 1 := by field_simp [hN0.ne']
    calc
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N) := by
        linarith only [hup, (by ring :
          2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N =
            2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N))]
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 / 2) * (c * Real.exp 1) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hexp32 (by positivity))
          hewN (mul_nonneg (by linarith [Real.add_one_le_exp w]) hN0.le) (by positivity)
      _ = A_up * c := by dsimp only [A_up]; ring
  have hU_col : ∀ j ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, U n j * ((A_up * c / Real.sqrt n) / (1 / Real.sqrt j))) ≤
        A_up * B_down * c ^ 2 * Real.log N := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
    have heq :
        (∑ n ∈ Icc 1 N, U n j * ((A_up * c / Real.sqrt n) / (1 / Real.sqrt j))) =
          (A_up * c) * ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
            ∑ n ∈ Icc 1 N, Real.sqrt ((j : ℝ) / n) * upInd w k n j := by
      dsimp only [U]
      simp_rw [sum_mul]
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [Real.sqrt_div hj0.le]
      field_simp [hsj.ne', (Real.sqrt_pos.mpr hn0).ne']
    rw [heq]
    have hdown := down_row_le (N := N) hw0.le hj1 K
    have hexp12 : Real.exp (w / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by dsimp only [w]; linarith only [hw_le1])
    have hjew : (j : ℝ) * (Real.exp w - 1) ≤ c * Real.exp 1 := by
      calc
        (j : ℝ) * (Real.exp w - 1) ≤ (N : ℝ) * ((c / N) * Real.exp 1) :=
          mul_le_mul hjN hew (by linarith [Real.add_one_le_exp w]) hN0.le
        _ = c * Real.exp 1 := by field_simp [hN0.ne']
    have hlogj : Real.log j + w ≤ 2 * Real.log N := by
      have hlj : Real.log j ≤ Real.log N := Real.log_le_log hj0 hjN
      linarith only [hlj, hw_le1, hL1]
    have hdown' :
        (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((j : ℝ) / n) * upInd w k n j) ≤
        B_down * c * Real.log N := by
      calc
        _ ≤ 2 * Real.exp (w / 2) * ((j : ℝ) * (Real.exp w - 1)) * (Real.log j + w) := by
          linarith only [hdown, (by ring :
            2 * Real.exp (w / 2) * (j : ℝ) * (Real.exp w - 1) * (Real.log j + w) =
              2 * Real.exp (w / 2) * ((j : ℝ) * (Real.exp w - 1)) * (Real.log j + w))]
        _ ≤ 2 * Real.exp (1 / 2) * (c * Real.exp 1) * (2 * Real.log N) :=
          mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_left hexp12 zero_le_two) hjew
              (mul_nonneg hj0.le (by linarith [Real.add_one_le_exp w])) (by positivity))
            hlogj (add_nonneg (Real.log_nonneg (by exact_mod_cast hj1)) hw0.le) (by positivity)
        _ = B_down * c * Real.log N := by dsimp only [B_down]; ring
    calc
      (A_up * c) * _ ≤ (A_up * c) * (B_down * c * Real.log N) :=
        mul_le_mul_of_nonneg_left hdown' (by positivity)
      _ = A_up * B_down * c ^ 2 * Real.log N := by ring
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U n j := fun n _ j _ =>
    sum_nonneg fun k _ => mul_nonneg (vonMangoldtAtom_nonneg' k)
      (by unfold upInd; split_ifs <;> norm_num)
  have hschur := sum_sq_abs_majorized_kernel_le' K_up U uTop
    (fun j => 1 / Real.sqrt j)
    (fun n => A_up * c / Real.sqrt n)
    (fun _ => A_up * B_down * c ^ 2 * Real.log N)
    hU_nonneg hKU
    (fun j hj => by
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      positivity)
    hU_row hU_col
  have hlog2T : 2 * (Real.log (2 * T) + 3) ≤ 16 * (1 + Real.log c) := by
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h2T : 2 * T ≤ 8 * c := by dsimp only [T]; nlinarith only [hc1, he1]
    have hlog8 : Real.log 8 ≤ 5 := by
      have he1' : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have he5 : (8 : ℝ) ≤ Real.exp 5 := by
        have hp : (2 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he1' 5
        rw [← Real.exp_nat_mul] at hp; norm_num at hp; linarith only [hp]
      exact (Real.log_le_log (by norm_num) he5).trans_eq (Real.log_exp 5)
    have hle : Real.log (2 * T) ≤ 5 + Real.log c := by
      calc
        Real.log (2 * T) ≤ Real.log (8 * c) := Real.log_le_log (by positivity) h2T
        _ = Real.log 8 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
        _ ≤ 5 + Real.log c := by linarith only [hlog8]
    have hlc0 := Real.log_nonneg hc1
    linarith only [hle, hlc0]
  have huTop_log :
      Real.log N * (∑ j ∈ Icc 1 N, uTop j ^ 2) ≤ 16 * (1 + Real.log c) * ‖u‖ ^ 2 := by
    have hfilt : (∑ j ∈ Icc 1 N, uTop j ^ 2) =
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (N : ℝ) / j < T), primeHorizonExtension u j ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun j _ => by dsimp only [uTop]; split_ifs <;> simp
    rw [hfilt]
    exact (sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hRNT hlog hu).trans
      (mul_le_mul_of_nonneg_right hlog2T (sq_nonneg _))
  have hnorm_sq :
      ‖upwardPrimeVector φ c N u‖ ^ 2 ≤
        (C_up * c * Real.sqrt (1 + Real.log c) * ‖u‖) ^ 2 := by
    rw [← sum_primeHorizonExtension_sq (upwardPrimeVector φ c N u),
      sum_congr rfl fun n hn => by rw [hrow_eq n hn]]
    have h16 : 16 * A_up * B_down ≤ C_up ^ 2 := by
      have hs : Real.sqrt (A_up * B_down) ^ 2 = A_up * B_down :=
        Real.sq_sqrt (mul_pos hA_up_pos hB_down_pos).le
      have hs0 : 0 ≤ Real.sqrt (A_up * B_down) := Real.sqrt_nonneg _
      dsimp only [C_up]
      nlinarith only [hs, hs0]
    have hlc1 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
    calc
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K_up n j * uTop j) ^ 2) ≤
          ∑ j ∈ Icc 1 N, (A_up * B_down * c ^ 2 * Real.log N) * uTop j ^ 2 := hschur
      _ = (A_up * B_down * c ^ 2) * (Real.log N * ∑ j ∈ Icc 1 N, uTop j ^ 2) := by
        rw [← mul_sum]; ring
      _ ≤ (A_up * B_down * c ^ 2) * (16 * (1 + Real.log c) * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left huTop_log (by positivity)
      _ = (16 * A_up * B_down) * (c ^ 2 * (1 + Real.log c) * ‖u‖ ^ 2) := by ring
      _ ≤ C_up ^ 2 * (c ^ 2 * (1 + Real.log c) * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = (C_up * c * Real.sqrt (1 + Real.log c) * ‖u‖) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hlc1]; ring
  have hrhs0 : 0 ≤ C_up * c * Real.sqrt (1 + Real.log c) * ‖u‖ := by
    have : 0 < C_up := by dsimp only [C_up]; positivity
    positivity
  nlinarith only [hnorm_sq, norm_nonneg (upwardPrimeVector φ c N u), hrhs0]

/-! ### 4. Bilinear `O(c (1 + log c))` bound for `overlapMatrix` on conductor subspaces -/

private theorem overlapMatrix_inner_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, y⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension y n *
        ∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension x j := by
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
      (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y.ofLp n *
    ∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j * x.ofLp j) = _
  rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension y n *
    ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension x j)]
  refine sum_congr rfl fun n _ => ?_
  rw [primeHorizonExtension_coe y n]
  congr 1
  rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe x j]
  dsimp only [overlapMatrix, K_ov]
  by_cases h : (j : ℕ) ≠ (n : ℕ) ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N
  · rw [if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩, if_pos h]
  · rw [if_neg fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩, if_neg h, zero_mul]

/-- Bilinear bound on `overlapMatrix φ c N` across arbitrary `v_A ∈ conductorSubspace R_A N` and
`v_B ∈ conductorSubspace R_B N` (`1 ≤ c ≤ log N`), completely free of `R_A` and `R_B`. -/
theorem exists_overlapMatrix_inner_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ov : ℝ, 0 < C_ov ∧
      ∀ {R_A R_B N : ℕ} {c : ℝ},
        2 ≤ R_A → 2 ≤ R_B →
        18 * (1 + Real.log R_A) ≤ Real.log N →
        18 * (1 + Real.log R_B) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        ((R_A * R_A : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R_B * R_B : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {v_A v_B : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        v_A ∈ conductorSubspace R_A N →
        v_B ∈ conductorSubspace R_B N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_A, v_B⟫| ≤
          C_ov * c * (1 + Real.log c) * ‖v_A‖ * ‖v_B‖ := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let M_ov : ℝ := K_pair + 2 + Real.exp (1 / 2)
  let K_nb : ℝ := 80 * (2 * Real.exp 2) ^ 2
  let C_ov : ℝ := Real.sqrt (20 * K_nb) * M_ov + 1
  refine ⟨C_ov, by dsimp only [C_ov, K_nb, M_ov]; positivity, ?_⟩
  intro R_A R_B N c hRA hRB hlogA hlogB hc1 hcL hw1 hRNTA hRNTB v_A v_B hvA hvB
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < ((R_A * R_A : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hRNTA]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((R_A * R_A : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) := by
      have h1 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have h2 : (0 : ℝ) ≤ (R_A * R_A : ℕ) := by positivity
      nlinarith only [h1, h2]
    exact_mod_cast this.trans hRNTA
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R_A; linarith only [hlogA, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  let g := atomDilate φ (c / N)
  let G0 := ∫ t, g t ^ 2
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair g n j / G0 + (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  let T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    dsimp only [T]; linarith only [h0]
  let vB_top : ℕ → ℝ := fun n => if (N : ℝ) / n < T then primeHorizonExtension v_B n else 0
  have hinner_eq :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_A, v_B⟫ =
        ∑ n ∈ Icc 1 N, vB_top n *
          ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_A j := by
    rw [overlapMatrix_inner_eq φ c N v_A v_B]
    refine sum_congr rfl fun n hn => ?_
    dsimp only [vB_top, K_ov, g, G0]
    split_ifs with hlt
    · rfl
    · rw [zero_mul]
      have hempty : nearRowIndices c N n = ∅ := by
        ext j
        simp only [notMem_empty, iff_false]
        intro hj
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.1
        have hle : (N : ℝ) / n ≤ linearNearRowRadius c := (div_le_iff₀ hn0).mpr hgeom
        exact hlt (by dsimp only [T]; linarith only [hle])
      rw [hempty, sum_empty, mul_zero]
  have hKov_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |K_ov n j| ≤ M_ov * Real.log N := by
    intro n hn j hj
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)
    have hrem : |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| ≤ K_pair := by
      simpa only [g, G0, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
    have hq : |q| ≤ 1 := by
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    have hlog_inv : |Real.log (1 / (c / N))| ≤ Real.log N := by
      have heq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 (by linarith only [hcN2, hc0])))]
      linarith [Real.log_nonneg hc1]
    have hnc : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
        (1 + Real.exp (1 / 2)) * Real.log N := by
      have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
      have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
        rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
          Real.sqrt_one, div_one]
      rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
        abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
      have hpole := (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le).trans hcL
      exact h1.trans (by simpa only [mul_comm (Real.log N)] using
        mul_le_mul_of_nonneg_right hpole (by positivity))
    have hid : K_ov n j = (atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q) +
        Real.log (1 / (c / N)) * q +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
      dsimp only [K_ov]; ring
    rw [hid]
    calc
      _ ≤ |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| +
            |Real.log (1 / (c / N)) * q| +
            |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| :=
        abs_add_three _ _ _
      _ ≤ K_pair + Real.log N * 1 + (1 + Real.exp (1 / 2)) * Real.log N := by
        rw [abs_mul]
        exact add_le_add (add_le_add hrem (mul_le_mul hlog_inv hq (abs_nonneg _) hL0.le)) hnc
      _ ≤ M_ov * Real.log N := by
        dsimp only [M_ov]; nlinarith only [hL1, hK_pair0]
  have hsqA := sum_nearBand_sq_le_of_mem_conductorSubspace hRA hlogA hc1 hw
    (by dsimp only [M_ov]; positivity) hRNTA K_ov hKov_le hvA
  have hvB_sq : (∑ n ∈ Icc 1 N, vB_top n ^ 2) ≤
      20 * (1 + Real.log c) / Real.log N * ‖v_B‖ ^ 2 := by
    have hfilt : (∑ n ∈ Icc 1 N, vB_top n ^ 2) =
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T), primeHorizonExtension v_B n ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun n _ => by dsimp only [vB_top]; split_ifs <;> simp
    rw [hfilt, div_mul_eq_mul_div, le_div_iff₀' hL0]
    have hq := sum_quotient_tail_sq_le_of_mem_conductorSubspace hRB hT1 hRNTB hlogB hvB
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _))
  rw [hinner_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) vB_top
    (fun n => ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_A j)
  have habs_sq :
      |∑ n ∈ Icc 1 N, vB_top n *
          ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_A j| ^ 2 ≤
        (C_ov * c * (1 + Real.log c) * ‖v_A‖ * ‖v_B‖) ^ 2 := by
    rw [sq_abs]
    have hCov_le : 20 * K_nb * M_ov ^ 2 ≤ C_ov ^ 2 := by
      have hs : Real.sqrt (20 * K_nb) ^ 2 = 20 * K_nb :=
        Real.sq_sqrt (by dsimp only [K_nb]; positivity)
      have hs0 : 0 ≤ Real.sqrt (20 * K_nb) := Real.sqrt_nonneg _
      have hMov0 : 0 ≤ M_ov := by dsimp only [M_ov]; positivity
      dsimp only [C_ov]
      nlinarith only [hs, hs0, hMov0, mul_nonneg hs0 hMov0]
    calc
      _ ≤ (∑ n ∈ Icc 1 N, vB_top n ^ 2) *
            (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n,
              K_ov n j * primeHorizonExtension v_A j) ^ 2) := hcs
      _ ≤ (20 * (1 + Real.log c) / Real.log N * ‖v_B‖ ^ 2) *
            (K_nb * c ^ 2 * (M_ov * Real.log N) ^ 2 *
              ((1 + Real.log c) / Real.log N) * ‖v_A‖ ^ 2) :=
        mul_le_mul hvB_sq hsqA
          (sum_nonneg fun _ _ => sq_nonneg _)
          (by have := Real.log_nonneg hc1; positivity)
      _ = (20 * K_nb * M_ov ^ 2) *
            (c ^ 2 * (1 + Real.log c) ^ 2 * ‖v_A‖ ^ 2 * ‖v_B‖ ^ 2) := by
        field_simp [hL0.ne']
      _ ≤ C_ov ^ 2 * (c ^ 2 * (1 + Real.log c) ^ 2 * ‖v_A‖ ^ 2 * ‖v_B‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hCov_le (by positivity)
      _ = (C_ov * c * (1 + Real.log c) * ‖v_A‖ * ‖v_B‖) ^ 2 := by ring
  have hrhs0 : 0 ≤ C_ov * c * (1 + Real.log c) * ‖v_A‖ * ‖v_B‖ := by
    have : 0 < C_ov := by dsimp only [C_ov, K_nb, M_ov]; positivity
    have := Real.log_nonneg hc1
    positivity
  nlinarith only [habs_sq, abs_nonneg (∑ n ∈ Icc 1 N, vB_top n *
    ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_A j), hrhs0]

/-! ### 5. Intermediate-band quadratic cancellation for `overlapMatrix` -/

/-- General summation-by-parts bound on `Ioc a b` in terms of uniform interval partial sums of `g`
and the total variation of `w`. -/
private theorem abs_sum_Ioc_mul_le_total_variation {a b : ℕ} (hab : a ≤ b)
    (w g : ℕ → ℝ) {B_part : ℝ}
    (hB : ∀ u v : ℕ, u ≤ v → |∑ n ∈ Ico u v, g n| ≤ B_part) :
    |∑ n ∈ Ioc a b, w n * g n| ≤
      B_part * (|w b| + ∑ i ∈ range (b - a - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)|) := by
  have hB0 : 0 ≤ B_part := (abs_nonneg _).trans (hB 0 0 le_rfl)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [Ioc_self, sum_empty, abs_zero]
    positivity
  · let L := b - a
    have hL1 : 1 ≤ L := by dsimp only [L]; omega
    have hIoc : Ioc a b = Ico (a + 1) (b + 1) := by
      ext n; simp only [mem_Ioc, mem_Ico]; omega
    have hlen : b + 1 - (a + 1) = L := by dsimp only [L]; omega
    have hrange : (∑ n ∈ Ioc a b, w n * g n) =
        ∑ i ∈ range L, w (a + 1 + i) * g (a + 1 + i) := by
      rw [hIoc, sum_Ico_eq_sum_range, hlen]
    rw [hrange]
    have hparts := Finset.sum_range_by_parts (fun i => w (a + 1 + i)) (fun i => g (a + 1 + i)) L
    simp only [smul_eq_mul] at hparts
    rw [hparts]
    have hpartial : ∀ k : ℕ, |∑ j ∈ range k, g (a + 1 + j)| ≤ B_part := fun k => by
      have heq : (∑ j ∈ range k, g (a + 1 + j)) = ∑ n ∈ Ico (a + 1) (a + 1 + k), g n := by
        rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rw [heq]
      exact hB (a + 1) (a + 1 + k) (Nat.le_add_right _ _)
    have hlast : a + 1 + (L - 1) = b := by dsimp only [L]; omega
    have hhead : |w (a + 1 + (L - 1)) * ∑ j ∈ range L, g (a + 1 + j)| ≤ B_part * |w b| := by
      rw [hlast, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpartial L) (abs_nonneg _)
    have htail :
        |∑ i ∈ range (L - 1),
            (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| ≤
          B_part * ∑ i ∈ range (L - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)| := by
      rw [mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpartial (i + 1)) (abs_nonneg _)
    calc
      |w (a + 1 + (L - 1)) * (∑ j ∈ range L, g (a + 1 + j)) -
          ∑ i ∈ range (L - 1),
            (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| ≤
          |w (a + 1 + (L - 1)) * ∑ j ∈ range L, g (a + 1 + j)| +
            |∑ i ∈ range (L - 1),
              (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| :=
        abs_sub _ _
      _ ≤ B_part * |w b| +
            B_part * ∑ i ∈ range (L - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)| :=
        add_le_add hhead htail
      _ = B_part * (|w b| + ∑ i ∈ range (b - a - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)|) := by
        dsimp only [L]; ring

/-- Uniform partial-sum bound for the zero-mean oscillating part of
`normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h)`. -/
private theorem shifted_mode_osc_Ico_le {m l R₂ : ℕ} (hR₂ : 2 ≤ R₂)
    (hm : m ∈ Icc 1 R₂) (hl : l ∈ Icc 1 R₂) (h u v : ℕ) (huv : u ≤ v) :
    |∑ n ∈ Ico u v,
        (normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) -
          (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0))| ≤
      4 * (R₂ : ℝ) ^ 3 := by
  obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
  obtain ⟨hl1, hlR⟩ := mem_Icc.mp hl
  let q := m * l
  have hq0 : 0 < q := Nat.mul_pos hm1 hl1
  let μ : ℝ := if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0
  let g_osc : ℕ → ℝ := fun n =>
    normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) - μ
  have hpm : ∀ n, normalizedRamanujanMode m (n + q) = normalizedRamanujanMode m n := fun n => by
    have hp := (normalizedRamanujanMode_periodic hm1).nat_mul l n
    simpa only [q, Nat.cast_id, Nat.mul_comm] using hp
  have hpl : ∀ n, normalizedRamanujanMode l (n + q + h) = normalizedRamanujanMode l (n + h) := fun n => by
    have hp := (normalizedRamanujanMode_periodic hl1).nat_mul m (n + h)
    simpa only [q, Nat.cast_id, show n + q + h = n + h + m * l by dsimp only [q]; omega] using hp
  have hper : Function.Periodic g_osc q := fun n => by
    dsimp only [g_osc]; rw [hpm n, hpl n]
  have hzero : (∑ n ∈ range q, g_osc n) = 0 := by
    dsimp only [g_osc]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have hprod : ∀ n : ℕ, normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) =
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))⁻¹ *
          (ramanujanLagCoefficient m (n + 0) * ramanujanLagCoefficient l (n + h)) := by
      intro n
      rw [normalizedRamanujanMode_eq_coefficient hm1, normalizedRamanujanMode_eq_coefficient hl1,
        Nat.add_zero]
      ring
    rw [sum_congr rfl fun n _ => hprod n, ← mul_sum,
      sum_range_ramanujanLagCoefficient_shift_mul hm1 hl1 (dvd_mul_right m l) (dvd_mul_left l m) 0 h,
      Nat.dist_zero_left]
    dsimp only [μ, q]
    by_cases hml : m = l
    · subst l
      rw [if_pos rfl, if_pos rfl]
      have hφ0 : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
      rw [Real.mul_self_sqrt hφ0.le]
      field_simp [hφ0.ne']
      ring
    · rw [if_neg hml, if_neg hml, mul_zero, mul_zero, sub_self]
  have habs_le : ∀ i : ℕ, |g_osc i| ≤ 2 * (R₂ : ℝ) := by
    intro i
    dsimp only [g_osc]
    have h1 := abs_normalizedRamanujanMode_le_sqrt_totient hm1 i
    have h2 := abs_normalizedRamanujanMode_le_sqrt_totient hl1 (i + h)
    have hφm : (m.totient : ℝ) ≤ R₂ := by exact_mod_cast (Nat.totient_le m).trans hmR
    have hφl : (l.totient : ℝ) ≤ R₂ := by exact_mod_cast (Nat.totient_le l).trans hlR
    have hprod_le : |normalizedRamanujanMode m i * normalizedRamanujanMode l (i + h)| ≤ R₂ := by
      rw [abs_mul]
      calc
        _ ≤ Real.sqrt m.totient * Real.sqrt l.totient :=
          mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt R₂ * Real.sqrt R₂ :=
          mul_le_mul (Real.sqrt_le_sqrt hφm) (Real.sqrt_le_sqrt hφl)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = R₂ := Real.mul_self_sqrt (Nat.cast_nonneg R₂)
    have hμ_le : |μ| ≤ 1 := by
      dsimp only [μ]
      split_ifs with hml
      · have hφ0 : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
        rw [abs_div, abs_of_pos hφ0, div_le_one hφ0]
        exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m h
      · rw [abs_zero]; exact zero_le_one
    have hR2_ge1 : (1 : ℝ) ≤ R₂ := by exact_mod_cast (show 1 ≤ R₂ by omega)
    exact (abs_sub _ _).trans (by linarith only [hprod_le, hμ_le, hR2_ge1])
  have hq_le : (q : ℝ) ≤ (R₂ : ℝ) ^ 2 := by
    have hnat : m * l ≤ R₂ * R₂ := Nat.mul_le_mul hmR hlR
    have hcast : ((m * l : ℕ) : ℝ) ≤ ((R₂ * R₂ : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [q, Nat.cast_mul, sq] using hcast
  calc
    |∑ n ∈ Ico u v, g_osc n| ≤ 2 * ∑ i ∈ range q, |g_osc i| :=
      abs_sum_Ico_le_of_periodic hq0 hper hzero u v huv
    _ ≤ 2 * ∑ _i ∈ range q, (2 * (R₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => habs_le i) zero_le_two
    _ = 4 * (q : ℝ) * R₂ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ 4 * (R₂ : ℝ) ^ 2 * R₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq_le (by norm_num))
        (Nat.cast_nonneg R₂)
    _ = 4 * (R₂ : ℝ) ^ 3 := by ring

/-- Telescoping total-variation bound `O(c^2 / N)` for the smooth reciprocal-offset weight
`w_h(n) = (1 / n) * G(N h / (c n))` on a non-empty interval `Ioc K₀ (N - h)`. -/
private theorem linearized_weight_tv_le {G : ℝ → ℝ} {K_lip : NNReal}
    (hG : LipschitzWith K_lip G) {M_φ : ℝ} (hM0 : 0 ≤ M_φ) (hM : ∀ t, |G t| ≤ M_φ)
    {c : ℝ} (hc1 : 1 ≤ c) {N h : ℕ} (hN1 : 1 ≤ N)
    (hh : h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊)
    (hK0_lt : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < N - h) :
    let K₀ := ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊
    let b := N - h
    let w_h : ℕ → ℝ := fun n => (1 / (n : ℝ)) * G ((N : ℝ) / c * ((h : ℝ) / n))
    |w_h b| + ∑ i ∈ range (b - K₀ - 1), |w_h (K₀ + 1 + (i + 1)) - w_h (K₀ + 1 + i)| ≤
      (2 * Real.exp 2 + 1) * (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) *
        c ^ 2 / N := by
  intro K₀ b w_h
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let A := linearNearRowRadius c + 1
  have hA0 : 0 < A := by dsimp only [A, linearNearRowRadius]; positivity
  have hA_le : A ≤ (2 * Real.exp 2 + 1) * c := by
    dsimp only [A, linearNearRowRadius]; nlinarith only [hc1]
  have hhB : (h : ℝ) ≤ 2 * Real.exp 2 * c := by
    have hle : (h : ℝ) ≤ linearNearRowRadius c :=
      (by exact_mod_cast (mem_Icc.mp hh).2 : (h : ℝ) ≤ ⌊linearNearRowRadius c⌋₊).trans
        (Nat.floor_le (by unfold linearNearRowRadius; positivity))
    simpa only [linearNearRowRadius, mul_comm c, mul_assoc] using hle
  let a₀ := K₀ + 1
  have ha0_pos : (0 : ℝ) < a₀ := by dsimp only [a₀]; positivity
  have ha0_inv : 1 / (a₀ : ℝ) ≤ A / N := by
    have hlt : (N : ℝ) / A < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_le_div_iff₀ ha0_pos hN0]
    have hm := (div_lt_iff₀ hA0).mp hlt
    dsimp only [a₀]
    push_cast
    linarith only [hm]
  have ha0_le_b : a₀ ≤ b := by dsimp only [a₀]; omega
  have hb_pos : (0 : ℝ) < b := lt_of_lt_of_le ha0_pos (by exact_mod_cast ha0_le_b)
  have hb_inv : 1 / (b : ℝ) ≤ A / N :=
    (one_div_le_one_div_of_le ha0_pos (by exact_mod_cast ha0_le_b)).trans ha0_inv
  have hwb_le : |w_h b| ≤ (A / N) * M_φ := by
    dsimp only [w_h]
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hb_pos)]
    exact mul_le_mul hb_inv (hM _) (abs_nonneg _) (div_nonneg hA0.le hN0.le)
  let L' := b - K₀ - 1
  let invF : ℕ → ℝ := fun i => 1 / ((a₀ + i : ℕ) : ℝ)
  let argF : ℕ → ℝ := fun i => (N : ℝ) / c * ((h : ℝ) / (a₀ + i : ℕ))
  have hstep : ∀ i : ℕ, |w_h (a₀ + (i + 1)) - w_h (a₀ + i)| ≤
      M_φ * (invF i - invF (i + 1)) +
        (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1)) := by
    intro i
    have hi_pos : (0 : ℝ) < (a₀ + i : ℕ) := by dsimp only [a₀]; positivity
    have hi_le : ((a₀ + i : ℕ) : ℝ) ≤ (a₀ + (i + 1) : ℕ) := by exact_mod_cast (by omega : a₀ + i ≤ a₀ + (i + 1))
    have hinv_mono : invF (i + 1) ≤ invF i := one_div_le_one_div_of_le hi_pos hi_le
    have hinv_le : invF i ≤ A / N := by
      have h0 : ((a₀ : ℕ) : ℝ) ≤ (a₀ + i : ℕ) := by exact_mod_cast Nat.le_add_right a₀ i
      exact (one_div_le_one_div_of_le ha0_pos h0).trans ha0_inv
    have hinv_nonneg : 0 ≤ invF i := by dsimp only [invF]; positivity
    have harg_mono : argF (i + 1) ≤ argF i := by
      dsimp only [argF]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Nat.cast_nonneg h) hi_pos hi_le) (by positivity)
    have hlip_i : |G (argF (i + 1)) - G (argF i)| ≤ (K_lip : ℝ) * (argF i - argF (i + 1)) := by
      have hdist := hG.dist_le_mul (argF (i + 1)) (argF i)
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr harg_mono)] at hdist
      linarith only [hdist]
    have hid : w_h (a₀ + (i + 1)) - w_h (a₀ + i) =
        (invF (i + 1) - invF i) * G (argF (i + 1)) +
          invF i * (G (argF (i + 1)) - G (argF i)) := by
      dsimp only [w_h, invF, argF]; ring
    rw [hid]
    calc
      _ ≤ |(invF (i + 1) - invF i) * G (argF (i + 1))| +
            |invF i * (G (argF (i + 1)) - G (argF i))| := abs_add_le _ _
      _ = |invF (i + 1) - invF i| * |G (argF (i + 1))| +
            invF i * |G (argF (i + 1)) - G (argF i)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hinv_nonneg]
      _ = (invF i - invF (i + 1)) * |G (argF (i + 1))| +
            invF i * |G (argF (i + 1)) - G (argF i)| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hinv_mono)]; ring
      _ ≤ (invF i - invF (i + 1)) * M_φ +
            (A / N) * ((K_lip : ℝ) * (argF i - argF (i + 1))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hM _) (sub_nonneg.mpr hinv_mono))
          (mul_le_mul hinv_le hlip_i (abs_nonneg _) (div_nonneg hA0.le hN0.le))
      _ = M_φ * (invF i - invF (i + 1)) +
            (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1)) := by ring
  have htel_inv : (∑ i ∈ range L', (invF i - invF (i + 1))) ≤ A / N := by
    rw [Finset.sum_range_sub']
    have hpos : 0 ≤ invF L' := by dsimp only [invF]; positivity
    have h0 : invF 0 = 1 / (a₀ : ℝ) := rfl
    linarith only [hpos, h0, ha0_inv]
  have htel_arg : (∑ i ∈ range L', (argF i - argF (i + 1))) ≤ 2 * Real.exp 2 * A := by
    rw [Finset.sum_range_sub']
    have hpos : 0 ≤ argF L' := by dsimp only [argF]; positivity
    have h0 : argF 0 ≤ 2 * Real.exp 2 * A := by
      have heq : argF 0 = ((N : ℝ) / c) * (h : ℝ) * (1 / (a₀ : ℝ)) := by
        dsimp only [argF]; ring
      rw [heq]
      calc
        ((N : ℝ) / c) * (h : ℝ) * (1 / (a₀ : ℝ)) ≤
            ((N : ℝ) / c) * (2 * Real.exp 2 * c) * (A / N) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hhB (by positivity))
            ha0_inv (by positivity) (by positivity)
        _ = 2 * Real.exp 2 * A := by field_simp [hc0.ne', hN0.ne']
    linarith only [hpos, h0]
  have hsum_le :
      (∑ i ∈ range L', |w_h (a₀ + (i + 1)) - w_h (a₀ + i)|) ≤
        M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A) := by
    calc
      _ ≤ ∑ i ∈ range L', (M_φ * (invF i - invF (i + 1)) +
            (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1))) :=
        sum_le_sum fun i _ => hstep i
      _ = M_φ * (∑ i ∈ range L', (invF i - invF (i + 1))) +
            (A / N) * (K_lip : ℝ) * (∑ i ∈ range L', (argF i - argF (i + 1))) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A) :=
        add_le_add
          (mul_le_mul_of_nonneg_left htel_inv hM0)
          (mul_le_mul_of_nonneg_left htel_arg (by positivity))
  have hfactor :
      2 * M_φ + 2 * Real.exp 2 * A * (K_lip : ℝ) ≤
        (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c := by
    have h1 : 2 * M_φ ≤ 2 * M_φ * c := by nlinarith only [hM0, hc1]
    have h2 : 2 * Real.exp 2 * A * (K_lip : ℝ) ≤
        2 * Real.exp 2 * ((2 * Real.exp 2 + 1) * c) * (K_lip : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA_le (by positivity)) K_lip.2
    linarith only [h1, h2, (by ring :
      2 * M_φ * c + 2 * Real.exp 2 * ((2 * Real.exp 2 + 1) * c) * (K_lip : ℝ) =
        (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c)]
  calc
    |w_h b| + ∑ i ∈ range L', |w_h (a₀ + (i + 1)) - w_h (a₀ + i)| ≤
        (A / N) * M_φ + (M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A)) :=
      add_le_add hwb_le hsum_le
    _ = A * (2 * M_φ + 2 * Real.exp 2 * A * (K_lip : ℝ)) / N := by ring
    _ ≤ ((2 * Real.exp 2 + 1) * c) *
          ((2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c) / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul hA_le hfactor (by positivity) (by positivity)) hN0.le
    _ = (2 * Real.exp 2 + 1) *
          (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c ^ 2 / N := by
      ring

/-- Off-diagonal symmetric double sum reindexed by positive lag `h = j - n`. -/
private theorem sum_offDiag_symm_eq_two_mul_sum_Icc_sub (N : ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n j, F n j = F j n) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n), F n j) =
      2 * ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - h), F n (n + h) := by
  have hsplit : ∀ n ∈ Icc 1 N,
      (∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n), F n j) =
        (∑ j ∈ Icc 1 N, if j < n then F n j else 0) +
          (∑ j ∈ Icc 1 N, if n < j then F n j else 0) := by
    intro n _
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy j n with hlt | rfl | hgt
    · rw [if_pos hlt.ne, if_pos hlt, if_neg (lt_asymm hlt), add_zero]
    · rw [if_neg (not_not.mpr rfl), if_neg (lt_irrefl j), add_zero]
    · rw [if_pos hgt.ne', if_neg (lt_asymm hgt), if_pos hgt, zero_add]
  have hsymm :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if j < n then F n j else 0) =
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if n < j then F n j else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun n _ => by rw [hF n j]
  have hupper : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, if n < j then F n j else 0) =
        ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hIoc : (∑ j ∈ Icc 1 N, if n < j then F n j else 0) = ∑ j ∈ Ioc n N, F n j := by
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_filter, mem_Icc, mem_Ioc]
      omega
    have hbij : (∑ j ∈ Ioc n N, F n j) = ∑ h ∈ Icc 1 (N - n), F n (n + h) := by
      refine (sum_bij (fun h _ => n + h) ?_ ?_ ?_ ?_).symm
      · intro h hh; simp only [mem_Icc, mem_Ioc] at *; omega
      · intro h₁ _ h₂ _ heq; omega
      · intro j hj
        refine ⟨j - n, ?_, ?_⟩
        · simp only [mem_Icc, mem_Ioc] at *; omega
        · simp only [mem_Ioc] at *; omega
      · intro _ _; rfl
    have hfilt : (∑ h ∈ Icc 1 (N - n), F n (n + h)) =
        ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0 := by
      rw [← sum_filter]
      congr 1
      ext h
      simp only [mem_filter, mem_Icc]
      omega
    rw [hIoc, hbij, hfilt]
  have hswap :
      (∑ n ∈ Icc 1 N, ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0) =
        ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - h), F n (n + h) := by
    rw [sum_comm]
    refine sum_congr rfl fun h hh => ?_
    obtain ⟨_, hhN⟩ := mem_Icc.mp hh
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  rw [sum_congr rfl hsplit, sum_add_distrib, hsymm, ← two_mul, sum_congr rfl hupper, hswap]

private def midBandSubKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
    (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j -
    (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N))

private def midBandLeadKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  shellAutocorr φ (|Real.log j - Real.log n| / (c / N))

private def midBandPacketMode (R₂ : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 R₂, a m * normalizedRamanujanMode m k

private def midBandLinearizedWeight (φ : ℝ → ℝ) (c : ℝ) (N h n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n))

private def midBandLagSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
    ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) * (1 / (n : ℝ)) *
        (Real.sqrt n / Real.sqrt (n + h : ℕ) *
          shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)))

private def midBandLinearizedSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
    ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
        midBandLinearizedWeight φ c N h n

private def midBandMeanSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∑ m ∈ Icc 1 R₂,
    a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
      ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        midBandLinearizedWeight φ c N h n

private def midBandOscMode (m l h n : ℕ) : ℝ :=
  normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) -
    if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0

private def midBandOscSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
    a m * a l *
      ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        midBandLinearizedWeight φ c N h n * midBandOscMode m l h n

private theorem midBand_primeHorizonExtension_eq (R₂ N : ℕ) (a : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 N) :
    primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k =
      (Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a k / Real.sqrt k) := by
  rw [primeHorizonExtension_coe _ ⟨k, hk⟩]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨k, hk⟩)
      (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) = _
  rw [map_sum, midBandPacketMode, sum_div, mul_sum]
  exact sum_congr rfl fun m _ => by
    change a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m k / Real.sqrt k)) = _
    ring

private theorem midBandPacketMode_sq_sum_le {R₂ N : ℕ} (hL0 : 0 < Real.log N) (a : ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2) ≤
      (N : ℝ) * Real.log N *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hpt : ∀ k ∈ Icc 1 N,
      midBandPacketMode R₂ a k ^ 2 ≤
        (N : ℝ) * Real.log N *
          primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr (mem_Icc.mp hk).2
    rw [midBand_primeHorizonExtension_eq R₂ N a hk, mul_pow, inv_pow, div_pow,
      Real.sq_sqrt hL0.le, Real.sq_sqrt hk0.le]
    have hid : (N : ℝ) * Real.log N * ((Real.log N)⁻¹ * (midBandPacketMode R₂ a k ^ 2 / k)) =
        ((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2 := by
      calc
        (N : ℝ) * Real.log N * ((Real.log N)⁻¹ * (midBandPacketMode R₂ a k ^ 2 / k)) =
            (Real.log N * (Real.log N)⁻¹) * (((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2) := by
          ring
        _ = ((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2 := by
          rw [mul_inv_cancel₀ hL0.ne', one_mul]
    rw [hid]
    exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_div hk0).mpr hkN)
  calc
    (∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2) ≤
        ∑ k ∈ Icc 1 N, (N : ℝ) * Real.log N *
          primeHorizonExtension
            (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 :=
      sum_le_sum hpt
    _ = (N : ℝ) * Real.log N *
          ∑ k ∈ Icc 1 N,
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 := by
      rw [← mul_sum]
    _ = (N : ℝ) * Real.log N *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      rw [sum_primeHorizonExtension_sq]

private theorem midBand_inv_le_of_floor_lt {c : ℝ} (hc1 : 1 ≤ c) {N n : ℕ} (hN0 : (0 : ℝ) < N)
    (hnK : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < n) :
    1 / (n : ℝ) ≤ (2 * Real.exp 2 + 1) * c / N := by
  have hArad_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hArad_le : linearNearRowRadius c + 1 ≤ (2 * Real.exp 2 + 1) * c := by
    unfold linearNearRowRadius; nlinarith only [hc1]
  have hn_ge : ((⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) : ℝ) ≤ n :=
    Nat.cast_le.mpr (by omega)
  have ha0_pos : (0 : ℝ) < (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) := by positivity
  have hlt : (N : ℝ) / (linearNearRowRadius c + 1) <
      (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha0_inv :
      1 / ((⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) : ℝ) ≤
        (linearNearRowRadius c + 1) / N := by
    rw [div_le_div_iff₀ ha0_pos hN0]
    have hm := (div_lt_iff₀ hArad_pos).mp hlt
    push_cast; linarith only [hm]
  exact (one_div_le_one_div_of_le ha0_pos hn_ge).trans
    (ha0_inv.trans (div_le_div_of_nonneg_right hArad_le hN0.le))

private theorem exists_midBand_subKernel_sum_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_1 : ℝ, 0 < C_1 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        2 ≤ R₂ → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R₂ N →
        |∑ n ∈ Icc 1 N, primeHorizonExtension u n *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j| ≤
          C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  refine ⟨Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
      (K_pair + (1 + Real.exp (1 / 2))) + 1, by positivity, ?_⟩
  intro R₂ N c hR₂ hlog hc1 hw1 hradN hRNT u hu_mem
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R₂; linarith only [hlog, this]
  have hT1 : 1 ≤ linearNearRowRadius c + 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    linarith only [h0]
  have htop_eq :
      (∑ n ∈ Icc 1 N, primeHorizonExtension u n *
          ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j) =
        ∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j := by
    refine sum_congr rfl fun n hn => ?_
    split_ifs with hlt
    · rfl
    · rw [zero_mul]
      have hempty : nearRowIndices c N n = ∅ := by
        ext j
        simp only [notMem_empty, iff_false]
        intro hj
        have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
        have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.1
        have hle : (N : ℝ) / n ≤ linearNearRowRadius c := (div_le_iff₀ hn0).mpr hgeom
        exact hlt (by linarith only [hle])
      rw [hempty, sum_empty, mul_zero]
  have hKsub_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |midBandSubKernel φ c N n j| ≤ (K_pair + (1 + Real.exp (1 / 2))) * c := by
    intro n hn j hj
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    have hrem :
        |atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) -
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ K_pair := by
      have h1 := hpair (c / N) hw0 hw1 n j hs
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using h1
    have hnc : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
        (1 + Real.exp (1 / 2)) * c := by
      have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
      have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
        rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
          Real.sqrt_one, div_one]
      rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
        abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
      have hpole := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
      exact h1.trans (by
        simpa only [mul_comm c] using mul_le_mul_of_nonneg_right hpole (by positivity))
    have hid : midBandSubKernel φ c N n j =
        (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) -
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            shellAutocorr φ (|Real.log j - Real.log n| / (c / N))) +
          (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
      unfold midBandSubKernel; ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add hrem hnc).trans (by nlinarith only [hc1, hK_pair0]))
  have hsqA := sum_nearBand_sq_le_of_mem_conductorSubspace hR₂ hlog hc1 hw
    (by positivity) hRNT (midBandSubKernel φ c N) hKsub_le hu_mem
  have huTop_sq :
      (∑ n ∈ Icc 1 N,
        (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) ^ 2) ≤
        20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by
    have hfilt :
        (∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) ^ 2) =
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < linearNearRowRadius c + 1),
          primeHorizonExtension u n ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun n _ => by split_ifs <;> simp
    rw [hfilt, div_mul_eq_mul_div, le_div_iff₀' hL0]
    have hq := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR₂ hT1 hRNT hlog hu_mem
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _))
  rw [htop_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
    (fun n => if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0)
    (fun n => ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j)
  have hC1_sq :
      20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2 ≤
        (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
          (K_pair + (1 + Real.exp (1 / 2))) + 1) ^ 2 := by
    have hs : Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) ^ 2 =
        20 * (80 * (2 * Real.exp 2) ^ 2) := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) := Real.sqrt_nonneg _
    have hM0 : 0 ≤ K_pair + (1 + Real.exp (1 / 2)) := by positivity
    nlinarith only [hs, hs0, hM0, mul_nonneg hs0 hM0]
  have habs_sq :
      |∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j| ^ 2 ≤
        ((Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
          (K_pair + (1 + Real.exp (1 / 2))) + 1) *
            (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by
    rw [sq_abs]
    calc
      _ ≤ _ := hcs
      _ ≤ (20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) *
            ((80 * (2 * Real.exp 2) ^ 2) * c ^ 2 *
              ((K_pair + (1 + Real.exp (1 / 2))) * c) ^ 2 *
              ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) :=
        mul_le_mul huTop_sq hsqA
          (sum_nonneg fun _ _ => sq_nonneg _)
          (by have := Real.log_nonneg hc1; positivity)
      _ = (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
            ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) := by
        calc
          (20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) *
              ((80 * (2 * Real.exp 2) ^ 2) * c ^ 2 *
                ((K_pair + (1 + Real.exp (1 / 2))) * c) ^ 2 *
                ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) =
            (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
              (((c ^ 2 * (1 + Real.log c)) * (Real.log N)⁻¹) ^ 2 * (‖u‖ ^ 2) ^ 2) := by ring
          _ = (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
                ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) := by
            rw [div_eq_mul_inv (c ^ 2 * (1 + Real.log c)) (Real.log N)]
      _ ≤ (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
            (K_pair + (1 + Real.exp (1 / 2))) + 1) ^ 2 *
            ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hC1_sq (by positivity)
      _ = ((Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
            (K_pair + (1 + Real.exp (1 / 2))) + 1) *
              (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by ring
  have hrhs0 : 0 ≤ (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
      (K_pair + (1 + Real.exp (1 / 2))) + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
    have := Real.log_nonneg hc1; positivity
  nlinarith only [habs_sq, abs_nonneg (∑ n ∈ Icc 1 N,
    (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
      ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j), hrhs0]

private theorem midBand_leadKernel_sum_eq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    {R₂ N : ℕ} {c : ℝ} (hL0 : 0 < Real.log N) (hc0 : 0 < c) (hw : c / N ≤ 1)
    (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
        primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
          ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
      (Real.log N)⁻¹ * (2 * midBandLagSum φ R₂ N c a) := by
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hlead_eq :
      (∑ n ∈ Icc 1 N,
        primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
          ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
        (Real.log N)⁻¹ *
          ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n),
            (midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
              (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [midBand_primeHorizonExtension_eq R₂ N a hn, mul_sum, mul_sum]
    have hsub : nearRowIndices c N n ⊆ (Icc 1 N).filter (fun j => j ≠ n) := fun j hj => by
      obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨hjI, hjn⟩
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      have hjI := (mem_filter.mp hj).1
      rw [midBand_primeHorizonExtension_eq R₂ N a hjI]
      have hsqL : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hL0.le]
      calc
        (Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a n / Real.sqrt n) *
            (midBandLeadKernel φ c N n j *
              ((Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a j / Real.sqrt j))) =
          ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹) *
            ((midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
              (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j) := by ring
        _ = (Real.log N)⁻¹ *
              ((midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
                (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j) := by rw [hsqL]
    · intro j hjf hjnri
      obtain ⟨hjI, hjn⟩ := mem_filter.mp hjf
      have hgt : 2 * c / N < |Real.log j - Real.log n| := by
        by_contra hle
        exact hjnri (mem_filter.mpr ⟨hjI, hjn, not_lt.mp hle⟩)
      have hw0 : 0 < c / N := div_pos hc0 hN0
      have hge1 : 1 ≤ |(|Real.log j - Real.log n| / (c / N))| := by
        rw [abs_of_pos (div_pos (lt_of_le_of_lt (by positivity) hgt) hw0), le_div_iff₀ hw0]
        have : 2 * (c / N) < |Real.log j - Real.log n| := by simpa only [mul_div_assoc] using hgt
        linarith only [this, hw0]
      have hK0 : midBandLeadKernel φ c N n j = 0 :=
        shellAutocorr_eq_zero_of_one_le_abs hφ hsupp hge1
      rw [hK0, mul_zero, mul_zero]
  rw [hlead_eq]
  congr 1
  have hBN : ⌊linearNearRowRadius c⌋₊ ≤ N := by
    have h1 : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ linearNearRowRadius c :=
      Nat.floor_le (by unfold linearNearRowRadius; positivity)
    have h2 : linearNearRowRadius c ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have : (0 : ℝ) ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [this]
    exact_mod_cast (h1.trans h2).trans hradN
  rw [sum_offDiag_symm_eq_two_mul_sum_Icc_sub N
    (fun n j => (midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
      (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j)
    (fun n j => by
      unfold midBandLeadKernel
      rw [mul_comm (midBandPacketMode R₂ a n) (midBandPacketMode R₂ a j),
        mul_comm (Real.sqrt n) (Real.sqrt j), abs_sub_comm])]
  congr 1
  unfold midBandLagSum
  have hvanish : ∀ h ∈ Icc 1 N, ∀ n ∈ Icc 1 (N - h),
      (⌊linearNearRowRadius c⌋₊ < h ∨
        n ≤ ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊) →
      (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) /
        (Real.sqrt n * Real.sqrt (n + h : ℕ))) * midBandLeadKernel φ c N n (n + h) = 0 := by
    intro h hh n hn hcond
    obtain ⟨hh1, _⟩ := mem_Icc.mp hh
    obtain ⟨hn1, hnNh⟩ := mem_Icc.mp hn
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, by omega⟩
    have hnhI : n + h ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
    have hK0 : midBandLeadKernel φ c N n (n + h) = 0 := by
      by_contra hne
      have hlt1 : |(|Real.log (n + h : ℕ) - Real.log n| / (c / N))| < 1 := by
        by_contra hge
        exact hne (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (not_lt.mp hge))
      have hw0 : 0 < c / N := div_pos hc0 hN0
      have hdiv_lt : |Real.log (n + h : ℕ) - Real.log n| / (c / N) < 1 :=
        (le_abs_self _).trans_lt hlt1
      have hlog_le : |Real.log (n + h : ℕ) - Real.log n| ≤ 2 * c / N := by
        have := (div_lt_iff₀ hw0).mp hdiv_lt
        linarith only [this, hw0, (by ring : 1 * (c / N) = c / N),
          (by ring : 2 * (c / N) = 2 * c / N)]
      have hmem : n + h ∈ nearRowIndices c N n :=
        mem_filter.mpr ⟨hnhI, by omega, hlog_le⟩
      have hgeom := nearRow_geometry_small_width hc0 hnI hmem hw
      have hh_le_B : h ≤ ⌊linearNearRowRadius c⌋₊ := by
        apply Nat.le_floor
        have hsub : |((n + h : ℕ) : ℝ) - n| = h := by
          push_cast; rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg h)]
        linarith only [hgeom.1, hsub]
      have hK0_lt_n : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < n := by
        have hA_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
        have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hstrict : (N : ℝ) < (linearNearRowRadius c + 1) * n := by
          nlinarith only [hgeom.2.1, hn_real]
        exact Nat.floor_lt (div_nonneg hN0.le hA_pos.le) |>.mpr ((div_lt_iff₀' hA_pos).mpr hstrict)
      rcases hcond with hBh | hnK0 <;> omega
    rw [hK0, mul_zero]
  have hsub_h : Icc 1 ⌊linearNearRowRadius c⌋₊ ⊆ Icc 1 N := Icc_subset_Icc_right hBN
  rw [← sum_subset hsub_h]
  · refine sum_congr rfl fun h hh => ?_
    have hsub_n : Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h) ⊆ Icc 1 (N - h) :=
      fun n hn => by simp only [mem_Ioc, mem_Icc] at *; omega
    rw [← sum_subset hsub_n]
    · refine sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (mem_Icc.mp (hsub_n hn)).1
      have hh1 : 1 ≤ h := (mem_Icc.mp hh).1
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hnh0 : (0 : ℝ) < (n + h : ℕ) := Nat.cast_pos.mpr (by omega)
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hsnh : 0 < Real.sqrt (n + h : ℕ) := Real.sqrt_pos.mpr hnh0
      have hlog_nonneg : 0 ≤ Real.log (n + h : ℕ) - Real.log n :=
        sub_nonneg.mpr (Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.le_add_right n h)))
      have harg : |Real.log (n + h : ℕ) - Real.log n| / (c / N) =
          (N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n) := by
        rw [abs_of_nonneg hlog_nonneg, div_div_eq_mul_div]; ring
      unfold midBandLeadKernel
      rw [harg]
      have hjac : (1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ)) =
          1 / (Real.sqrt n * Real.sqrt (n + h : ℕ)) := by
        have hsqn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        nth_rw 1 [hsqn]
        calc
          (1 / (Real.sqrt n * Real.sqrt n)) * (Real.sqrt n / Real.sqrt (n + h : ℕ)) =
              (Real.sqrt n * (Real.sqrt n)⁻¹) *
                (1 / (Real.sqrt n * Real.sqrt (n + h : ℕ))) := by ring
          _ = 1 / (Real.sqrt n * Real.sqrt (n + h : ℕ)) := by
            rw [mul_inv_cancel₀ hsn.ne', one_mul]
      calc
        (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) /
            (Real.sqrt n * Real.sqrt (n + h : ℕ))) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) =
          midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
            (1 / (Real.sqrt n * Real.sqrt (n + h : ℕ))) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) := by ring
        _ = midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
              ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ))) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) := by rw [hjac]
        _ = midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) * (1 / (n : ℝ)) *
              (Real.sqrt n / Real.sqrt (n + h : ℕ) *
                shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n))) := by ring
    · intro n hnIcc hnIoc
      have hnK0 : n ≤ ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ := by
        simp only [mem_Icc, mem_Ioc, not_and] at hnIcc hnIoc
        omega
      exact hvanish h (hsub_h hh) n hnIcc (Or.inr hnK0)
  · intro h hhN hhB
    have hBh : ⌊linearNearRowRadius c⌋₊ < h := by
      simp only [mem_Icc, not_and, not_le] at hhN hhB
      exact hhB hhN.1
    exact sum_eq_zero fun n hn => hvanish h hhN n hn (Or.inl hBh)

private theorem exists_midBand_lag_sub_linearized_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_2 : ℝ, 0 ≤ C_2 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        0 < Real.log N → 1 ≤ c →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ a : ℕ → ℝ,
        |midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a| ≤
          C_2 * (c ^ 5 * Real.log N / N) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨K_lip, hG_lip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨(2 * Real.exp 2) * (2 * Real.exp 2 + 1) *
      (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
        (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)),
    by positivity, ?_⟩
  intro R₂ N c hL0 hc1 hradN a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hBN : ⌊linearNearRowRadius c⌋₊ ≤ N := by
    have h1 : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ linearNearRowRadius c :=
      Nat.floor_le (by unfold linearNearRowRadius; positivity)
    have h2 : linearNearRowRadius c ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have : (0 : ℝ) ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [this]
    exact_mod_cast (h1.trans h2).trans hradN
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have hArad_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hArad_le : linearNearRowRadius c + 1 ≤ (2 * Real.exp 2 + 1) * c := by
    unfold linearNearRowRadius; nlinarith only [hc1]
  have hf_sq_sum := midBandPacketMode_sq_sum_le (R₂ := R₂) hL0 a
  have hdiff : midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a =
      ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
        ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)) *
            ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
              shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n)))) := by
    unfold midBandLagSum midBandLinearizedSum midBandLinearizedWeight
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun h _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hdiff]
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)) *
            ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
              shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n))))| ≤
        ((2 * Real.exp 2 + 1) *
          (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
          (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    obtain ⟨hh1, hhB⟩ := mem_Icc.mp hh
    have hhB_N : h ≤ N := hhB.trans hBN
    have hker_n : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        |(1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
            shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n)))| ≤
          (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2 := by
      intro n hn
      obtain ⟨hnK0, _⟩ := mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hnh0 : (0 : ℝ) < (n + h : ℕ) := Nat.cast_pos.mpr (by omega)
      have hBr0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have hBr_eq : linearNearRowRadius c = (2 * Real.exp 2) * c := by
        unfold linearNearRowRadius; ring
      have hgap : |((n + h : ℕ) : ℝ) - n| ≤ linearNearRowRadius c := by
        have hsub : |((n + h : ℕ) : ℝ) - n| = h := by
          push_cast; rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg h)]
        rw [hsub]
        exact (Nat.cast_le.mpr hhB).trans (Nat.floor_le hBr0)
      have hNx : (N : ℝ) ≤ (linearNearRowRadius c + 1) * n := by
        have hlt : (N : ℝ) / (linearNearRowRadius c + 1) <
            (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have hm := (div_lt_iff₀ hArad_pos).mp hlt
        have hn_ge : (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 ≤ n := by
          have h1 : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 ≤ n := by omega
          exact_mod_cast h1
        have hmul := mul_le_mul_of_nonneg_left hn_ge hArad_pos.le
        linarith only [hm, hmul]
      have hNy : (N : ℝ) ≤ (linearNearRowRadius c + 1) * (n + h : ℕ) :=
        hNx.trans (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Nat.le_add_right n h)) hArad_pos.le)
      have hlarge : 2 * (linearNearRowRadius c + 1) * linearNearRowRadius c ≤ N := by
        have hle : 2 * (linearNearRowRadius c + 1) * linearNearRowRadius c ≤
            4 * (linearNearRowRadius c + 1) ^ 2 := by
          nlinarith only [hBr0, hArad_pos]
        exact hle.trans hradN
      have hlin := abs_sqrt_log_kernel_sub_linear_le hG_lip hG_le hc0 hN0
        hArad_pos.le hBr0 hn0 hnh0 hgap hNx hNy hlarge
      have harg_eq : (((n + h : ℕ) : ℝ) - n) / n = (h : ℝ) / n := by
        push_cast; rw [add_sub_cancel_left]
      rw [harg_eq] at hlin
      have hker_le :
          (4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 * linearNearRowRadius c ^ 2 / c +
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2)) / N ≤
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3 / N := by
        refine div_le_div_of_nonneg_right ?_ hN0.le
        have hA2 : (linearNearRowRadius c + 1) ^ 2 ≤ (2 * Real.exp 2 + 1) ^ 2 * c ^ 2 := by
          have := pow_le_pow_left₀ hArad_pos.le hArad_le 2
          rwa [mul_pow] at this
        have hterm1 :
            4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 * linearNearRowRadius c ^ 2 / c ≤
              4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 * c ^ 3 := by
          calc
            4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 *
                linearNearRowRadius c ^ 2 / c ≤
              4 * (K_lip : ℝ) * ((2 * Real.exp 2 + 1) ^ 2 * c ^ 2) *
                linearNearRowRadius c ^ 2 / c :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hA2 (by positivity)) (sq_nonneg _)) hc0.le
            _ = (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 *
                  (2 * Real.exp 2) ^ 2 * c ^ 3) * c / c := by rw [hBr_eq]; ring
            _ = 4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 *
                  (2 * Real.exp 2) ^ 2 * c ^ 3 := mul_div_cancel_right₀ _ hc0.ne'
        have hterm2 :
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2) ≤
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 := by
          have hc23 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 3)
          calc
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2) ≤
                ((2 * Real.exp 2 + 1) * c) * linearNearRowRadius c * (∫ t, φ t ^ 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hArad_le hBr0) hM.le
            _ = (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 2 := by
              rw [hBr_eq]; ring
            _ ≤ (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 :=
              mul_le_mul_of_nonneg_left hc23 (by positivity)
        linarith only [hterm1, hterm2, (by ring :
          4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 * c ^ 3 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 =
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3)]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
      calc
        _ ≤ ((2 * Real.exp 2 + 1) * c / N) *
              ((4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3 / N) :=
          mul_le_mul (midBand_inv_le_of_floor_lt hc1 hN0 hnK0)
            (hlin.trans hker_le) (abs_nonneg _) (by positivity)
        _ = (2 * Real.exp 2 + 1) *
              (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
              c ^ 4 / (N : ℝ) ^ 2 := by ring
    have hf_prod_sum :
        (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)|) ≤
          (N : ℝ) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      have h1 :
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandPacketMode R₂ a n ^ 2) ≤
            ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => sq_nonneg _
        simp only [mem_Ioc, mem_Icc] at *; omega
      have h2 :
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandPacketMode R₂ a (n + h) ^ 2) ≤
            ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by
        have himg :
            (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandPacketMode R₂ a (n + h) ^ 2) =
              ∑ k ∈ (Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h)).image (fun x => x + h),
                midBandPacketMode R₂ a k ^ 2 :=
          (Finset.sum_image (f := fun k => midBandPacketMode R₂ a k ^ 2) (g := fun x => x + h)
            fun x _ y _ hxy => by dsimp only at hxy; omega).symm
        rw [himg]
        refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
        rcases mem_image.mp hk with ⟨n, hn, rfl⟩
        simp only [mem_Ioc, mem_Icc] at *; omega
      have hpt : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| ≤
            (midBandPacketMode R₂ a n ^ 2 + midBandPacketMode R₂ a (n + h) ^ 2) / 2 :=
        fun n _ => by
          rw [abs_mul]
          nlinarith only [sq_nonneg (|midBandPacketMode R₂ a n| - |midBandPacketMode R₂ a (n + h)|),
            sq_abs (midBandPacketMode R₂ a n), sq_abs (midBandPacketMode R₂ a (n + h))]
      calc
        (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)|) ≤
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              (midBandPacketMode R₂ a n ^ 2 + midBandPacketMode R₂ a (n + h) ^ 2) / 2 :=
          sum_le_sum hpt
        _ = ((∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandPacketMode R₂ a n ^ 2) +
              (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandPacketMode R₂ a (n + h) ^ 2)) / 2 := by
          rw [← sum_div, sum_add_distrib]
        _ ≤ ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by linarith only [h1, h2]
        _ ≤ (N : ℝ) * Real.log N *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := hf_sq_sum
    have hN_sq : c ^ 4 / (N : ℝ) ^ 2 * (N : ℝ) = c ^ 4 / N := by
      rw [sq, ← div_div, div_mul_cancel₀ _ hN0.ne']
    calc
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h), _| ≤
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| *
              ((2 * Real.exp 2 + 1) *
                (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                  (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
                c ^ 4 / (N : ℝ) ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hker_n n hn) (abs_nonneg _)
      _ = ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| := by
        rw [← sum_mul, mul_comm]
      _ ≤ ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2) *
          ((N : ℝ) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hf_prod_sum (by positivity)
      _ = (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 / (N : ℝ) ^ 2 * (N : ℝ)) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
      _ = (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 / N) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by rw [hN_sq]
      _ = ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          (((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          (((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le (by positivity)
    _ = (2 * Real.exp 2) * (2 * Real.exp 2 + 1) *
          (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
          (c ^ 5 * Real.log N / N) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private theorem midBandLinearizedSum_eq_mean_add_osc (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ)
    (a : ℕ → ℝ) :
    midBandLinearizedSum φ R₂ N c a =
      midBandMeanSum φ R₂ N c a + midBandOscSum φ R₂ N c a := by
  unfold midBandLinearizedSum midBandMeanSum midBandOscSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun h _ => ?_
  have hexp : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
          midBandLinearizedWeight φ c N h n =
        ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          (a m * a l *
            (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
              midBandLinearizedWeight φ c N h n +
            a m * a l * (midBandLinearizedWeight φ c N h n * midBandOscMode m l h n)) := by
    intro n _
    unfold midBandPacketMode
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun l _ => ?_
    unfold midBandOscMode
    ring
  rw [sum_congr rfl hexp, sum_comm]
  have hcomm2 :
      (∑ m ∈ Icc 1 R₂, ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          ∑ l ∈ Icc 1 R₂,
            (a m * a l *
              (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
                midBandLinearizedWeight φ c N h n +
              a m * a l * (midBandLinearizedWeight φ c N h n * midBandOscMode m l h n))) =
        (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l * (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n) +
        (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n * midBandOscMode m l h n) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hcomm2]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  have hdiag : ∀ l ∈ Icc 1 R₂,
      a m * a l * (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandLinearizedWeight φ c N h n) =
        if l = m then
          a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n
        else 0 := by
    intro l _
    by_cases hlm : l = m
    · subst l; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg (Ne.symm hlm), if_neg hlm, mul_zero, zero_mul]
  rw [sum_congr rfl hdiag, sum_ite_eq', if_pos hm]

private theorem exists_midBand_mean_sum_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_3 : ℝ, 0 ≤ C_3 ∧
      ∀ {Q₁ R₂ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        |midBandMeanSum φ R₂ N c a| ≤
          C_3 * (c ^ 4 / Real.sqrt Q₁) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨8 * (2 * Real.exp 2) ^ 3 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2),
    by positivity, ?_⟩
  intro Q₁ R₂ N c hQ₁ hQR hR₂N hlog hc1 hradN a ha0
  have hR₂ : 2 ≤ R₂ := hQ₁.trans hQR
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hQ₁0 : (0 : ℝ) < Q₁ := Nat.cast_pos.mpr (by omega)
  have hsQ1 : 0 < Real.sqrt Q₁ := Real.sqrt_pos.mpr hQ₁0
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have ha_riesz :
      (∑ m ∈ Icc 1 R₂, a m ^ 2) ≤
        4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR₂ hR₂N hlog a).1
    nlinarith only [hr, sq_nonneg ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖]
  have hw_sum : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          midBandLinearizedWeight φ c N h n| ≤
        (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) * c := by
    intro h _
    have hcard :
        (((Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h)).card : ℕ) : ℝ) ≤ N := by
      rw [Nat.card_Ioc]; exact Nat.cast_le.mpr (by omega)
    calc
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          midBandLinearizedWeight φ c N h n| ≤
          ∑ _n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            ((2 * Real.exp 2 + 1) * c / N) * (∫ t, φ t ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
        have hnK0 := (mem_Ioc.mp hn).1
        have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
        unfold midBandLinearizedWeight
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
        exact mul_le_mul (midBand_inv_le_of_floor_lt hc1 hN0 hnK0)
          (hG_le _) (abs_nonneg _) (by positivity)
      _ = ((Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h)).card : ℝ) *
            (((2 * Real.exp 2 + 1) * c / N) * (∫ t, φ t ^ 2)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (((2 * Real.exp 2 + 1) * c / N) * (∫ t, φ t ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ((N : ℝ) * ((N : ℝ)⁻¹)) * ((2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) * c) := by
        rw [div_eq_mul_inv]; ring
      _ = (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) * c := by
        rw [mul_inv_cancel₀ hN0.ne', one_mul]
  have hm_term : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∀ m ∈ Icc 1 R₂,
      |a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandLinearizedWeight φ c N h n| ≤
        a m ^ 2 *
          (2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
            (c ^ 3 / Real.sqrt Q₁)) := by
    intro h hh m hm
    obtain ⟨hh1, hhB⟩ := mem_Icc.mp hh
    obtain ⟨hm1, _⟩ := mem_Icc.mp hm
    rcases le_or_gt m Q₁ with hmQ | hmQ
    · rw [ha0 m (mem_Icc.mpr ⟨hm1, hmQ⟩), sq, zero_mul, zero_mul, zero_mul, abs_zero, zero_mul]
    · have hφ0 : (0 : ℝ) < m.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm1)
      have htot_inv : 1 / (m.totient : ℝ) ≤ 2 / Real.sqrt Q₁ := by
        have hnat : Q₁ ≤ 4 * m.totient ^ 2 := by
          have h2 := nat_le_two_mul_totient_sq m
          omega
        have hcast : (Q₁ : ℝ) ≤ (2 * (m.totient : ℝ)) ^ 2 := by
          have hc' : (Q₁ : ℝ) ≤ ((4 * m.totient ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hnat
          push_cast at hc'
          linarith only [hc', (by ring : (2 * (m.totient : ℝ)) ^ 2 = 4 * (m.totient : ℝ) ^ 2)]
        have hsqrt : Real.sqrt Q₁ ≤ 2 * (m.totient : ℝ) := by
          calc
            Real.sqrt Q₁ ≤ Real.sqrt ((2 * (m.totient : ℝ)) ^ 2) := Real.sqrt_le_sqrt hcast
            _ = 2 * (m.totient : ℝ) := Real.sqrt_sq (by positivity)
        rw [div_le_div_iff₀ hφ0 hsQ1]
        linarith only [hsqrt]
      have hlag_le : |ramanujanLagCoefficient m h| ≤ (2 * Real.exp 2) ^ 2 * c ^ 2 := by
        have h1 := abs_ramanujanLagCoefficient_le_lag_sq m hh1
        have hh_le : (h : ℝ) ≤ (2 * Real.exp 2) * c := (Nat.cast_le.mpr hhB).trans hB_le
        have hp := pow_le_pow_left₀ (Nat.cast_nonneg h) hh_le 2
        rw [mul_pow] at hp
        exact h1.trans hp
      have hdiv_le : |ramanujanLagCoefficient m h / (m.totient : ℝ)| ≤
          2 * (2 * Real.exp 2) ^ 2 * c ^ 2 / Real.sqrt Q₁ := by
        rw [abs_div, abs_of_pos hφ0, div_eq_mul_one_div]
        calc
          |ramanujanLagCoefficient m h| * (1 / (m.totient : ℝ)) ≤
              ((2 * Real.exp 2) ^ 2 * c ^ 2) * (2 / Real.sqrt Q₁) :=
            mul_le_mul hlag_le htot_inv (by positivity) (by positivity)
          _ = 2 * (2 * Real.exp 2) ^ 2 * c ^ 2 / Real.sqrt Q₁ := by ring
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      calc
        |ramanujanLagCoefficient m h / (m.totient : ℝ)| *
            |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n| ≤
            (2 * (2 * Real.exp 2) ^ 2 * c ^ 2 / Real.sqrt Q₁) *
              ((2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) * c) :=
          mul_le_mul hdiv_le (hw_sum h hh) (abs_nonneg _) (by positivity)
        _ = 2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
              (c ^ 3 / Real.sqrt Q₁) := by ring
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ m ∈ Icc 1 R₂, a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandLinearizedWeight φ c N h n| ≤
        (8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
          (c ^ 3 / Real.sqrt Q₁)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    have hK_pos :
        0 ≤ 2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
          (c ^ 3 / Real.sqrt Q₁) := by
      have hc0 : 0 ≤ c := zero_le_one.trans hc1
      positivity
    calc
      |∑ m ∈ Icc 1 R₂, _| ≤
          ∑ m ∈ Icc 1 R₂, a m ^ 2 *
            (2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
              (c ^ 3 / Real.sqrt Q₁)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum (hm_term h hh))
      _ = (∑ m ∈ Icc 1 R₂, a m ^ 2) *
            (2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
              (c ^ 3 / Real.sqrt Q₁)) := by rw [← sum_mul]
      _ ≤ (4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) *
            (2 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
              (c ^ 3 / Real.sqrt Q₁)) :=
        mul_le_mul_of_nonneg_right ha_riesz hK_pos
      _ = (8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
            (c ^ 3 / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  unfold midBandMeanSum
  have hRHS_pos :
      0 ≤ (8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
        (c ^ 3 / Real.sqrt Q₁)) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc1
    positivity
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
            (c ^ 3 / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          ((8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
            (c ^ 3 / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          ((8 * (2 * Real.exp 2) ^ 2 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
            (c ^ 3 / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le hRHS_pos
    _ = 8 * (2 * Real.exp 2) ^ 3 * (2 * Real.exp 2 + 1) * (∫ t, φ t ^ 2) *
          (c ^ 4 / Real.sqrt Q₁) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private theorem exists_midBand_osc_sum_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_4 : ℝ, 0 ≤ C_4 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        2 ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ a : ℕ → ℝ,
        |midBandOscSum φ R₂ N c a| ≤
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨K_lip, hG_lip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨16 * (2 * Real.exp 2) *
      ((2 * Real.exp 2 + 1) *
        (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))),
    by positivity, ?_⟩
  intro R₂ N c hR₂ hR₂N hlog hc1 hradN a
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have ha_riesz :
      (∑ m ∈ Icc 1 R₂, a m ^ 2) ≤
        4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR₂ hR₂N hlog a).1
    nlinarith only [hr, sq_nonneg ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖]
  have ha_l1_sq :
      (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) ≤
        4 * (R₂ : ℝ) * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have heq : (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) =
        (∑ m ∈ Icc 1 R₂, 1 * |a m|) ^ 2 := by
      simp only [one_mul]
      rw [sq, sum_mul]
      exact sum_congr rfl fun m _ => by rw [mul_sum]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R₂) (fun _ => (1 : ℝ)) (fun m => |a m|)
    have hcard : (∑ _m ∈ Icc 1 R₂, (1 : ℝ) ^ 2) = R₂ := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, one_pow, mul_one]
    rw [heq]
    calc
      (∑ m ∈ Icc 1 R₂, 1 * |a m|) ^ 2 ≤
          (∑ _m ∈ Icc 1 R₂, (1 : ℝ) ^ 2) * ∑ m ∈ Icc 1 R₂, |a m| ^ 2 := hcs
      _ = (R₂ : ℝ) * ∑ m ∈ Icc 1 R₂, a m ^ 2 := by
        rw [hcard]; congr 1; exact sum_congr rfl fun m _ => sq_abs (a m)
      _ ≤ (R₂ : ℝ) * (4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ha_riesz (Nat.cast_nonneg R₂)
      _ = 4 * (R₂ : ℝ) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  have hosc_inner : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∀ m ∈ Icc 1 R₂, ∀ l ∈ Icc 1 R₂,
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          midBandLinearizedWeight φ c N h n * midBandOscMode m l h n| ≤
        4 * (R₂ : ℝ) ^ 3 *
          (((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              c ^ 2 / N) := by
    intro h hh m hm l hl
    rcases le_or_gt (N - h) ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ with hle | hgt
    · rw [Ioc_eq_empty_of_le hle, sum_empty, abs_zero]
      positivity
    · have hab := abs_sum_Ioc_mul_le_total_variation hgt.le
        (midBandLinearizedWeight φ c N h) (midBandOscMode m l h)
        (shifted_mode_osc_Ico_le hR₂ hm hl h)
      have htv := linearized_weight_tv_le hG_lip hM.le hG_le hc1 hN1 hh hgt
      exact hab.trans (mul_le_mul_of_nonneg_left htv (by positivity))
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n * midBandOscMode m l h n| ≤
        (16 * ((2 * Real.exp 2 + 1) *
          (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
            (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    calc
      |∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, _| ≤
          ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
            |a m| * |a l| *
              (4 * (R₂ : ℝ) ^ 3 *
                (((2 * Real.exp 2 + 1) *
                  (2 * (∫ t, φ t ^ 2) +
                    (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
                  c ^ 2 / N)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hosc_inner h hh m hm l hl) (by positivity)
      _ = (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) *
            (4 * (R₂ : ℝ) ^ 3 *
              (((2 * Real.exp 2 + 1) *
                (2 * (∫ t, φ t ^ 2) +
                  (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
                c ^ 2 / N)) := by
        rw [sum_mul]; exact sum_congr rfl fun m _ => (sum_mul _ _ _).symm
      _ ≤ (4 * (R₂ : ℝ) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) *
          (4 * (R₂ : ℝ) ^ 3 *
            (((2 * Real.exp 2 + 1) *
              (2 * (∫ t, φ t ^ 2) +
                (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              c ^ 2 / N)) :=
        mul_le_mul_of_nonneg_right ha_l1_sq (by positivity)
      _ = (16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  unfold midBandOscSum
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          ((16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          ((16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le (by positivity)
    _ = 16 * (2 * Real.exp 2) *
          ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
          (c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

/-- Quadratic-form bound on `overlapMatrix φ c N` for intermediate-band packets
`u = ∑_{m=1}^{R₂} a_m v_m` vanishing on `1 ≤ m ≤ Q₁`. -/
theorem exists_overlapMatrix_midBand_inner_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_mid : ℝ, 0 < C_mid ∧
      ∀ {Q₁ R₂ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        let u := ∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N +
            c ^ 4 / Real.sqrt Q₁ +
            c ^ 3 * (R₂ : ℝ) ^ 4 / N) * ‖u‖ ^ 2 := by
  obtain ⟨C_1, hC1_pos, hsub_le⟩ := exists_midBand_subKernel_sum_le hφ hsupp hM
  obtain ⟨C_2, hC2_nonneg, herr_le⟩ := exists_midBand_lag_sub_linearized_le hφ hsupp hM
  obtain ⟨C_3, hC3_nonneg, hmean_le⟩ := exists_midBand_mean_sum_le hφ hsupp hM
  obtain ⟨C_4, hC4_nonneg, hosc_le⟩ := exists_midBand_osc_sum_le hφ hsupp hM
  refine ⟨C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
      (2 / ∫ t, φ t ^ 2) * C_4 + 1, by positivity, ?_⟩
  intro Q₁ R₂ N c hQ₁ hQR hR₂N hlog hc1 _hcL hw1 hradN hRNT a ha0
  dsimp only
  have hR₂ : 2 ≤ R₂ := hQ₁.trans hQR
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R₂; linarith only [hlog, this]
  have hu_mem :
      (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) ∈ conductorSubspace R₂ N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R₂ N a
  have hinner_split :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
          (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N⟫ =
        (∑ n ∈ Icc 1 N,
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
              ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) +
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            (∑ n ∈ Icc 1 N,
              primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
                ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                  primeHorizonExtension
                    (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) := by
    rw [overlapMatrix_inner_eq φ c N, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hrow :
        (∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
          (∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j *
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) +
            (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
              ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by unfold midBandSubKernel midBandLeadKernel; ring
    rw [hrow]; ring
  have hI_sub := hsub_le hR₂ hlog hc1 hw1 hradN hRNT hu_mem
  have hlead_eq := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw hradN a
  have hS_err := herr_le (R₂ := R₂) hL0 hc1 hradN a
  have hS_mean := hmean_le hQ₁ hQR hR₂N hlog hc1 hradN ha0
  have hS_osc := hosc_le (R₂ := R₂) hR₂ hR₂N hlog hc1 hradN a
  have hS_lag_le :
      |midBandLagSum φ R₂ N c a| ≤
        (C_2 * (c ^ 5 * Real.log N / N) +
          C_3 * (c ^ 4 / Real.sqrt Q₁) +
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hid : midBandLagSum φ R₂ N c a =
        (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a) +
          midBandMeanSum φ R₂ N c a + midBandOscSum φ R₂ N c a := by
      linarith only [midBandLinearizedSum_eq_mean_add_osc φ R₂ N c a]
    rw [hid]
    exact (abs_add_three _ _ _).trans ((add_le_add (add_le_add hS_err hS_mean) hS_osc).trans_eq
      (by ring))
  have hL_scale_le :
      |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹| ≤ 1 / ∫ t, φ t ^ 2 := by
    have hlog_inv : |Real.log (1 / (c / N))| ≤ Real.log N := by
      have heq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 (by linarith only [hcN2, hc0])))]
      linarith [Real.log_nonneg hc1]
    have hdiv1 : |Real.log (1 / (c / N))| * (Real.log N)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact div_le_one_of_le₀ hlog_inv hL0.le
    rw [abs_mul, abs_div, abs_of_pos hM, abs_inv, abs_of_pos hL0]
    calc
      (|Real.log (1 / (c / N))| / ∫ t, φ t ^ 2) * (Real.log N)⁻¹ =
          (|Real.log (1 / (c / N))| * (Real.log N)⁻¹) / ∫ t, φ t ^ 2 := by ring
      _ ≤ 1 / ∫ t, φ t ^ 2 := div_le_div_of_nonneg_right hdiv1 hM.le
  have hI_lead :
      |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
          (∑ n ∈ Icc 1 N,
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
              ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j)| ≤
        (2 / ∫ t, φ t ^ 2) *
          (C_2 * (c ^ 5 * Real.log N / N) +
            C_3 * (c ^ 4 / Real.sqrt Q₁) +
            C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    rw [hlead_eq,
      show (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * ((Real.log N)⁻¹ * (2 * midBandLagSum φ R₂ N c a)) =
        2 * ((Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹) *
          midBandLagSum φ R₂ N c a by ring,
      abs_mul, abs_mul, abs_of_pos zero_lt_two]
    calc
      2 * |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹| *
          |midBandLagSum φ R₂ N c a| ≤
        2 * (1 / ∫ t, φ t ^ 2) *
          ((C_2 * (c ^ 5 * Real.log N / N) +
            C_3 * (c ^ 4 / Real.sqrt Q₁) +
            C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL_scale_le zero_le_two)
          hS_lag_le (abs_nonneg _) (by positivity)
      _ = (2 / ∫ t, φ t ^ 2) *
            (C_2 * (c ^ 5 * Real.log N / N) +
              C_3 * (c ^ 4 / Real.sqrt Q₁) +
              C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  have h2M_nonneg : 0 ≤ 2 / ∫ t, φ t ^ 2 := by positivity
  have h2C2 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_2 := mul_nonneg h2M_nonneg hC2_nonneg
  have h2C3 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_3 := mul_nonneg h2M_nonneg hC3_nonneg
  have h2C4 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_4 := mul_nonneg h2M_nonneg hC4_nonneg
  have hT1 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by
    have := Real.log_nonneg hc1; positivity
  have hT2 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
  have hT3 : 0 ≤ c ^ 4 / Real.sqrt Q₁ := by positivity
  have hT4 : 0 ≤ c ^ 3 * (R₂ : ℝ) ^ 4 / N := by positivity
  rw [hinner_split]
  refine (abs_add_le _ _).trans ((add_le_add hI_sub hI_lead).trans ?_)
  calc
    C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
      (2 / ∫ t, φ t ^ 2) *
        (C_2 * (c ^ 5 * Real.log N / N) +
          C_3 * (c ^ 4 / Real.sqrt Q₁) +
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      (C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) +
        ((2 / ∫ t, φ t ^ 2) * C_2) * (c ^ 5 * Real.log N / N) +
        ((2 / ∫ t, φ t ^ 2) * C_3) * (c ^ 4 / Real.sqrt Q₁) +
        ((2 / ∫ t, φ t ^ 2) * C_4) * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
    _ ≤ ((C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
          (2 / ∫ t, φ t ^ 2) * C_4 + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N +
          c ^ 5 * Real.log N / N +
          c ^ 4 / Real.sqrt Q₁ +
          c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith only [hC1_pos, h2C2, h2C3, h2C4, hT1, hT2, hT3, hT4]
    _ = (C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
          (2 / ∫ t, φ t ^ 2) * C_4 + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N +
          c ^ 5 * Real.log N / N +
          c ^ 4 / Real.sqrt Q₁ +
          c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

end GaloisForLFunctions.CompletedArithmeticForms

end

#print axioms GaloisForLFunctions.CompletedArithmeticForms.fullWeilNonRatioMatrix_eq_downward_add_upward
#print axioms GaloisForLFunctions.CompletedArithmeticForms.upwardPrimeVector_self_inner_eq_downward
#print axioms GaloisForLFunctions.CompletedArithmeticForms.overlap_sub_nonRatio_inner_eq
#print axioms GaloisForLFunctions.CompletedArithmeticForms.completedConductorEnergy_le_of_one_le
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_overlapMatrix_inner_le_of_mem_conductorSubspace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_overlapMatrix_midBand_inner_le
