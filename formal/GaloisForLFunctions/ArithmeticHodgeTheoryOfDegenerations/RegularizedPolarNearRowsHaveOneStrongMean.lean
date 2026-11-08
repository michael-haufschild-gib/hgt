import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarGammaMeansHaveOneLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalStripsVanishAtCriticalScale
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarRowsHaveSummableTerminalTails

/-!
# Regularized near polar rows converge in square mean

Retaining the logarithmic Gram defect exposes a smooth near row and a harmonic
collar. Interior quadrature converges; the terminal strip has vanishing mass
even under the global logarithmic envelope.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- The near polar row with its exact logarithmic Gram defect retained. -/
def regularizedPolarNearRow (c : ℝ) (N n : ℕ) : ℝ :=
  (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
    (completeWeilPoleShift tiltedUnitSpline c / N) *
      ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n) +
    (Real.log c + Real.log ((n : ℝ) / N)) *
      (poleRowDefect tiltedUnitSpline c N n / Real.sqrt n + atomPoleErrorCoefficient tiltedUnitSpline c N)) /
        (c / N)

/-- Dividing the joint near-row quadrature error by the atomic width gives its scalar error. -/
lemma exists_regularizedPolarNearRow_interior_bound :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c →
      n ∈ Icc 1 N → 2 * c / N ≤ 1 / 8 → 8 ≤ (n : ℝ) * (2 * c / N) →
      (n : ℝ) * Real.exp (2 * c / N) ≤ N →
      |regularizedPolarNearRow c N n - polarNearJointMean (c / N)| ≤
        C * ((N : ℝ) / n) / c + D * (c / N) := by
  obtain ⟨C, D, hC, hD, hb⟩ := exists_joint_near_polar_scalar_mean_bound
  refine ⟨C, D, hC, hD, ?_⟩
  intro c N n hc hn hw hwide hint
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hw0 : 0 < c / N := div_pos hc hN0
  have hh := div_le_div_of_nonneg_right (hb hc hn hw hwide hint) hw0.le
  have hid (a b : ℝ) : |a - (c / N) * b| / (c / N) = |a / (c / N) - b| := by
    rw [← abs_of_pos hw0, ← abs_div]
    congr 1
    field_simp [hw0.ne']
  rw [hid] at hh
  exact hh.trans_eq (by field_simp [hc.ne', hN0.ne', hn0.ne']; ring)

/-- The regularized row differs from its harmonic collar by a uniformly bounded smooth row. -/
lemma exists_regularizedPolarNearRow_sub_center_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c → c / N ≤ 1 / 4 →
      n ∈ Icc 1 N →
      |regularizedPolarNearRow c N n -
        ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
            Real.log c - Real.log ((n : ℝ) / N))| ≤ B := by
  obtain ⟨A, L, hA, hL, hbound, _⟩ := polarNearKernel_bounds
  refine ⟨4 * Real.exp 3 * A + 20 * Real.exp 3, by positivity, ?_⟩
  intro c N n hc hw hn
  have hn1 := (mem_Icc.mp hn).1
  have hN1 := hn1.trans (mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hw0 : 0 < c / N := div_pos hc hN0
  let S : ℝ := ∑ j ∈ nearRowIndices c N n,
    (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
      (∫ u, tiltedUnitSpline u ^ 2)) / (Real.sqrt n * Real.sqrt j)
  have hS : |S| ≤ 4 * Real.exp 3 * A * (c / N) := by
    have hset : nearRowIndices c N n = logarithmicBallIndices (2 * (c / N)) N n := by
      simp only [nearRowIndices, logarithmicBallIndices, mul_div_assoc]
    have hm := sum_logarithmic_ball_reciprocal_sqrt_le (mul_pos (by norm_num) hw0)
      (by linarith only [hw] : 2 * (c / N) ≤ 2) hn
    rw [← hset] at hm
    have hp : ∀ j ∈ nearRowIndices c N n,
        |(nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
          (∫ u, tiltedUnitSpline u ^ 2)) / (Real.sqrt n * Real.sqrt j)| ≤
        A * (1 / (Real.sqrt n * Real.sqrt j)) := by
      intro j hj
      have hgap : |Real.log j - Real.log n| / (c / N) ≤ 2 :=
        (div_le_iff₀ hw0).mpr (by simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2)
      have ht0 : 0 ≤ |Real.log j - Real.log n| / (c / N) := by positivity
      have ht : |Real.log j - Real.log n| / (c / N) ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith only [ht0], hgap⟩
      have hb := hbound _ ht
      rw [abs_of_nonneg ht0] at hb
      rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt j)]
      exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by ring)
    calc
      |S| ≤ ∑ j ∈ nearRowIndices c N n, A * (1 / (Real.sqrt n * Real.sqrt j)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hp)
      _ = A * ∑ j ∈ nearRowIndices c N n, 1 / (Real.sqrt n * Real.sqrt j) := (mul_sum _ _ _).symm
      _ ≤ A * (2 * Real.exp 3 * (2 * (c / N))) := mul_le_mul_of_nonneg_left hm hA
      _ = _ := by ring
  have hgam := div_le_div_of_nonneg_right
    (abs_nearGammaDownwardRow_one_sub_smooth_le hc hN1 (hw.trans (by norm_num)) hn) hsn.le
  have hsum : (∑ j ∈ nearRowIndices c N n,
      (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
        (∫ u, tiltedUnitSpline u ^ 2)) / Real.sqrt j) / Real.sqrt n = S := by
    rw [sum_div]
    exact sum_congr rfl fun j _ => by ring
  have hgam' : |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
      (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S| ≤
        20 * Real.exp 3 * (c / N) ^ 2 := by
    have heq : |nearGammaDownwardRow tiltedUnitSpline c N 1 n -
        ((∑ j ∈ nearRowIndices c N n,
          (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
            (∫ u, tiltedUnitSpline u ^ 2)) / Real.sqrt j) -
          (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n)| / Real.sqrt n =
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S| := by
      rw [← abs_of_pos hsn, ← abs_div]
      congr 1
      rw [sub_div, sub_div, hsum]
      ring
    rw [heq] at hgam
    exact hgam.trans_eq (by field_simp [hsn.ne', hN0.ne']; ring)
  have hP : nearPoleRow tiltedUnitSpline c N n = poleRowDefect tiltedUnitSpline c N n +
      (atomPoleErrorCoefficient tiltedUnitSpline c N + completeWeilPoleShift tiltedUnitSpline c / N) *
        Real.sqrt n := by
    unfold poleRowDefect
    rw [exactPoleCoefficient_eq]
    ring
  have hid : regularizedPolarNearRow c N n -
      ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
        ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
          Real.log c - Real.log ((n : ℝ) / N)) =
      (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n) /
          (c / N) := by
    rw [hP]
    unfold regularizedPolarNearRow completeWeilPoleShift
    field_simp [hc.ne', hN0.ne', hsn.ne']
    ring
  rw [hid, abs_div, abs_of_pos hw0]
  have htriangle : |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
      (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n| ≤
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S| + |S| := by
    simpa only [sub_add_cancel] using abs_add_le
      (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S) S
  have htri := htriangle.trans (add_le_add hgam' hS)
  have hb := div_le_div_of_nonneg_right htri hw0.le
  have he : (20 * Real.exp 3 * (c / N) ^ 2 + 4 * Real.exp 3 * A * (c / N)) / (c / N) =
      20 * Real.exp 3 * (c / N) + 4 * Real.exp 3 * A := by field_simp [hc.ne', hN0.ne']; ring
  rw [he] at hb
  have hw1 : c / N ≤ 1 := hw.trans (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ 20 * Real.exp 3)
  linarith only [hb, hh]

/-- A logarithmic harmonic envelope controls the regularized row even at the terminal boundary. -/
lemma exists_regularizedPolarNearRow_global_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {c : ℝ} {N n : ℕ}, 1 ≤ c → 8 * c ≤ N →
      n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N →
      |regularizedPolarNearRow c N n - polarNearJointMean (c / N)| ≤ K * c := by
  obtain ⟨B, hB, hb⟩ := exists_regularizedPolarNearRow_sub_center_bound
  obtain ⟨C, hC, hcmean⟩ := exists_abs_polarNearJointMean_sub_zero_le
  let a : ℝ := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  let Cu : ℝ := 4 + 2 * Real.exp 2
  let K : ℝ := B + a * (Cu + |Real.log δ|) + |polarNearJointMean 0| + C
  have ha : 0 ≤ a := div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le
  have hCu : 0 ≤ Cu := by dsimp only [Cu]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro c N n hc1 h8c hn
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hnN := (mem_Ioc.mp hn).2
  have hni : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, hnN⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn1.trans hnN
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw : c / N ≤ 1 / 4 := (div_le_iff₀ hN0).mpr (by linarith only [h8c])
  have hx0 : 0 < (n : ℝ) / N := div_pos hn0 hN0
  have hx1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hnN)
  have hδx : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr
    (le_of_lt ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1))
  have hlogx : |Real.log ((n : ℝ) / N)| ≤ |Real.log δ| := by
    rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1)]
    have hh := Real.log_le_log hδ hδx
    linarith only [hh, neg_abs_le (Real.log δ)]
  have hlogc : 1 + Real.log c ≤ c := by
    linarith only [Real.log_le_sub_one_of_pos hc0]
  let H : ℝ := (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n
  have hcenter : |H - Real.log c| ≤ Cu * c := by
    have hh := div_le_div_of_nonneg_right (abs_polarCenterCollar_sub_log_le hc1 h8c hni) hsn.le
    have he : |(∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
        Real.log c * Real.sqrt n| / Real.sqrt n = |H - Real.log c| := by
      rw [← abs_of_pos hsn, ← abs_div]
      congr 1
      dsimp only [H]
      field_simp [hsn.ne']
    rw [he] at hh
    have heR : (4 + 2 * Real.exp 2) * (1 + Real.log c) * Real.sqrt n / Real.sqrt n =
        Cu * (1 + Real.log c) := by dsimp only [Cu]; field_simp [hsn.ne']
    rw [heR] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlogc hCu)
  have hcenterx : |a * (H - Real.log c - Real.log ((n : ℝ) / N))| ≤
      a * (Cu * c + |Real.log δ|) := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (add_le_add hcenter hlogx)) ha
  have hmean : |polarNearJointMean (c / N)| ≤ |polarNearJointMean 0| + C := by
    have hh := hcmean (by rw [abs_of_pos hw0]; exact hw)
    rw [abs_of_pos hw0] at hh
    have htri : |polarNearJointMean (c / N)| ≤
        |polarNearJointMean (c / N) - polarNearJointMean 0| + |polarNearJointMean 0| := by
      simpa only [sub_add_cancel] using abs_add_le
        (polarNearJointMean (c / N) - polarNearJointMean 0) (polarNearJointMean 0)
    have hcw := mul_le_mul_of_nonneg_left (hw.trans (by norm_num : (1 : ℝ) / 4 ≤ 1)) hC
    linarith only [hh, htri, hcw]
  have hrow := hb hc0 hw hni
  have hsum : |regularizedPolarNearRow c N n| ≤ B + a * (Cu * c + |Real.log δ|) := by
    have hh : |regularizedPolarNearRow c N n| ≤
        |regularizedPolarNearRow c N n - a * (H - Real.log c - Real.log ((n : ℝ) / N))| +
          |a * (H - Real.log c - Real.log ((n : ℝ) / N))| := by
      simpa only [sub_add_cancel] using abs_add_le
        (regularizedPolarNearRow c N n - a * (H - Real.log c - Real.log ((n : ℝ) / N)))
        (a * (H - Real.log c - Real.log ((n : ℝ) / N)))
    exact hh.trans (add_le_add hrow hcenterx)
  have hh := (abs_sub _ _).trans (add_le_add hsum hmean)
  have hBscale := mul_le_mul_of_nonneg_left hc1 hB
  have hδscale := mul_le_mul_of_nonneg_left hc1 (mul_nonneg ha (abs_nonneg (Real.log δ)))
  have hMscale := mul_le_mul_of_nonneg_left hc1 (abs_nonneg (polarNearJointMean 0))
  have hCscale := mul_le_mul_of_nonneg_left hc1 hC
  dsimp only [K]
  nlinarith only [hh, hBscale, hδscale, hMscale, hCscale]

/-- The regularized near row has a single strong scalar mean on every fixed terminal fraction. -/
theorem tendsto_regularizedPolarNearRow_square_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (regularizedPolarNearRow (c N) N n - polarNearJointMean (c N / N)) ^ 2) / N)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := exists_regularizedPolarNearRow_global_bound hδ
  obtain ⟨C, D, hC, hD, hi⟩ := exists_regularizedPolarNearRow_interior_bound
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hevent : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ c N / N ≤ 1 / 16 ∧ 4 / δ ≤ c N := by
    filter_upwards [eventually_ge_atTop 1,
      hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
      hcinf.eventually_ge_atTop (4 / δ)] with N hN hw hwide
    exact ⟨hN, hw.le, hwide⟩
  apply tendsto_normalized_square_mean_of_terminal_strip hc hR hcrit
    (T := 2) (C := C / δ) (D := D) (K := K) (by norm_num)
  · filter_upwards [hevent] with N hN n hn
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.1
    have hw := (div_le_iff₀ hN0).mp hN.2.1
    exact hb (hc N) (by linarith only [hw]) hn
  · filter_upwards [hevent] with N hN n hn hint
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.1
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hnδ : δ * (N : ℝ) ≤ n := le_of_lt
      ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1)
    have hwide : 8 ≤ (n : ℝ) * (2 * c N / N) := by
      have hh := mul_le_mul_of_nonneg_right hnδ (by positivity : 0 ≤ 2 * c N / N)
      have hδc := (div_le_iff₀ hδ).mp hN.2.2
      have he : δ * (N : ℝ) * (2 * c N / N) = 2 * (c N * δ) := by field_simp [hN0.ne']; ring
      rw [he] at hh
      linarith only [hh, hδc]
    have hh := hi hc0 (mem_Icc.mpr ⟨hn1, (mem_Ioc.mp hn).2⟩)
      (by rw [mul_div_assoc]; linarith only [hN.2.1]) hwide
      (by simpa only [mul_div_assoc] using hint)
    have hratio : (N : ℝ) / n ≤ 1 / δ := by
      apply (div_le_div_iff₀ hn0 hδ).mpr
      simpa only [one_mul, mul_comm] using hnδ
    have hpay := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) hc0.le
    exact hh.trans (add_le_add (hpay.trans_eq (by ring)) le_rfl)

/-- The logarithmic polar Gram correction vanishes in sampled square mean. -/
theorem tendsto_polar_near_gram_correction_square_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      ((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        poleRowDefect tiltedUnitSpline (c N) N n / (Real.sqrt n * (c N / N))) ^ 2) / N)
      atTop (𝓝 0) := by
  let K := (1 + |Real.log δ|) ^ 2 / δ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlim := (tendsto_log_scaled_poleRowDefect_sq hc hR hcrit).const_mul K
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  have hclog := Real.tendsto_log_atTop.comp (criticalCurve_facts hc hR hcrit).1
  filter_upwards [eventually_ge_atTop 1, hclog.eventually_ge_atTop 1] with N hN hlogc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hpt : ∀ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      ((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        poleRowDefect tiltedUnitSpline (c N) N n / (Real.sqrt n * (c N / N))) ^ 2 / N ≤
      K * (Real.log (c N) / c N) ^ 2 * poleRowDefect tiltedUnitSpline (c N) N n ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN := (mem_Ioc.mp hn).2
    have hnδ : δ * (N : ℝ) ≤ n := le_of_lt
      ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1)
    have hxδ : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr hnδ
    have hx1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hnN)
    have hlogx : |Real.log ((n : ℝ) / N)| ≤ |Real.log δ| := by
      rw [abs_of_nonpos (Real.log_nonpos (by positivity) hx1)]
      have hh := Real.log_le_log hδ hxδ
      linarith only [hh, neg_abs_le (Real.log δ)]
    have hlog : |Real.log (c N) + Real.log ((n : ℝ) / N)| ≤
        (1 + |Real.log δ|) * Real.log (c N) := by
      have hh := (abs_add_le _ _).trans (add_le_add le_rfl hlogx)
      rw [abs_of_nonneg (Real.log_nonneg (hc N))] at hh
      have hprod := mul_le_mul_of_nonneg_left hlogc (abs_nonneg (Real.log δ))
      nlinarith only [hh, hprod]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hlog 2
    rw [sq_abs, mul_pow] at hs
    have hratio : (N : ℝ) / n ≤ 1 / δ := by
      apply (div_le_div_iff₀ hn0 hδ).mpr
      simpa only [one_mul, mul_comm] using hnδ
    have he : ((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        poleRowDefect tiltedUnitSpline (c N) N n / (Real.sqrt n * (c N / N))) ^ 2 / N =
      (Real.log (c N) + Real.log ((n : ℝ) / N)) ^ 2 * ((N : ℝ) / n) *
        (poleRowDefect tiltedUnitSpline (c N) N n ^ 2 / c N ^ 2) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hn0.le]
      field_simp [hN0.ne', hn0.ne', hc0.ne']
      ring
    rw [he]
    have hp := mul_le_mul hs hratio (div_nonneg hN0.le hn0.le) (by positivity)
    exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans_eq (by dsimp only [K]; ring)
  have hsub : Ioc ⌊δ * (N : ℝ)⌋₊ N ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  rw [sum_div]
  calc
    _ ≤ ∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        K * (Real.log (c N) / c N) ^ 2 * poleRowDefect tiltedUnitSpline (c N) N n ^ 2 :=
      sum_le_sum hpt
    _ ≤ ∑ n ∈ Icc 1 N,
        K * (Real.log (c N) / c N) ^ 2 * poleRowDefect tiltedUnitSpline (c N) N n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := by rw [← mul_sum]; ring

/-- The quadratic atom error remains negligible after multiplication by the near-row logarithm. -/
theorem tendsto_polar_near_atom_correction_square_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      ((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        atomPoleErrorCoefficient tiltedUnitSpline (c N) N / (c N / N)) ^ 2) / N)
      atTop (𝓝 0) := by
  let D := |atomPoleMomentErrorConstant tiltedUnitSpline|
  have hD : 0 ≤ D := abs_nonneg _
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hc2N : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
  have hboundlim : Tendsto (fun N : ℕ => D * (c N / N) * (c N + |Real.log δ|)) atTop (𝓝 0) := by
    have hh := (hc2N.add (hcN.const_mul |Real.log δ|)).const_mul D
    simp only [mul_zero, add_zero] at hh
    exact hh.congr fun N => by ring
  apply tendsto_normalized_square_mean_of_uniform_bound
    (fun N => by rw [Nat.card_Ioc]; exact Nat.sub_le _ _) hboundlim
  filter_upwards [eventually_ge_atTop 1,
    hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hw n hn
  have hc0 := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c N / N := div_pos hc0 hN0
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hxδ : δ ≤ (n : ℝ) / N := (le_div_iff₀ hN0).mpr
    (le_of_lt ((Nat.floor_lt (by positivity : 0 ≤ δ * (N : ℝ))).mp (mem_Ioc.mp hn).1))
  have hx1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Ioc.mp hn).2)
  have hlogx : |Real.log ((n : ℝ) / N)| ≤ |Real.log δ| := by
    rw [abs_of_nonpos (Real.log_nonpos (by positivity) hx1)]
    have hh := Real.log_le_log hδ hxδ
    linarith only [hh, neg_abs_le (Real.log δ)]
  have hlog : |Real.log (c N) + Real.log ((n : ℝ) / N)| ≤ c N + |Real.log δ| := by
    have hh := (abs_add_le _ _).trans (add_le_add le_rfl hlogx)
    rw [abs_of_nonneg (Real.log_nonneg (hc N))] at hh
    linarith only [hh, Real.log_le_sub_one_of_pos hc0]
  have hatom : |atomPoleErrorCoefficient tiltedUnitSpline (c N) N| ≤ D * (c N / N) ^ 2 :=
    (RenormalizedArithmeticPotentialTheory.abs_atomPoleErrorCoefficient_le_of_le
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hN ((div_le_one hN0).mp hw.le)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  rw [abs_div, abs_mul, abs_of_pos hw0]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul hlog hatom (abs_nonneg _) (by positivity)) hw0.le).trans_eq
      (by field_simp [hw0.ne']; ring)

/-- The actual joint near Gamma and harmonic center row, without its vanishing corrections. -/
def polarNearRow (c : ℝ) (N n : ℕ) : ℝ :=
  (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
    (completeWeilPoleShift tiltedUnitSpline c / N) *
      ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n)) /
        (c / N)

/-- Removing the Gram and atom corrections leaves the exact zero-width near scalar mean. -/
theorem tendsto_polarNearRow_square_mean
    {δ : ℝ} (hδ : 0 < δ) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarNearRow (c N) N n - polarNearJointMean 0) ^ 2) / N) atTop (𝓝 0) := by
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  obtain ⟨C, hC, hmean⟩ := exists_abs_polarNearJointMean_sub_zero_le
  have hm : Tendsto (fun N : ℕ => polarNearJointMean (c N / N) - polarNearJointMean 0)
      atTop (𝓝 0) := by
    have hlim := hcN.const_mul C
    rw [mul_zero] at hlim
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1,
      hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with N hN hw
    have hw0 : 0 < c N / N := div_pos (zero_lt_one.trans_le (hc N)) (by exact_mod_cast hN)
    simpa only [Real.norm_eq_abs, abs_of_pos hw0] using
      hmean (by rw [abs_of_pos hw0]; exact hw.le)
  have hm2 := tendsto_normalized_square_mean_const
    (S := fun N => Ioc ⌊δ * (N : ℝ)⌋₊ N)
    (fun N => by rw [Nat.card_Ioc]; exact Nat.sub_le _ _) hm
  have hG : Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (-((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        poleRowDefect tiltedUnitSpline (c N) N n / (Real.sqrt n * (c N / N)))) ^ 2) / N)
      atTop (𝓝 0) := by
    simpa only [neg_div, neg_mul, neg_sq] using tendsto_polar_near_gram_correction_square_mean hδ hc hR hcrit
  have hE : Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (-((Real.log (c N) + Real.log ((n : ℝ) / N)) *
        atomPoleErrorCoefficient tiltedUnitSpline (c N) N / (c N / N))) ^ 2) / N)
      atTop (𝓝 0) := by
    simpa only [neg_div, neg_mul, neg_sq] using tendsto_polar_near_atom_correction_square_mean hδ hc hR hcrit
  have hs := tendsto_normalized_square_mean_add
    (tendsto_normalized_square_mean_add
      (tendsto_normalized_square_mean_add (tendsto_regularizedPolarNearRow_square_mean hδ hc hR hcrit) hm2) hG) hE
  exact hs.congr fun N => by
    congr 1
    refine sum_congr rfl fun n _ => ?_
    congr 1
    unfold regularizedPolarNearRow polarNearRow
    ring

#print axioms tendsto_polar_near_atom_correction_square_mean
#print axioms tendsto_polarNearRow_square_mean

#print axioms tendsto_polar_near_gram_correction_square_mean

#print axioms exists_regularizedPolarNearRow_global_bound
#print axioms tendsto_regularizedPolarNearRow_square_mean

#print axioms exists_regularizedPolarNearRow_interior_bound
#print axioms exists_regularizedPolarNearRow_sub_center_bound
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
