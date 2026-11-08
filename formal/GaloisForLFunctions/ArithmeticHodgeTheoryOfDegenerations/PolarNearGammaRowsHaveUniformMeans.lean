import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarNearRowsReduceToHarmonicCollars
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarCenterCollarHasHarmonicCoordinates

/-!
# The polar near Gamma rows have one annular mean

Closed lattice quadrature accounts for both the omitted diagonal and a possible
endpoint lattice point. Away from the terminal boundary, the smooth near row
depends on its receiving index only through its square-root weight.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- Positive horizon indices in a symmetric logarithmic ball, excluding its center. -/
def logarithmicBallIndices (t : ℝ) (N n : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun j => j ≠ n ∧ |Real.log j - Real.log n| ≤ t)

/-- A symmetric logarithmic ball has a receiving-index-independent annular mean whenever
it lies below the terminal boundary. -/
theorem abs_logarithmic_ball_row_sub_mean_le {K : ℝ → ℝ} {A L T w : ℝ} {N n : ℕ}
    (hT : 0 < T) (hw0 : 0 < w) (hTw : T * w ≤ 1 / 2) (hL0 : 0 ≤ L)
    (hA : ∀ s ∈ Set.Icc (-T) T, |K s| ≤ A)
    (hL : ∀ s ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      |K s - K t| ≤ L * |s - t|)
    (hn : n ∈ Icc 1 N) (hinterior : (n : ℝ) * Real.exp (T * w) ≤ N) :
    |(∑ j ∈ logarithmicBallIndices (T * w) N n,
        K ((Real.log j - Real.log n) / w) / (Real.sqrt n * Real.sqrt j)) -
      ∫ t in (-T)..T, K t * (w * Real.exp (w * t / 2))| ≤
      (32 * T * L + 17 * A) / n := by
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let a : ℝ := n * Real.exp (-T * w)
  let b : ℝ := n * Real.exp (T * w)
  let S := Icc ⌈a⌉₊ ⌊b⌋₊
  let f : ℕ → ℝ := fun j => K (Real.log ((j : ℝ) / n) / w) /
    Real.sqrt ((n : ℝ) * j)
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have han : a ≤ n := by
    have he := Real.exp_le_one_iff.mpr (by nlinarith only [hT, hw0] : -T * w ≤ 0)
    exact (mul_le_mul_of_nonneg_left he hn0.le).trans_eq (mul_one _)
  have hnb : (n : ℝ) ≤ b := by
    have he := Real.one_le_exp (by positivity : 0 ≤ T * w)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hn0.le
  have hnS : n ∈ S := mem_Icc.mpr ⟨Nat.ceil_le.mpr han, Nat.le_floor hnb⟩
  have hset : logarithmicBallIndices (T * w) N n = S.erase n := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjI, hjn, hgap⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have hb := (abs_log_gap_le_iff_exp_bounds hj0 hn0).mp hgap
      have hlo : a ≤ (j : ℝ) := by simpa only [a, neg_mul, mul_div_assoc] using hb.1
      have hhi : (j : ℝ) ≤ b := by simpa only [b, mul_div_assoc] using hb.2
      exact mem_erase.mpr ⟨hjn, mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩⟩
    · intro hj
      obtain ⟨hjn, hjS⟩ := mem_erase.mp hj
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hjS
      have hlo' : a ≤ (j : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hlo)
      have hj0 : (0 : ℝ) < j := ha0.trans_le hlo'
      have hhi' : (j : ℝ) ≤ b := (by exact_mod_cast hhi : (j : ℝ) ≤ ⌊b⌋₊).trans
        (Nat.floor_le (by dsimp only [b]; positivity))
      have hjN : j ≤ N := by exact_mod_cast hhi'.trans hinterior
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by exact_mod_cast hj0, hjN⟩, hjn, ?_⟩
      apply (abs_log_gap_le_iff_exp_bounds hj0 hn0).mpr
      constructor
      · simpa only [a, neg_mul, mul_div_assoc] using hlo'
      · simpa only [b, mul_div_assoc] using hhi'
  have hrow : (∑ j ∈ logarithmicBallIndices (T * w) N n,
      K ((Real.log j - Real.log n) / w) / (Real.sqrt n * Real.sqrt j)) =
      ∑ j ∈ S.erase n, f j := by
    rw [← hset]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj).1).1
    dsimp only [f]
    rw [Real.log_div hj0.ne' hn0.ne', Real.sqrt_mul hn0.le]
  have hdiag : |f n| ≤ A / n := by
    dsimp only [f]
    rw [div_self hn0.ne', Real.log_one, zero_div, ← pow_two, Real.sqrt_sq hn0.le,
      abs_div, abs_of_pos hn0]
    exact div_le_div_of_nonneg_right (hA 0 (by constructor <;> linarith only [hT])) hn0.le
  have hmean := abs_closed_logarithmic_row_sum_sub_mean_le (K := K)
    hT le_rfl (by linarith only [hT] : -T ≤ T) le_rfl
    hw0 hTw hL0 hA hL hn1
  have herase := sum_erase_add S f hnS
  rw [hrow]
  have he : (∑ j ∈ S.erase n, f j) -
      (∫ t in (-T)..T, K t * (w * Real.exp (w * t / 2))) =
      ((∑ j ∈ S, f j) -
        (∫ t in (-T)..T, K t * (w * Real.exp (w * t / 2)))) - f n := by
    linarith only [herase]
  rw [he]
  exact ((abs_sub _ _).trans (add_le_add hmean hdiag)).trans_eq (by ring)

/-- The smooth near row has a receiving-index-independent annular mean whenever its collar
lies below the terminal boundary. -/
theorem abs_near_smooth_row_sub_mean_le {K : ℝ → ℝ} {A L c : ℝ} {N n : ℕ}
    (hc : 0 < c) (hw : c / N ≤ 1 / 4) (hL0 : 0 ≤ L)
    (hA : ∀ s ∈ Set.Icc (-2 : ℝ) 2, |K s| ≤ A)
    (hL : ∀ s ∈ Set.Icc (-2 : ℝ) 2, ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      |K s - K t| ≤ L * |s - t|)
    (hn : n ∈ Icc 1 N) (hinterior : (n : ℝ) * Real.exp (2 * (c / N)) ≤ N) :
    |(∑ j ∈ nearRowIndices c N n,
        K ((Real.log j - Real.log n) / (c / N)) / (Real.sqrt n * Real.sqrt j)) -
      ∫ t in (-2 : ℝ)..2, K t * ((c / N) * Real.exp ((c / N) * t / 2))| ≤
      (64 * L + 17 * A) / n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have h := abs_logarithmic_ball_row_sub_mean_le (K := K)
    (by norm_num : (0 : ℝ) < 2) (div_pos hc hN0) (by linarith only [hw])
    hL0 hA hL hn hinterior
  norm_num only [show (32 : ℝ) * 2 = 64 by norm_num] at h
  simpa only [logarithmicBallIndices, nearRowIndices, mul_div_assoc] using h

/-- The scalar annular mean of the smooth polar near kernel. -/
def polarNearSmoothMean (w : ℝ) : ℝ :=
  ∫ t in (-2 : ℝ)..2,
    (nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)) * Real.exp (w * t / 2)

/-- The normalized near Gamma row has one scalar smooth mean after its exact logarithmic
Gram term is retained. Interior error consists only of lattice quadrature and atomic curvature. -/
theorem exists_nearGamma_polar_scalar_mean_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c → c / N ≤ 1 / 4 →
      n ∈ Icc 1 N → (n : ℝ) * Real.exp (2 * (c / N)) ≤ N →
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) *
          nearPoleRow tiltedUnitSpline c N n / Real.sqrt n -
        (c / N) * polarNearSmoothMean (c / N)| ≤
          C / n + 20 * Real.exp 3 * (c / N) ^ 2 := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  obtain ⟨A, L, hL0, hA, hL⟩ := exists_nearKernel_bounds hφ hsupp
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (by constructor <;> norm_num))
  let K : ℝ → ℝ := fun t => nearKernel tiltedUnitSpline |t| / (∫ u, tiltedUnitSpline u ^ 2)
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (-2 : ℝ) 2) : |t| ∈ Set.Icc (0 : ℝ) 2 :=
    ⟨abs_nonneg _, abs_le.mpr ht⟩
  have hKA : ∀ t ∈ Set.Icc (-2 : ℝ) 2, |K t| ≤ A / (∫ u, tiltedUnitSpline u ^ 2) := by
    intro t ht
    dsimp only [K]
    rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (hA _ (hmem t ht)) hM.le
  have hKL : ∀ s ∈ Set.Icc (-2 : ℝ) 2, ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      |K s - K t| ≤ (L / (∫ u, tiltedUnitSpline u ^ 2)) * |s - t| := by
    intro s hs t ht
    dsimp only [K]
    rw [← sub_div, abs_div, abs_of_pos hM]
    have hh := (hL _ (hmem s hs) _ (hmem t ht)).trans
      (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le s t) hL0)
    exact (div_le_div_of_nonneg_right hh hM.le).trans_eq (by ring)
  refine ⟨(64 * L + 17 * A) / (∫ u, tiltedUnitSpline u ^ 2), by positivity, ?_⟩
  intro c N n hc hw hn hinterior
  have hn1 := (mem_Icc.mp hn).1
  have hN1 := hn1.trans (mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hw0 : 0 < c / N := div_pos hc hN0
  let S : ℝ := ∑ j ∈ nearRowIndices c N n,
    (nearKernel tiltedUnitSpline (|Real.log j - Real.log n| / (c / N)) /
      (∫ u, tiltedUnitSpline u ^ 2)) / Real.sqrt j
  have hrow : (∑ j ∈ nearRowIndices c N n,
      K ((Real.log j - Real.log n) / (c / N)) / (Real.sqrt n * Real.sqrt j)) =
        S / Real.sqrt n := by
    dsimp only [S]
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [K]
    rw [abs_div, abs_of_pos hw0]
    ring
  have hmean : (∫ t in (-2 : ℝ)..2, K t * ((c / N) * Real.exp ((c / N) * t / 2))) =
      (c / N) * polarNearSmoothMean (c / N) := by
    unfold polarNearSmoothMean
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by dsimp only [K]; ring)
  have hsm := abs_near_smooth_row_sub_mean_le hc hw (div_nonneg hL0 hM.le) hKA hKL hn hinterior
  rw [hrow, hmean] at hsm
  have hgam := div_le_div_of_nonneg_right
    (abs_nearGammaDownwardRow_one_sub_smooth_le hc hN1 (hw.trans (by norm_num)) hn) hsn.le
  have hgam' :
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) *
          nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S / Real.sqrt n| ≤
      20 * Real.exp 3 * (c / N) ^ 2 := by
    have hleft : |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) *
          nearPoleRow tiltedUnitSpline c N n / Real.sqrt n - S / Real.sqrt n| =
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n -
        (S - (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n)| /
          Real.sqrt n := by
      calc
        _ = |(nearGammaDownwardRow tiltedUnitSpline c N 1 n -
            (S - (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n)) /
              Real.sqrt n| := by congr 1; ring
        _ = _ := by rw [abs_div, abs_of_pos hsn]
    rw [hleft]
    exact hgam.trans_eq (by field_simp [hsn.ne', hN0.ne'])
  have htri := (abs_sub_le
    (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
      (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n)
    (S / Real.sqrt n) ((c / N) * polarNearSmoothMean (c / N))).trans
      (add_le_add hgam' hsm)
  exact htri.trans_eq (by ring)

/-- The joint near-Gamma and harmonic-center scalar mean. -/
def polarNearJointMean (w : ℝ) : ℝ :=
  polarNearSmoothMean w +
    ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      (Real.log 2 + Real.eulerMascheroniConstant)

/-- The near Gamma logarithm cancels the harmonic collar logarithm. Only the Gram defect and
the pole Taylor error remain outside a receiving-index-independent scalar mean. -/
theorem exists_joint_near_polar_scalar_mean_bound :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ {c : ℝ} {N n : ℕ}, 0 < c →
      n ∈ Icc 1 N → 2 * c / N ≤ 1 / 8 → 8 ≤ (n : ℝ) * (2 * c / N) →
      (n : ℝ) * Real.exp (2 * c / N) ≤ N →
      |nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (completeWeilPoleShift tiltedUnitSpline c / N) *
          ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n) +
        (Real.log c + Real.log ((n : ℝ) / N)) *
          (poleRowDefect tiltedUnitSpline c N n / Real.sqrt n + atomPoleErrorCoefficient tiltedUnitSpline c N) -
        (c / N) * polarNearJointMean (c / N)| ≤ C / n + D * (c / N) ^ 2 := by
  obtain ⟨C, hC, hnear⟩ := exists_nearGamma_polar_scalar_mean_bound
  let a : ℝ := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)
  have ha : 0 ≤ a := div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le
  refine ⟨C + 2 * a, 20 * Real.exp 3 + a * (8 + 2 * Real.exp 2), by positivity, by positivity, ?_⟩
  intro c N n hc hn hw hwide hinterior
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hw0 : 0 < c / N := div_pos hc hN0
  have hwquarter : c / N ≤ 1 / 4 := by
    have hh : 2 * (c / N) ≤ 1 / 8 := by simpa only [mul_div_assoc] using hw
    linarith only [hh]
  have hnearN := hnear hc hwquarter hn
    (by simpa only [mul_div_assoc] using hinterior)
  have hcenter := abs_near_polarCenter_row_sub_interior_profile_le hc hn hw hwide hinterior
  have hshift : completeWeilPoleShift tiltedUnitSpline c / N = a * (c / N) := by
    unfold completeWeilPoleShift
    dsimp only [a]
    ring
  have hP : nearPoleRow tiltedUnitSpline c N n =
      poleRowDefect tiltedUnitSpline c N n +
        (atomPoleErrorCoefficient tiltedUnitSpline c N +
          completeWeilPoleShift tiltedUnitSpline c / N) * Real.sqrt n := by
    unfold poleRowDefect
    rw [exactPoleCoefficient_eq]
    ring
  have hlog : Real.log (2 * c * n / N) =
      Real.log c + Real.log ((n : ℝ) / N) + Real.log 2 := by
    rw [show 2 * c * (n : ℝ) / N = 2 * (c * ((n : ℝ) / N)) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero hc.ne' (div_ne_zero hn0.ne' hN0.ne')),
      Real.log_mul hc.ne' (div_ne_zero hn0.ne' hN0.ne')]
    ring
  have hscaled : |(completeWeilPoleShift tiltedUnitSpline c / N) *
      ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
        (Real.log (2 * c * n / N) + Real.eulerMascheroniConstant))| ≤
      a * (8 + 2 * Real.exp 2) * (c / N) ^ 2 + 2 * a / n := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (completeWeilPoleShift_nonneg _ hc.le) hN0.le)]
    exact (mul_le_mul_of_nonneg_left hcenter
      (div_nonneg (completeWeilPoleShift_nonneg _ hc.le) hN0.le)).trans_eq (by
        rw [hshift]
        field_simp [hc.ne', hn0.ne', hN0.ne'])
  have he : nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
      (completeWeilPoleShift tiltedUnitSpline c / N) *
        ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n) +
      (Real.log c + Real.log ((n : ℝ) / N)) *
        (poleRowDefect tiltedUnitSpline c N n / Real.sqrt n + atomPoleErrorCoefficient tiltedUnitSpline c N) -
      (c / N) * polarNearJointMean (c / N) =
      (nearGammaDownwardRow tiltedUnitSpline c N 1 n / Real.sqrt n +
        (Real.log c + Real.log ((n : ℝ) / N)) * nearPoleRow tiltedUnitSpline c N n / Real.sqrt n -
          (c / N) * polarNearSmoothMean (c / N)) +
      (completeWeilPoleShift tiltedUnitSpline c / N) *
        ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
          (Real.log (2 * c * n / N) + Real.eulerMascheroniConstant)) := by
    rw [hP, hlog, hshift]
    unfold polarNearJointMean
    dsimp only [a]
    field_simp [hsn]
    ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add hnearN hscaled)).trans_eq (by ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
