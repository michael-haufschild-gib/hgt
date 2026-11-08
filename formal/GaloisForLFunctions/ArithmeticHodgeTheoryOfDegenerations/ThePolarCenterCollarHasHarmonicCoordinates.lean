import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Exact harmonic coordinates for the polar center collar

The two half-widths of a logarithmic collar determine its singular reciprocal
sum exactly. The remaining reciprocal sum is smooth.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- A symmetric logarithmic interval has multiplicative exponential endpoints. -/
lemma abs_log_gap_le_iff_exp_bounds {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ t ↔ y * Real.exp (-t) ≤ x ∧ x ≤ y * Real.exp t := by
  rw [← Real.log_div hx.ne' hy.ne', abs_le, Real.le_log_iff_exp_le (div_pos hx hy),
    Real.log_le_iff_le_exp (div_pos hx hy), le_div_iff₀ hy, div_le_iff₀ hy]
  simp only [mul_comm]

/-- The polar center collar is exactly the sum of its two harmonic half-widths and a smooth
reciprocal row; this includes empty halves and terminal truncation. -/
theorem near_polarCenter_row_eq_harmonics {c : ℝ} {N n : ℕ}
    (hc : 0 < c) (hn : n ∈ Icc 1 N) :
    let t := 2 * c / N
    let lo := ⌈(n : ℝ) * Real.exp (-t)⌉₊
    let hi := min N ⌊(n : ℝ) * Real.exp t⌋₊
    (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) =
      (Real.sqrt n / 2) * ((harmonic (n - lo) : ℝ) + harmonic (hi - n) +
        ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) := by
  intro t lo hi
  have hn1 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn1.trans hnN
  have ht : 0 < t := by dsimp only [t]; positivity
  have hlo1 : 1 ≤ lo := Nat.one_le_iff_ne_zero.mpr
    (Nat.ceil_pos.mpr (mul_pos hn0 (Real.exp_pos _))).ne'
  have hlon : lo ≤ n := Nat.ceil_le.mpr (by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    exact (mul_le_mul_of_nonneg_left he hn0.le).trans_eq (mul_one _))
  have hnhi : n ≤ hi := le_min hnN (Nat.le_floor (by
    have he := Real.one_le_exp ht.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hn0.le))
  have hhiN : hi ≤ N := min_le_left _ _
  have hset : nearRowIndices c N n = (Icc lo hi).erase n := by
    ext j
    constructor
    · intro hj
      obtain ⟨hjI, hjn, hgap⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have hb := (abs_log_gap_le_iff_exp_bounds hj0 hn0).mp hgap
      refine mem_erase.mpr ⟨hjn, mem_Icc.mpr ⟨Nat.ceil_le.mpr hb.1, ?_⟩⟩
      exact le_min (mem_Icc.mp hjI).2 (Nat.le_floor hb.2)
    · intro hj
      obtain ⟨hjn, hjI⟩ := mem_erase.mp hj
      obtain ⟨hjlo, hjhi⟩ := mem_Icc.mp hjI
      have hj1 : 1 ≤ j := hlo1.trans hjlo
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hlow : (n : ℝ) * Real.exp (-t) ≤ j :=
        (Nat.le_ceil _).trans (by exact_mod_cast hjlo)
      have hhigh : (j : ℝ) ≤ (n : ℝ) * Real.exp t :=
        (by exact_mod_cast hjhi.trans (min_le_right _ _)).trans (Nat.floor_le (by positivity))
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hjhi.trans hhiN⟩, hjn, ?_⟩
      exact (abs_log_gap_le_iff_exp_bounds hj0 hn0).mpr ⟨hlow, hhigh⟩
  let Sl := Ico lo n
  let Sh := Ioc n hi
  have hsplit : nearRowIndices c N n = Sl ∪ Sh := by
    rw [hset]
    ext j
    simp only [Sl, Sh, mem_erase, mem_Icc, mem_union, mem_Ico, mem_Ioc]
    omega
  have hdisj : Disjoint Sl Sh := disjoint_left.mpr fun j hjl hjh => by
    have h1 := (mem_Ico.mp hjl).2
    have h2 := (mem_Ioc.mp hjh).1
    omega
  have hsumlo : (∑ j ∈ Sl, 1 / |(n : ℝ) - j|) = (harmonic (n - lo) : ℝ) := by
    rw [HTGeometry.harmonic_eq_sum_Ioc]
    change (∑ j ∈ Sl, 1 / |(n : ℝ) - j|) = ∑ k ∈ Icc 1 (n - lo), (k : ℝ)⁻¹
    refine sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hjl, hjn⟩ := mem_Ico.mp hj
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      obtain ⟨_, _⟩ := mem_Ico.mp hi
      obtain ⟨_, _⟩ := mem_Ico.mp hj
      omega
    · intro k hk
      obtain ⟨hk1, hkle⟩ := mem_Icc.mp hk
      exact ⟨n - k, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      have hjn := (mem_Ico.mp hj).2.le
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hjn))]
      rw [Nat.cast_sub hjn, one_div]
  have hsumhi : (∑ j ∈ Sh, 1 / |(n : ℝ) - j|) = (harmonic (hi - n) : ℝ) := by
    rw [HTGeometry.harmonic_eq_sum_Ioc]
    change (∑ j ∈ Sh, 1 / |(n : ℝ) - j|) = ∑ k ∈ Icc 1 (hi - n), (k : ℝ)⁻¹
    refine sum_bij (fun j _ => j - n) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hnj, hjhi⟩ := mem_Ioc.mp hj
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      obtain ⟨_, _⟩ := mem_Ioc.mp hi
      obtain ⟨_, _⟩ := mem_Ioc.mp hj
      omega
    · intro k hk
      obtain ⟨hk1, hkle⟩ := mem_Icc.mp hk
      exact ⟨n + k, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      have hnj := (mem_Ioc.mp hj).1.le
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnj)), neg_sub]
      rw [Nat.cast_sub hnj, one_div]
  have hkernel : (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) =
      (Real.sqrt n / 2) * ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
        ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hj
    have hj1 := (mem_Icc.mp hjI).1
    have hsj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hj1)).ne'
    have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    have he := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 (Ne.symm hjn)
    calc
      _ = Real.sqrt n * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) := by
        field_simp [hsn, hsj]
      _ = _ := by rw [he]; ring
  have hsing : (∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) =
      (harmonic (n - lo) : ℝ) + harmonic (hi - n) := by
    rw [hsplit, sum_union hdisj, hsumlo, hsumhi]
  rw [hkernel, hsing]



/-- The upper half-width differs from its linearized width only by exponential curvature
and one lattice rounding unit. -/
lemma upper_polar_half_width_bounds {n : ℕ} {t : ℝ}
    (hn : 1 ≤ n) (ht : 0 < t) (ht1 : t ≤ 1 / 8) (hwide : 8 ≤ (n : ℝ) * t) :
    let d := ⌊(n : ℝ) * Real.exp t⌋₊ - n
    (n : ℝ) * t / 2 ≤ d ∧ |(d : ℝ) - n * t| ≤ 2 * ((n : ℝ) * t) * t + 1 := by
  intro d
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have helo := Real.add_one_le_exp t
  have he1 : Real.exp t ≤ 1 + 2 * t := by
    have hh := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_pos ht]; linarith only [ht1])
    rw [abs_of_pos ht] at hh
    have hle := (le_abs_self (Real.exp t - 1)).trans hh
    linarith only [hle]
  have he2 : Real.exp t - 1 ≤ t + 2 * t ^ 2 := by
    have h1 : Real.exp t - 1 ≤ t * Real.exp t := exp_sub_one_le_mul_exp
    have h2 := mul_le_mul_of_nonneg_left he1 ht.le
    nlinarith only [h1, h2]
  have hnf : n ≤ ⌊(n : ℝ) * Real.exp t⌋₊ := Nat.le_floor (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp ht.le) hn0.le)
  have hd : (d : ℝ) = (⌊(n : ℝ) * Real.exp t⌋₊ : ℝ) - n := Nat.cast_sub hnf
  have hfloorlo := Nat.sub_one_lt_floor ((n : ℝ) * Real.exp t)
  have hfloorhi := Nat.floor_le (mul_nonneg hn0.le (Real.exp_pos t).le)
  have hexplo := mul_le_mul_of_nonneg_left helo hn0.le
  have hexphi := mul_le_mul_of_nonneg_left he2 hn0.le
  constructor
  · rw [hd]
    nlinarith only [hfloorlo, hexplo, hwide]
  · rw [hd, abs_le]
    constructor
    · have htterm : 0 ≤ 2 * ((n : ℝ) * t) * t := by positivity
      nlinarith only [hfloorlo, hexplo, htterm]
    · nlinarith only [hfloorhi, hexphi]

/-- The lower half-width obeys the same curvature and rounding bound. -/
lemma lower_polar_half_width_bounds {n : ℕ} {t : ℝ}
    (hn : 1 ≤ n) (ht : 0 < t) (ht1 : t ≤ 1 / 8) (hwide : 8 ≤ (n : ℝ) * t) :
    let d := n - ⌈(n : ℝ) * Real.exp (-t)⌉₊
    (n : ℝ) * t / 2 ≤ d ∧ |(d : ℝ) - n * t| ≤ 2 * ((n : ℝ) * t) * t + 1 := by
  intro d
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have helo : 1 - t ≤ Real.exp (-t) := by linarith only [Real.add_one_le_exp (-t)]
  have hehi : Real.exp (-t) ≤ 1 - t + t ^ 2 := by
    have hprod : Real.exp (-t) * (1 + t) ≤ 1 := by
      calc
        _ ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hpoly : 1 ≤ (1 - t + t ^ 2) * (1 + t) := by nlinarith only [pow_nonneg ht.le 3]
    have hh := hprod.trans hpoly
    exact (mul_le_mul_iff_of_pos_right (by linarith only [ht] : 0 < 1 + t)).mp hh
  have hln : ⌈(n : ℝ) * Real.exp (-t)⌉₊ ≤ n := Nat.ceil_le.mpr (by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hn0.le)
  have hd : (d : ℝ) = (n : ℝ) - ⌈(n : ℝ) * Real.exp (-t)⌉₊ := Nat.cast_sub hln
  have hceillo := Nat.le_ceil ((n : ℝ) * Real.exp (-t))
  have hceilhi := Nat.ceil_lt_add_one (mul_nonneg hn0.le (Real.exp_pos (-t)).le)
  have hexplo := mul_le_mul_of_nonneg_left helo hn0.le
  have hexphi := mul_le_mul_of_nonneg_left hehi hn0.le
  have hcurv := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ (n : ℝ) * t by positivity)
  constructor
  · rw [hd]
    nlinarith only [hceilhi, hexphi, hcurv, hwide]
  · rw [hd, abs_le]
    constructor
    · nlinarith only [hceilhi, hexphi, mul_nonneg hn0.le (sq_nonneg t)]
    · nlinarith only [hceillo, hexplo, mul_nonneg hn0.le (sq_nonneg t)]

/-- An integer half-width close to a positive real width has the same harmonic logarithm,
with explicit rounding and relative-width errors. -/
lemma abs_harmonic_sub_log_of_width_error {k : ℕ} {r t : ℝ}
    (hr : 0 < r) (_ht : 0 ≤ t) (hk : r / 2 ≤ k)
    (herr : |(k : ℝ) - r| ≤ 2 * r * t + 1) :
    |(harmonic k : ℝ) - Real.log r - Real.eulerMascheroniConstant| ≤ 4 * t + 4 / r := by
  have hk0 : (0 : ℝ) < k := (half_pos hr).trans_le hk
  have hk1 : 1 ≤ k := by exact_mod_cast hk0
  have hH := HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hk1
  have hinv : 1 / (k : ℝ) ≤ 2 / r :=
    (one_div_le_one_div_of_le (half_pos hr) hk).trans_eq (by ring)
  have hlog : |Real.log (k : ℝ) - Real.log r| ≤ 2 * |(k : ℝ) - r| / r := by
    have h := abs_log_one_add_div_sub_le (half_pos hr)
      (sub_nonneg.mpr hk) (by linarith only [hr] : 0 ≤ r - r / 2)
    have he (x : ℝ) : 1 + (x - r / 2) / (r / 2) = x / (r / 2) := by field_simp; ring
    rw [he, he, Real.log_div hk0.ne' (half_pos hr).ne',
      Real.log_div hr.ne' (half_pos hr).ne', sub_sub_sub_cancel_right,
      show ((k : ℝ) - r / 2) - (r - r / 2) = k - r by ring] at h
    exact h.trans_eq (by ring)
  have hlogbound : |Real.log (k : ℝ) - Real.log r| ≤ 4 * t + 2 / r := by
    calc
      _ ≤ 2 * |(k : ℝ) - r| / r := hlog
      _ ≤ 2 * (2 * r * t + 1) / r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left herr (by norm_num)) hr.le
      _ = _ := by field_simp [hr.ne']; ring
  have he : (harmonic k : ℝ) - Real.log r - Real.eulerMascheroniConstant =
      ((harmonic k : ℝ) - Real.log k - Real.eulerMascheroniConstant) +
        (Real.log k - Real.log r) := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add (hH.trans hinv) hlogbound)).trans_eq (by ring)


/-- The smooth half of the center collar is proportional to the atomic width. -/
lemma sum_near_smooth_reciprocal_le {c : ℝ} {N n : ℕ}
    (hc : 0 < c) (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1) :
    (∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) ≤ 4 * Real.exp 2 * (c / N) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hcard := (nearRowIndices_card_and_pointwise_local contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hN0 hw hn).1
  calc
    _ ≤ ((nearRowIndices c N n).card : ℝ) * (1 / (n : ℝ)) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun j _ => one_div_le_one_div_of_le hn0
        (le_add_of_nonneg_right (Nat.cast_nonneg j))
    _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by unfold linearNearRowRadius; field_simp [hn0.ne']; ring

/-- Away from terminal truncation, the harmonic collar has its logarithmic profile with a
uniform curvature and rounding error. -/
theorem abs_near_polarCenter_row_sub_interior_profile_le {c : ℝ} {N n : ℕ}
    (hc : 0 < c) (hn : n ∈ Icc 1 N) (hw : 2 * c / N ≤ 1 / 8)
    (hwide : 8 ≤ (n : ℝ) * (2 * c / N))
    (hinterior : (n : ℝ) * Real.exp (2 * c / N) ≤ N) :
    |(∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
        (Real.log (2 * c * n / N) + Real.eulerMascheroniConstant)| ≤
      (8 + 2 * Real.exp 2) * (c / N) + 2 * N / (c * n) := by
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hn1.trans (mem_Icc.mp hn).2
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  let t : ℝ := 2 * c / N
  let r : ℝ := (n : ℝ) * t
  let lo := ⌈(n : ℝ) * Real.exp (-t)⌉₊
  let hi := ⌊(n : ℝ) * Real.exp t⌋₊
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr : 0 < r := mul_pos hn0 ht
  have hhiN : hi ≤ N := Nat.floor_le_of_le hinterior
  obtain ⟨hdhi, hehi⟩ := upper_polar_half_width_bounds hn1 ht hw hwide
  obtain ⟨hdlo, helo⟩ := lower_polar_half_width_bounds hn1 ht hw hwide
  have hHhi := abs_harmonic_sub_log_of_width_error hr ht.le hdhi hehi
  have hHlo := abs_harmonic_sub_log_of_width_error hr ht.le hdlo helo
  let smooth := ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)
  have hs0 : 0 ≤ smooth := sum_nonneg fun _ _ => by positivity
  have hsle : smooth ≤ 4 * Real.exp 2 * (c / N) :=
    sum_near_smooth_reciprocal_le hc hn (by
      have hcN : 0 < c / N := div_pos hc hN0
      have hh : 2 * (c / N) ≤ 1 / 8 := by simpa only [mul_div_assoc] using hw
      linarith only [hh, hcN])
  have hrow := near_polarCenter_row_eq_harmonics hc hn
  change (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) =
    (Real.sqrt n / 2) * ((harmonic (n - lo) : ℝ) + harmonic (min N hi - n) + smooth) at hrow
  rw [min_eq_right hhiN] at hrow
  have he : (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) / Real.sqrt n -
      (Real.log (2 * c * n / N) + Real.eulerMascheroniConstant) =
      (((harmonic (n - lo) : ℝ) - Real.log r - Real.eulerMascheroniConstant) +
        ((harmonic (hi - n) : ℝ) - Real.log r - Real.eulerMascheroniConstant) + smooth) / 2 := by
    rw [hrow]
    have hr_eq : 2 * c * (n : ℝ) / N = r := by dsimp only [r, t]; ring
    rw [hr_eq]
    field_simp [hsn]
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hab : |((harmonic (n - lo) : ℝ) - Real.log r - Real.eulerMascheroniConstant) +
        ((harmonic (hi - n) : ℝ) - Real.log r - Real.eulerMascheroniConstant) + smooth| ≤
      (4 * t + 4 / r) + (4 * t + 4 / r) + 4 * Real.exp 2 * (c / N) := by
    have hsum := (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hHlo hHhi))
        (by simpa only [abs_of_nonneg hs0] using hsle))
    exact hsum
  exact (div_le_div_of_nonneg_right hab (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by
    dsimp only [r, t]
    field_simp [hc.ne', hn0.ne', hN0.ne']
    ring)

#print axioms near_polarCenter_row_eq_harmonics
#print axioms abs_near_polarCenter_row_sub_interior_profile_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
