import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne
import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum

/-!
# The archimedean cross kernel at the spacing scale

Let `f = Σ_{n ≤ N} x_n g(· − log n)` be an atomic test with a bump `g` supported in `[0, w]`. Its
Lévy energy collects, from the shifts `y ∈ (w, 1]`, the full self-energy `log(1/w)` per unit mass
(`TheSelfEnergyOfAnAtomHasConstantOne`), minus the interaction of distinct atoms. This file computes
that interaction and bounds it.

* **Windowed autocorrelation** (`integral_atomicTest_mul_shift`): with `G(t) = ∫ g(v) g(v + t) dv`,
  `∫ f(u) f(u + y) du = Σ_{m,n} x_m x_n G(y − log(n/m))`; for `y > w` the diagonal vanishes.
* **The pair window** (`setIntegral_indicator_archLevyDensity_le`): two atoms at log-distance `s`,
  `|s| ≥ 2w`, interact only for `|y − s| ≤ w`, where `ω(y) ≤ e^{1/2}/|s|`, and only when `|s| ≤ 2`.
* **The cross-kernel row** (`sum_crossBound_le`): the row of the cross kernel at the atom `m` is at
  most `4e^{5/2} w m (1 + log(N + 1))`, since `1/|log(n/m)| ≤ e² m/|n − m|` and the harmonic row
  `Σ 1/|n − m|` is logarithmic.
* **The Lévy energy of an atomic test** (`levyEnergy_atomicTest_ge`): for `w ≤ δ_N/2`,
  `levyEnergy f ≥ ‖g‖² Σ_m x_m² (log(1/w) − 8e^{5/2} w m (1 + log(N + 1)))`.

The cross-kernel row at a scale is the **relative width** `w·m` at that scale times `log N`. At the
spacing, `w = cδ_N`, it is `c (m/N) log N`: largest on the top dyadic block, where Weil's prime form
has no entries.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The autocorrelation of a bump -/

/-- The autocorrelation `G(t) = ∫ g(v) g(v + t) dv` of a bump. -/
def bumpCorr (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ v, g v * g (v + t)

theorem integrable_comp_sub_mul_comp_add (hg : Continuous g) (hgc : HasCompactSupport g)
    (a b : ℝ) : Integrable fun u => g (u - a) * g (u + b) :=
  ((hg.comp (continuous_sub_right a)).mul (hg.comp (continuous_add_const b))).integrable_of_hasCompactSupport
    (hgc.comp_homeomorph (Homeomorph.subRight a)).mul_right

theorem integrable_sq_of_continuous (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable fun u => g u ^ 2 := by
  have h := integrable_comp_sub_mul_comp_add hg hgc 0 0
  simp only [sub_zero, add_zero] at h
  simpa [pow_two] using h

/-- `|G(t)| ≤ ‖g‖²`. -/
theorem abs_bumpCorr_le (hg : Continuous g) (hgc : HasCompactSupport g) (t : ℝ) :
    |bumpCorr g t| ≤ ∫ v, g v ^ 2 := by
  have h1 := integrable_sq_of_continuous hg hgc
  have h2 : Integrable fun v => g (v + t) ^ 2 := h1.comp_add_right t
  have h3 : Integrable fun v => g v * g (v + t) := by
    simpa using integrable_comp_sub_mul_comp_add hg hgc 0 t
  have hle : ∀ v, |g v * g (v + t)| ≤ (g v ^ 2 + g (v + t) ^ 2) / 2 := fun v => by
    rw [abs_mul]
    nlinarith [sq_nonneg (|g v| - |g (v + t)|), sq_abs (g v), sq_abs (g (v + t))]
  calc |bumpCorr g t| ≤ ∫ v, |g v * g (v + t)| := abs_integral_le_integral_abs
    _ ≤ ∫ v, (g v ^ 2 + g (v + t) ^ 2) / 2 := integral_mono h3.abs ((h1.add h2).div_const 2) hle
    _ = ∫ v, g v ^ 2 := by
        rw [integral_div, integral_add h1 h2, integral_add_right_eq_self (fun v => g v ^ 2) t]
        ring

/-- `G(t) = 0` once `|t| > w`. -/
theorem bumpCorr_eq_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {t : ℝ} (ht : w < |t|) :
    bumpCorr g t = 0 := by
  have hpt : ∀ v, g v * g (v + t) = 0 := fun v => by
    by_cases hv : v ∈ Set.Icc 0 w
    · by_cases hvt : v + t ∈ Set.Icc 0 w
      · exfalso
        have : |t| ≤ w := abs_le.mpr ⟨by linarith [hv.2, hvt.1], by linarith [hv.1, hvt.2]⟩
        linarith
      · rw [hgsupp _ hvt, mul_zero]
    · rw [hgsupp _ hv, zero_mul]
  simp [bumpCorr, hpt]

/-! ### The windowed autocorrelation of an atomic test -/

/-- **Windowed autocorrelation**: `∫ f(u) f(u + y) du = Σ_{m,n} x_m x_n G(y − (log n − log m))`. -/
theorem integral_atomicTest_mul_shift (hg : Continuous g) (hgc : HasCompactSupport g) (N : ℕ)
    (x : ℕ → ℝ) (y : ℝ) :
    ∫ u, atomicTest N x g u * atomicTest N x g (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * x n * bumpCorr g (y - (Real.log n - Real.log m)) := by
  have hpt : ∀ u, atomicTest N x g u * atomicTest N x g (u + y) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * x n * (g (u - Real.log m) * g (u + (y - Real.log n))) := by
    intro u
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [show u + y - Real.log n = u + (y - Real.log n) by ring]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (integrable_comp_sub_mul_comp_add hg hgc _ _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ => (integrable_comp_sub_mul_comp_add hg hgc _ _).const_mul _]
  refine sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, bumpCorr,
    ← integral_sub_right_eq_self (fun v => g v * g (v + (y - (Real.log n - Real.log m))))
      (Real.log m)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [show u - Real.log m + (y - (Real.log n - Real.log m)) = u + (y - Real.log n) by ring]

/-- `∫ (f(u) − f(u + y))² = 2‖f‖² − 2 ∫ f(u) f(u + y)`. -/
theorem integral_sub_shift_sq_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (y : ℝ) :
    ∫ u, (f u - f (u + y)) ^ 2 = 2 * ∫ u, f u ^ 2 - 2 * ∫ u, f u * f (u + y) := by
  have h1 := integrable_sq_of_continuous hf hfc
  have h2 : Integrable fun u => f (u + y) ^ 2 := h1.comp_add_right y
  have h3 : Integrable fun u => f u * f (u + y) := by
    simpa using integrable_comp_sub_mul_comp_add hf hfc 0 y
  have hpt : ∀ u, (f u - f (u + y)) ^ 2 = f u ^ 2 + f (u + y) ^ 2 - 2 * (f u * f (u + y)) :=
    fun u => by ring
  simp_rw [hpt]
  rw [integral_sub (h1.add h2 : Integrable fun u => f u ^ 2 + f (u + y) ^ 2) (h3.const_mul 2),
    integral_add h1 h2, integral_const_mul,
    integral_add_right_eq_self (fun u => f u ^ 2) y]
  ring

/-! ### The pair window -/

/-- The log-distance `log n − log m` of two atoms. -/
def logGap (m n : ℕ) : ℝ := Real.log n - Real.log m

/-- The window `[s − w, s + w]` of shifts on which two atoms at log-distance `s` interact. -/
def pairWindow (w s : ℝ) : Set ℝ := Set.Icc (s - w) (s + w)

/-- The bound on one pair's share of the windowed Lévy integral. -/
def crossBound (w s : ℝ) : ℝ := if |s| ≤ 2 then 2 * Real.exp (1 / 2) * w / |s| else 0

theorem crossBound_nonneg (hw : 0 ≤ w) (s : ℝ) : 0 ≤ crossBound w s := by
  unfold crossBound
  split_ifs
  · positivity
  · exact le_rfl

/-- **The pair window**: `∫_{(w,1]} ω 𝟙_{[s−w, s+w]} ≤ crossBound w s` for `|s| ≥ 2w`, `w < 1`. -/
theorem setIntegral_indicator_archLevyDensity_le {s : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (hs : 2 * w ≤ |s|) :
    ∫ y in Set.Ioc w 1, (pairWindow w s).indicator archLevyDensity y ≤ crossBound w s := by
  rw [setIntegral_indicator (show MeasurableSet (pairWindow w s) from measurableSet_Icc)]
  -- on the window: `s > 0`, `y ≥ s/2`, so `ω(y) ≤ e^{1/2}/s`
  have hwin : ∀ y ∈ Set.Ioc w 1 ∩ pairWindow w s, 0 < s ∧ s / 2 ≤ y ∧ s ≤ 1 + w := by
    intro y hy
    obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
    have hs0 : 0 < s := by linarith
    rw [abs_of_pos hs0] at hs
    exact ⟨hs0, by linarith, by linarith⟩
  unfold crossBound
  split_ifs with h2
  · have hint : IntegrableOn archLevyDensity (Set.Ioc w 1 ∩ pairWindow w s) :=
      (integrableOn_archLevyDensity_Ioc hw0).mono_set Set.inter_subset_left
    have hle : ∫ y in Set.Ioc w 1 ∩ pairWindow w s, archLevyDensity y ≤
        ∫ y in Set.Ioc w 1 ∩ pairWindow w s, Real.exp (1 / 2) / |s| := by
      refine setIntegral_mono_on hint (integrableOn_const ?_ ) (measurableSet_Ioc.inter
        measurableSet_Icc) fun y hy => ?_
      · exact (measure_mono Set.inter_subset_right).trans_lt (by simp [pairWindow])
      obtain ⟨hs0, hys, -⟩ := hwin y hy
      have hy0 : 0 < y := lt_trans hw0 hy.1.1
      calc archLevyDensity y ≤ Real.exp (1 / 2) / (2 * y) :=
            archLevyDensity_le_sqrt_e_div hy0 hy.1.2
        _ ≤ Real.exp (1 / 2) / |s| := by
            rw [abs_of_pos hs0]
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le hs0 (by linarith)
    have hvol : volume.real (Set.Ioc w 1 ∩ pairWindow w s) ≤ 2 * w := by
      have hle' : volume (Set.Ioc w 1 ∩ pairWindow w s) ≤ ENNReal.ofReal (2 * w) := by
        refine (measure_mono Set.inter_subset_right).trans ?_
        simp only [pairWindow, Real.volume_Icc]
        exact le_of_eq (by ring_nf)
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle'
    rw [setIntegral_const, smul_eq_mul] at hle
    have hs0 : 0 < |s| := by linarith
    calc _ ≤ volume.real (Set.Ioc w 1 ∩ pairWindow w s) * (Real.exp (1 / 2) / |s|) := hle
      _ ≤ 2 * w * (Real.exp (1 / 2) / |s|) :=
          mul_le_mul_of_nonneg_right hvol (by positivity)
      _ = 2 * Real.exp (1 / 2) * w / |s| := by ring
  · -- `|s| > 2`: the window misses `(w, 1]`
    have hempty : Set.Ioc w 1 ∩ pairWindow w s = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => h2 ?_
      obtain ⟨hs0, -, hs1⟩ := hwin y hy
      rw [abs_of_pos hs0]
      linarith
    rw [hempty, Measure.restrict_empty, integral_zero_measure]

/-! ### The cross-kernel row -/

/-- `1/|log n − log m| ≤ e² m/|n − m|` for distinct `m, n ≥ 1` with `|log n − log m| ≤ 2`. -/
theorem inv_abs_logGap_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n)
    (h2 : |logGap m n| ≤ 2) :
    1 / |logGap m n| ≤ Real.exp 2 * m / |(n : ℝ) - m| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- `m < n`: `log(n/m) ≥ 1 − m/n` and `n ≤ e² m`
    have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
    have hgap : logGap m n = Real.log (n / m) := by
      rw [logGap, Real.log_div hn0.ne' hm0.ne']
    have hlow : ((n : ℝ) - m) / n ≤ logGap m n := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / m by positivity)
      rw [hgap, inv_div] at *
      calc ((n : ℝ) - m) / n = 1 - m / n := by field_simp
        _ ≤ _ := this
    have hpos : 0 < logGap m n := lt_of_lt_of_le (by apply div_pos <;> linarith) hlow
    have hnm : (n : ℝ) ≤ Real.exp 2 * m := by
      have h := Real.exp_le_exp.mpr ((abs_of_pos hpos).symm.le.trans h2)
      rw [hgap, Real.exp_log (by positivity), div_le_iff₀ hm0] at h
      exact h
    rw [abs_of_pos hpos, abs_of_pos (by linarith : (0 : ℝ) < n - m)]
    rw [div_le_div_iff₀ hpos (by linarith)]
    have : ((n : ℝ) - m) ≤ logGap m n * n := by
      rw [div_le_iff₀ hn0] at hlow; linarith
    nlinarith
  · -- `n < m`: `log(m/n) ≥ 1 − n/m`
    have hgt' : (n : ℝ) < m := by exact_mod_cast hgt
    have hgap : -logGap m n = Real.log (m / n) := by
      rw [logGap, Real.log_div hm0.ne' hn0.ne']; ring
    have hlow : ((m : ℝ) - n) / m ≤ -logGap m n := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < m / n by positivity)
      rw [hgap, inv_div] at *
      calc ((m : ℝ) - n) / m = 1 - n / m := by field_simp
        _ ≤ _ := this
    have hneg : 0 < -logGap m n := lt_of_lt_of_le (by apply div_pos <;> linarith) hlow
    rw [abs_of_neg (by linarith : logGap m n < 0), abs_of_neg (by linarith : (n : ℝ) - m < 0)]
    rw [div_le_div_iff₀ hneg (by linarith)]
    have : ((m : ℝ) - n) ≤ -logGap m n * m := by
      rw [div_le_iff₀ hm0] at hlow; linarith
    nlinarith

/-- `|log n − log m| ≥ δ_N` for distinct atoms `m, n ∈ [1, N]`. -/
theorem atomSpacing_le_abs_logGap {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N)
    (hmn : m ≠ n) : atomSpacing N ≤ |logGap m n| := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (atomSpacing_le_log_sub hm1 hmN hlt).trans (le_abs_self _)
  · have := atomSpacing_le_log_sub hn1 hnN hgt
    rw [logGap, abs_sub_comm]
    exact this.trans (le_abs_self _)

/-- **The cross-kernel row**: `Σ_{n ≠ m} crossBound w (log n − log m) ≤ 4e^{5/2} w m (1 + log(N+1))`. -/
theorem sum_crossBound_le {N m : ℕ} (hm : m ∈ Icc 1 N) (hw0 : 0 ≤ w) :
    ∑ n ∈ Icc 1 N, (if m = n then 0 else crossBound w (logGap m n)) ≤
      4 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1)) := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  set C : ℝ := 2 * Real.exp (5 / 2) * w * m
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ n ∈ Icc 1 N, (if m = n then 0 else crossBound w (logGap m n)) ≤
      if n = m then 0 else C * (1 / |(n : ℝ) - m|) := by
    intro n hn
    by_cases hmn : m = n
    · subst hmn; simp
    rw [if_neg hmn, if_neg (Ne.symm hmn), crossBound]
    split_ifs with h2
    · have hinv := inv_abs_logGap_le hm1 (Finset.mem_Icc.mp hn).1 hmn h2
      have he : Real.exp (5 / 2) = Real.exp (1 / 2) * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      calc 2 * Real.exp (1 / 2) * w / |logGap m n| =
            2 * Real.exp (1 / 2) * w * (1 / |logGap m n|) := by ring
        _ ≤ 2 * Real.exp (1 / 2) * w * (Real.exp 2 * m / |(n : ℝ) - m|) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = C * (1 / |(n : ℝ) - m|) := by simp only [C, he]; ring
    · positivity
  have hsub : (Icc 1 N).erase m ⊆ (range (N + 1)).erase m := fun n hn => by
    rw [mem_erase] at hn ⊢
    exact ⟨hn.1, mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn.2).2)⟩
  have hrow := RHTower.Sieve.sum_inv_abs_int_dist_le (N := N + 1) (m := m) (by omega)
  push_cast at hrow
  calc ∑ n ∈ Icc 1 N, (if m = n then 0 else crossBound w (logGap m n))
      ≤ ∑ n ∈ Icc 1 N, (if n = m then 0 else C * (1 / |(n : ℝ) - m|)) := sum_le_sum hterm
    _ = ∑ n ∈ (Icc 1 N).erase m, C * (1 / |(n : ℝ) - m|) := by
        rw [← sum_erase_add _ _ hm, if_pos rfl, add_zero]
        exact sum_congr rfl fun n hn => if_neg (ne_of_mem_erase hn)
    _ ≤ ∑ n ∈ (range (N + 1)).erase m, C * (1 / |(n : ℝ) - m|) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = C * ∑ n ∈ (range (N + 1)).erase m, 1 / |(n : ℝ) - m| := by rw [mul_sum]
    _ ≤ C * (2 * (1 + Real.log (N + 1))) := mul_le_mul_of_nonneg_left hrow hC
    _ = 4 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1)) := by simp only [C]; ring

/-! ### The Lévy energy of an atomic test -/

/-- The pointwise lower bound on `∫ (f(u) − f(u + y))²` for `y > w`: distinct atoms interact only
inside their pair windows. -/
theorem integral_sub_shift_sq_atomicTest_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) {y : ℝ}
    (hy : w < y) :
    2 * ∫ u, atomicTest N x g u ^ 2 - 2 * (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m = n then 0 else |x m| * |x n| * (pairWindow w (logGap m n)).indicator 1 y) ≤
      ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 := by
  have hf := (contDiff_atomicTest hg N x).continuous
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [integral_sub_shift_sq_eq hf hfc, integral_atomicTest_mul_shift hg.continuous hgc]
  have hG := integral_nonneg fun u => sq_nonneg (g u)
  have hpair : ∀ m n : ℕ, x m * x n * bumpCorr g (y - (Real.log n - Real.log m)) ≤
      (∫ u, g u ^ 2) *
        (if m = n then 0 else |x m| * |x n| * (pairWindow w (logGap m n)).indicator 1 y) := by
    intro m n
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, sub_self, sub_zero, bumpCorr_eq_zero hgsupp
        (by rwa [abs_of_pos (by linarith)])]
      simp
    rw [if_neg hmn]
    by_cases hwin : y ∈ pairWindow w (logGap m n)
    · rw [Set.indicator_of_mem hwin, Pi.one_apply, mul_one]
      have hb := abs_bumpCorr_le hg.continuous hgc (y - (Real.log n - Real.log m))
      calc x m * x n * bumpCorr g (y - (Real.log n - Real.log m))
          ≤ |x m * x n * bumpCorr g (y - (Real.log n - Real.log m))| := le_abs_self _
        _ = |x m| * |x n| * |bumpCorr g (y - (Real.log n - Real.log m))| := by
            rw [abs_mul, abs_mul]
        _ ≤ |x m| * |x n| * ∫ u, g u ^ 2 := mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hwin, mul_zero, mul_zero]
      have hout : w < |y - (Real.log n - Real.log m)| := by
        by_contra h
        push_neg at h
        exact hwin ⟨by linarith [(abs_le.mp h).2, logGap], by linarith [(abs_le.mp h).1, logGap]⟩
      rw [bumpCorr_eq_zero hgsupp hout, mul_zero]
  have hsum : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * bumpCorr g (y - (Real.log n - Real.log m))
      ≤ (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m = n then 0 else |x m| * |x n| * (pairWindow w (logGap m n)).indicator 1 y) := by
    rw [mul_sum]
    refine sum_le_sum fun m _ => ?_
    rw [mul_sum]
    exact sum_le_sum fun n _ => hpair m n
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
