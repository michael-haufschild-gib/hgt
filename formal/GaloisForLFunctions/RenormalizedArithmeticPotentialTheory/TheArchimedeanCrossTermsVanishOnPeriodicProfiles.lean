import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PeriodicPairSumsOfADecreasingKernelAreLinear
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheStabilityLawReachesTheSpacingUpToALogarithm
import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm

/-!
# The archimedean cross terms vanish on periodic profiles

For an atomic test `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a bump `g ≥ 0` on `[0, w]` below the
spacing, the archimedean (Lévy) energy is the self-energy of the atoms minus their interaction:

* **The exact expansion** (`levyEnergy_atomicTest_eq_cross`):
  `L(f_x) = |x|² L(g) − 2 Σ_{m<n} x_m x_n Ω(log n − log m)`, with the **cross kernel**
  `Ω(t) = ∫_0^∞ ω(s) G(s − t) ds` and `G` the autocorrelation of `g`.
* **The cross kernel** is nonnegative, decreasing in `t`, and at most `2w‖g‖²(1/t + 1)` for
  `t ≥ 4w` (`atomCrossKernel_nonneg`, `atomCrossKernel_anti`, `atomCrossKernel_le`).
* **Periodic profiles** (`abs_levyEnergy_atomicTest_sub_le_of_periodic`): for `x_n = ψ(n)/√n` with
  `ψ` `q`-periodic of mean zero and `|ψ| ≤ B`, `|L(f_x) − |x|² L(g)| ≤ 168 q B² (wN) ‖g‖²`. Since
  `|x|² ≍ log N`, the cross terms are `O(wN/log N)` per unit mass: they vanish at every fixed
  overlap ratio `wN`. On the pole `ψ = 1` they are a nonzero constant per unit mass.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### 1. The cross kernel -/

/-- The cross kernel of two atoms at log-distance `t`: `Ω(t) = ∫_0^∞ ω(s) G(s − t) ds`. -/
def atomCrossKernel (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioi 0, archLevyDensity s * bumpCorr g (s - t)

theorem archLevyDensity_anti {y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    archLevyDensity y₂ ≤ archLevyDensity y₁ := by
  unfold archLevyDensity
  have e1 : Real.exp (-y₂ / 2) ≤ Real.exp (-y₁ / 2) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-2 * y₂) ≤ Real.exp (-2 * y₁) := Real.exp_le_exp.mpr (by linarith)
  have d1 : 0 < 1 - Real.exp (-2 * y₁) := by
    have : Real.exp (-2 * y₁) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_le_div_iff₀ (by linarith) d1]
  have := Real.exp_pos (-y₂ / 2)
  nlinarith [Real.exp_pos (-y₁ / 2)]

theorem continuous_bumpCorr (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Continuous (bumpCorr g) :=
  RHTower.ArchimedeanExactForm.continuous_autocorr hg hgc

theorem bumpCorr_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ bumpCorr g t :=
  integral_nonneg fun v => mul_nonneg (hg0 v) (hg0 _)

theorem integrableOn_crossIntegrand (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) {t : ℝ} (ht : w < t) :
    IntegrableOn (fun s => archLevyDensity s * bumpCorr g (s - t)) (Set.Ioi 0) := by
  have hK : IntegrableOn (fun s => archLevyDensity s * bumpCorr g (s - t))
      (Set.Icc (t - w) (t + w)) :=
    ContinuousOn.integrableOn_Icc ((continuousOn_archLevyDensity_Ioi.mono fun s hs =>
      lt_of_lt_of_le (by linarith) hs.1).mul
        ((continuous_bumpCorr hg hgc).comp (continuous_sub_right t)).continuousOn)
  refine hK.of_forall_sdiff_eq_zero measurableSet_Ioi fun s hs => ?_
  have hs' : w < |s - t| := by
    rcases hs with ⟨-, hs2⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hs2
    rcases hs2 with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [bumpCorr_eq_zero hgsupp hs', mul_zero]

theorem atomCrossKernel_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ atomCrossKernel g t :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs =>
    mul_nonneg (archLevyDensity_pos hs).le (bumpCorr_nonneg hg0 _)

/-- The cross kernel lives on the window `[t − w, t + w]`. -/
theorem atomCrossKernel_eq_window (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w)
    {t : ℝ} (ht : w < t) :
    atomCrossKernel g t = ∫ s in Set.Icc (t - w) (t + w), archLevyDensity s * bumpCorr g (s - t) := by
  rw [atomCrossKernel]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun s (hs : s ∈ Set.Icc (t - w) (t + w)) => (lt_of_lt_of_le (by linarith) hs.1 : 0 < s))
    fun s hs => ?_
  have hs' : w < |s - t| := by
    rcases hs with ⟨-, hs2⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at hs2
    rcases hs2 with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [bumpCorr_eq_zero hgsupp hs', mul_zero]

/-- `Ω(t) ≤ 2w‖g‖²(1/t + 1)` for `t ≥ 4w`. -/
theorem atomCrossKernel_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) {t : ℝ} (ht : 4 * w ≤ t) :
    atomCrossKernel g t ≤ 2 * w * (∫ u, g u ^ 2) * (1 / t + 1) := by
  have ht' : w < t := by linarith
  have ht0 : 0 < t := by linarith
  rw [atomCrossKernel_eq_window hgsupp hw0 ht']
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg (g u)
  have hbound : ∀ s ∈ Set.Icc (t - w) (t + w),
      archLevyDensity s * bumpCorr g (s - t) ≤ (1 / t + 1) * ∫ u, g u ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by linarith) hs.1
    have h1 := archLevyDensity_le hs0
    have h2 : 1 / (2 * s) ≤ 1 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]; linarith [hs.1]
    have h3 := (abs_le.mp (abs_bumpCorr_le hg.continuous hgc (s - t))).2
    have h4 : 0 ≤ archLevyDensity s := (archLevyDensity_pos hs0).le
    calc archLevyDensity s * bumpCorr g (s - t) ≤ archLevyDensity s * ∫ u, g u ^ 2 :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ (1 / t + 1) * ∫ u, g u ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hG
  calc ∫ s in Set.Icc (t - w) (t + w), archLevyDensity s * bumpCorr g (s - t)
      ≤ ∫ _s in Set.Icc (t - w) (t + w), (1 / t + 1) * ∫ u, g u ^ 2 :=
        setIntegral_mono_on ((integrableOn_crossIntegrand hg hgc hgsupp hw0 ht').mono_set
          fun s hs => lt_of_lt_of_le (by linarith) hs.1)
          continuousOn_const.integrableOn_Icc measurableSet_Icc hbound
    _ = 2 * w * (∫ u, g u ^ 2) * (1 / t + 1) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

/-- The cross kernel in the coordinates of the bump: `Ω(t) = ∫_{−w}^{w} ω(τ + t) G(τ) dτ`. -/
theorem atomCrossKernel_eq_shift (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w)
    {t : ℝ} (ht : w < t) :
    atomCrossKernel g t = ∫ τ in Set.Icc (-w) w, archLevyDensity (τ + t) * bumpCorr g τ := by
  have hzero : ∀ s, s ∉ Set.Ioi 0 → archLevyDensity s * bumpCorr g (s - t) = 0 := fun s hs => by
    have : w < |s - t| := by
      rw [abs_sub_comm, abs_of_pos (by simp only [Set.mem_Ioi, not_lt] at hs; linarith)]
      simp only [Set.mem_Ioi, not_lt] at hs; linarith
    rw [bumpCorr_eq_zero hgsupp this, mul_zero]
  rw [atomCrossKernel, setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← integral_add_right_eq_self (fun s => archLevyDensity s * bumpCorr g (s - t)) t]
  simp only [add_sub_cancel_right]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_).symm
  have : w < |τ| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hτ
    rcases hτ with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  rw [bumpCorr_eq_zero hgsupp this, mul_zero]

/-- The cross kernel decreases in the log-distance. -/
theorem atomCrossKernel_anti (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hw0 : 0 < w) {t₁ t₂ : ℝ}
    (h1 : w < t₁) (h12 : t₁ ≤ t₂) : atomCrossKernel g t₂ ≤ atomCrossKernel g t₁ := by
  rw [atomCrossKernel_eq_shift hgsupp hw0 (by linarith), atomCrossKernel_eq_shift hgsupp hw0 h1]
  have hint : ∀ t, w < t → IntegrableOn (fun τ => archLevyDensity (τ + t) * bumpCorr g τ)
      (Set.Icc (-w) w) := fun t ht =>
    ContinuousOn.integrableOn_Icc ((continuousOn_archLevyDensity_Ioi.comp
      (continuous_add_const t).continuousOn fun τ hτ => by
        simp only [Set.mem_Ioi]; linarith [hτ.1]).mul (continuous_bumpCorr hg hgc).continuousOn)
  refine setIntegral_mono_on (hint t₂ (by linarith)) (hint t₁ h1) measurableSet_Icc fun τ hτ => ?_
  exact mul_le_mul_of_nonneg_right (archLevyDensity_anti (by linarith [hτ.1]) (by linarith))
    (bumpCorr_nonneg hg0 τ)

/-! ### 2. The exact expansion -/

/-- **The Lévy energy of an atomic test**, below the spacing:
`L(f_x) = |x|² L(g) − 2 Σ_{m<n} x_m x_n Ω(log n − log m)`. -/
theorem levyEnergy_atomicTest_eq_cross (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    levyEnergy (atomicTest N x g) = (∑ n ∈ Icc 1 N, x n ^ 2) * levyEnergy g -
      2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if m < n then x m * x n * atomCrossKernel g (Real.log n - Real.log m) else 0) := by
  set f := atomicTest N x g
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  -- the gaps exceed the width
  have hgap : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m < n → w < Real.log n - Real.log m := by
    intro m hm n hn hmn
    have := atomSpacing_le_abs_logGap hm hn (by omega)
    rw [logGap, abs_of_pos (by
      have h1 : (m : ℝ) < n := by exact_mod_cast hmn
      have h0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      linarith [Real.log_lt_log h0 h1])] at this
    linarith
  -- the shift expansion, pair by pair
  have hpair : ∀ s, 0 < s → ∀ m ∈ Icc 1 N,
      ∑ n ∈ Icc 1 N, x m * x n * bumpCorr g (s - (Real.log n - Real.log m)) =
        x m ^ 2 * bumpCorr g s +
          ∑ n ∈ Icc 1 N, (if m < n then x m * x n * bumpCorr g (s - (Real.log n - Real.log m))
            else 0) := by
    intro s hs m hm
    have hterm : ∀ n ∈ Icc 1 N, x m * x n * bumpCorr g (s - (Real.log n - Real.log m)) =
        (if n = m then x m ^ 2 * bumpCorr g s else 0) +
          (if m < n then x m * x n * bumpCorr g (s - (Real.log n - Real.log m)) else 0) := by
      intro n hn
      rcases lt_trichotomy n m with hnm | rfl | hmn
      · rw [if_neg (by omega), if_neg (by omega), zero_add]
        have h := hgap n hn m hm hnm
        rw [bumpCorr_eq_zero hgsupp (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
      · rw [if_pos rfl, if_neg (lt_irrefl _), add_zero, sub_self, sub_zero]; ring
      · rw [if_neg (by omega), if_pos hmn, zero_add]
    rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq' (Icc 1 N) m, if_pos hm]
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ), archLevyDensity s * ∫ u, (f u - f (u + s)) ^ 2 =
      (∑ n ∈ Icc 1 N, x n ^ 2) * (archLevyDensity s * ∫ u, (g u - g (u + s)) ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
          x m * x n * (archLevyDensity s * bumpCorr g (s - (Real.log n - Real.log m))) else 0) := by
    intro s hs
    have hcross : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
        x m * x n * (archLevyDensity s * bumpCorr g (s - (Real.log n - Real.log m))) else 0) =
        archLevyDensity s * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
          x m * x n * bumpCorr g (s - (Real.log n - Real.log m)) else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [integral_sub_shift_sq_eq hf.continuous hfc s, integral_sub_shift_sq_eq hg.continuous hgc s,
      integral_atomicTest_sq hg hgc hgsupp hw x,
      SpacingScaleHarmonicAnalysis.integral_atomicTest_mul_shift hg.continuous hgc N x s,
      sum_congr rfl (hpair s hs), sum_add_distrib, ← sum_mul,
      show ∫ u, g u * g (u + s) = bumpCorr g s from rfl, hcross]
    ring
  rw [levyEnergy, setIntegral_congr_fun measurableSet_Ioi hpt]
  have hI1 : IntegrableOn (fun s => archLevyDensity s * ∫ u, (g u - g (u + s)) ^ 2) (Set.Ioi 0) :=
    integrableOn_levyIntegrand hg hgc
  have hI2 : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, IntegrableOn (fun s => if m < n then
      x m * x n * (archLevyDensity s * bumpCorr g (s - (Real.log n - Real.log m))) else 0)
      (Set.Ioi 0) := by
    intro m hm n hn
    by_cases hmn : m < n
    · simp only [hmn, if_true]
      exact (integrableOn_crossIntegrand hg hgc hgsupp hw0 (hgap m hm n hn hmn)).const_mul _
    · simp only [hmn, if_false]
      exact integrableOn_zero
  rw [integral_sub (hI1.const_mul _) ((integrable_finsetSum _ fun m hm =>
      integrable_finsetSum _ fun n hn => hI2 m hm n hn).const_mul _),
    integral_const_mul, integral_const_mul, ← levyEnergy,
    integral_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn => hI2 m hm n hn]
  congr 2
  refine sum_congr rfl fun m hm => ?_
  rw [integral_finsetSum _ fun n hn => hI2 m hm n hn]
  refine sum_congr rfl fun n _ => ?_
  split_ifs
  · rw [integral_const_mul, atomCrossKernel]
  · simp

/-! ### 3. Periodic profiles -/

/-- **The archimedean cross terms vanish on periodic profiles.** For `x_n = ψ(n)/√n` with `ψ`
`q`-periodic of mean zero, `|ψ| ≤ B`, and a bump `g ≥ 0` on `[0, w]`, `4w ≤ δ_N`:
`|L(f_x) − |x|² L(g)| ≤ 168 q B² (wN) ‖g‖²`. -/
theorem abs_levyEnergy_atomicTest_sub_le_of_periodic (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u)
    {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : 4 * w ≤ atomSpacing N) {q : ℕ} (hq : 1 ≤ q) {B : ℝ}
    (ψ : ℕ → ℝ) (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hB : ∀ n, |ψ n| ≤ B) :
    |levyEnergy (atomicTest N (fun n => ψ n / Real.sqrt n) g) -
        (∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) * levyEnergy g| ≤
      168 * q * B ^ 2 * (w * N) * ∫ u, g u ^ 2 := by
  have hδw : w < atomSpacing N := by linarith
  rw [levyEnergy_atomicTest_eq_cross hg hgc hgsupp hN hw0 hδw]
  set Φ : ℝ → ℝ := fun t => atomCrossKernel g (max t (atomSpacing N))
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg (g u)
  have hS : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
      ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * atomCrossKernel g (Real.log n - Real.log m) else 0) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
        ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * Φ (Real.log n - Real.log m) else 0) := by
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    split_ifs with hmn
    · have := atomSpacing_le_abs_logGap hm hn (by omega)
      rw [logGap, abs_of_pos (by
        have h1 : (m : ℝ) < n := by exact_mod_cast hmn
        have h0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
        linarith [Real.log_lt_log h0 h1])] at this
      show _ = _ * atomCrossKernel g (max (Real.log n - Real.log m) (atomSpacing N))
      rw [max_eq_left this]
    · rfl
  have hpair := abs_sum_periodicPair_le hq (N := N) (A := 2 * w * ∫ u, g u ^ 2) (by positivity) ψ
    hper hmean hB Φ (fun t _ => atomCrossKernel_nonneg hg0 _)
    (fun t ht => by
      have h1 := atomCrossKernel_le hg hgc hgsupp hw0 (t := max t (atomSpacing N))
        (le_trans hw (le_max_right _ _))
      have h2 : 1 / max t (atomSpacing N) ≤ 1 / t := one_div_le_one_div_of_le ht (le_max_left _ _)
      refine h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
    (fun t₁ t₂ _ h12 => atomCrossKernel_anti hg hgc hgsupp hg0 hw0
      (lt_of_lt_of_le hδw (le_max_right _ _)) (max_le_max h12 le_rfl))
  rw [← hS] at hpair
  rw [sub_sub_cancel_left, abs_neg, abs_mul, abs_two]
  calc 2 * |∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m < n then
          ψ m / Real.sqrt m * (ψ n / Real.sqrt n) * atomCrossKernel g (Real.log n - Real.log m)
            else 0)| ≤ 2 * (42 * q * B ^ 2 * (2 * w * ∫ u, g u ^ 2) * N) :=
        mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = 168 * q * B ^ 2 * (w * N) * ∫ u, g u ^ 2 := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
