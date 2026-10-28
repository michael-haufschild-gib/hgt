import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel

/-!
# The finite part of the Markov form at the spacing scale

Let `f = Σ_{n ≤ N} x_n g(· − log n)` with the atom `g = φ(·/w)` of a profile `φ` on `[0, 1]`, at
width `w ≤ δ_N/2`. Its Markov form is `M(f) = 2θ′(0)‖f‖² + levyEnergy f − ‖g‖² P_N(x)`. This file
computes its ground energy at the spacing scale up to `O(wN) + o(1)`:

  `M(f) ≥ (2θ′(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2) w − A·wN) ‖f‖²`

eventually in `N`, for `wN ≤ 1/(64e²)`, and the pole vector attains it up to `ε` for nonnegative
profiles. So the finite part of the Markov form is the Robin constant `κ_L(φ)` of the atom
(`TheRobinConstantOfAnAtom`) plus the Euler constant `γ` of the pole (`ThePoleIsTheTopOfThePrimeForm`).

* **The Lévy energy with its diagonal** (`levyEnergy_atomicTest_ge_diag`,
  `levyEnergy_atomicTest_le_diag`): `levyEnergy f = Σ x_m² levyEnergy g − 2 Σ_{m ≠ n} x_m x_n
  ∫ ω(y) G(y − log(n/m)) dy`; the pair `(m, n)` is seen only through the window
  `|y − log(n/m)| ≤ w`, which carries at most `2w(1/|log(n/m)| + 1)` of the density `ω`.
* **The rows** (`sum_inv_abs_logGap_add_one_le`): `Σ_{n ≠ m} (1/|log(n/m)| + 1) ≤
  2e² m (1 + log(N + 1)) + (3/2) N`.
* **The cross terms are paid in mean square** (`cross_penalty_le`): the rows grow like
  `(m/N) log N` at width `w ≍ 1/N`, so pointwise they are unbounded on the top atoms; the pole
  defect pays exactly these (`sum_top_le_poleDefect`), and the Markov form keeps
  `(1 − ε − 32e² wN) D_N ≥ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset RHTower
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### 1. The Lévy density off the origin -/

theorem continuousOn_archLevyDensity_Ioi : ContinuousOn archLevyDensity (Set.Ioi 0) := by
  intro y hy
  have hy0 : (0 : ℝ) < y := hy
  have h2 : 1 - Real.exp (-2 * y) ≠ 0 := by
    have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  unfold archLevyDensity
  exact (((by fun_prop : Continuous fun y : ℝ => Real.exp (-y / 2)).continuousAt).div
    ((by fun_prop : Continuous fun y : ℝ => 1 - Real.exp (-2 * y)).continuousAt) h2).continuousWithinAt

theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

/-- `ω(y) ≤ 1/(2y) + 1` for every `y > 0`. -/
theorem archLevyDensity_le_inv_add_one {y : ℝ} (hy : 0 < y) :
    archLevyDensity y ≤ 1 / (2 * y) + 1 := by
  have he : Real.exp (1 / 2) / 4 ≤ 1 / 2 := by linarith [exp_half_lt_two]
  rcases le_or_gt y 1 with h1 | h1
  · linarith [SpacingScaleHarmonicAnalysis.archLevyDensity_le_inv_two_mul_add hy h1]
  · have hmono := SpacingScaleHarmonicAnalysis.archLevyDensity_antitoneOn
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show y ∈ Set.Ioi 0 from hy) h1.le
    have hone := SpacingScaleHarmonicAnalysis.archLevyDensity_le_inv_two_mul_add
      (by norm_num : (0 : ℝ) < 1) le_rfl
    have : 0 ≤ 1 / (2 * y) := by positivity
    linarith

/-- **A pair window off the origin** is integrable against `ω` on `(0, ∞)` and carries at most
`2w(1/|s| + 1)` of it, for `|s| ≥ 2w`. -/
theorem window_integrable_and_le {s : ℝ} (hw : 0 < w) (hs : 2 * w ≤ |s|) :
    IntegrableOn ((Set.Icc (s - w) (s + w)).indicator archLevyDensity) (Set.Ioi 0) ∧
      ∫ y in Set.Ioi 0, (Set.Icc (s - w) (s + w)).indicator archLevyDensity y ≤
        2 * w * (1 / |s| + 1) := by
  have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hs; linarith
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · -- the window lies left of the origin
    rw [abs_of_neg hneg] at hs
    have hzero : ∀ y ∈ Set.Ioi (0 : ℝ),
        (Set.Icc (s - w) (s + w)).indicator archLevyDensity y = 0 := by
      intro y hy
      refine Set.indicator_of_notMem (fun hmem => ?_) _
      have : (0 : ℝ) < y := hy
      linarith [hmem.2]
    refine ⟨integrableOn_zero.congr_fun (fun y hy => (hzero y hy).symm) measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]
    have : 0 < |s| := abs_pos.mpr hs0
    positivity
  · rw [abs_of_pos hpos] at hs ⊢
    have ha : 0 < s - w := by linarith
    have hsub : Set.Icc (s - w) (s + w) ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
    have hint : IntegrableOn archLevyDensity (Set.Icc (s - w) (s + w)) :=
      (continuousOn_archLevyDensity_Ioi.mono hsub).integrableOn_Icc
    have hglob : Integrable ((Set.Icc (s - w) (s + w)).indicator archLevyDensity) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hint
    refine ⟨hglob.integrableOn, ?_⟩
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub]
    have hbound : ∀ y ∈ Set.Icc (s - w) (s + w), archLevyDensity y ≤ archLevyDensity (s - w) :=
      fun y hy => SpacingScaleHarmonicAnalysis.archLevyDensity_antitoneOn
        (show s - w ∈ Set.Ioi 0 from ha) (hsub hy) hy.1
    have hle : ∫ y in Set.Icc (s - w) (s + w), archLevyDensity y ≤
        ∫ _ in Set.Icc (s - w) (s + w), archLevyDensity (s - w) :=
      setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Icc hbound
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
    have hω := archLevyDensity_le_inv_add_one ha
    have hinv : 1 / (2 * (s - w)) ≤ 1 / s :=
      one_div_le_one_div_of_le hpos (by linarith)
    have hω0 : 0 ≤ archLevyDensity (s - w) := (archLevyDensity_pos ha).le
    nlinarith

/-! ### 2. The Lévy energy of an atomic test with its diagonal -/

/-- `Σ_n F n = F m + Σ_{n ≠ m} F n`. -/
theorem sum_eq_diag_add {s : Finset ℕ} {m : ℕ} (hm : m ∈ s) (F : ℕ → ℝ) :
    ∑ n ∈ s, F n = F m + ∑ n ∈ s, (if m = n then 0 else F n) := by
  have h : ∀ n, F n = (if m = n then F n else 0) + (if m = n then 0 else F n) := fun n => by
    split_ifs <;> simp
  rw [sum_congr rfl (fun n _ => h n), sum_add_distrib, sum_ite_eq, if_pos hm]

/-- **The shifted energy with its diagonal**: `∫ (f − f(·+y))² = Σ x_m² ∫ (g − g(·+y))² −
2 Σ_{m ≠ n} x_m x_n G(y − log(n/m))`. -/
theorem integral_sub_shift_sq_atomicTest_eq (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ)
    (y : ℝ) :
    ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 =
      ∑ m ∈ Icc 1 N, x m ^ 2 * (∫ u, (g u - g (u + y)) ^ 2) -
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          x m * x n * SpacingScaleHarmonicAnalysis.bumpCorr g (y - (Real.log n - Real.log m))) := by
  have hf := (contDiff_atomicTest hg N x).continuous
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  set G := SpacingScaleHarmonicAnalysis.bumpCorr g
  set M := ∫ u, g u ^ 2
  rw [SpacingScaleHarmonicAnalysis.integral_sub_shift_sq_eq hf hfc,
    SpacingScaleHarmonicAnalysis.integral_atomicTest_mul_shift hg.continuous hgc,
    integral_atomicTest_sq hg hgc hgsupp hw]
  have hself : ∀ m ∈ Icc 1 N, x m ^ 2 * ∫ u, (g u - g (u + y)) ^ 2 =
      2 * (x m ^ 2 * M) - 2 * (x m * x m * G (y - (Real.log m - Real.log m))) := by
    intro m _
    rw [SpacingScaleHarmonicAnalysis.integral_sub_shift_sq_eq hg.continuous hgc, sub_self,
      sub_zero]
    simp only [G, SpacingScaleHarmonicAnalysis.bumpCorr, M]
    ring
  have hdiag : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * G (y - (Real.log n - Real.log m)) =
      ∑ m ∈ Icc 1 N, x m * x m * G (y - (Real.log m - Real.log m)) +
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          x m * x n * G (y - (Real.log n - Real.log m))) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m hm => sum_eq_diag_add hm _
  have hS : ∑ m ∈ Icc 1 N, x m ^ 2 * ∫ u, (g u - g (u + y)) ^ 2 =
      2 * ((∑ m ∈ Icc 1 N, x m ^ 2) * M) -
        2 * ∑ m ∈ Icc 1 N, x m * x m * G (y - (Real.log m - Real.log m)) := by
    rw [sum_congr rfl hself, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_mul]
  rw [hdiag, hS]
  ring

/-- **Lower bound on the Lévy energy of an atomic test.** With the diagonal kept exactly,
`levyEnergy f ≥ Σ x_m² levyEnergy g − 2‖g‖² Σ_{m ≠ n} |x_m| |x_n| · 2w(1/|log(n/m)| + 1)`. -/
theorem levyEnergy_atomicTest_ge_diag (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) (x : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, x m ^ 2) * levyEnergy g -
        2 * (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
          |x m| * |x n| * (2 * w * (1 / |Real.log n - Real.log m| + 1))) ≤
      levyEnergy (atomicTest N x g) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  set M := ∫ u, g u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  set G := SpacingScaleHarmonicAnalysis.bumpCorr g
  set ω := archLevyDensity
  set win : ℕ → ℕ → Set ℝ := fun m n =>
    Set.Icc (Real.log n - Real.log m - w) (Real.log n - Real.log m + w)
  -- distinct atoms are at log-distance at least `δ_N ≥ 2w`
  have hsep : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → 2 * w ≤ |Real.log n - Real.log m| := by
    intro m hm n hn hmn
    have := SpacingScaleHarmonicAnalysis.atomSpacing_le_abs_logGap hm hn hmn
    simp only [SpacingScaleHarmonicAnalysis.logGap] at this
    linarith
  have hwin : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n →
      IntegrableOn ((win m n).indicator ω) (Set.Ioi 0) ∧
        ∫ y in Set.Ioi 0, (win m n).indicator ω y ≤
          2 * w * (1 / |Real.log n - Real.log m| + 1) :=
    fun m hm n hn hmn => window_integrable_and_le hw0 (hsep m hm n hn hmn)
  set c : ℕ → ℕ → ℝ → ℝ := fun m n y =>
    if m = n then 0 else |x m| * |x n| * (win m n).indicator ω y
  have hcint : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, IntegrableOn (c m n) (Set.Ioi 0) := by
    intro m hm n hn
    by_cases hmn : m = n
    · simp only [c, if_pos hmn]; exact integrableOn_zero
    · simp only [c, if_neg hmn]; exact (hwin m hm n hn hmn).1.const_mul _
  have hgint := integrableOn_levyIntegrand hg hgc
  set ℓ : ℝ → ℝ := fun y => (∑ m ∈ Icc 1 N, x m ^ 2) * (ω y * ∫ u, (g u - g (u + y)) ^ 2) -
    2 * M * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n y
  have hcsum : IntegrableOn (fun y => ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n y) (Set.Ioi 0) :=
    integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun n hn => hcint m hm n hn
  have hℓint : IntegrableOn ℓ (Set.Ioi 0) :=
    (hgint.const_mul _).sub (hcsum.const_mul _)
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  -- pointwise in the shift
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ),
      ℓ y ≤ ω y * ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 := by
    intro y hy
    have hω0 : 0 ≤ ω y := (archLevyDensity_pos hy).le
    rw [integral_sub_shift_sq_atomicTest_eq hg hgc hgsupp hw' x y]
    have hpair : ∀ m n, (if m = n then 0 else ω y * (x m * x n * G (y - (Real.log n - Real.log m))))
        ≤ M * c m n y := by
      intro m n
      by_cases hmn : m = n
      · simp [c, hmn]
      simp only [c, if_neg hmn]
      by_cases hmem : y ∈ win m n
      · rw [Set.indicator_of_mem hmem]
        have hb := SpacingScaleHarmonicAnalysis.abs_bumpCorr_le hg.continuous hgc
          (y - (Real.log n - Real.log m))
        have h1 : x m * x n * G (y - (Real.log n - Real.log m)) ≤ |x m| * |x n| * M := by
          calc x m * x n * G (y - (Real.log n - Real.log m))
              ≤ |x m * x n * G (y - (Real.log n - Real.log m))| := le_abs_self _
            _ = |x m| * |x n| * |G (y - (Real.log n - Real.log m))| := by rw [abs_mul, abs_mul]
            _ ≤ |x m| * |x n| * M := mul_le_mul_of_nonneg_left hb (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left h1 hω0]
      · rw [Set.indicator_of_notMem hmem, mul_zero, mul_zero]
        have hout : w < |y - (Real.log n - Real.log m)| := by
          by_contra h
          obtain ⟨h1, h2⟩ := abs_le.mp (not_lt.mp h)
          exact hmem ⟨by linarith, by linarith⟩
        have hz : G (y - (Real.log n - Real.log m)) = 0 :=
          SpacingScaleHarmonicAnalysis.bumpCorr_eq_zero hgsupp hout
        rw [hz, mul_zero, mul_zero]
    have hsum : ω y * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        x m * x n * G (y - (Real.log n - Real.log m))) ≤
        M * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m n y := by
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun m _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_le_sum fun n _ => ?_
      have := hpair m n
      split_ifs at this ⊢ with hmn
      · simp [c, hmn]
      · exact this
    simp only [ℓ]
    have hdiag : ω y * ∑ m ∈ Icc 1 N, x m ^ 2 * (∫ u, (g u - g (u + y)) ^ 2) =
        (∑ m ∈ Icc 1 N, x m ^ 2) * (ω y * ∫ u, (g u - g (u + y)) ^ 2) := by
      rw [mul_sum, sum_mul]; exact sum_congr rfl fun m _ => by ring
    nlinarith [hdiag, hsum]
  have hLint : IntegrableOn
      (fun y => ω y * ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2) (Set.Ioi 0) :=
    integrableOn_levyIntegrand hf hfc
  have hmono := setIntegral_mono_on hℓint hLint measurableSet_Ioi hpt
  -- integrate the lower bound
  have hℓ : ∫ y in Set.Ioi 0, ℓ y = (∑ m ∈ Icc 1 N, x m ^ 2) * levyEnergy g -
      2 * M * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ y in Set.Ioi 0, c m n y := by
    simp only [ℓ]
    rw [integral_sub (hgint.const_mul _) (hcsum.const_mul _), integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun m hm =>
        integrable_finsetSum _ fun n hn => hcint m hm n hn]
    unfold levyEnergy
    congr 2
    exact sum_congr rfl fun m hm => integral_finsetSum _ fun n hn => hcint m hm n hn
  have hcbound : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∫ y in Set.Ioi 0, c m n y ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        |x m| * |x n| * (2 * w * (1 / |Real.log n - Real.log m| + 1))) := by
    refine sum_le_sum fun m hm => sum_le_sum fun n hn => ?_
    by_cases hmn : m = n
    · simp [c, hmn]
    simp only [c, if_neg hmn]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hwin m hm n hn hmn).2 (by positivity)
  rw [hℓ] at hmono
  have hL : levyEnergy (atomicTest N x g) = ∫ y in Set.Ioi 0,
      ω y * ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 := rfl
  nlinarith [mul_le_mul_of_nonneg_left hcbound (by positivity : (0 : ℝ) ≤ 2 * M)]

/-- **Upper bound for nonnegative atoms**: if `g ≥ 0` and `x ≥ 0`, the atoms only lower each
other's energy, `levyEnergy f ≤ Σ x_m² levyEnergy g`. -/
theorem levyEnergy_atomicTest_le_diag (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) :
    levyEnergy (atomicTest N x g) ≤ (∑ m ∈ Icc 1 N, x m ^ 2) * levyEnergy g := by
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hgint := integrableOn_levyIntegrand hg hgc
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ),
      archLevyDensity y * ∫ u, (atomicTest N x g u - atomicTest N x g (u + y)) ^ 2 ≤
        (∑ m ∈ Icc 1 N, x m ^ 2) * (archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2) := by
    intro y hy
    have hω0 : 0 ≤ archLevyDensity y := (archLevyDensity_pos hy).le
    rw [integral_sub_shift_sq_atomicTest_eq hg hgc hgsupp hw x y]
    have hcross : 0 ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        x m * x n * SpacingScaleHarmonicAnalysis.bumpCorr g (y - (Real.log n - Real.log m))) := by
      refine sum_nonneg fun m _ => sum_nonneg fun n _ => ?_
      split_ifs
      · exact le_rfl
      · refine mul_nonneg (mul_nonneg (hx m) (hx n)) ?_
        exact integral_nonneg fun v => mul_nonneg (hg0 v) (hg0 _)
    rw [sum_mul]
    have hdiag : ∑ m ∈ Icc 1 N, x m ^ 2 * (archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2) =
        archLevyDensity y * ∑ m ∈ Icc 1 N, x m ^ 2 * ∫ u, (g u - g (u + y)) ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
    rw [hdiag]
    nlinarith [mul_nonneg hω0 hcross]
  have h := setIntegral_mono_on (integrableOn_levyIntegrand hf hfc) (hgint.const_mul _)
    measurableSet_Ioi hpt
  rw [integral_const_mul] at h
  unfold levyEnergy
  exact h

/-! ### 3. The rows of the cross kernel -/

/-- **The rows**: `Σ_{n ≠ m} (1/|log n − log m| + 1) ≤ 2e² m (1 + log(N + 1)) + (3/2) N`. -/
theorem sum_inv_abs_logGap_add_one_le {N m : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m| + 1) ≤
      2 * Real.exp 2 * m * (1 + Real.log (N + 1)) + 3 / 2 * N := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  set C : ℝ := Real.exp 2 * m
  have hC : 0 ≤ C := by positivity
  have hterm : ∀ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m| + 1) ≤
      (if n = m then 0 else C * (1 / |(n : ℝ) - m|)) + 3 / 2 := by
    intro n hn
    by_cases hmn : m = n
    · subst hmn; norm_num
    rw [if_neg hmn, if_neg (Ne.symm hmn)]
    have hn1 := (Finset.mem_Icc.mp hn).1
    by_cases h2 : |SpacingScaleHarmonicAnalysis.logGap m n| ≤ 2
    · have hinv := SpacingScaleHarmonicAnalysis.inv_abs_logGap_le hm1 hn1 hmn h2
      simp only [SpacingScaleHarmonicAnalysis.logGap] at hinv
      have : Real.exp 2 * m / |(n : ℝ) - m| = C * (1 / |(n : ℝ) - m|) := by ring
      linarith
    · replace h2 := not_le.mp h2
      simp only [SpacingScaleHarmonicAnalysis.logGap] at h2
      have hpos : 0 < |Real.log n - Real.log m| := by linarith
      have : 1 / |Real.log n - Real.log m| ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) h2.le
      have : 0 ≤ C * (1 / |(n : ℝ) - m|) := by positivity
      linarith
  have hsub : (Icc 1 N).erase m ⊆ (range (N + 1)).erase m := fun n hn => by
    rw [mem_erase] at hn ⊢
    exact ⟨hn.1, mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn.2).2)⟩
  have hrow := RHTower.Sieve.sum_inv_abs_int_dist_le (N := N + 1) (m := m) (by omega)
  push_cast at hrow
  have hharm : ∑ n ∈ Icc 1 N, (if n = m then 0 else C * (1 / |(n : ℝ) - m|)) ≤
      C * (2 * (1 + Real.log (N + 1))) := by
    calc ∑ n ∈ Icc 1 N, (if n = m then 0 else C * (1 / |(n : ℝ) - m|))
        = ∑ n ∈ (Icc 1 N).erase m, C * (1 / |(n : ℝ) - m|) := by
          rw [← sum_erase_add _ _ hm, if_pos rfl, add_zero]
          exact sum_congr rfl fun n hn => if_neg (ne_of_mem_erase hn)
      _ ≤ ∑ n ∈ (range (N + 1)).erase m, C * (1 / |(n : ℝ) - m|) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = C * ∑ n ∈ (range (N + 1)).erase m, 1 / |(n : ℝ) - m| := by rw [mul_sum]
      _ ≤ C * (2 * (1 + Real.log (N + 1))) := mul_le_mul_of_nonneg_left hrow hC
  have hconst : ∑ n ∈ Icc 1 N, (3 / 2 : ℝ) = 3 / 2 * N := by
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m| + 1)
      ≤ ∑ n ∈ Icc 1 N, ((if n = m then 0 else C * (1 / |(n : ℝ) - m|)) + 3 / 2) :=
        sum_le_sum hterm
    _ = ∑ n ∈ Icc 1 N, (if n = m then 0 else C * (1 / |(n : ℝ) - m|)) + 3 / 2 * N := by
        rw [sum_add_distrib, hconst]
    _ ≤ C * (2 * (1 + Real.log (N + 1))) + 3 / 2 * N := by linarith
    _ = 2 * Real.exp 2 * m * (1 + Real.log (N + 1)) + 3 / 2 * N := by simp only [C]; ring

/-- **Symmetric Schur test**: `Σ_{m ≠ n} |x_m| |x_n| k_{mn} ≤ Σ_m x_m² Σ_{n ≠ m} k_{mn}` for a
symmetric nonnegative `k`. -/
theorem sum_abs_mul_sym_le (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℕ → ℝ) (hk : ∀ m n, 0 ≤ k m n)
    (hks : ∀ m n, k n m = k m n) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |x m| * |x n| * k m n) ≤
      ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, (if m = n then 0 else k m n) := by
  set B : ℕ → ℕ → ℝ := fun m n => if m = n then 0 else k m n
  have hBs : ∀ m n, B n m = B m n := fun m n => by
    simp only [B]
    by_cases h : m = n
    · subst h; rfl
    · rw [if_neg (Ne.symm h), if_neg h, hks]
  have hpt : ∀ m n, (if m = n then 0 else |x m| * |x n| * k m n) ≤
      (x m ^ 2 * B m n + x n ^ 2 * B n m) / 2 := fun m n => by
    rw [hBs m n]
    have hle : |x m| * |x n| ≤ (x m ^ 2 + x n ^ 2) / 2 := by
      nlinarith [sq_nonneg (|x m| - |x n|), sq_abs (x m), sq_abs (x n)]
    simp only [B]
    split_ifs
    · simp
    · nlinarith [hk m n]
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else |x m| * |x n| * k m n)
      ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (x m ^ 2 * B m n + x n ^ 2 * B n m) / 2 :=
        sum_le_sum fun m _ => sum_le_sum fun n _ => hpt m n
    _ = ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, B m n := by
        have hswap : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x n ^ 2 * B n m =
            ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m ^ 2 * B m n := sum_comm
        simp only [← sum_div, sum_add_distrib, hswap, mul_sum]
        ring

/-- `(m/N) log N ≤ 2 (m/N) log m + 2` for `1 ≤ m ≤ N`. -/
theorem div_mul_log_le {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (m : ℝ) / N * Real.log N ≤ 2 * ((m : ℝ) / N * Real.log m) + 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hr0 : 0 ≤ (m : ℝ) / N := by positivity
  by_cases hsq : (N : ℝ) ≤ (m : ℝ) ^ 2
  · have : Real.log N ≤ 2 * Real.log m := by
      have h := Real.log_le_log hN0 (by exact_mod_cast hsq : (N : ℝ) ≤ (m : ℝ) ^ 2)
      rw [Real.log_pow] at h; push_cast at h; exact h
    nlinarith [mul_le_mul_of_nonneg_left this hr0]
  · replace hsq := not_le.mp hsq
    -- `m < √N` and `log N ≤ 2√N`
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have hms : (m : ℝ) < Real.sqrt N := by
      rw [show (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) by rw [Real.sqrt_sq hm0.le]]
      exact Real.sqrt_lt_sqrt (by positivity) hsq
    have hlog : Real.log N ≤ 2 * Real.sqrt N := by
      have h1 := Real.log_le_sub_one_of_pos hsN
      have h2 : Real.log N = 2 * Real.log (Real.sqrt N) := by
        rw [← Real.log_rpow hsN, Real.rpow_two, Real.sq_sqrt hN0.le]
      linarith
    have hNs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have : (m : ℝ) / N * Real.log N ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      nlinarith [mul_le_mul_of_nonneg_left hlog hm0.le, mul_le_mul_of_nonneg_right hms.le hsN.le]
    nlinarith [mul_nonneg hr0 hlogm]

/-- **The cross terms are paid in mean square**: for `w > 0`,
`Σ_{m ≠ n} |x_m| |x_n| 2w(1/|log(n/m)| + 1) ≤ wN ((16e² + 3 + 16e²(log 4 + 4))|x|² + 16e² D_N(x))`. -/
theorem cross_penalty_le {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (x : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        |x m| * |x n| * (2 * w * (1 / |Real.log n - Real.log m| + 1))) ≤
      w * N * ((16 * Real.exp 2 + 3 + 16 * Real.exp 2 * (Real.log 4 + 4)) *
        ∑ n ∈ Icc 1 N, x n ^ 2 + 16 * Real.exp 2 * poleDefect N x) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hk : ∀ m n : ℕ, 0 ≤ 2 * w * (1 / |Real.log n - Real.log m| + 1) := fun m n => by
    positivity
  have hks : ∀ m n : ℕ, 2 * w * (1 / |Real.log m - Real.log n| + 1) =
      2 * w * (1 / |Real.log n - Real.log m| + 1) := fun m n => by rw [abs_sub_comm]
  have hschur := sum_abs_mul_sym_le N x (fun m n => 2 * w * (1 / |Real.log n - Real.log m| + 1))
    hk hks
  -- each row is at most `w N ((16e² + 3) + 8e² (m/N) log m)`
  have hrow : ∀ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N,
      (if m = n then 0 else 2 * w * (1 / |Real.log n - Real.log m| + 1)) ≤
      w * N * ((16 * Real.exp 2 + 3) * x m ^ 2 +
        8 * Real.exp 2 * ((m : ℝ) / N * Real.log m * x m ^ 2)) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hsum : ∑ n ∈ Icc 1 N,
        (if m = n then 0 else 2 * w * (1 / |Real.log n - Real.log m| + 1)) =
        2 * w * ∑ n ∈ Icc 1 N, (if m = n then 0 else 1 / |Real.log n - Real.log m| + 1) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by split_ifs <;> ring
    rw [hsum]
    have hr := sum_inv_abs_logGap_add_one_le hm
    -- `log(N + 1) ≤ 1 + log N`
    have hlogN1 : Real.log (N + 1) ≤ 1 + Real.log N := by
      have h2N : ((N : ℝ) + 1) ≤ 2 * N := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hN0.ne'] at this
      have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hdm := div_mul_log_le hm1 hmN
    have hr0 : 0 ≤ (m : ℝ) / N := by positivity
    -- `(m/N)(1 + log(N + 1)) ≤ 4 + 2 (m/N) log m`
    have hmN' : (m : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hmN)
    have hkey : (m : ℝ) / N * (1 + Real.log (N + 1)) ≤ 4 + 2 * ((m : ℝ) / N * Real.log m) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogN1 hr0]
    have hxm := sq_nonneg (x m)
    have hbound : 2 * w * (2 * Real.exp 2 * m * (1 + Real.log (N + 1)) + 3 / 2 * N) =
        w * N * (4 * Real.exp 2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 3) := by
      field_simp; ring
    calc x m ^ 2 * (2 * w * ∑ n ∈ Icc 1 N,
          (if m = n then 0 else 1 / |Real.log n - Real.log m| + 1))
        ≤ x m ^ 2 * (2 * w * (2 * Real.exp 2 * m * (1 + Real.log (N + 1)) + 3 / 2 * N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity)) hxm
      _ = x m ^ 2 * (w * N * (4 * Real.exp 2 * ((m : ℝ) / N * (1 + Real.log (N + 1))) + 3)) := by
          rw [hbound]
      _ ≤ x m ^ 2 * (w * N * (4 * Real.exp 2 * (4 + 2 * ((m : ℝ) / N * Real.log m)) + 3)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hxm
          nlinarith
      _ = w * N * ((16 * Real.exp 2 + 3) * x m ^ 2 +
            8 * Real.exp 2 * ((m : ℝ) / N * Real.log m * x m ^ 2)) := by ring
  have htop := sum_top_le_poleDefect N x
  have hsum2 : ∑ m ∈ Icc 1 N, w * N * ((16 * Real.exp 2 + 3) * x m ^ 2 +
        8 * Real.exp 2 * ((m : ℝ) / N * Real.log m * x m ^ 2)) =
      w * N * ((16 * Real.exp 2 + 3) * ∑ n ∈ Icc 1 N, x n ^ 2 +
        8 * Real.exp 2 * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2) := by
    rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  have hwN : 0 ≤ w * N := by positivity
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then 0 else
        |x m| * |x n| * (2 * w * (1 / |Real.log n - Real.log m| + 1)))
      ≤ ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N,
          (if m = n then 0 else 2 * w * (1 / |Real.log n - Real.log m| + 1)) := hschur
    _ ≤ ∑ m ∈ Icc 1 N, w * N * ((16 * Real.exp 2 + 3) * x m ^ 2 +
          8 * Real.exp 2 * ((m : ℝ) / N * Real.log m * x m ^ 2)) := sum_le_sum hrow
    _ = _ := hsum2
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hwN
        nlinarith [htop]

/-! ### 4. The finite part -/

/-- The cross constant `A = 2(16e² + 3 + 16e²(log 4 + 4))`. -/
def markovCrossConstant : ℝ := 2 * (16 * Real.exp 2 + 3 + 16 * Real.exp 2 * (Real.log 4 + 4))

/-- The overlap bound `1/(64e²)` on `wN`: below it the pole defect keeps a nonnegative weight. -/
def markovOverlapBound : ℝ := 1 / (64 * Real.exp 2)

/-- The atom `φ(·/w)` of a profile on `[0, 1]` is a `C²` bump on `[0, w]`. -/
theorem atomDilate_facts {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hw0 : 0 < w) :
    ContDiff ℝ 2 (SpacingScaleHarmonicAnalysis.atomDilate φ w) ∧
      (∀ u, u ∉ Set.Icc 0 w → SpacingScaleHarmonicAnalysis.atomDilate φ w u = 0) ∧
      HasCompactSupport (SpacingScaleHarmonicAnalysis.atomDilate φ w) := by
  have hsupp : ∀ u, u ∉ Set.Icc 0 w → SpacingScaleHarmonicAnalysis.atomDilate φ w u = 0 := by
    intro u hu
    refine hφsupp (u / w) fun h => hu ⟨?_, ?_⟩
    · have := h.1; rw [le_div_iff₀ hw0] at this; linarith
    · have := h.2; rw [div_le_iff₀ hw0] at this; linarith
  exact ⟨hφ.comp (contDiff_id.div_const w), hsupp,
    HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu⟩

/-- **The Markov form is bounded below by its finite part.** For a `K`-Lipschitz `C²` profile `φ`
on `[0, 1]` and `0 < ε ≤ 1/2`, eventually in `N`, every atomic test `f` of the atom `φ(·/w)`,
`w ≤ δ_N/2`, `wN ≤ 1/(64e²)`, has
`M(f) ≥ (2θ′(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2) w − A·wN) ‖f‖²`. -/
theorem eventually_markovEnergy_atomicTest_ge {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      w * N ≤ markovOverlapBound → ∀ x : ℕ → ℝ,
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) +
            SpacingScaleHarmonicAnalysis.profileRobin φ + γ - ε - Real.exp (1 / 2) / 2 * w -
            markovCrossConstant * (w * N)) *
            ∫ u, atomicTest N x (SpacingScaleHarmonicAnalysis.atomDilate φ w) u ^ 2 ≤
          markovEnergy
            (fun u => (atomicTest N x (SpacingScaleHarmonicAnalysis.atomDilate φ w) u : ℂ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨max N₁ 1, fun N hN w hw0 hw hwN x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hself := SpacingScaleHarmonicAnalysis.abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0
    hw1 hK
  have hf := contDiff_atomicTest hgc2 N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hgc2 hgc hgsupp hw' x, integral_atomicTest_sq hgc2 hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge_diag hgc2 hgc hgsupp hN1 hw0 hw x
  have hpen := cross_penalty_le hN1 hw0 x
  have hP := hN₁ N hNN₁ x
  have hD := poleDefect_nonneg N x
  have hM : 0 ≤ ∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hX : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg (x n)
  have hg_low : (Real.log (1 / w) + SpacingScaleHarmonicAnalysis.profileRobin φ -
      Real.exp (1 / 2) / 2 * w) * ∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2 ≤
      levyEnergy (SpacingScaleHarmonicAnalysis.atomDilate φ w) := by
    have := (abs_le.mp hself).1; linarith
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  have hwN' : 32 * Real.exp 2 * (w * N) ≤ 1 / 2 := by
    have h := hwN
    unfold markovOverlapBound at h
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hg_low hX
  have h2 := mul_le_mul_of_nonneg_left hpen
    (by positivity : (0 : ℝ) ≤ 2 * ∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hP hM
  have h4 : 0 ≤ (∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2) * poleDefect N x *
      (1 - ε - 32 * Real.exp 2 * (w * N)) :=
    mul_nonneg (mul_nonneg hM hD) (by linarith)
  rw [hlog]
  unfold markovCrossConstant
  linarith

/-- **The pole attains the finite part.** For a nonnegative profile, eventually in `N`, the pole
vector `x_n = n^{−1/2}` has
`M(f) ≤ (2θ′(0) + log(1/(wN)) + κ_L(φ) + γ + ε + (e^{1/2}/2) w) ‖f‖²` at every width `w ≤ δ_N/2`. -/
theorem eventually_markovEnergy_truncPole_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hφnn : ∀ u, 0 ≤ φ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      markovEnergy
          (fun u => (atomicTest N (truncPole N) (SpacingScaleHarmonicAnalysis.atomDilate φ w) u : ℂ)) ≤
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) +
            SpacingScaleHarmonicAnalysis.profileRobin φ + γ + ε + Real.exp (1 / 2) / 2 * w) *
          ∫ u, atomicTest N (truncPole N) (SpacingScaleHarmonicAnalysis.atomDilate φ w) u ^ 2 := by
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_truncPole_ge hε
  refine ⟨max N₂ 1, fun N hN w hw0 hw => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hself := SpacingScaleHarmonicAnalysis.abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0
    hw1 hK
  set x := truncPole N
  have hx : ∀ n, 0 ≤ x n := fun n => by
    simp only [x, truncPole]
    split_ifs
    · unfold poleVector; positivity
    · exact le_rfl
  have hg0 : ∀ u, 0 ≤ SpacingScaleHarmonicAnalysis.atomDilate φ w u := fun u => hφnn _
  have hf := contDiff_atomicTest hgc2 N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hgc2 hgc hgsupp hw' x, integral_atomicTest_sq hgc2 hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_le_diag hgc2 hgc hgsupp hg0 hw' x hx
  have hP := hN₂ N hNN₂
  have hM : 0 ≤ ∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hX : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg (x n)
  have hg_up : levyEnergy (SpacingScaleHarmonicAnalysis.atomDilate φ w) ≤
      (Real.log (1 / w) + SpacingScaleHarmonicAnalysis.profileRobin φ +
        Real.exp (1 / 2) / 2 * w) * ∫ u, SpacingScaleHarmonicAnalysis.atomDilate φ w u ^ 2 := by
    have := (abs_le.mp hself).2; linarith
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  have h1 := mul_le_mul_of_nonneg_left hg_up hX
  have h3 := mul_le_mul_of_nonneg_left hP hM
  rw [hlog]
  linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
