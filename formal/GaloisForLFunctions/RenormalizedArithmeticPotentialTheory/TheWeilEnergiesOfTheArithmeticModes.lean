import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanCrossTermsVanishOnPeriodicProfiles
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanFinitePartIsMinusLogTwoPi

/-!
# The Weil energies of the arithmetic modes

On a periodic profile of mean zero, `x_n = ψ(n)/√n`, Weil's form of an atomic test below the spacing
is the self-energy of the atoms minus the prime form. The archimedean cross terms are
`O(wN ‖g‖²)` (`TheArchimedeanCrossTermsVanishOnPeriodicProfiles`), and the pole term is
`O(e^{w/2} (∫g)²)` because `Σ ψ(n)/n` and `Σ ψ(n)` are bounded (`abs_weilQuad_atomicTest_periodic_sub_le`).

For the Ramanujan modes of conductor `m ≥ 2` the prime form is known to `o(log N)` (the Ramanujan
quasimodes). This gives the Weil energy of the arithmetic modes at overlap ratio `K = w/δ_N`
(`tendsto_weilQuad_ramanujanMode`):
`W(f)/‖f‖² → log(1/K) − log 2π + β(φ)/‖φ‖² + log m + d(m)`, with `d` the tame different and
`β(φ)/‖φ‖²` the shape constant of the profile. So the `m`-th arithmetic mode is positive exactly
below the overlap ratio `m e^{d(m)} e^{β(φ)/‖φ‖²}/(2π)`: the pole's Robin–Euler threshold multiplied
by `m e^{d(m)}`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

local notation "γ" => Real.eulerMascheroniConstant

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### 1. Periodic sums -/

/-- Re-indexing: `Σ_{1 ≤ n ≤ N} f(n) = Σ_{i < N} f(i + 1)`. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n = ∑ i ∈ range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- The partial sums of a `q`-periodic sequence of mean zero are bounded by `2qB`. -/
theorem abs_sum_range_succ_periodic_le {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B)
    (k : ℕ) : |∑ i ∈ range k, ψ (i + 1)| ≤ 2 * q * B := by
  have hmean' : ∑ i ∈ range q, ψ (i + 1) = 0 := by
    have h := sum_range_shift_of_periodic ψ hper 1
    rw [hmean] at h
    rw [← h]
    exact sum_congr rfl fun i _ => by rw [add_comm]
  have h := abs_sum_range_sub_mul_mean_le hq (fun i => ψ (i + 1)) (fun i => hper (i + 1))
    (fun i => hB (i + 1)) k
  rwa [hmean', zero_div, mul_zero, sub_zero] at h

/-- `|Σ_{n ≤ N} ψ(n)/n| ≤ 2qB` for a `q`-periodic `ψ` of mean zero, by Abel summation. -/
theorem abs_sum_Icc_periodic_div_le {q N : ℕ} (hq : 1 ≤ q) {B : ℝ} (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B) :
    |∑ n ∈ Icc 1 N, ψ n / n| ≤ 2 * q * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Icc_eq_empty (by norm_num), sum_empty, abs_zero]
    positivity
  have hbm : ∀ i : ℕ, i + 1 < N →
      (1 : ℝ) / (((i + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := fun i _ => by
    push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have habel := abs_sum_range_mul_le (fun i => ψ (i + 1)) (fun i : ℕ => 1 / ((i : ℝ) + 1)) N
    (P := 2 * q * B) fun k _ => abs_sum_range_succ_periodic_le hq ψ hper hmean hB k
  rw [abs_last_add_sum_abs_sub_eq (fun i : ℕ => 1 / ((i : ℝ) + 1)) hN (fun i _ => by positivity)
    hbm] at habel
  have e : ∑ i ∈ range N, ψ (i + 1) / ((i + 1 : ℕ) : ℝ) =
      ∑ i ∈ range N, 1 / ((i : ℝ) + 1) * ψ (i + 1) :=
    sum_congr rfl fun i _ => by push_cast; ring
  rw [sum_Icc_one_eq_sum_range (fun n => ψ n / n), e]
  simpa using habel

/-! ### 2. The Weil form of a periodic profile -/

/-- **Weil's form of a periodic profile of mean zero**, below a quarter of the spacing:
`W(f_x) = |x|² (2θ′(0)‖g‖² + L(g)) − ‖g‖² P_N(x) + O(qB²(wN)‖g‖² + q²B² e^{w/2}(∫g)²)`. -/
theorem abs_weilQuad_atomicTest_periodic_sub_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hw0 : 0 < w)
    (hw : 4 * w ≤ atomSpacing N) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B) :
    |weilQuad (atomicTest N (fun n => ψ n / Real.sqrt n) g) -
        ((∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) *
            (2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g) -
          (∫ u, g u ^ 2) * atomicWeilForm N (fun n => ψ n / Real.sqrt n))| ≤
      168 * q * B ^ 2 * (w * N) * (∫ u, g u ^ 2) +
        8 * q ^ 2 * B ^ 2 * Real.exp (w / 2) * (∫ u, g u) ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hw' : w < atomSpacing N := by linarith
  have hf := contDiff_atomicTest hg N (fun n => ψ n / Real.sqrt n)
  have hfc := hasCompactSupport_atomicTest hgsupp N (fun n => ψ n / Real.sqrt n)
  have hcross := abs_levyEnergy_atomicTest_sub_le_of_periodic hg hgc hgsupp hg0 hw0 hw hq ψ hper
    hmean hB
  rw [weilQuad_eq_markov_add_pole hf hfc, markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc,
    archForm_eq_levyEnergy hf hfc, integral_atomicTest_sq hg hgc hgsupp hw',
    primeSum_atomicTest hg hgc hgsupp hw',
    integral_atomicTest_mul_exp_neg_half hg.continuous hgsupp,
    integral_atomicTest_mul_exp_half hg.continuous hgsupp]
  -- the pole moments of a periodic profile are bounded sums
  have hS1 : ∑ n ∈ Icc 1 N, ψ n / Real.sqrt n / Real.sqrt n = ∑ n ∈ Icc 1 N, ψ n / n :=
    sum_congr rfl fun n hn => by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_div, Real.mul_self_sqrt hn0]
  have hS2 : ∑ n ∈ Icc 1 N, ψ n / Real.sqrt n * Real.sqrt n = ∑ n ∈ Icc 1 N, ψ n :=
    sum_congr rfl fun n hn => by
      have hn0 : (0 : ℝ) < Real.sqrt n :=
        Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)
      exact div_mul_cancel₀ (ψ n) hn0.ne'
  rw [hS1, hS2]
  have hb1 := abs_sum_Icc_periodic_div_le (N := N) hq ψ hper hmean hB
  have hb2 : |∑ n ∈ Icc 1 N, ψ n| ≤ 2 * q * B := by
    rw [sum_Icc_one_eq_sum_range]
    exact abs_sum_range_succ_periodic_le hq ψ hper hmean hB N
  -- the bump moments
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hA : |∫ u, g u * Real.exp (-(u / 2))| ≤ ∫ u, g u := by
    have h0 : 0 ≤ ∫ u, g u * Real.exp (-(u / 2)) :=
      integral_nonneg fun u => mul_nonneg (hg0 u) (Real.exp_pos _).le
    rw [abs_of_nonneg h0]
    refine integral_mono ((hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hgc.mul_right) hgint fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · exact mul_le_of_le_one_right (hg0 u) (Real.exp_le_one_iff.mpr (by linarith [hu.1]))
    · rw [hgsupp u hu, zero_mul]
  have hB' : |∫ u, g u * Real.exp (u / 2)| ≤ Real.exp (w / 2) * ∫ u, g u := by
    have h0 : 0 ≤ ∫ u, g u * Real.exp (u / 2) :=
      integral_nonneg fun u => mul_nonneg (hg0 u) (Real.exp_pos _).le
    rw [abs_of_nonneg h0, ← integral_const_mul]
    refine integral_mono ((hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hgc.mul_right) (hgint.const_mul _) fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · rw [mul_comm (Real.exp (w / 2))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu.2])) (hg0 u)
    · rw [hgsupp u hu, zero_mul, mul_zero]
  have hpole : |2 * ((∫ u, g u * Real.exp (-(u / 2))) * ∑ n ∈ Icc 1 N, ψ n / n) *
      ((∫ u, g u * Real.exp (u / 2)) * ∑ n ∈ Icc 1 N, ψ n)| ≤
        8 * q ^ 2 * B ^ 2 * Real.exp (w / 2) * (∫ u, g u) ^ 2 := by
    simp only [abs_mul, abs_two]
    calc 2 * (|∫ u, g u * Real.exp (-(u / 2))| * |∑ n ∈ Icc 1 N, ψ n / n|) *
          (|∫ u, g u * Real.exp (u / 2)| * |∑ n ∈ Icc 1 N, ψ n|)
        ≤ 2 * ((∫ u, g u) * (2 * q * B)) * ((Real.exp (w / 2) * ∫ u, g u) * (2 * q * B)) := by
          gcongr
      _ = 8 * q ^ 2 * B ^ 2 * Real.exp (w / 2) * (∫ u, g u) ^ 2 := by ring
  calc _ = |(levyEnergy (atomicTest N (fun n => ψ n / Real.sqrt n) g) -
          (∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) * levyEnergy g) +
        2 * ((∫ u, g u * Real.exp (-(u / 2))) * ∑ n ∈ Icc 1 N, ψ n / n) *
          ((∫ u, g u * Real.exp (u / 2)) * ∑ n ∈ Icc 1 N, ψ n)| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcross hpole)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
