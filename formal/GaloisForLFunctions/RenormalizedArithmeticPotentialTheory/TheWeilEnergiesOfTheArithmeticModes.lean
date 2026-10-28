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
  GaloisForLFunctions.RenormalizedBiarithmeticGeometry GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### 1. Periodic sums -/

/-- Re-indexing: `Σ_{1 ≤ n ≤ N} f(n) = Σ_{i < N} f(i + 1)`. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n = ∑ i ∈ range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The partial sums of a `q`-periodic sequence of mean zero are bounded by `2qB`. -/
theorem abs_sum_range_succ_periodic_le {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B)
    (k : ℕ) : |∑ i ∈ range k, ψ (i + 1)| ≤ 2 * q * B := by
  have hmean' : ∑ i ∈ range q, ψ (i + 1) = 0 := by
    have h := sum_range_shift_of_periodic ψ hper 1
    rw [hmean] at h
    rw [← h]
    exact sum_congr rfl fun i _ => by rw [add_comm]
  have h := abs_sum_range_sub_mul_mean_le hq (fun i => ψ (i + 1))
    (fun i => by rw [show i + q + 1 = i + 1 + q by omega]; exact hper (i + 1))
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
    have hgi0 : 0 ≤ ∫ u, g u := integral_nonneg hg0
    have h2q : 0 ≤ 2 * (q : ℝ) * B := by positivity
    have h1 := mul_le_mul hA hb1 (abs_nonneg _) hgi0
    have h2 := mul_le_mul hB' hb2 (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hgi0)
    simp only [abs_mul, abs_two]
    calc 2 * (|∫ u, g u * Real.exp (-(u / 2))| * |∑ n ∈ Icc 1 N, ψ n / n|) *
          (|∫ u, g u * Real.exp (u / 2)| * |∑ n ∈ Icc 1 N, ψ n|)
        ≤ 2 * ((∫ u, g u) * (2 * q * B)) * ((Real.exp (w / 2) * ∫ u, g u) * (2 * q * B)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity)
            (mul_nonneg (by norm_num) (mul_nonneg hgi0 h2q))
      _ = 8 * q ^ 2 * B ^ 2 * Real.exp (w / 2) * (∫ u, g u) ^ 2 := by ring
  calc _ = |(levyEnergy (atomicTest N (fun n => ψ n / Real.sqrt n) g) -
          (∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) * levyEnergy g) +
        2 * ((∫ u, g u * Real.exp (-(u / 2))) * ∑ n ∈ Icc 1 N, ψ n / n) *
          ((∫ u, g u * Real.exp (u / 2)) * ∑ n ∈ Icc 1 N, ψ n)| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcross hpole)

theorem div_sub_rayleigh_eq {W X G θ L P : ℝ} (hX : X ≠ 0) (hG : G ≠ 0) :
    W / (X * G) - (2 * θ + L / G - P / X) = (W - (X * (2 * θ * G + L) - G * P)) / (X * G) := by
  field_simp
  ring

/-- Weil's form of a periodic profile, as a Rayleigh quotient: with `X = |x|²` and `G = ‖g‖²`,
`W(f_x)/(XG) = 2θ′(0) + L(g)/G − P_N(x)/X + O((qB²(wN)G + q²B²e^{w/2}(∫g)²)/(XG))`. -/
theorem abs_weilQuad_div_periodic_sub_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hw0 : 0 < w)
    (hw : 4 * w ≤ atomSpacing N) {q : ℕ} (hq : 1 ≤ q) {B : ℝ} (ψ : ℕ → ℝ)
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0) (hB : ∀ n, |ψ n| ≤ B)
    (hX : 0 < ∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) (hG : 0 < ∫ u, g u ^ 2) :
    |weilQuad (atomicTest N (fun n => ψ n / Real.sqrt n) g) /
        ((∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) * ∫ u, g u ^ 2) -
      (2 * gammaHardyPhaseRate 0 + levyEnergy g / (∫ u, g u ^ 2) -
        atomicWeilForm N (fun n => ψ n / Real.sqrt n) /
          ∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2)| ≤
      (168 * q * B ^ 2 * (w * N) * (∫ u, g u ^ 2) +
        8 * q ^ 2 * B ^ 2 * Real.exp (w / 2) * (∫ u, g u) ^ 2) /
        ((∑ n ∈ Icc 1 N, (ψ n / Real.sqrt n) ^ 2) * ∫ u, g u ^ 2) := by
  have h := abs_weilQuad_atomicTest_periodic_sub_le hg hgc hgsupp hg0 hw0 hw hq ψ hper hmean hB
  have hXG := mul_pos hX hG
  rw [div_sub_rayleigh_eq hX.ne' hG.ne', abs_div, abs_of_pos hXG]
  exact div_le_div_of_nonneg_right h hXG.le

/-! ### 3. The arithmetic modes -/

/-- The conductor-one mode is the constant `1`. -/
theorem normalizedRamanujanMode_one (n : ℕ) : normalizedRamanujanMode 1 n = 1 := by
  simp [normalizedRamanujanMode, ramanujanMode, ArithmeticEffectivityTheory.ramanujanSum,
    IsPrimitiveRoot.primitiveRoots_one]

/-- Every Ramanujan mode of conductor `m ≥ 2` has mean zero over a period. -/
theorem sum_range_normalizedRamanujanMode {m : ℕ} (hm : 2 ≤ m) :
    ∑ r ∈ range m, normalizedRamanujanMode m r = 0 := by
  have hm0 : 0 < m := by omega
  have h := periodMean_normalizedRamanujanMode_mul hm0 one_pos dvd_rfl (one_dvd m) hm0
  rw [if_neg (by omega), periodMean] at h
  simp only [normalizedRamanujanMode_one, mul_one] at h
  rcases div_eq_zero_iff.mp h with h | h
  · exact h
  · exact absurd h (by positivity)

/-- **The prime form on a Ramanujan pole profile is its eigenvalue**: from the quasimode residual,
`P_N(y_m)/|y_m|² − (log N − E_m) → 0`, with `E_m = γ + log m + d(m)`. -/
theorem tendsto_atomicWeilForm_ramanujanPoleProfile_div {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => atomicWeilForm N (ramanujanPoleProfile m) /
        (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) -
          (Real.log N - ramanujanAdjunctionEnergy m)) atTop (𝓝 0) := by
  have hR := tendsto_ramanujanPoleProfile_residual_sq hm
  have hX := tendsto_ramanujanPoleProfile_sq hm
  have hRX := (hR.div hX one_ne_zero).sqrt
  rw [zero_div, Real.sqrt_zero] at hRX
  have hlog : ∀ᶠ N : ℕ in atTop, 0 < Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact Real.log_pos (by exact_mod_cast hN)
  have hXl : ∀ᶠ N : ℕ in atTop,
      0 < (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) / Real.log N :=
    hX.eventually (lt_mem_nhds one_pos)
  refine squeeze_zero_norm' ?_ hRX
  filter_upwards [hlog, hXl] with N hl hXN
  simp only [Pi.div_apply]
  set y := ramanujanPoleProfile m
  set X := ∑ n ∈ Icc 1 N, y n ^ 2
  set lam := Real.log N - ramanujanAdjunctionEnergy m
  have hX0 : 0 < X := by
    have := mul_pos hXN hl
    rwa [div_mul_cancel₀ _ hl.ne'] at this
  -- `P − λ|y|² = ⟨y, r⟩` with `r` the residual
  have hP : atomicWeilForm N y - lam * X =
      ∑ n ∈ Icc 1 N, y n * ((∑ j ∈ Icc 1 N, ArithmeticEffectivityTheory.weilPrimeKernel n j * y j) - lam * y n) := by
    rw [atomicWeilForm, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sub, mul_sum]
    congr 1
    · exact sum_congr rfl fun j _ => by ring
    · ring
  have hCS := sum_mul_sq_le_sq_mul_sq (Icc 1 N) y
    (fun n => (∑ j ∈ Icc 1 N, ArithmeticEffectivityTheory.weilPrimeKernel n j * y j) - lam * y n)
  rw [← hP] at hCS
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have e1 : atomicWeilForm N y / X - lam = (atomicWeilForm N y - lam * X) / X := by
    field_simp
  have e2 : (∑ n ∈ Icc 1 N, ((∑ j ∈ Icc 1 N, ArithmeticEffectivityTheory.weilPrimeKernel n j * y j) - lam * y n) ^ 2) /
      Real.log N / (X / Real.log N) =
      (∑ n ∈ Icc 1 N, ((∑ j ∈ Icc 1 N, ArithmeticEffectivityTheory.weilPrimeKernel n j * y j) - lam * y n) ^ 2) / X := by
    field_simp
  rw [e1, e2, div_pow, div_le_div_iff₀ (by positivity) hX0]
  calc (atomicWeilForm N y - lam * X) ^ 2 * X ≤
      (X * ∑ n ∈ Icc 1 N, ((∑ j ∈ Icc 1 N, ArithmeticEffectivityTheory.weilPrimeKernel n j * y j) - lam * y n) ^ 2) * X :=
        mul_le_mul_of_nonneg_right hCS hX0.le
    _ = _ := by ring

/-- Integrating a dilated profile: `∫ φ(u/w) du = w ∫ φ`. -/
theorem integral_atomDilate {φ : ℝ → ℝ} (hw : 0 < w) :
    ∫ u, atomDilate φ w u = w * ∫ u, φ u := by
  have h := MeasureTheory.Measure.integral_comp_div (fun x => φ x) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  exact h

/-- The spacing of the atoms is at least `1/(N + 1)`. -/
theorem one_div_succ_le_atomSpacing {N : ℕ} (hN : 1 ≤ N) : 1 / ((N : ℝ) + 1) ≤ atomSpacing N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
  have hinv : 1 - (1 + 1 / (N : ℝ))⁻¹ = 1 / (N + 1) := by
    have : (N : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hinv] at h
  exact h

/-- The `m`-th **arithmetic mode** at horizon `N`: the atomic test of the Ramanujan pole profile
`y_m(n) = c_m(n)/√(φ(m) n)` with the profile `φ` dilated to the width `K/N`. -/
def arithmeticMode (φ : ℝ → ℝ) (K : ℝ) (m N : ℕ) : ℝ → ℝ :=
  atomicTest N (ramanujanPoleProfile m) (atomDilate φ (K / N))

/-- The error of the Rayleigh quotient of an arithmetic mode is `O(1/|y_m|²)`. -/
theorem abs_weilQuad_arithmeticMode_div_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {m : ℕ} (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 < K) {N : ℕ} (hN : 1 ≤ N) (hw1 : K / N ≤ 1)
    (hw : 4 * (K / N) ≤ atomSpacing N) (hX : 0 < ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) :
    |weilQuad (arithmeticMode φ K m N) / (∫ u, arithmeticMode φ K m N u ^ 2) -
      (2 * gammaHardyPhaseRate 0 + levyEnergy (atomDilate φ (K / N)) /
          (∫ u, atomDilate φ (K / N) u ^ 2) -
        atomicWeilForm N (ramanujanPoleProfile m) /
          ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2)| ≤
      (168 * m * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * K +
        8 * m ^ 2 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * Real.exp (1 / 2) *
          (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) /
        ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2 := by
  have hm0 : 0 < m := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < K / N := by positivity
  set w := K / N with hwdef
  set B := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  set g := atomDilate φ w
  set X := ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2
  have hcd : ContDiff ℝ 2 g := hφ.comp (contDiff_id.div_const w)
  have hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := by
    intro u hu
    refine hφsupp (u / w) fun h => hu ⟨?_, ?_⟩
    · have := h.1; rw [le_div_iff₀ hw0] at this; linarith
    · have := h.2; rw [div_le_iff₀ hw0] at this; linarith
  have hcs : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := 0) (b := w)) fun u hu => hsupp u hu
  have hG : ∫ u, g u ^ 2 = w * ∫ u, φ u ^ 2 := integral_atomDilate_sq hw0
  have hG0 : 0 < ∫ u, g u ^ 2 := by rw [hG]; positivity
  have hI : ∫ u, g u = w * ∫ u, φ u := integral_atomDilate hw0
  have hB0 : 0 ≤ B := sum_nonneg fun j _ => abs_nonneg _
  have hmain := abs_weilQuad_div_periodic_sub_le hcd hcs hsupp (fun u => hφ0 _) hw0 hw
    (q := m) (by omega) (normalizedRamanujanMode m) (fun n => normalizedRamanujanMode_periodic hm0 n)
    (sum_range_normalizedRamanujanMode hm) (abs_normalizedRamanujanMode_le hm0) hX hG0
  have hnorm : ∫ u, arithmeticMode φ K m N u ^ 2 = X * ∫ u, g u ^ 2 :=
    integral_atomicTest_sq hcd hcs hsupp (by linarith) _
  rw [hnorm]
  refine hmain.trans ?_
  -- the error constant
  have hwN : w * N = K := by rw [hwdef]; field_simp
  rw [hwN, hI, div_le_div_iff₀ (mul_pos hX hG0) hX]
  have hexp : Real.exp (w / 2) * w ≤ Real.exp (1 / 2) := by
    calc Real.exp (w / 2) * w ≤ Real.exp (1 / 2) * 1 :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hw1 hw0.le (Real.exp_pos _).le
      _ = Real.exp (1 / 2) := mul_one _
  have hc : 0 ≤ 8 * (m : ℝ) ^ 2 * B ^ 2 * (∫ u, φ u) ^ 2 := by positivity
  rw [hG]
  have e : (168 * m * B ^ 2 * K + 8 * m ^ 2 * B ^ 2 * Real.exp (1 / 2) * (∫ u, φ u) ^ 2 /
      (∫ u, φ u ^ 2)) * (X * (w * ∫ u, φ u ^ 2)) =
      X * (168 * m * B ^ 2 * K * (w * ∫ u, φ u ^ 2) +
        8 * m ^ 2 * B ^ 2 * (∫ u, φ u) ^ 2 * (Real.exp (1 / 2) * w)) := by
    field_simp
  rw [e, mul_comm _ X]
  refine mul_le_mul_of_nonneg_left ?_ hX.le
  have : 8 * (m : ℝ) ^ 2 * B ^ 2 * Real.exp (w / 2) * (w * ∫ u, φ u) ^ 2 =
      8 * m ^ 2 * B ^ 2 * (∫ u, φ u) ^ 2 * (Real.exp (w / 2) * w * w) := by ring
  rw [this]
  have hexp' : Real.exp (w / 2) * w * w ≤ Real.exp (1 / 2) * w :=
    mul_le_mul_of_nonneg_right hexp hw0.le
  nlinarith [mul_le_mul_of_nonneg_left hexp' hc]

/-- **The Weil energies of the arithmetic modes.** For a nonnegative Lipschitz profile `φ` on
`[0, 1]`, a conductor `m ≥ 2` and an overlap ratio `0 < K < 1/4`,
`W(f_N)/‖f_N‖² → log(1/K) − log 2π + β(φ)/‖φ‖² + log m + d(m)` for the arithmetic modes
`f_N = arithmeticMode φ K m N`. The archimedean cross terms and the pole term are `O(1/log N)`,
the self-energy is `log(N/K) + κ_L(φ)`, the prime form is `log N − γ − log m − d(m)`, and the
finite part `2θ′(0) + 2c_∞ + γ` is `−log 2π`. -/
theorem tendsto_weilQuad_arithmeticMode {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u) (hφ2 : 0 < ∫ u, φ u ^ 2)
    {L : ℝ} (hL : ∀ u v, |φ u - φ v| ≤ L * |u - v|) {m : ℕ} (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 < K)
    (hK : K < 1 / 4) :
    Tendsto (fun N : ℕ => weilQuad (arithmeticMode φ K m N) / ∫ u, arithmeticMode φ K m N u ^ 2)
      atTop (𝓝 (Real.log (1 / K) - Real.log (2 * Real.pi) + bumpRobin φ 1 / (∫ u, φ u ^ 2) +
        (Real.log m + tameDifferent m))) := by
  have hm0 : 0 < m := by omega
  set B := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  set C := 168 * m * B ^ 2 * K + 8 * m ^ 2 * B ^ 2 * Real.exp (1 / 2) * (∫ u, φ u) ^ 2 /
    (∫ u, φ u ^ 2)
  -- the three convergent pieces
  have hwt : Tendsto (fun N : ℕ => K / N) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat K,
      eventually_atTop.mpr ⟨1, fun N hN => by
        have : (0 : ℝ) < N := by exact_mod_cast hN
        exact div_pos hK0 this⟩⟩
  have hself := (tendsto_levyEnergy_atomDilate_sub_log hφ hφsupp hφ2 hL).comp hwt
  have hprime := tendsto_atomicWeilForm_ramanujanPoleProfile_div hm0
  have hXl := tendsto_ramanujanPoleProfile_sq hm0
  have hXinf : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) atTop atTop := by
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    refine (hXl.pos_mul_atTop one_pos hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    exact div_mul_cancel₀ _ this.ne'
  have herr : Tendsto (fun N : ℕ => C / ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) atTop
      (𝓝 0) := hXinf.const_div_atTop C
  -- eventually the hypotheses of the error bound hold
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ K / N ≤ 1 ∧ 4 * (K / N) ≤ atomSpacing N ∧
      0 < ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2 := by
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * K / (1 - 4 * K))
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N₁,
      hXinf.eventually_gt_atTop 0] with N hN hN1 hX
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h14 : 0 < 1 - 4 * K := by linarith
    have hNK : 4 * K / (1 - 4 * K) < N := lt_of_lt_of_le hN₁ (by exact_mod_cast hN1)
    rw [div_lt_iff₀ h14] at hNK
    refine ⟨hN, (div_le_one (by linarith)).mpr (by linarith), ?_, hX⟩
    refine le_trans ?_ (one_div_succ_le_atomSpacing hN)
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hE : Tendsto (fun N : ℕ =>
      weilQuad (arithmeticMode φ K m N) / (∫ u, arithmeticMode φ K m N u ^ 2) -
        (2 * gammaHardyPhaseRate 0 + levyEnergy (atomDilate φ (K / N)) /
            (∫ u, atomDilate φ (K / N) u ^ 2) -
          atomicWeilForm N (ramanujanPoleProfile m) /
            ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [hev] with N ⟨hN, hw1, hw, hX⟩
    exact abs_weilQuad_arithmeticMode_div_sub_le hφ hφsupp hφ0 hφ2 hm hK0 hN hw1 hw hX
  have hsum := ((hself.add hE).sub hprime).const_add (2 * gammaHardyPhaseRate 0 - Real.log K)
  have hlim : 2 * gammaHardyPhaseRate 0 - Real.log K + (profileRobin φ + 0 - 0) +
      ramanujanAdjunctionEnergy m = Real.log (1 / K) - Real.log (2 * Real.pi) +
        bumpRobin φ 1 / (∫ u, φ u ^ 2) + (Real.log m + tameDifferent m) := by
    have h := finitePart_profileRobin_eq φ
    rw [ramanujanAdjunctionEnergy, one_div, Real.log_inv]
    linarith
  rw [← hlim]
  refine (hsum.add_const (ramanujanAdjunctionEnergy m)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogw : Real.log (1 / (K / N)) = Real.log N - Real.log K := by
    rw [one_div_div, Real.log_div (by positivity) hK0.ne']
  simp only [Function.comp_apply, hlogw]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
