import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCofactorGramIsATranslationGram
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeRankCountsTheDominantZeros

/-!
# The power rows of the zeros are dominant configurations

A translated zero `ρ − ε` enters the cofactor through its power row `n ↦ Re(c n^{ρ−ε})`.
`TheEscapeRankCountsTheDominantZeros` classifies the escape states of exponential profiles; this
file transfers the classification to the actual rows.

* **The floor costs a factor `e^{−u}`** (`sub_log_floor_exp_le`, `norm_floor_cpow_sub_le`). For
  `u ≥ 0` and `Re z ≥ 0`, `0 ≤ u − log⌊e^u⌋ ≤ 2e^{−u}` and `|⌊e^u⌋^z − e^{zu}| ≤ 4|z| e^{(Re z − 1)u}`.
* **Power rows have exponential profiles** (`abs_logProfile_powerSum_sub_le`). For `z_k` on one line
  `Re z_k = ½ + x`, the log profile of `Σ_k Re(c_k n^{z_k})` is within `K e^{(x − 1)u}` of
  `Σ_k Re(c_k e^{(z_k − ½)u})`, for every real `u`.
* **Profiles within `e^{(x−1)u}` have the same escape states** (`tendsto_scaled_gram_sub`,
  `tendsto_scaled_rowGram_sub`). If a profile `f` is within `K e^{(x−1)u}` of a profile `h` of size
  `B e^{xu}`, the scaled Grams `e^{−2xL} ∫_0^L f(u−a) f(u−b) du` and those of `h` differ by at most
  `M L e^{−min(2x,1) L}`. For a row, the left side is `√j √k ⟨D_j v, D_k v⟩_T` at `L = log(T+1)`.
* **The real profile is a dominant configuration** (`domProfile_append_eq`). `Σ_k Re(c_k e^{(z_k−½)u})`
  is the configuration with frequencies `±Im z_k` and coefficients `c_k/2`, `c̄_k/2`.
* **Escape states of power rows** (`exists_tendsto_powerSum_escapeKernel`). Along any horizons, a
  subsequence of the scaled cofactor Grams of `Σ_k Re(c_k n^{z_k})` converges, for all dilations
  `j, k` at once, to a phase kernel `K_θ(log j, log k)` of that configuration.

So the escape states of the row of `r` dominant translated zeros (with distinct `±Im z_k`) are phase
kernels of rank exactly `2r` (`escapeForm_log_eq_zero_iff`), each zero seen through the pair of
characters `j^{−(ρ−ε)}`, `j^{−(ρ̄−ε)}`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (pronicPairing rowDilate)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile measurable_logProfile)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-! ### The floor of `e^u` -/

/-- `0 ≤ u − log⌊e^u⌋ ≤ 2e^{−u}` for `u ≥ 0`. -/
theorem sub_log_floor_exp_le {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - Real.log ⌊Real.exp u⌋₊ ∧ u - Real.log ⌊Real.exp u⌋₊ ≤ 2 * Real.exp (-u) := by
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu
  have hm1 : (1 : ℝ) ≤ ⌊Real.exp u⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).mpr he
  have hmle : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hlt : Real.exp u < ⌊Real.exp u⌋₊ + 1 := Nat.lt_floor_add_one _
  have hm0 : (0 : ℝ) < ⌊Real.exp u⌋₊ := by linarith
  have hlog : u - Real.log ⌊Real.exp u⌋₊ = Real.log (Real.exp u / ⌊Real.exp u⌋₊) := by
    rw [Real.log_div (Real.exp_pos u).ne' hm0.ne', Real.log_exp]
  refine ⟨?_, ?_⟩
  · rw [hlog]
    exact Real.log_nonneg ((one_le_div hm0).mpr hmle)
  · rw [hlog]
    refine (Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos u) hm0)).trans ?_
    -- `e^u/m − 1 ≤ 2e^{−u}` since `(e^u − m) e^u ≤ e^u < m + 1 ≤ 2m`
    rw [Real.exp_neg, div_sub_one hm0.ne', div_le_iff₀ hm0]
    have h1 : (Real.exp u - ⌊Real.exp u⌋₊) * Real.exp u ≤ 1 * Real.exp u :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos u).le
    have h2 : 2 * (Real.exp u)⁻¹ * ⌊Real.exp u⌋₊ * Real.exp u = 2 * ⌊Real.exp u⌋₊ := by
      field_simp
    nlinarith [Real.exp_pos u, inv_pos.mpr (Real.exp_pos u)]

/-- **The floor costs a factor `e^{−u}`**: `|⌊e^u⌋^z − e^{zu}| ≤ 4|z| e^{(Re z − 1)u}`. -/
theorem norm_floor_cpow_sub_le {z : ℂ} (hz : 0 ≤ z.re) {u : ℝ} (hu : 0 ≤ u) :
    ‖((⌊Real.exp u⌋₊ : ℕ) : ℂ) ^ z - Complex.exp (z * u)‖ ≤ 4 * ‖z‖ * Real.exp ((z.re - 1) * u) := by
  obtain ⟨hd0, hd1⟩ := sub_log_floor_exp_le hu
  have hm0 : (0 : ℝ) < ⌊Real.exp u⌋₊ := by
    have : (1 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
      exact_mod_cast (Nat.one_le_floor_iff _).mpr (Real.one_le_exp hu)
    linarith
  set m := ⌊Real.exp u⌋₊
  set w : ℂ := z * ((Real.log m - u : ℝ) : ℂ)
  have hpow : ((m : ℕ) : ℂ) ^ z = Complex.exp (z * u) * Complex.exp w := by
    rw [← Complex.exp_add, Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne'),
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hm0.le]
    congr 1
    simp only [w]
    push_cast
    ring
  have hw_re : w.re ≤ 0 := by
    have : w.re = z.re * (Real.log m - u) := by
      simp only [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hz (by linarith)
  have hw_norm : ‖w‖ = ‖z‖ * (u - Real.log m) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  -- `|e^w − 1| ≤ 2|w|` when `Re w ≤ 0`
  have hexp : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
    by_cases h : ‖w‖ ≤ 1
    · exact Complex.norm_exp_sub_one_le h
    · have h1 : ‖Complex.exp w‖ ≤ 1 := by
        rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hw_re
      calc ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
        _ ≤ 2 * ‖w‖ := by linarith [not_le.mp h]
  rw [hpow, ← mul_sub_one, norm_mul, Complex.norm_exp]
  have hre : (z * (u : ℂ)).re = z.re * u := by simp
  rw [hre, hw_norm] at *
  have hz0 := norm_nonneg z
  calc Real.exp (z.re * u) * ‖Complex.exp w - 1‖
      ≤ Real.exp (z.re * u) * (2 * (‖z‖ * (2 * Real.exp (-u)))) := by
        refine mul_le_mul_of_nonneg_left (hexp.trans ?_) (Real.exp_pos _).le
        nlinarith
    _ = 4 * ‖z‖ * Real.exp ((z.re - 1) * u) := by
        rw [show (z.re - 1) * u = z.re * u + -u by ring, Real.exp_add]
        ring

/-! ### Power rows and their exponential profiles -/

/-- The real power row `n ↦ Re(c n^z)`. -/
def powerRow (c z : ℂ) (n : ℕ) : ℝ := (c * (n : ℂ) ^ z).re

/-- Its exponential profile `u ↦ Re(c e^{(z − ½)u})`. -/
def powerProfile (c z : ℂ) (u : ℝ) : ℝ := (c * Complex.exp ((z - 1 / 2) * u)).re

theorem abs_powerProfile_le (c z : ℂ) (u : ℝ) :
    |powerProfile c z u| ≤ ‖c‖ * Real.exp ((z.re - 1 / 2) * u) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp]
  have : ((z - 1 / 2) * (u : ℂ)).re = (z.re - 1 / 2) * u := by
    simp [Complex.sub_re]
  rw [this]

/-- The log profile of a power row is its exponential profile up to `‖c‖(4|z| + 1) e^{(Re z − 3/2)u}`. -/
theorem abs_logProfile_powerRow_sub_le (c : ℂ) {z : ℂ} (hz : 0 < z.re) (u : ℝ) :
    |logProfile (powerRow c z) u - powerProfile c z u| ≤
      ‖c‖ * (4 * ‖z‖ + 1) * Real.exp ((z.re - 3 / 2) * u) := by
  have hc := norm_nonneg c
  have hz0 := norm_nonneg z
  by_cases hu : 0 ≤ u
  · -- `e^{(z−½)u} = e^{−u/2} e^{zu}`, so the difference is `e^{−u/2} Re(c(⌊e^u⌋^z − e^{zu}))`
    have hsplit : powerProfile c z u =
        Real.exp (-(u / 2)) * (c * Complex.exp (z * u)).re := by
      rw [powerProfile, show (z - 1 / 2) * (u : ℂ) = ((-(u / 2) : ℝ) : ℂ) + z * u by
        push_cast; ring, Complex.exp_add, ← Complex.ofReal_exp, mul_left_comm, Complex.re_ofReal_mul]
    have hdiff : logProfile (powerRow c z) u - powerProfile c z u =
        Real.exp (-(u / 2)) * (c * (((⌊Real.exp u⌋₊ : ℕ) : ℂ) ^ z - Complex.exp (z * u))).re := by
      rw [hsplit, logProfile, powerRow, mul_sub, Complex.sub_re]
      ring
    rw [hdiff, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := norm_floor_cpow_sub_le hz.le hu
    calc Real.exp (-(u / 2)) * |(c * (((⌊Real.exp u⌋₊ : ℕ) : ℂ) ^ z - Complex.exp (z * u))).re|
        ≤ Real.exp (-(u / 2)) * (‖c‖ * (4 * ‖z‖ * Real.exp ((z.re - 1) * u))) := by
          refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_)
            (Real.exp_pos _).le
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hb hc
      _ = ‖c‖ * (4 * ‖z‖) * Real.exp ((z.re - 3 / 2) * u) := by
          rw [show (z.re - 3 / 2) * u = -(u / 2) + (z.re - 1) * u by ring, Real.exp_add]
          ring
      _ ≤ ‖c‖ * (4 * ‖z‖ + 1) * Real.exp ((z.re - 3 / 2) * u) := by
          gcongr
          linarith
  · -- for `u < 0` the row profile vanishes and the exponential is below `e^{(Re z − 3/2)u}`
    have hu' : u < 0 := not_le.mp hu
    have hfloor : ⌊Real.exp u⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hu')
    have hz0' : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    have hrow : logProfile (powerRow c z) u = 0 := by
      rw [logProfile, hfloor, powerRow, Nat.cast_zero, Complex.zero_cpow hz0', mul_zero,
        Complex.zero_re, mul_zero]
    rw [hrow, zero_sub, abs_neg]
    refine (abs_powerProfile_le c z u).trans ?_
    have hexp : Real.exp ((z.re - 1 / 2) * u) ≤ Real.exp ((z.re - 3 / 2) * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc ‖c‖ * Real.exp ((z.re - 1 / 2) * u) ≤ ‖c‖ * Real.exp ((z.re - 3 / 2) * u) :=
          mul_le_mul_of_nonneg_left hexp hc
      _ ≤ ‖c‖ * (4 * ‖z‖ + 1) * Real.exp ((z.re - 3 / 2) * u) := by
          have := (Real.exp_pos ((z.re - 3 / 2) * u)).le
          nlinarith [mul_nonneg (mul_nonneg hc hz0) this]

theorem logProfile_sum {r : ℕ} (w : Fin r → ℕ → ℝ) (u : ℝ) :
    logProfile (fun n => ∑ k, w k n) u = ∑ k, logProfile (w k) u := by
  simp only [logProfile, Finset.mul_sum]

/-- **Power rows have exponential profiles**: on the line `Re z_k = ½ + x`, the log profile of
`Σ_k Re(c_k n^{z_k})` is within `K e^{(x − 1)u}` of `Σ_k Re(c_k e^{(z_k − ½)u})`. -/
theorem abs_logProfile_powerSum_sub_le {r : ℕ} (c z : Fin r → ℂ) {x : ℝ} (hx : 0 < x)
    (hz : ∀ k, (z k).re = 1 / 2 + x) (u : ℝ) :
    |logProfile (fun n => ∑ k, powerRow (c k) (z k) n) u - ∑ k, powerProfile (c k) (z k) u| ≤
      (∑ k, ‖c k‖ * (4 * ‖z k‖ + 1)) * Real.exp ((x - 1) * u) := by
  rw [logProfile_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have h := abs_logProfile_powerRow_sub_le (c k) (z := z k) (by rw [hz k]; linarith) u
  rwa [hz k, show 1 / 2 + x - 3 / 2 = x - 1 by ring] at h

theorem abs_powerSumProfile_le {r : ℕ} (c z : Fin r → ℂ) {x : ℝ} (hz : ∀ k, (z k).re = 1 / 2 + x)
    (u : ℝ) : |∑ k, powerProfile (c k) (z k) u| ≤ (∑ k, ‖c k‖) * Real.exp (x * u) := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have h := abs_powerProfile_le (c k) (z k) u
  rwa [hz k, show 1 / 2 + x - 1 / 2 = x by ring] at h

/-! ### Profiles close in `e^{(x−1)u}` have the same escape states -/

/-- **Comparison of scaled Grams.** -/
theorem tendsto_scaled_gram_sub {f h : ℝ → ℝ} (hfm : Measurable f) (hh : Continuous h) {x K B : ℝ}
    (hx : 0 < x) (hK : 0 ≤ K) (hB : 0 ≤ B) (hfh : ∀ u, |f u - h u| ≤ K * Real.exp ((x - 1) * u))
    (hhb : ∀ u, |h u| ≤ B * Real.exp (x * u)) (a b : ℝ) :
    Tendsto (fun L : ℝ => Real.exp (-(2 * x * L)) *
      ((∫ u in (0 : ℝ)..L, f (u - a) * f (u - b)) - ∫ u in (0 : ℝ)..L, h (u - a) * h (u - b)))
      atTop (𝓝 0) := by
  set μ := min (2 * x) 1 with hμ
  have hμpos : 0 < μ := lt_min (by linarith) one_pos
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμ2 : μ ≤ 2 * x := min_le_left _ _
  have hfb : ∀ v, |f v| ≤ B * Real.exp (x * v) + K * Real.exp ((x - 1) * v) := fun v => by
    have := abs_sub_abs_le_abs_sub (f v) (h v)
    linarith [hfh v, hhb v]
  -- the constant of the pointwise bound
  set A₁ := Real.exp (-((x - 1) * a)) * Real.exp (-(x * b))
  set A₂ := Real.exp (-((x - 1) * a)) * Real.exp (-((x - 1) * b))
  set A₃ := Real.exp (-(x * a)) * Real.exp (-((x - 1) * b))
  set M := K * B * A₁ + K * K * A₂ + B * K * A₃
  have hM : 0 ≤ M := by positivity
  have hprod : ∀ u, 0 ≤ u →
      |f (u - a) * f (u - b) - h (u - a) * h (u - b)| ≤ M * Real.exp ((2 * x - 1) * u) := by
    intro u hu
    have e : f (u - a) * f (u - b) - h (u - a) * h (u - b) =
        (f (u - a) - h (u - a)) * f (u - b) + h (u - a) * (f (u - b) - h (u - b)) := by ring
    have hE1 : Real.exp ((x - 1) * (u - a)) * Real.exp (x * (u - b)) =
        A₁ * Real.exp ((2 * x - 1) * u) := by
      simp only [A₁, ← Real.exp_add]; congr 1; ring
    have hE2 : Real.exp ((x - 1) * (u - a)) * Real.exp ((x - 1) * (u - b)) ≤
        A₂ * Real.exp ((2 * x - 1) * u) := by
      simp only [A₂, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hE3 : Real.exp (x * (u - a)) * Real.exp ((x - 1) * (u - b)) =
        A₃ * Real.exp ((2 * x - 1) * u) := by
      simp only [A₃, ← Real.exp_add]; congr 1; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (hfh (u - a)) (hfb (u - b)) (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul (hhb (u - a)) (hfh (u - b)) (abs_nonneg _) (by positivity)
    have hKK := mul_le_mul_of_nonneg_left hE2 (mul_nonneg hK hK)
    have hexp := (Real.exp_pos ((2 * x - 1) * u)).le
    calc |f (u - a) - h (u - a)| * |f (u - b)| + |h (u - a)| * |f (u - b) - h (u - b)|
        ≤ K * Real.exp ((x - 1) * (u - a)) *
            (B * Real.exp (x * (u - b)) + K * Real.exp ((x - 1) * (u - b))) +
          B * Real.exp (x * (u - a)) * (K * Real.exp ((x - 1) * (u - b))) := add_le_add h1 h2
      _ = K * B * (Real.exp ((x - 1) * (u - a)) * Real.exp (x * (u - b))) +
          K * K * (Real.exp ((x - 1) * (u - a)) * Real.exp ((x - 1) * (u - b))) +
          B * K * (Real.exp (x * (u - a)) * Real.exp ((x - 1) * (u - b))) := by ring
      _ ≤ M * Real.exp ((2 * x - 1) * u) := by
          rw [hE1, hE3]
          nlinarith
  -- integrability of the row product
  have hfi : ∀ L, IntervalIntegrable (fun u => f (u - a) * f (u - b)) volume 0 L := by
    intro L
    refine IntervalIntegrable.mono_fun' (g := fun u =>
      (B * Real.exp (x * (u - a)) + K * Real.exp ((x - 1) * (u - a))) *
        (B * Real.exp (x * (u - b)) + K * Real.exp ((x - 1) * (u - b)))) ?_ ?_ ?_
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact ((hfm.comp (measurable_id.sub_const a)).mul
        (hfm.comp (measurable_id.sub_const b))).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hfb _) (hfb _) (abs_nonneg _) (by positivity)
  have hhi : ∀ L, IntervalIntegrable (fun u => h (u - a) * h (u - b)) volume 0 L := fun L =>
    Continuous.intervalIntegrable (by fun_prop) _ _
  -- the bound `|e^{−2xL}(…)| ≤ M L e^{−μL}`
  have hbound : ∀ L : ℝ, 0 ≤ L → ‖Real.exp (-(2 * x * L)) *
      ((∫ u in (0 : ℝ)..L, f (u - a) * f (u - b)) - ∫ u in (0 : ℝ)..L, h (u - a) * h (u - b))‖ ≤
        M * L * Real.exp (-(μ * L)) := by
    intro L hL
    rw [← intervalIntegral.integral_sub (hfi L) (hhi L), norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h1 : ‖∫ u in (0 : ℝ)..L, (f (u - a) * f (u - b) - h (u - a) * h (u - b))‖ ≤
        ∫ u in (0 : ℝ)..L, M * Real.exp ((2 * x - 1) * u) :=
      intervalIntegral.norm_integral_le_of_norm_le hL
        (Eventually.of_forall fun u hu => by
          rw [Real.norm_eq_abs]; exact hprod u hu.1.le)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    have h2 : ∫ u in (0 : ℝ)..L, M * Real.exp ((2 * x - 1) * u) ≤
        ∫ u in (0 : ℝ)..L, M * Real.exp ((2 * x - μ) * L) := by
      refine intervalIntegral.integral_mono_on hL (Continuous.intervalIntegrable (by fun_prop) _ _)
        intervalIntegrable_const fun u hu => mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ?_) hM
      rcases le_or_gt 0 (2 * x - 1) with h | h
      · nlinarith [hu.1, hu.2]
      · nlinarith [hu.1, hu.2]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h2
    have h3 : Real.exp (-(2 * x * L)) * (L * (M * Real.exp ((2 * x - μ) * L))) =
        M * L * Real.exp (-(μ * L)) := by
      rw [show (2 * x - μ) * L = 2 * x * L + -(μ * L) by ring, Real.exp_add]
      have hinv : Real.exp (-(2 * x * L)) * Real.exp (2 * x * L) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (L * M * Real.exp (-(μ * L))) * hinv
    calc Real.exp (-(2 * x * L)) *
          ‖∫ u in (0 : ℝ)..L, (f (u - a) * f (u - b) - h (u - a) * h (u - b))‖
        ≤ Real.exp (-(2 * x * L)) * (L * (M * Real.exp ((2 * x - μ) * L))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = M * L * Real.exp (-(μ * L)) := h3
  -- `M L e^{−μL} → 0`
  have hlim : Tendsto (fun L : ℝ => M * L * Real.exp (-(μ * L))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hμpos)
    have h2 := h1.const_mul (M / μ)
    rw [mul_zero] at h2
    refine h2.congr fun L => ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  exact squeeze_zero_norm' (eventually_ge_atTop 0 |>.mono fun L hL => hbound L hL) hlim

/-- For a row, the scaled cofactor Gram at the horizon `T` is the scaled Gram of its log profile at
`L = log(T+1)`; so a row whose log profile is within `K e^{(x−1)u}` of `h` has the escape states
of `h`. -/
theorem tendsto_scaled_rowGram_sub (v : ℕ → ℝ) {h : ℝ → ℝ} (hh : Continuous h) {x K B : ℝ}
    (hx : 0 < x) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hvh : ∀ u, |logProfile v u - h u| ≤ K * Real.exp ((x - 1) * u))
    (hhb : ∀ u, |h u| ≤ B * Real.exp (x * u)) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Tendsto (fun T : ℕ => Real.exp (-(2 * x * Real.log ((T : ℝ) + 1))) *
      (Real.sqrt j * Real.sqrt k * pronicPairing T (rowDilate j v) (rowDilate k v) -
        ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), h (u - Real.log j) * h (u - Real.log k)))
      atTop (𝓝 0) := by
  have hjk : Real.sqrt j * Real.sqrt k ≠ 0 :=
    mul_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hj))
      (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hk))
  have hL : Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ((tendsto_scaled_gram_sub (measurable_logProfile v) hh hx hK hB hvh hhb (Real.log j)
    (Real.log k)).comp hL).congr fun T => ?_
  simp only [Function.comp_apply]
  rw [pronicPairing_rowDilate_eq_translationGram v hj hk T, ← mul_assoc, mul_inv_cancel₀ hjk,
    one_mul]

/-! ### Power rows as dominant configurations -/

/-- **The real profile is a dominant configuration** with frequencies `±Im z_k`. -/
theorem domProfile_append_eq {r : ℕ} {x : ℝ} (c z : Fin r → ℂ) (hz : ∀ k, (z k).re = 1 / 2 + x)
    (u : ℝ) :
    domProfile x (Fin.append (fun k => (z k).im) fun k => -(z k).im)
        (Fin.append (fun k => c k / 2) fun k => conj (c k) / 2) u =
      ((∑ k, powerProfile (c k) (z k) u : ℝ) : ℂ) := by
  unfold domProfile
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hzk : z k - 1 / 2 = (x : ℂ) + ((z k).im : ℂ) * I := by
    have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h12]
    apply Complex.ext <;> simp [hz k]
  have hconj : conj (Complex.exp ((z k - 1 / 2) * (u : ℂ))) =
      Complex.exp (((x : ℂ) + ((-(z k).im : ℝ) : ℂ) * I) * u) := by
    rw [← Complex.exp_conj, hzk]
    congr 1
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [powerProfile, Complex.re_eq_add_conj, map_mul, hconj, hzk]
  push_cast
  ring

/-- The Hermitian Gram of the configuration is the real Gram of the power-sum profile. -/
theorem hermGram_append_eq {r : ℕ} {x : ℝ} (c z : Fin r → ℂ) (hz : ∀ k, (z k).re = 1 / 2 + x)
    (L a b : ℝ) :
    hermGram (domProfile x (Fin.append (fun k => (z k).im) fun k => -(z k).im)
        (Fin.append (fun k => c k / 2) fun k => conj (c k) / 2)) L a b =
      ((∫ u in (0 : ℝ)..L, (∑ k, powerProfile (c k) (z k) (u - a)) *
        ∑ k, powerProfile (c k) (z k) (u - b) : ℝ) : ℂ) := by
  unfold hermGram
  simp_rw [domProfile_append_eq c z hz, Complex.conj_ofReal, ← Complex.ofReal_mul]
  exact intervalIntegral.integral_ofReal

/-- **Escape states of power rows.** Along any horizons, a subsequence of the scaled cofactor Grams
of `Σ_k Re(c_k n^{z_k})`, `Re z_k = ½ + x`, converges for all dilations at once to a phase kernel of
the configuration with frequencies `±Im z_k`. -/
theorem exists_tendsto_powerSum_escapeKernel {r : ℕ} {x : ℝ} (hx : 0 < x) (c z : Fin r → ℂ)
    (hz : ∀ k, (z k).re = 1 / 2 + x) {Ts : ℕ → ℕ} (hT : Tendsto Ts atTop atTop) :
    ∃ θ : Fin (r + r) → ℂ, (∀ i, ‖θ i‖ = 1) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
        Tendsto (fun m => ((Real.exp (-(2 * x * Real.log ((Ts (φ m) : ℝ) + 1))) *
          (Real.sqrt j * Real.sqrt k * pronicPairing (Ts (φ m))
            (rowDilate j fun n => ∑ i, powerRow (c i) (z i) n)
            (rowDilate k fun n => ∑ i, powerRow (c i) (z i) n)) : ℝ) : ℂ)) atTop
          (𝓝 (escapeKernel x (Fin.append (fun k => (z k).im) fun k => -(z k).im)
            (Fin.append (fun k => c k / 2) fun k => conj (c k) / 2) θ (Real.log j)
            (Real.log k))) := by
  have hLT : Tendsto (fun m => Real.log ((Ts m : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hT))
  obtain ⟨θ, hθ, φ, hφ, hlim⟩ := exists_tendsto_escapeKernel hx
    (Fin.append (fun k => (z k).im) fun k => -(z k).im)
    (Fin.append (fun k => c k / 2) fun k => conj (c k) / 2) hLT
  refine ⟨θ, hθ, φ, hφ, fun j k hj hk => ?_⟩
  have hK : 0 ≤ ∑ i, ‖c i‖ * (4 * ‖z i‖ + 1) := by positivity
  have hB : 0 ≤ ∑ i, ‖c i‖ := by positivity
  have hcont : Continuous fun u : ℝ => ∑ i, powerProfile (c i) (z i) u := by
    unfold powerProfile
    fun_prop
  have hrow := (tendsto_scaled_rowGram_sub (fun n => ∑ i, powerRow (c i) (z i) n) hcont hx hK hB
    (abs_logProfile_powerSum_sub_le c z hx hz) (abs_powerSumProfile_le c z hz) hj hk).comp
    (hT.comp hφ.tendsto_atTop)
  have hrowC := (Complex.continuous_ofReal.tendsto 0).comp hrow
  rw [Complex.ofReal_zero] at hrowC
  have hsum := (hlim (Real.log j) (Real.log k)).add hrowC
  rw [add_zero] at hsum
  refine hsum.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [hermGram_append_eq c z hz]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
