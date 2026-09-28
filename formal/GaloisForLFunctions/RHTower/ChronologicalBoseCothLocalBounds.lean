import GaloisForLFunctions.RHTower.ChronologicalBoseCothRemainder
import GaloisForLFunctions.RHTower.ChronologicalBoseKernelJets
import GaloisForLFunctions.RHTower.ChronologicalTailMellin
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Local `L²` bounds for moment-matched residuals near `t = 0`

For a unit row with `Σ a_k = -2` and `Σ a_k k^{2j-1} = -2j/B_{2j}` (`1 ≤ j ≤ m`), the exact
decomposition `r_N(t) = cosh t - 1 - [sinh t - Σ_{j ≤ m} t^{2j-1}/(2j-1)!] + Σ_k a_k R_m(kt)`,
the series tails `cosh t - 1 ≤ (t²/2) cosh t`, `sinh t - Σ_{j ≤ m} … ≤ t^{2m+1}/(2m+1)! · cosh t`
(from `(a + b)! ≥ a! b!`) and `|R_m(z)| ≤ 4 z^{2m+1}/(2π)^{2m+2}` give on `0 < t < 1/N`

  `|r_N(t)| ≤ (e/2) t² + e t^{2m+1}/(2m+1)! + 4 N^{2m+2} t^{2m+1}/(2π)^{2m+2}`,

and Minkowski's inequality gives

  `‖r_N‖_{L²(0,1/N)} ≤ e/(2√5 N^{5/2}) + e/((2m+1)! √(4m+3) N^{2m+3/2}) + 4√N/((2π)^{2m+2} √(4m+3))`.

On the rescaled window `0 ≤ u ≤ log N` the absolute arithmetic remainder
`Σ_k |a_k| |R_m(ku/N)|` has normalized `L²` norm at most
`4 √N (log N)^{2m+3/2}/((2π)^{2m+2} √(4m+3))`, a majorant that increases with `m` once
`log N ≥ 4π`.
-/

open MeasureTheory Set Filter
open scoped Topology Nat Real
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-! ### Tails of the hyperbolic series -/

theorem factorial_mul_factorial_le_factorial_add (i j : ℕ) : i ! * j ! ≤ (i + j)! :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add i j)

/-- `Σ_n t^{2n+k}/(2n+k)! ≤ (t^k/k!) cosh t` for `t ≥ 0`. -/
theorem le_cosh_of_hasSum_shift {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {S : ℝ}
    (hS : HasSum (fun n : ℕ => t ^ (2 * n + k) / (2 * n + k)!) S) :
    S ≤ t ^ k / k ! * Real.cosh t := by
  refine hasSum_le (fun n => ?_) hS ((Real.hasSum_cosh t).mul_left (t ^ k / k !))
  have hfac : ((k ! * (2 * n)! : ℕ) : ℝ) ≤ ((2 * n + k)! : ℝ) := by
    exact_mod_cast (by simpa [add_comm] using factorial_mul_factorial_le_factorial_add k (2 * n))
  have hpos : (0 : ℝ) < k ! * (2 * n)! := by positivity
  rw [pow_add, mul_comm (t ^ (2 * n)), div_mul_div_comm]
  exact div_le_div_of_nonneg_left (by positivity) hpos (by exact_mod_cast hfac)

theorem sinh_sub_taylor_le {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)! ≤
      t ^ (2 * m + 1) / (2 * m + 1)! * Real.cosh t := by
  have h := (hasSum_nat_add_iff' m).mpr (Real.hasSum_sinh t)
  beta_reduce at h
  have hfun : (fun n : ℕ => t ^ (2 * (n + m) + 1) / (2 * (n + m) + 1)!) =
      fun n : ℕ => t ^ (2 * n + (2 * m + 1)) / (2 * n + (2 * m + 1))! := by
    funext n; rw [show 2 * (n + m) + 1 = 2 * n + (2 * m + 1) by ring]
  rw [hfun] at h
  exact le_cosh_of_hasSum_shift ht _ h

theorem sinh_sub_taylor_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)! := by
  have h := (hasSum_nat_add_iff' m).mpr (Real.hasSum_sinh t)
  exact h.nonneg fun n => by positivity

theorem cosh_le_exp_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Real.cosh t ≤ Real.exp 1 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1
  have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  linarith

/-! ### The pointwise majorant -/

/-- **Pointwise bound near `0`.** -/
theorem abs_heatError_le_local {a : ℕ → ℝ} {N m : ℕ}
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1)
    (hsum : ∑ k ∈ Finset.Ioc 0 N, a k = -2)
    (hodd : ∀ j < m, ∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ (2 * j + 1) =
      -(2 * (j + 1)) / (bernoulli (2 * (j + 1)) : ℝ))
    {t : ℝ} (ht0 : 0 < t) (htN : (N : ℝ) * t ≤ 1) :
    |chronologicalHeatError a N t| ≤ Real.exp 1 / 2 * t ^ 2 +
      Real.exp 1 * t ^ (2 * m + 1) / (2 * m + 1)! +
      4 * (N : ℝ) ^ (2 * m + 2) * t ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by
  have hB : ∀ j < m, (bernoulli (2 * (j + 1)) : ℝ) ≠ 0 := fun j _ => by
    exact_mod_cast GaloisForLFunctions.HTGeometry.bernoulli_two_mul_ne_zero (by omega)
  rw [heatError_eq_cosh_sinh_remainder hsum hodd hB ht0]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- the empty row cannot have total mass `-2`
    simp at hsum
  have ht1 : t ≤ 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hcosh := cosh_le_exp_one ht0.le ht1
  have hA0 : 0 ≤ Real.cosh t - 1 := by linarith [Real.one_le_cosh t]
  have hA : Real.cosh t - 1 ≤ Real.exp 1 / 2 * t ^ 2 := by
    refine (HTGeometry.cosh_sub_one_le ht0.le).trans ?_
    calc t ^ 2 / 2 * Real.cosh t ≤ t ^ 2 / 2 * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hcosh (by positivity)
      _ = _ := by ring
  have hS0 := sinh_sub_taylor_nonneg ht0.le m
  have hS : Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)! ≤
      Real.exp 1 * t ^ (2 * m + 1) / (2 * m + 1)! := by
    refine (sinh_sub_taylor_le ht0.le m).trans ?_
    calc t ^ (2 * m + 1) / (2 * m + 1)! * Real.cosh t
        ≤ t ^ (2 * m + 1) / (2 * m + 1)! * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hcosh (by positivity)
      _ = _ := by ring
  have hC : |∑ k ∈ Finset.Ioc 0 N, a k * boseRemainder m (k * t)| ≤
      4 * (N : ℝ) ^ (2 * m + 2) * t ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ioc 0 N, |a k * boseRemainder m (k * t)|
        ≤ ∑ _k ∈ Finset.Ioc 0 N, 4 * ((N : ℝ) * t) ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hk).2
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) (hbound k hk)).trans
            ((abs_boseRemainder_le m (by positivity)).trans ?_)
          gcongr
      _ = _ := by
          rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_pow]; ring
  calc |Real.cosh t - 1 - (Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)!) +
        ∑ k ∈ Finset.Ioc 0 N, a k * boseRemainder m (k * t)|
      ≤ |Real.cosh t - 1| +
          |Real.sinh t - ∑ j ∈ Finset.range m, t ^ (2 * j + 1) / (2 * j + 1)!| +
          |∑ k ∈ Finset.Ioc 0 N, a k * boseRemainder m (k * t)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by
        rw [abs_of_nonneg hA0, abs_of_nonneg hS0]
        linarith

/-! ### Minkowski on an interval -/

theorem sqrt_setIntegral_sq_eq_lpNorm {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable (s.indicator f) volume) :
    Real.sqrt (∫ t in s, f t ^ 2) = lpNorm (s.indicator f) 2 volume := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  have hfun : (fun x => ‖s.indicator f x‖ ^ (2 : ENNReal).toReal) = s.indicator (fun t => f t ^ 2) := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx, Real.norm_eq_abs, sq_abs]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integral_indicator hs, Real.sqrt_eq_rpow]
  norm_num

theorem sqrt_integral_Ioo_sq_monomial (c : ℝ) (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt (∫ t in Ioo 0 δ, (c * t ^ p) ^ 2) =
      |c| * δ ^ p * Real.sqrt δ / Real.sqrt (2 * p + 1) := by
  have hint : ∫ t in Ioo 0 δ, (c * t ^ p) ^ 2 = c ^ 2 * (δ ^ (2 * p + 1) / (2 * p + 1)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ.le]
    simp only [mul_pow, ← pow_mul]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast; ring_nf
  rw [hint, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_div' _ (by positivity),
    show δ ^ (2 * p + 1) = (δ ^ p) ^ 2 * δ by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  ring

/-- Measurable functions bounded on a bounded interval are square integrable after truncation. -/
theorem memLp_indicator_Ioo_of_continuous {δ : ℝ} {F : ℝ → ℝ} (hF : Continuous F) :
    MemLp ((Ioo 0 δ).indicator F) 2 volume := by
  refine (memLp_indicator_iff_restrict measurableSet_Ioo).mpr ?_
  have hc : ContinuousOn F (Icc 0 δ) := hF.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; simp)
  refine MemLp.of_bound hF.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun x hx => hC x (Ioo_subset_Icc_self hx)

/-- **Local `L²` bound on `(0, 1/N)`.** -/
theorem sqrt_integral_sq_heatError_local_le {a : ℕ → ℝ} {N m : ℕ} (hN : 0 < N)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1)
    (hsum : ∑ k ∈ Finset.Ioc 0 N, a k = -2)
    (hodd : ∀ j < m, ∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ (2 * j + 1) =
      -(2 * (j + 1)) / (bernoulli (2 * (j + 1)) : ℝ)) :
    Real.sqrt (∫ t in Ioo 0 (1 / (N : ℝ)), chronologicalHeatError a N t ^ 2) ≤
      Real.exp 1 / (2 * Real.sqrt 5 * (N : ℝ) ^ 2 * Real.sqrt N) +
      Real.exp 1 / ((2 * m + 1)! * Real.sqrt (4 * m + 3) * (N : ℝ) ^ (2 * m + 1) * Real.sqrt N) +
      4 * Real.sqrt N / ((2 * π) ^ (2 * m + 2) * Real.sqrt (4 * m + 3)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := 1 / N with hδ
  have hδ0 : 0 < δ := by positivity
  set s := Ioo (0 : ℝ) δ with hs
  set c₁ : ℝ := Real.exp 1 / 2 with hc₁
  set c₂ : ℝ := Real.exp 1 / (2 * m + 1)! with hc₂
  set c₃ : ℝ := 4 * (N : ℝ) ^ (2 * m + 2) / (2 * π) ^ (2 * m + 2) with hc₃
  set F₁ : ℝ → ℝ := fun t => c₁ * t ^ 2 with hF₁
  set F₂ : ℝ → ℝ := fun t => c₂ * t ^ (2 * m + 1) with hF₂
  set F₃ : ℝ → ℝ := fun t => c₃ * t ^ (2 * m + 1) with hF₃
  have hm₁ := memLp_indicator_Ioo_of_continuous (δ := δ) (F := F₁) (by fun_prop)
  have hm₂ := memLp_indicator_Ioo_of_continuous (δ := δ) (F := F₂) (by fun_prop)
  have hm₃ := memLp_indicator_Ioo_of_continuous (δ := δ) (F := F₃) (by fun_prop)
  have hmeas : Measurable (chronologicalHeatError a N) := by
    have hb := measurable_fusionBoseDefect
    unfold chronologicalHeatError
    fun_prop
  have hr : AEStronglyMeasurable (s.indicator (chronologicalHeatError a N)) volume :=
    (hmeas.indicator measurableSet_Ioo).aestronglyMeasurable
  rw [sqrt_setIntegral_sq_eq_lpNorm measurableSet_Ioo hr]
  have hpt : ∀ t, ‖s.indicator (chronologicalHeatError a N) t‖ ≤
      (s.indicator F₁ + s.indicator F₂ + s.indicator F₃) t := by
    intro t
    by_cases ht : t ∈ s
    · simp only [Pi.add_apply, Set.indicator_of_mem ht, Real.norm_eq_abs, hF₁, hF₂, hF₃, hc₁, hc₂,
        hc₃]
      have htN : (N : ℝ) * t ≤ 1 := by
        have := ht.2; rw [hδ, lt_div_iff₀ hNr] at this; linarith
      refine (abs_heatError_le_local hbound hsum hodd ht.1 htN).trans_eq ?_
      ring
    · simp [Set.indicator_of_notMem ht]
  have hsum3 : MemLp (s.indicator F₁ + s.indicator F₂ + s.indicator F₃) 2 volume :=
    (hm₁.add hm₂).add hm₃
  refine (lpNorm_mono_real hsum3 hpt).trans ?_
  refine (lpNorm_add_le (hm₁.add hm₂) (by norm_num)).trans (add_le_add
    (lpNorm_add_le hm₁ (by norm_num)) le_rfl) |>.trans (le_of_eq ?_)
  have hF : ∀ (c : ℝ) (p : ℕ), lpNorm (s.indicator fun t => c * t ^ p) 2 volume =
      |c| * δ ^ p * Real.sqrt δ / Real.sqrt (2 * p + 1) := fun c p => by
    rw [← sqrt_setIntegral_sq_eq_lpNorm measurableSet_Ioo
      ((memLp_indicator_Ioo_of_continuous (by fun_prop)).aestronglyMeasurable),
      sqrt_integral_Ioo_sq_monomial c p hδ0]
  rw [hF₁, hF₂, hF₃, hF, hF, hF, hc₁, hc₂, hc₃, hδ]
  have h5 : Real.sqrt (2 * (2 : ℕ) + 1) = Real.sqrt 5 := by norm_num
  have h43 : Real.sqrt (2 * ((2 * m + 1 : ℕ) : ℝ) + 1) = Real.sqrt (4 * m + 3) := by
    push_cast; ring_nf
  rw [h5, h43, Real.sqrt_div' 1 hNr.le, Real.sqrt_one, abs_of_pos (by positivity),
    abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hsN2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have h5p : 0 < Real.sqrt 5 := by positivity
  have h43p : 0 < Real.sqrt (4 * m + 3) := Real.sqrt_pos.mpr (by positivity)
  have t1 : Real.exp 1 / 2 * (1 / (N : ℝ)) ^ 2 * (1 / Real.sqrt N) / Real.sqrt 5 =
      Real.exp 1 / (2 * Real.sqrt 5 * (N : ℝ) ^ 2 * Real.sqrt N) := by
    rw [div_pow, one_pow]; field_simp
  have t2 : Real.exp 1 / (2 * m + 1)! * (1 / (N : ℝ)) ^ (2 * m + 1) * (1 / Real.sqrt N) /
      Real.sqrt (4 * m + 3) =
      Real.exp 1 / ((2 * m + 1)! * Real.sqrt (4 * m + 3) * (N : ℝ) ^ (2 * m + 1) * Real.sqrt N) := by
    rw [div_pow, one_pow]; field_simp
  have t3 : 4 * (N : ℝ) ^ (2 * m + 2) / (2 * π) ^ (2 * m + 2) * (1 / (N : ℝ)) ^ (2 * m + 1) *
      (1 / Real.sqrt N) / Real.sqrt (4 * m + 3) =
      4 * Real.sqrt N / ((2 * π) ^ (2 * m + 2) * Real.sqrt (4 * m + 3)) := by
    have hNs : (N : ℝ) / Real.sqrt N = Real.sqrt N := by
      rw [div_eq_iff hsN.ne']; exact hsN2.symm
    calc 4 * (N : ℝ) ^ (2 * m + 2) / (2 * π) ^ (2 * m + 2) * (1 / (N : ℝ)) ^ (2 * m + 1) *
          (1 / Real.sqrt N) / Real.sqrt (4 * m + 3)
        = 4 * ((N : ℝ) / Real.sqrt N) / ((2 * π) ^ (2 * m + 2) * Real.sqrt (4 * m + 3)) := by
          rw [div_pow, one_pow]; field_simp; ring
      _ = _ := by rw [hNs]
  rw [t1, t2, t3]

/-! ### The rescaled logarithmic window -/

/-- The absolute arithmetic remainder `Σ_k |a_k| |R_m(ku/N)|` in the rescaled variable. -/
def absArithRemainder (a : ℕ → ℝ) (N m : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 N, |a k| * |boseRemainder m (k * u / N)|

/-- The window majorant `4 √N (log N)^{2m+3/2}/((2π)^{2m+2} √(4m+3))`. -/
def logWindowMajorant (N m : ℕ) : ℝ :=
  4 * Real.sqrt N * Real.log N ^ (2 * m + 1) * Real.sqrt (Real.log N) /
    ((2 * π) ^ (2 * m + 2) * Real.sqrt (4 * m + 3))

/-- **The absolute remainder on the logarithmic window.** -/
theorem sqrt_window_absArithRemainder_le {a : ℕ → ℝ} {N : ℕ} (m : ℕ) (hN : 1 ≤ N)
    (hbound : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ 1) :
    Real.sqrt ((N : ℝ)⁻¹ * ∫ u in (0 : ℝ)..Real.log N, absArithRemainder a N m u ^ 2) ≤
      logWindowMajorant N m := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hNr
  set c : ℝ := 4 * N / (2 * π) ^ (2 * m + 2) with hc
  have hpt : ∀ u ∈ Icc (0 : ℝ) L, absArithRemainder a N m u ^ 2 ≤ c ^ 2 * u ^ (4 * m + 2) := by
    intro u hu
    have hW0 : 0 ≤ absArithRemainder a N m u :=
      Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hW : absArithRemainder a N m u ≤ c * u ^ (2 * m + 1) := by
      calc absArithRemainder a N m u
          ≤ ∑ _k ∈ Finset.Ioc 0 N, 4 * u ^ (2 * m + 1) / (2 * π) ^ (2 * m + 2) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hk).2
            have hz0 : 0 ≤ (k : ℝ) * u / N := by have := hu.1; positivity
            have hzu : (k : ℝ) * u / N ≤ u := by
              rw [div_le_iff₀ hN0]; nlinarith [hu.1]
            refine (mul_le_of_le_one_left (abs_nonneg _) (hbound k hk)).trans
              ((abs_boseRemainder_le m hz0).trans ?_)
            gcongr
          _ = c * u ^ (2 * m + 1) := by
            rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, hc]; ring
    calc absArithRemainder a N m u ^ 2 ≤ (c * u ^ (2 * m + 1)) ^ 2 := pow_le_pow_left₀ hW0 hW 2
      _ = c ^ 2 * u ^ (4 * m + 2) := by ring
  have hint_rhs : ∫ u in (0 : ℝ)..L, c ^ 2 * u ^ (4 * m + 2) = c ^ 2 * (L ^ (4 * m + 3) / (4 * m + 3)) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; push_cast; ring_nf
  have hle : ∫ u in (0 : ℝ)..L, absArithRemainder a N m u ^ 2 ≤ c ^ 2 * (L ^ (4 * m + 3) / (4 * m + 3)) := by
    by_cases hint : IntervalIntegrable (fun u => absArithRemainder a N m u ^ 2) volume 0 L
    · rw [← hint_rhs]
      exact intervalIntegral.integral_mono_on hL0 hint
        ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _) hpt
    · rw [intervalIntegral.integral_undef hint]; positivity
  have hmaj : Real.sqrt ((N : ℝ)⁻¹ * (c ^ 2 * (L ^ (4 * m + 3) / (4 * m + 3)))) = logWindowMajorant N m := by
    rw [logWindowMajorant, ← hL, hc]
    have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
    have h43 : 0 < Real.sqrt (4 * m + 3) := Real.sqrt_pos.mpr (by positivity)
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have h43s : Real.sqrt (4 * m + 3) * Real.sqrt (4 * m + 3) = 4 * m + 3 :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    rw [show L ^ (4 * m + 3) = (L ^ (2 * m + 1)) ^ 2 * L by ring]
    simp only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * m + 3), Real.sq_sqrt hN0.le,
      Real.sq_sqrt hL0]
    ring
  calc Real.sqrt ((N : ℝ)⁻¹ * ∫ u in (0 : ℝ)..L, absArithRemainder a N m u ^ 2)
      ≤ Real.sqrt ((N : ℝ)⁻¹ * (c ^ 2 * (L ^ (4 * m + 3) / (4 * m + 3)))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle (by positivity))
    _ = logWindowMajorant N m := hmaj

/-- **The window majorant increases with the order** once `log N ≥ 4π`: absolute Taylor estimates
cannot prove the full-window limit. -/
theorem logWindowMajorant_le_succ {N : ℕ} (m : ℕ) (hN : 4 * π ≤ Real.log N) :
    logWindowMajorant N m ≤ logWindowMajorant N (m + 1) := by
  set L := Real.log N with hL
  have hpi := Real.pi_pos
  have hL0 : 0 < L := by linarith
  have hNr : (1 : ℝ) < N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg N) h
    linarith
  have hN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have ha : 0 < Real.sqrt (4 * m + 3) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < Real.sqrt (4 * (m + 1 : ℕ) + 3) := Real.sqrt_pos.mpr (by positivity)
  -- `√(4m+7) ≤ 2 √(4m+3)`
  have hroot : Real.sqrt (4 * (m + 1 : ℕ) + 3) ≤ 2 * Real.sqrt (4 * m + 3) := by
    rw [show (2 : ℝ) * Real.sqrt (4 * m + 3) = Real.sqrt (4 * (4 * m + 3)) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hL2 : 4 * (2 * π) ^ 2 ≤ L ^ 2 := by nlinarith
  rw [logWindowMajorant, logWindowMajorant, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (2 * π) ^ 2 * Real.sqrt (4 * (m + 1 : ℕ) + 3) ≤ L ^ 2 * Real.sqrt (4 * m + 3) := by
    calc (2 * π) ^ 2 * Real.sqrt (4 * (m + 1 : ℕ) + 3) ≤ (2 * π) ^ 2 * (2 * Real.sqrt (4 * m + 3)) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ ≤ (L ^ 2 / 2) * Real.sqrt (4 * m + 3) := by nlinarith
      _ ≤ L ^ 2 * Real.sqrt (4 * m + 3) := by nlinarith [sq_nonneg L]
  have hpow : L ^ (2 * (m + 1) + 1) = L ^ (2 * m + 1) * L ^ 2 := by ring
  have hpow2 : (2 * π) ^ (2 * (m + 1) + 2) = (2 * π) ^ (2 * m + 2) * (2 * π) ^ 2 := by ring
  rw [hpow, hpow2]
  have hP : 0 < 4 * Real.sqrt N * L ^ (2 * m + 1) * Real.sqrt L * (2 * π) ^ (2 * m + 2) := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left key hP.le]

/-- **A sufficient order for the local arithmetic term.**  If
`m_N - log N/(4 log 2π) → +∞`, the third term `4√N/((2π)^{2m_N+2} √(4m_N+3))` of the local bound
tends to zero. -/
theorem tendsto_local_arith_term_of_rate {mN : ℕ → ℕ}
    (hrate : Tendsto (fun N : ℕ => (mN N : ℝ) - Real.log N / (4 * Real.log (2 * π))) atTop atTop) :
    Tendsto (fun N : ℕ => 4 * Real.sqrt N / ((2 * π) ^ (2 * mN N + 2) *
      Real.sqrt (4 * mN N + 3))) atTop (𝓝 0) := by
  have hpi := Real.pi_gt_three
  have h2π : 1 < 2 * π := by linarith
  set L := Real.log (2 * π) with hL
  have hL0 : 0 < L := Real.log_pos h2π
  -- the dominating exponential
  set X : ℕ → ℝ := fun N => (mN N : ℝ) - Real.log N / (4 * L) with hX
  have hlim : Tendsto (fun N : ℕ => 4 * Real.exp (-(2 * L * X N + 2 * L))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 2 * L * X N + 2 * L) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (hrate.const_mul_atTop (by positivity))
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 4
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt N = Real.exp (Real.log N / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNr]; ring_nf
  have hpow : (2 * π) ^ (2 * mN N + 2) = Real.exp ((2 * mN N + 2 : ℕ) * L) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hroot : 1 ≤ Real.sqrt (4 * mN N + 3) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by have := (Nat.cast_nonneg (mN N) : (0 : ℝ) ≤ mN N); linarith)
  calc 4 * Real.sqrt N / ((2 * π) ^ (2 * mN N + 2) * Real.sqrt (4 * mN N + 3))
      ≤ 4 * Real.sqrt N / (2 * π) ^ (2 * mN N + 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact le_mul_of_one_le_right (by positivity) hroot
    _ = 4 * Real.exp (-(2 * L * X N + 2 * L)) := by
        rw [hsq, hpow, mul_div_assoc, ← Real.exp_sub, hX]
        congr 2
        push_cast
        field_simp
        ring

end RHTower
