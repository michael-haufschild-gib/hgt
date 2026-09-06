import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant

/-!
# The unconditional frontier of the lag function

RH is `Φ(L) = O(1)`.  The prime number theorem with the error term of the corpus gives, with no
hypothesis, `Φ(L) = O(e^{L/2} e^{−c L^{1/10}})`, i.e. `a_n = O(√n · e^{−c (log n)^{1/10}})`: the lag
exponent is `½` minus a subexponential loss, and the whole distance to RH is the exponent `½`.
The input is the quantitative Mertens deviation `Σ_{k≤x}Λ(k)/k − log x + γ = E(x)/x − ∫_x^∞ E(t)t^{−2}dt`
with `E = ψ − id`, bounded by the same error term.
-/

open MeasureTheory Set Filter Topology
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The Mertens deviation as a tail integral of the Chebyshev error -/

theorem mertensSum_eq_Icc_zero (n : ℕ) :
    mertensSum n = ∑ k ∈ Finset.Icc 0 n, vonMangoldt k / (k : ℝ) := by
  unfold mertensSum
  have h : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert (by simp)]
  simp

theorem mertens_key {x : ℝ} (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x =
      1 + chebyshevError x / x + ∫ t in (1 : ℝ)..x, chebyshevError t / t ^ 2 := by
  rw [sum_vonMangoldt_div_eq hx]
  have hx0 : 0 < x := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => chebyshevError t / t ^ 2) volume 1 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact integrableOn_chebyshevError_div_sq.mono_set Ioc_subset_Ioi_self
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (by linarith [ht.1]))
  have hpsi : (fun t : ℝ => ψ t / t ^ 2) = fun t => t⁻¹ + chebyshevError t / t ^ 2 := by
    funext t
    unfold chebyshevError
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
      ring
  rw [hpsi, intervalIntegral.integral_add hinv hint, integral_inv_of_pos one_pos hx0, div_one]
  unfold chebyshevError
  field_simp
  ring

/-- `Σ_{k≤x}Λ(k)/k − log x + γ = E(x)/x − ∫_x^∞ E(t) t^{−2} dt`. -/
theorem mertensDeviation_eq {x : ℝ} (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x + Real.eulerMascheroniConstant
      = chebyshevError x / x - ∫ t in Ioi x, chebyshevError t / t ^ 2 := by
  have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi 1) :=
    integrableOn_chebyshevError_div_sq
  have hsplit : ∫ t in Ioi 1, chebyshevError t / t ^ 2
      = (∫ t in Ioc 1 x, chebyshevError t / t ^ 2) + ∫ t in Ioi x, chebyshevError t / t ^ 2 := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx)),
      Set.Ioc_union_Ioi_eq_Ioi hx]
  rw [integral_chebyshevError_div_sq] at hsplit
  have hkey := mertens_key hx
  rw [intervalIntegral.integral_of_le hx] at hkey
  linarith

/-! ## An integrable majorant -/

/-- `e^{−c (log t)^{1/10}}/t` is integrable on `(1, ∞)`. -/
theorem integrableOn_expDecay_div {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) / t) (Ioi 1) := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hmeas : Measurable (fun t : ℝ => Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) / t) := by
    fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi he.le]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 < t := ht.1
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le)]
    calc Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) / t ≤ 1 / t := by
          refine div_le_div_of_nonneg_right ?_ ht0.le
          rw [Real.exp_le_one_iff]
          have : 0 ≤ Real.log t ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Real.log_nonneg ht1.le) _
          nlinarith
      _ ≤ 1 := by rw [div_le_one ht0]; exact ht1.le
  · refine Integrable.mono' (integrableOn_inv_mul_log_sq.const_mul ((Nat.factorial 20 : ℝ) / c ^ 20))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hte : Real.exp 1 < t := ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos 1) hte
    have hlog : 1 < Real.log t := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_lt_log (Real.exp_pos 1) hte
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le)]
    have h1 := exp_neg_rpow_tenth_le hc (by linarith : 0 < Real.log t)
    calc Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) / t
        ≤ ((Nat.factorial 20 : ℝ) / (c ^ 20 * Real.log t ^ 2)) / t := by gcongr
      _ = (Nat.factorial 20 : ℝ) / c ^ 20 * (1 / (t * Real.log t ^ 2)) := by
          field_simp

/-! ## The quantitative Mertens deviation -/

theorem mertensDeviation_bound : ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x + Real.eulerMascheroniConstant|
      ≤ C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := chebyshevError_bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  have hc2 : 0 < c / 2 := by linarith
  set h : ℝ → ℝ := fun t => Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10)) / t with hh
  have hhint : IntegrableOn h (Ioi 1) := integrableOn_expDecay_div hc2
  have hh0 : ∀ t, 0 < t → 0 ≤ h t := fun t ht => by rw [hh]; positivity
  set K : ℝ := ∫ t in Ioi 1, h t with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun t ht => hh0 t (lt_trans one_pos ht)
  refine ⟨c / 2, hc2, C * (1 + K), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with x hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxT : T₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [mertensDeviation_eq hx1]
  set A : ℝ := Real.exp (-(c / 2) * Real.log x ^ ((1 : ℝ) / 10)) with hA
  have hA0 : 0 < A := Real.exp_pos _
  -- the pointwise term
  have h1 : |chebyshevError x / x| ≤ C * A := by
    have := hT₀ x hxT
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc |chebyshevError x| ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := this
      _ ≤ C * (x * A) := by
          gcongr
          rw [hA]
          apply Real.exp_le_exp.mpr
          have : 0 ≤ Real.log x ^ ((1 : ℝ) / 10) := by positivity
          nlinarith
      _ = C * A * x := by ring
  -- the tail term
  have hmaj : ∀ t ∈ Ioi x, ‖chebyshevError t / t ^ 2‖ ≤ (C * A) * h t := by
    intro t ht
    have htx : x < t := ht
    have ht0 : 0 < t := lt_trans hx0 htx
    have htT : T₀ ≤ t := le_trans hxT htx.le
    have hlogt : Real.log x ≤ Real.log t := Real.log_le_log hx0 htx.le
    have hrpow : Real.log x ^ ((1 : ℝ) / 10) ≤ Real.log t ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hlogx hlogt (by norm_num)
    have hE := hT₀ t htT
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    have hsplit : Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))
        = Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10)) *
          Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10)) ≤ A := by
      rw [hA]; apply Real.exp_le_exp.mpr; nlinarith
    calc |chebyshevError t| ≤ C * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := hE
      _ = C * t * (Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10)) *
            Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10))) := by rw [hsplit]; ring
      _ ≤ C * t * (A * Real.exp (-(c / 2) * Real.log t ^ ((1 : ℝ) / 10))) := by
          gcongr
      _ = (C * A) * h t * t ^ 2 := by rw [hh]; field_simp
  have hEint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hx1)
  have hhx : IntegrableOn h (Ioi x) := hhint.mono_set (Ioi_subset_Ioi hx1)
  have h2 : ‖∫ t in Ioi x, chebyshevError t / t ^ 2‖ ≤ C * A * K := by
    calc ‖∫ t in Ioi x, chebyshevError t / t ^ 2‖
        ≤ ∫ t in Ioi x, ‖chebyshevError t / t ^ 2‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi x, (C * A) * h t :=
          setIntegral_mono_on hEint.norm (hhx.const_mul _) measurableSet_Ioi hmaj
      _ = (C * A) * ∫ t in Ioi x, h t := integral_const_mul _ _
      _ ≤ (C * A) * K := by
          gcongr
          refine setIntegral_mono_set hhint ?_ ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hh0 t (lt_trans one_pos ht)
          · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hx1)
  rw [Real.norm_eq_abs] at h2
  calc |chebyshevError x / x - ∫ t in Ioi x, chebyshevError t / t ^ 2|
      ≤ |chebyshevError x / x| + |∫ t in Ioi x, chebyshevError t / t ^ 2| := abs_sub _ _
    _ ≤ C * A + C * A * K := add_le_add h1 h2
    _ = C * (1 + K) * A := by ring

/-! ## The frontier bound for the lag function -/

/-- **The unconditional lag frontier.**  `|Φ(L)| ≤ C e^{L/2} e^{−c L^{1/10}}` for large `L`. -/
theorem weilLagFunctionReal_frontier : ∃ c > 0, ∃ C : ℝ, ∀ᶠ L : ℝ in atTop,
    |weilLagFunctionReal L| ≤ C * Real.exp (L / 2) * Real.exp (-c * L ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁0, hE⟩ := chebyshevError_bound
  obtain ⟨c₂, hc₂, C₂, hC₂0, hM⟩ := mertensDeviation_bound
  set c : ℝ := min (min c₁ c₂) 1 with hc
  have hc0 : 0 < c := by positivity
  have hcc₁ : c ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1 : c ≤ 1 := min_le_right _ _
  refine ⟨c, hc0, C₁ + C₂ + (Real.log (2 * Real.pi) + 1), ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hE, Real.tendsto_exp_atTop.eventually hM,
    eventually_ge_atTop 1] with L hEL hML hL1
  have hL0 : 0 < L := by linarith
  have hX1 : (1 : ℝ) ≤ Real.exp L := by
    have := Real.add_one_le_exp L; linarith
  have hL10 : 0 ≤ L ^ ((1 : ℝ) / 10) := by positivity
  rw [weilLagFunctionReal_eq_prime_side hL0, mertensSum_eq_Icc_zero]
  rw [Real.log_exp] at hEL hML
  set D : ℝ := Real.exp (-c * L ^ ((1 : ℝ) / 10)) with hD
  have hD0 : 0 < D := Real.exp_pos _
  have hDle : ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * L ^ ((1 : ℝ) / 10)) ≤ D := by
    intro c' hc'
    rw [hD]; apply Real.exp_le_exp.mpr; nlinarith
  -- the three pieces
  have hp1 : |Real.exp (-L / 2) * (Real.exp L - ψ (Real.exp L))| ≤ C₁ * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have : |Real.exp L - ψ (Real.exp L)| = |chebyshevError (Real.exp L)| := by
      unfold chebyshevError; rw [← abs_neg]; congr 1; ring
    rw [this]
    calc Real.exp (-L / 2) * |chebyshevError (Real.exp L)|
        ≤ Real.exp (-L / 2) * (C₁ * (Real.exp L * Real.exp (-c₁ * L ^ ((1 : ℝ) / 10)))) := by
          gcongr
      _ ≤ Real.exp (-L / 2) * (C₁ * (Real.exp L * D)) := by gcongr; exact hDle c₁ hcc₁
      _ = C₁ * Real.exp (L / 2) * D := by
          rw [show Real.exp (-L / 2) * (C₁ * (Real.exp L * D))
            = C₁ * (Real.exp (-L / 2) * Real.exp L) * D by ring, ← Real.exp_add]
          congr 2; ring
  have hp2 : |Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / k) - L
      + Real.eulerMascheroniConstant)| ≤ C₂ * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (L / 2) * |(∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / k) - L
          + Real.eulerMascheroniConstant|
        ≤ Real.exp (L / 2) * (C₂ * Real.exp (-c₂ * L ^ ((1 : ℝ) / 10))) := by gcongr
      _ ≤ Real.exp (L / 2) * (C₂ * D) := by gcongr; exact hDle c₂ hcc₂
      _ = C₂ * Real.exp (L / 2) * D := by ring
  have hp3 : |Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi))|
      ≤ (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hS0 := trivialZeroSeriesReal_nonneg hX1
    have hS1 := trivialZeroSeriesReal_le_one hX1
    have hl0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have habs : |trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)|
        ≤ Real.log (2 * Real.pi) + 1 := by
      rw [abs_le]; constructor <;> linarith
    -- e^{−L/2} ≤ e^{L/2} D since e^{−L} ≤ D
    have hexp : Real.exp (-L / 2) ≤ Real.exp (L / 2) * D := by
      rw [hD, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : L ^ ((1 : ℝ) / 10) ≤ L := by
        calc L ^ ((1 : ℝ) / 10) ≤ L ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          _ = L := Real.rpow_one L
      have h2 : c * L ^ ((1 : ℝ) / 10) ≤ L := by
        calc c * L ^ ((1 : ℝ) / 10) ≤ 1 * L ^ ((1 : ℝ) / 10) :=
              mul_le_mul_of_nonneg_right hc1 hL10
          _ ≤ L := by linarith
      linarith
    calc Real.exp (-L / 2) * |trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)|
        ≤ (Real.exp (L / 2) * D) * (Real.log (2 * Real.pi) + 1) :=
          mul_le_mul hexp habs (abs_nonneg _) (by positivity)
      _ = (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D := by ring
  have hsplit : Real.exp (-L / 2) * ((Real.exp L - ψ (Real.exp L))
      + Real.exp L * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / k) - L
        + Real.eulerMascheroniConstant) - Real.log (2 * Real.pi) + trivialZeroSeriesReal (Real.exp L))
      = Real.exp (-L / 2) * (Real.exp L - ψ (Real.exp L))
        + Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / k) - L
          + Real.eulerMascheroniConstant)
        + Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi)) := by
    have : Real.exp (-L / 2) * Real.exp L = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  rw [hsplit]
  calc _ ≤ |Real.exp (-L / 2) * (Real.exp L - ψ (Real.exp L))|
        + |Real.exp (L / 2) * ((∑ k ∈ Finset.Icc 0 ⌊Real.exp L⌋₊, vonMangoldt k / k) - L
          + Real.eulerMascheroniConstant)|
        + |Real.exp (-L / 2) * (trivialZeroSeriesReal (Real.exp L) - Real.log (2 * Real.pi))| :=
        (abs_add_three _ _ _)
    _ ≤ C₁ * Real.exp (L / 2) * D + C₂ * Real.exp (L / 2) * D
        + (Real.log (2 * Real.pi) + 1) * Real.exp (L / 2) * D := add_le_add (add_le_add hp1 hp2) hp3
    _ = (C₁ + C₂ + (Real.log (2 * Real.pi) + 1)) * Real.exp (L / 2) * D := by ring

/-- **The unconditional integer frontier.**  `|a_n| ≤ C √n e^{−c (log n)^{1/10}}` for large `n`,
against RH's `|a_n| ≤ a_1`. -/
theorem integerLag_frontier : ∃ c > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    |integerLag n| ≤ C * Real.sqrt n * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, C, hL⟩ := weilLagFunctionReal_frontier
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hL
  refine ⟨c, hc, C, ?_⟩
  filter_upwards [eventually_ge_atTop (⌈Real.exp L₀⌉₊ + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hlog : L₀ ≤ Real.log n := by
    rw [← Real.log_exp L₀]
    apply Real.log_le_log (Real.exp_pos _)
    calc Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast (by omega : ⌈Real.exp L₀⌉₊ ≤ n)
  have := hL₀ _ hlog
  unfold integerLag
  rwa [Real.exp_half, Real.exp_log hn0] at this

/-- The lag function is `o(e^{L/2})`: the lag exponent is at most `½` unconditionally. -/
theorem tendsto_weilLagFunctionReal_mul_exp_neg_half :
    Tendsto (fun L : ℝ => weilLagFunctionReal L * Real.exp (-L / 2)) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hL⟩ := weilLagFunctionReal_frontier
  have h1 : Tendsto (fun L : ℝ => |C| * Real.exp (-c * L ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun L : ℝ => c * L ^ ((1 : ℝ) / 10)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).const_mul_atTop hc
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul |C|
    simp only [mul_zero] at h3
    refine h3.congr fun L => ?_
    simp only [Function.comp_def, neg_mul]
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [hL, eventually_ge_atTop 0] with L hLb hL0
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |weilLagFunctionReal L| * Real.exp (-L / 2)
      ≤ (C * Real.exp (L / 2) * Real.exp (-c * L ^ ((1 : ℝ) / 10))) * Real.exp (-L / 2) :=
        mul_le_mul_of_nonneg_right hLb (Real.exp_pos _).le
    _ = C * Real.exp (-c * L ^ ((1 : ℝ) / 10)) * (Real.exp (L / 2) * Real.exp (-L / 2)) := by ring
    _ = C * Real.exp (-c * L ^ ((1 : ℝ) / 10)) := by
        rw [← Real.exp_add, show L / 2 + -L / 2 = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ |C| * Real.exp (-c * L ^ ((1 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le

end

end RHTower
