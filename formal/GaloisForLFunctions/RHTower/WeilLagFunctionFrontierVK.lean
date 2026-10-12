import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem

/-!
# The lag frontier at Vinogradov–Korobov strength

The corpus frontier `weilLagFunctionReal_frontier` gives `Φ(L) = O(e^{L/2} e^{−c L^{1/10}})` from the
medium prime number theorem.  With the Vinogradov–Korobov prime number theorem
(`chebyshevPsi_sub_id_isBigO_vinogradovKorobov`) the same argument gives, for every `θ < 3/5`,

`|Φ(L)| ≤ C e^{L/2} e^{−c L^θ}`   (`weilLagFunctionReal_frontier_rpow`),

and `|a_n| ≤ C √n e^{−c (log n)^θ}` (`integerLag_frontier_rpow`).  The loss `(log log x)^{−5/3}` of the
VK error term is absorbed by `θ < 3/5`.  Against RH's `O(1)` and quasi-RH's `O(e^{(½−δ)L})`, the
proved saving is exactly the VK one.
-/

open MeasureTheory Set Filter Topology
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The Chebyshev error at VK strength -/

/-- For `ex < 3/5`, eventually `(log x)^ex ≤ (log x)^{3/5} (log log x)^{−5/3}`. -/
theorem eventually_rpow_le_vkExponent {ex : ℝ} (hex : ex < 3 / 5) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ ex ≤
      Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-((5 : ℝ) / 3)) := by
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 3 * (3 / 5 - ex) / 5 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  have hlo := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < 1 by norm_num)
  have hL := Real.tendsto_log_atTop
  filter_upwards [hL.eventually hlo, hL.eventually (eventually_ge_atTop (Real.exp 1))] with x h1 h2
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  rw [← hLdef] at h1 h2 ⊢
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) h2
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (Real.rpow_nonneg hL0.le r), one_mul] at h1
  have h3 : Real.log L ^ ((5 : ℝ) / 3) ≤ L ^ (3 / 5 - ex) := by
    have := Real.rpow_le_rpow (by linarith) h1 (show (0 : ℝ) ≤ 5 / 3 by norm_num)
    rwa [← Real.rpow_mul hL0.le, show r * (5 / 3) = 3 / 5 - ex by rw [hrdef]; ring] at this
  have hp1 : 0 < Real.log L ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp1]
  have hsplit : L ^ ((3 : ℝ) / 5) = L ^ ex * L ^ (3 / 5 - ex) := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hL0.le ex)

/-- **The Chebyshev error at VK strength.**  For `0 < ex < 3/5`,
`|ψ(t) − t| ≤ C t e^{−c (log t)^ex}` for large `t`. -/
theorem chebyshevError_bound_rpow {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5) :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
      |chebyshevError t| ≤ C * (t * Real.exp (-c * Real.log t ^ ex)) := by
  obtain ⟨c, hc, hO⟩ := Sieve.chebyshevPsi_sub_id_isBigO_vinogradovKorobov
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, hc, |C|, abs_nonneg _, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1, eventually_rpow_le_vkExponent hex] with t ht ht1 hvk
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
  simp only [Pi.sub_apply, id_eq] at ht
  unfold chebyshevError
  have hpos : 0 ≤ t * Real.exp (-c * (Real.log t ^ ((3 : ℝ) / 5) *
      Real.log (Real.log t) ^ (-((5 : ℝ) / 3)))) := by positivity
  rw [abs_of_nonneg hpos] at ht
  have hle : Real.exp (-c * (Real.log t ^ ((3 : ℝ) / 5) *
      Real.log (Real.log t) ^ (-((5 : ℝ) / 3)))) ≤ Real.exp (-c * Real.log t ^ ex) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc |ψ t - t| ≤ C * (t * Real.exp (-c * (Real.log t ^ ((3 : ℝ) / 5) *
        Real.log (Real.log t) ^ (-((5 : ℝ) / 3))))) := ht
    _ ≤ |C| * (t * Real.exp (-c * (Real.log t ^ ((3 : ℝ) / 5) *
        Real.log (Real.log t) ^ (-((5 : ℝ) / 3))))) := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * (t * Real.exp (-c * Real.log t ^ ex)) := by gcongr

/-- `e^{−c u^ex} ≤ N!/(c^N u²)` for `u ≥ 1`, `N = ⌈2/ex⌉`. -/
theorem exp_neg_rpow_le_inv_sq {c ex u : ℝ} (hc : 0 < c) (hex : 0 < ex) (hu : 1 ≤ u) :
    Real.exp (-c * u ^ ex) ≤ (Nat.factorial ⌈2 / ex⌉₊ : ℝ) / (c ^ ⌈2 / ex⌉₊ * u ^ 2) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈2 / ex⌉₊ := ⟨_, rfl⟩
  rw [← hN]
  have hu0 : 0 < u := by linarith
  have hx : 0 ≤ c * u ^ ex := by positivity
  have h := Real.pow_div_factorial_le_exp (c * u ^ ex) hx N
  have hNex : 2 ≤ (N : ℝ) * ex := by
    have := Nat.le_ceil (2 / ex); rw [← hN] at this
    rw [div_le_iff₀ hex] at this; linarith
  have hpow : u ^ (2 : ℝ) ≤ (u ^ ex) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
    exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hcN : 0 < c ^ N := pow_pos hc N
  have hE : 0 < Real.exp (c * u ^ ex) := Real.exp_pos _
  have hA : 0 < (c * u ^ ex) ^ N / N.factorial := by
    have : 0 < c * u ^ ex := by positivity
    positivity
  have hpow' : u ^ 2 ≤ (u ^ ex) ^ N := by
    have := hpow; rwa [Real.rpow_two] at this
  rw [show -c * u ^ ex = -(c * u ^ ex) by ring, Real.exp_neg]
  calc (Real.exp (c * u ^ ex))⁻¹ ≤ ((c * u ^ ex) ^ N / N.factorial)⁻¹ := inv_anti₀ hA h
    _ = N.factorial / (c ^ N * (u ^ ex) ^ N) := by rw [inv_div, mul_pow]
    _ ≤ N.factorial / (c ^ N * u ^ 2) :=
        div_le_div_of_nonneg_left hfac.le (by positivity) (mul_le_mul_of_nonneg_left hpow' hcN.le)


theorem integrableOn_expDecay_div_rpow {ex c : ℝ} (hex : 0 < ex) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * Real.log t ^ ex) / t) (Ioi 1) := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hmeas : Measurable (fun t : ℝ => Real.exp (-c * Real.log t ^ ex) / t) := by
    fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi he.le]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : 1 < t := ht.1
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le)]
    calc Real.exp (-c * Real.log t ^ ex) / t ≤ 1 / t := by
          refine div_le_div_of_nonneg_right ?_ ht0.le
          rw [Real.exp_le_one_iff]
          have : 0 ≤ Real.log t ^ ex := Real.rpow_nonneg (Real.log_nonneg ht1.le) _
          nlinarith
      _ ≤ 1 := by rw [div_le_one ht0]; exact ht1.le
  · refine Integrable.mono' (integrableOn_inv_mul_log_sq.const_mul
      ((Nat.factorial ⌈2 / ex⌉₊ : ℝ) / c ^ ⌈2 / ex⌉₊)) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hte : Real.exp 1 < t := ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos 1) hte
    have hlog : 1 < Real.log t := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_lt_log (Real.exp_pos 1) hte
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le)]
    have h1 := exp_neg_rpow_le_inv_sq hc hex hlog.le
    calc Real.exp (-c * Real.log t ^ ex) / t
        ≤ ((Nat.factorial ⌈2 / ex⌉₊ : ℝ) / (c ^ ⌈2 / ex⌉₊ * Real.log t ^ 2)) / t := by gcongr
      _ = (Nat.factorial ⌈2 / ex⌉₊ : ℝ) / c ^ ⌈2 / ex⌉₊ * (1 / (t * Real.log t ^ 2)) := by
          field_simp

/-! ## The Mertens deviation and the lag frontier -/

theorem mertensDeviation_bound_rpow {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5) : ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x + Real.eulerMascheroniConstant|
      ≤ C * Real.exp (-c * Real.log x ^ ex) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := chebyshevError_bound_rpow hex0 hex
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  have hc2 : 0 < c / 2 := by linarith
  set h : ℝ → ℝ := fun t => Real.exp (-(c / 2) * Real.log t ^ ex) / t with hh
  have hhint : IntegrableOn h (Ioi 1) := integrableOn_expDecay_div_rpow hex0 hc2
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
  set A : ℝ := Real.exp (-(c / 2) * Real.log x ^ ex) with hA
  have hA0 : 0 < A := Real.exp_pos _
  -- the pointwise term
  have h1 : |chebyshevError x / x| ≤ C * A := by
    have := hT₀ x hxT
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc |chebyshevError x| ≤ C * (x * Real.exp (-c * Real.log x ^ ex)) := this
      _ ≤ C * (x * A) := by
          gcongr
          rw [hA]
          apply Real.exp_le_exp.mpr
          have : 0 ≤ Real.log x ^ ex := by positivity
          nlinarith
      _ = C * A * x := by ring
  -- the tail term
  have hmaj : ∀ t ∈ Ioi x, ‖chebyshevError t / t ^ 2‖ ≤ (C * A) * h t := by
    intro t ht
    have htx : x < t := ht
    have ht0 : 0 < t := lt_trans hx0 htx
    have htT : T₀ ≤ t := le_trans hxT htx.le
    have hlogt : Real.log x ≤ Real.log t := Real.log_le_log hx0 htx.le
    have hrpow : Real.log x ^ ex ≤ Real.log t ^ ex :=
      Real.rpow_le_rpow hlogx hlogt hex0.le
    have hE := hT₀ t htT
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    have hsplit : Real.exp (-c * Real.log t ^ ex)
        = Real.exp (-(c / 2) * Real.log t ^ ex) *
          Real.exp (-(c / 2) * Real.log t ^ ex) := by
      rw [← Real.exp_add]; congr 1; ring
    have hle : Real.exp (-(c / 2) * Real.log t ^ ex) ≤ A := by
      rw [hA]; apply Real.exp_le_exp.mpr; nlinarith
    calc |chebyshevError t| ≤ C * (t * Real.exp (-c * Real.log t ^ ex)) := hE
      _ = C * t * (Real.exp (-(c / 2) * Real.log t ^ ex) *
            Real.exp (-(c / 2) * Real.log t ^ ex)) := by rw [hsplit]; ring
      _ ≤ C * t * (A * Real.exp (-(c / 2) * Real.log t ^ ex)) := by
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


/-- **The lag frontier at VK strength.**  `|Φ(L)| ≤ C e^{L/2} e^{−c L^θ}` for every `θ < 3/5`. -/
theorem weilLagFunctionReal_frontier_rpow {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5) : ∃ c > 0, ∃ C : ℝ, ∀ᶠ L : ℝ in atTop,
    |weilLagFunctionReal L| ≤ C * Real.exp (L / 2) * Real.exp (-c * L ^ ex) := by
  obtain ⟨c₁, hc₁, C₁, hC₁0, hE⟩ := chebyshevError_bound_rpow hex0 hex
  obtain ⟨c₂, hc₂, C₂, hC₂0, hM⟩ := mertensDeviation_bound_rpow hex0 hex
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
  have hL10 : 0 ≤ L ^ ex := by positivity
  rw [weilLagFunctionReal_eq_prime_side hL0, mertensSum_eq_Icc_zero]
  rw [Real.log_exp] at hEL hML
  set D : ℝ := Real.exp (-c * L ^ ex) with hD
  have hD0 : 0 < D := Real.exp_pos _
  have hDle : ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * L ^ ex) ≤ D := by
    intro c' hc'
    rw [hD]; apply Real.exp_le_exp.mpr; nlinarith
  -- the three pieces
  have hp1 : |Real.exp (-L / 2) * (Real.exp L - ψ (Real.exp L))| ≤ C₁ * Real.exp (L / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have : |Real.exp L - ψ (Real.exp L)| = |chebyshevError (Real.exp L)| := by
      unfold chebyshevError; rw [← abs_neg]; congr 1; ring
    rw [this]
    calc Real.exp (-L / 2) * |chebyshevError (Real.exp L)|
        ≤ Real.exp (-L / 2) * (C₁ * (Real.exp L * Real.exp (-c₁ * L ^ ex))) := by
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
        ≤ Real.exp (L / 2) * (C₂ * Real.exp (-c₂ * L ^ ex)) := by gcongr
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
      have h1 : L ^ ex ≤ L := by
        calc L ^ ex ≤ L ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
          _ = L := Real.rpow_one L
      have h2 : c * L ^ ex ≤ L := by
        calc c * L ^ ex ≤ 1 * L ^ ex :=
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


/-- **The integer lag frontier at VK strength.**  `|a_n| ≤ C √n e^{−c (log n)^θ}` for every
`θ < 3/5`. -/
theorem integerLag_frontier_rpow {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |integerLag n| ≤ C * Real.sqrt n * Real.exp (-c * Real.log n ^ ex) := by
  obtain ⟨c, hc, C, hL⟩ := weilLagFunctionReal_frontier_rpow hex0 hex
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

end

end RHTower
