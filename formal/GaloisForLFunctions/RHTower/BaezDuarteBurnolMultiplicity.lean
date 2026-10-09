import GaloisForLFunctions.RHTower.BaezDuarteLogDualCrossEnergy
import GaloisForLFunctions.RHTower.BaezDuarteDistanceBurnolLowerBound
import GaloisForLFunctions.HTGeometry.LegendreEndpointExtremal

/-!
# Burnol's multiplicity-weighted lower bound for the Báez-Duarte distances

For a zero `ρ` of `ζ` on the critical line at which `ζ, ζ′, …, ζ^{(m−1)}` vanish,

  `liminf_{N→∞} d_N² log N ≥ 2m²/|ρ|²`   (`eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZero`).

For `m = 1` this is the corpus bound `eventually_le_bdDistDiscrete_sq_mul_log_of_zero`.  For a
finite set `Z` of such zeros with orders `≥ m(ρ)`,
`liminf d_N² log N ≥ Σ_{ρ ∈ Z} 2m(ρ)²/|ρ|²` (`eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZeros`).

**Proof.**  Take `Y = N^{1+η}`, `L = log Y`, and the dual `A_k = Re(p_m(log k/L)k^{−ρ})ψ(k/Y)` with
the Legendre endpoint extremal `p_m` (`p_m(0) = 1`, `∫_0^1 p_m² = 1/m²`, module
`HTGeometry/LegendreEndpointExtremal`).
* It is a combination of the derivative duals `(−log k)^j k^{−ρ}ψ(k/Y)`, `j < m`, whose divisor
  defects are `O(m^A Y^{−A})` (`exists_norm_bdModDefect_logZeroSmoothDual_le`).  The corpus Möbius
  correction removes them at bounded energy.
* Its energy is at most `(|ρ|²/2)Σ_{k ≤ 3Y} p_m(log k/L)²/k + O(1)`
  (`exists_bdDualEnergy_polyLogDual_le`), and the sum is `L∫_0^1 p_m² + O(1) = L/m² + O(1)`
  (`exists_sum_polyLog_sq_div_le`).
* The dual-sequence inequality gives `1 ≤ d_N²((1 + η)²(|ρ|²/2m²) log N + K)`, and `η → 0`.
-/

open Complex Set Filter Topology Metric MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.LegendreEndpoint

/-! ## From the log sum to the integral -/

/-- `Σ_{k ≤ 3Y} p(log k/L)²/k ≤ L ∫_0^1 p² + C`, `L = log Y`, for all `Y ≥ e`. -/
theorem exists_sum_polyLog_sq_div_le (p : Polynomial ℝ) :
    ∃ C : ℝ, ∀ Y : ℝ, Real.exp 1 ≤ Y →
      ∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊, p.eval (Real.log k / Real.log Y) ^ 2 / k ≤
        Real.log Y * (∫ x in (0 : ℝ)..1, p.eval x ^ 2) + C := by
  obtain ⟨H₀, hH₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  obtain ⟨Λ₀, hΛ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.derivative.continuous.continuousOn
  set H : ℝ := max H₀ 0 with hHdef
  set Λ : ℝ := max Λ₀ 0 with hΛdef
  have hH0 : 0 ≤ H := le_max_right _ _
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hpH : ∀ x ∈ Icc (0 : ℝ) 4, |p.eval x| ≤ H := fun x hx =>
    (hH₀ x hx).trans (le_max_left _ _)
  have hpLip : ∀ x ∈ Icc (0 : ℝ) 4, ∀ y ∈ Icc (0 : ℝ) 4,
      |p.eval x - p.eval y| ≤ Λ * |x - y| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => p.eval x) (C := Λ)
      (fun z _ => p.differentiableAt) (fun z hz => by
        rw [p.deriv]; exact (hΛ₀ z hz).trans (le_max_left _ _)) (convex_Icc 0 4) hy hx
    simpa [Real.norm_eq_abs] using h
  refine ⟨4 * H ^ 2 + 4 * H * Λ, fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hY
  have hY0 : 0 < Y := by linarith
  set L : ℝ := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL0 : 0 < L := by linarith
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  set g : ℝ → ℝ := fun t => p.eval (t / L) ^ 2 with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hlogM1 : Real.log ((M : ℝ) + 1) ≤ L + 2 := by
    have h1 : (M : ℝ) + 1 ≤ 4 * Y := by
      have : (M : ℝ) ≤ 3 * Y := Nat.floor_le (by positivity)
      linarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) hY0.ne'] at this
    have hl4 : Real.log 4 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have h3 := Real.log_two_lt_d9
      norm_num at h3
      linarith
    linarith
  have hdom : ∀ t, 0 ≤ t → t ≤ L + 2 → t / L ∈ Icc (0 : ℝ) 4 := by
    intro t ht0 ht
    refine ⟨div_nonneg ht0 hL0.le, ?_⟩
    rw [div_le_iff₀ hL0]; linarith
  have hgH : ∀ t, 0 ≤ t → t ≤ L + 2 → g t ≤ H ^ 2 := by
    intro t ht0 ht
    simp only [hg]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hpH _ (hdom t ht0 ht)) 2
  have hgLip : ∀ s t, 0 ≤ s → s ≤ L + 2 → 0 ≤ t → t ≤ L + 2 → |g s - g t| ≤ 2 * H * Λ * |s - t| := by
    intro s t hs0 hs ht0 ht
    simp only [hg]
    have h1 := hpLip _ (hdom s hs0 hs) _ (hdom t ht0 ht)
    have hs' := hpH _ (hdom s hs0 hs)
    have ht' := hpH _ (hdom t ht0 ht)
    rw [show p.eval (s / L) ^ 2 - p.eval (t / L) ^ 2 =
      (p.eval (s / L) - p.eval (t / L)) * (p.eval (s / L) + p.eval (t / L)) by ring, abs_mul]
    have hsum : |p.eval (s / L) + p.eval (t / L)| ≤ 2 * H := by
      have := abs_add_le (p.eval (s / L)) (p.eval (t / L)); linarith
    have hdiv : |s / L - t / L| ≤ |s - t| := by
      rw [← sub_div, abs_div, abs_of_pos hL0]
      exact div_le_self (abs_nonneg _) hL1
    calc |p.eval (s / L) - p.eval (t / L)| * |p.eval (s / L) + p.eval (t / L)|
        ≤ (Λ * |s - t|) * (2 * H) :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left hdiv hΛ0)) hsum (abs_nonneg _)
            (by positivity)
      _ = 2 * H * Λ * |s - t| := by ring
  -- one step
  have hstep : ∀ k : ℕ, 1 ≤ k → k ≤ M →
      g (Real.log k) / k ≤ (∫ t in Real.log k..Real.log ((k + 1 : ℕ) : ℝ), g t) +
        (H ^ 2 + 2 * H * Λ) * (1 / (k : ℝ) ^ 2) := by
    intro k hk1 hkM
    have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    set a : ℝ := Real.log k with ha
    set b : ℝ := Real.log ((k + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 ≤ a := Real.log_nonneg hkk
    have hbL : b ≤ L + 2 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by push_cast; exact_mod_cast (by omega : k + 1 ≤ M + 1)
      exact (Real.log_le_log (by positivity) this).trans hlogM1
    have hab : a ≤ b := Real.log_le_log hk0 (by push_cast; linarith)
    have hbaup : b - a ≤ 1 / k := by
      rw [ha, hb, ← Real.log_div (by positivity) hk0.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
      have e : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by push_cast; field_simp; ring
      linarith
    have hbalo : 1 / ((k : ℝ) + 1) ≤ b - a := by
      rw [ha, hb, ← Real.log_div (by positivity) hk0.ne']
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
      have e : 1 - (((k + 1 : ℕ) : ℝ) / k)⁻¹ = 1 / ((k : ℝ) + 1) := by
        push_cast; field_simp; ring
      linarith
    -- `∫_a^b g ≥ (g a − 2HΛ(b − a))(b − a)`
    have hint : (g a - 2 * H * Λ * (b - a)) * (b - a) ≤ ∫ t in a..b, g t := by
      have hconst : ∫ t in a..b, (g a - 2 * H * Λ * (b - a)) = (g a - 2 * H * Λ * (b - a)) * (b - a) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (hgc.intervalIntegrable _ _) fun t ht => ?_
      have hl := hgLip t a (ha0.trans ht.1) (ht.2.trans hbL) ha0 (hab.trans hbL)
      have hta : |t - a| ≤ b - a := by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
      have h2 : g a - g t ≤ 2 * H * Λ * (b - a) := by
        have := abs_sub_comm (g t) (g a) ▸ hl
        have h3 := (le_abs_self (g a - g t)).trans this
        nlinarith [mul_le_mul_of_nonneg_left hta (by positivity : (0 : ℝ) ≤ 2 * H * Λ)]
      linarith
    have hga0 : 0 ≤ g a := by simp only [hg]; positivity
    have hgaH : g a ≤ H ^ 2 := hgH a ha0 (hab.trans hbL)
    -- assemble
    have h1 : g a / k ≤ g a * (b - a) + H ^ 2 * (1 / (k : ℝ) ^ 2) := by
      have e1 : g a / k = g a * (1 / ((k : ℝ) + 1)) + g a * (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
        field_simp
      have e2 : g a * (1 / ((k : ℝ) * ((k : ℝ) + 1))) ≤ H ^ 2 * (1 / (k : ℝ) ^ 2) := by
        refine mul_le_mul hgaH ?_ (by positivity) (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e3 : g a * (1 / ((k : ℝ) + 1)) ≤ g a * (b - a) := mul_le_mul_of_nonneg_left hbalo hga0
      linarith
    have h2 : g a * (b - a) ≤ (∫ t in a..b, g t) + 2 * H * Λ * (1 / (k : ℝ) ^ 2) := by
      have hsq : (b - a) ^ 2 ≤ 1 / (k : ℝ) ^ 2 := by
        rw [show 1 / (k : ℝ) ^ 2 = (1 / k) ^ 2 by ring]
        exact pow_le_pow_left₀ (by linarith) hbaup 2
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * H * Λ)
      nlinarith
    linarith
  -- sum by induction
  have hind : ∀ M' : ℕ, M' ≤ M → ∑ k ∈ Finset.Icc 1 M', g (Real.log k) / k ≤
      (∫ t in (0 : ℝ)..Real.log ((M' + 1 : ℕ) : ℝ), g t) +
        (H ^ 2 + 2 * H * Λ) * ∑ k ∈ Finset.Icc 1 M', 1 / (k : ℝ) ^ 2 := by
    intro M'
    induction M' with
    | zero => intro _; simp
    | succ M'' ih =>
      intro hM''
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        ← intervalIntegral.integral_add_adjacent_intervals (b := Real.log ((M'' + 1 : ℕ) : ℝ))
          (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
      have := hstep (M'' + 1) (by omega) hM''
      have hi := ih (by omega)
      push_cast at this hi ⊢
      linarith
  have htot := hind M le_rfl
  have hinvsq : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ^ 2 ≤ 2 := by
    simpa only [one_div] using sum_Icc_inv_sq_le_two M
  -- the integral
  have hsub : ∫ t in (0 : ℝ)..Real.log ((M + 1 : ℕ) : ℝ), g t =
      L * ∫ x in (0 : ℝ)..Real.log ((M + 1 : ℕ) : ℝ) / L, p.eval x ^ 2 := by
    have := intervalIntegral.integral_comp_div (a := 0) (b := Real.log ((M + 1 : ℕ) : ℝ))
      (fun x => p.eval x ^ 2) hL0.ne'
    simp only [zero_div, smul_eq_mul] at this
    exact this
  set β : ℝ := Real.log ((M + 1 : ℕ) : ℝ) / L with hβ
  have hβ1 : 1 ≤ β := by
    rw [hβ, le_div_iff₀ hL0, one_mul, hLdef]
    refine Real.log_le_log hY0 ?_
    have : 3 * Y < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    push_cast; linarith
  have hβ4 : L * (β - 1) ≤ 2 := by
    rw [hβ, mul_sub, mul_div_cancel₀ _ hL0.ne', mul_one]
    push_cast at hlogM1 ⊢
    linarith
  have hsplit : ∫ x in (0 : ℝ)..β, p.eval x ^ 2 =
      (∫ x in (0 : ℝ)..1, p.eval x ^ 2) + ∫ x in (1 : ℝ)..β, p.eval x ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals ((p.continuous.pow 2).intervalIntegrable _ _)
      ((p.continuous.pow 2).intervalIntegrable _ _)).symm
  have htail : ∫ x in (1 : ℝ)..β, p.eval x ^ 2 ≤ (β - 1) * H ^ 2 := by
    have hβ' : β ≤ 4 := by
      rw [hβ, div_le_iff₀ hL0]
      push_cast at hlogM1 ⊢
      linarith
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (f := fun x => p.eval x ^ 2) (g := fun _ => H ^ 2) hβ1 ((p.continuous.pow 2).intervalIntegrable _ _)
      intervalIntegrable_const fun x hx => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpH x ⟨by linarith [hx.1], by linarith [hx.2]⟩) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  have hfin : L * ∫ x in (0 : ℝ)..β, p.eval x ^ 2 ≤
      L * (∫ x in (0 : ℝ)..1, p.eval x ^ 2) + 2 * H ^ 2 := by
    rw [hsplit, mul_add]
    have := mul_le_mul_of_nonneg_left htail hL0.le
    have h2 : L * ((β - 1) * H ^ 2) ≤ 2 * H ^ 2 := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hβ4 (sq_nonneg _)
    linarith
  have hgoal : ∑ k ∈ Finset.Icc 1 M, p.eval (Real.log k / L) ^ 2 / k =
      ∑ k ∈ Finset.Icc 1 M, g (Real.log k) / k := rfl
  rw [hgoal]
  have h3 := mul_le_mul_of_nonneg_left hinvsq (by positivity : (0 : ℝ) ≤ H ^ 2 + 2 * H * Λ)
  rw [hsub] at htot
  calc ∑ k ∈ Finset.Icc 1 M, g (Real.log k) / k
      ≤ (L * ∫ x in (0 : ℝ)..β, p.eval x ^ 2) +
          (H ^ 2 + 2 * H * Λ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ^ 2 := htot
    _ ≤ (L * (∫ x in (0 : ℝ)..1, p.eval x ^ 2) + 2 * H ^ 2) + (H ^ 2 + 2 * H * Λ) * 2 :=
        add_le_add hfin h3
    _ = L * (∫ x in (0 : ℝ)..1, p.eval x ^ 2) + (4 * H ^ 2 + 4 * H * Λ) := by ring

/-! ## The dual -/

/-- The polynomial weight `p(log k/L)` is a combination of the derivative duals. -/
theorem sum_logZeroSmoothDual_eq (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) (m₀ : ℕ) (L : ℝ)
    (k : ℕ) :
    ∑ j ∈ Finset.range m₀, ((endpointExtremalCoeff m₀ j * (-1) ^ j / L ^ j : ℝ) : ℂ) *
        logZeroSmoothDual ν ε ρ Y j k =
      (((endpointExtremalPoly m₀).eval (Real.log k / L) : ℝ) : ℂ) * zeroSmoothDual ν ε ρ Y k := by
  simp only [logZeroSmoothDual, endpointExtremalPoly, Polynomial.eval_finsetSum,
    Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one]
  set x : ℂ := ((Real.log k : ℝ) : ℂ)
  set z : ℂ := zeroSmoothDual ν ε ρ Y k
  set cj : ℂ := ((endpointExtremalCoeff m₀ j : ℝ) : ℂ)
  have hsgn : ((-1 : ℂ)) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  rw [neg_pow x j, div_pow]
  have e : cj * (-1) ^ j / (L : ℂ) ^ j * ((-1) ^ j * x ^ j * z) =
      cj * (x ^ j / (L : ℂ) ^ j) * z * ((-1) ^ j * (-1) ^ j) := by ring
  rw [e, hsgn, mul_one]

/-- **The energy bound at a multiple zero.**  If `Re ρ = ½`, `Im ρ > 0` and `ζ^{(i)}(ρ) = 0` for
`i < m`, then for every `η > 0` there is `K₁` with
`1 ≤ d_N²((1 + η)²(|ρ|²/(2m²)) log N + K₁)` for all `N ≥ 3`. -/
theorem exists_one_le_bdDistDiscrete_sq_mul_log_of_multipleZero {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hζ : ∀ i < m₀, iteratedDeriv i riemannZeta ρ = 0) {η : ℝ} (hη : 0 < η) :
    ∃ K₁ : ℝ, ∀ N : ℕ, 3 ≤ N →
      1 ≤ bdDistDiscrete N ^ 2 *
        ((1 + η) ^ 2 * (‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2)) * Real.log N + K₁) := by
  obtain ⟨ν, hνsmooth, hνnn, hνsupp, hνmass⟩ := SmoothExistence
  have hν : IsHalfTwoBump ν := ⟨hνsmooth, hνsupp⟩
  have νpos : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnn x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; norm_num
  have hε1 : ε < 1 := by rw [hεdef]; norm_num
  set A : ℝ := 4 / η with hAdef
  have hA0 : 0 < A := by positivity
  -- the disc around `ρ`
  have hball : ∀ z ∈ closedBall ρ (1 / 4), 0 < z.re ∧ z.re < 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h := (Complex.abs_re_le_norm (z - ρ)).trans hz
    rw [Complex.sub_re, hre, abs_le] at h
    constructor <;> linarith [h.1, h.2]
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_bdModDefect_logZeroSmoothDual_le hν νpos mass_one hε0 hε1
    (by norm_num : (0 : ℝ) < 1 / 4) hball hζ hA0
  set p : Polynomial ℝ := endpointExtremalPoly m₀ with hp
  set c : ℕ → ℝ := endpointExtremalCoeff m₀ with hc
  obtain ⟨K₀, hK₀⟩ := exists_bdDualEnergy_polyLogDual_le hν νpos mass_one hε0 hε1 hre him.ne' p
  obtain ⟨C₄, hC₄⟩ := exists_sum_polyLog_sq_div_le p
  obtain ⟨c₁, _, hc₁, hbelow⟩ := Smooth1Properties_below hν.2 mass_one
  set Cc : ℝ := ∑ j ∈ Finset.range m₀, |c j| with hCc
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun j _ => abs_nonneg _
  set Cs : ℝ := Cc * Cd / 2 with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set KK : ℝ := ‖ρ‖ ^ 2 / 2 * C₄ + K₀ with hKK
  have hm0R : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  refine ⟨(1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2), fun N hN => ?_⟩
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set Y : ℝ := (N : ℝ) ^ (1 + η) with hYdef
  have hNY : (N : ℝ) ≤ Y := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
  have hY0 : 0 < Y := by linarith
  have hYe : Real.exp 1 ≤ Y := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  set L : ℝ := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hYe
  have hL0 : 0 < L := by linarith
  set K : ℕ := ⌈3 * Y⌉₊ + 2 * N with hKdef
  have hYK : 3 * Y ≤ K := by
    have := Nat.le_ceil (3 * Y)
    have h2 : ((⌈3 * Y⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : ⌈3 * Y⌉₊ ≤ K)
    linarith
  obtain ⟨P, hP, hNP, hP2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hPK : P ≤ K := by omega
  set q : ℕ → ℝ := fun j => c j * (-1) ^ j / L ^ j with hq
  set a : ℕ → ℂ := fun k => ∑ j ∈ Finset.range m₀, (q j : ℂ) * logZeroSmoothDual ν ε ρ Y j k
    with ha
  have hae : ∀ k, a k = ((p.eval (Real.log k / L) : ℝ) : ℂ) * zeroSmoothDual ν ε ρ Y k :=
    fun k => sum_logZeroSmoothDual_eq ν ε ρ Y m₀ L k
  have hare : ∀ k, (a k).re = p.eval (Real.log k / L) * (zeroSmoothDual ν ε ρ Y k).re := by
    intro k; rw [hae k, Complex.re_ofReal_mul]
  set v : ℕ → ℂ := fun m => -bdModDefect a K m with hv
  set b : ℕ → ℂ := bdMoebiusCorrection N P v with hb
  set Aseq : ℕ → ℝ := fun k => (a k).re + (b k).re with hAseq
  -- support, value at one, constraints
  have hAsupp : ∀ k, K < k → Aseq k = 0 := by
    intro k hk
    have hk' : 3 * Y ≤ k := by
      have : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith
    simp only [hAseq, hare]
    rw [zeroSmoothDual_eq_zero hν hε0 hε1 ρ hY0 hk', hb,
      bdMoebiusCorrection_eq_zero hNP v (by omega)]
    simp
  have hψ : Smooth1 ν ε ((1 : ℕ) / Y) = 1 := by
    refine hbelow ε _ hε0 (by positivity) ?_
    rw [hc₁, hεdef]
    have hl := Real.log_two_lt_d9
    have : ((1 : ℕ) : ℝ) / Y ≤ 1 / 2 := by
      rw [Nat.cast_one, div_le_div_iff₀ hY0 (by norm_num)]; linarith
    norm_num at this hl ⊢
    linarith
  have hA1 : Aseq 1 = 1 := by
    simp only [hAseq, hare, hb]
    rw [bdMoebiusCorrection_one hP.two_le]
    have hp0 : p.eval (Real.log ((1 : ℕ) : ℝ) / L) = 1 := by
      rw [Nat.cast_one, Real.log_one, zero_div, hp, endpointExtremalPoly_eval_zero hm₀]
    rw [hp0]
    unfold zeroSmoothDual zeroCoeff
    rw [if_neg one_ne_zero, hψ]
    simp
  have hC' : ∀ m, 2 ≤ m → m ≤ N →
      ∑ n ∈ (Finset.range K).filter (fun n => m ∣ n + 1), Aseq (n + 1) =
        (1 / (m : ℝ)) * ∑ n ∈ Finset.range K, Aseq (n + 1) := by
    intro m hm2 hmN
    have h := dual_constraint_re (a := a + b) (K := K) (m := m) (by
      rw [bdModDefect_add, hb, bdModDefect_bdMoebiusCorrection hP hNP hPK v hm2 hmN, hv]
      ring)
    simpa only [Pi.add_apply, Complex.add_re, hAseq] using h
  have hmain := one_le_bdDistDiscrete_sq_mul_energy hAsupp hA1 hC'
  -- the energy of `Re a`
  have hlogY : L = (1 + η) * Real.log N := by
    rw [hLdef, hYdef, Real.log_rpow hN0]
  have hEa : bdDualEnergy (fun k => (a k).re) K ≤
      ‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2) * ((1 + η) * Real.log N) + KK := by
    have hfun : (fun k : ℕ => (a k).re) =
        fun k : ℕ => p.eval (Real.log k / Real.log Y) * (zeroSmoothDual ν ε ρ Y k).re := by
      funext k; exact hare k
    rw [hfun]
    refine (hK₀ Y hYe K).trans ?_
    have hsum := hC₄ Y hYe
    rw [hp, integral_endpointExtremalPoly_sq hm₀] at hsum
    rw [← hp] at hsum
    have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ ‖ρ‖ ^ 2 / 2)
    have e : ‖ρ‖ ^ 2 / 2 * (Real.log Y * (1 / (m₀ : ℝ) ^ 2) + C₄) =
        ‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2) * ((1 + η) * Real.log N) + ‖ρ‖ ^ 2 / 2 * C₄ := by
      rw [← hLdef, hlogY]; field_simp
    rw [hKK]
    linarith only [h1, e]
  -- the energy of the correction
  set δ : ℝ := 2 * Cs * ((N : ℝ) ^ 4)⁻¹ with hδ
  have hNA : ∀ m : ℕ, 1 ≤ m → m ≤ N → (m : ℝ) ^ A * Y ^ (-A) ≤ ((N : ℝ) ^ 4)⁻¹ := by
    intro m hm1 hmN
    have hmA : (m : ℝ) ^ A ≤ (N : ℝ) ^ A :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmN) hA0.le
    have hYA : Y ^ (-A) = (N : ℝ) ^ ((1 + η) * (-A)) := by
      rw [hYdef, ← Real.rpow_mul hN0.le]
    have hNY' : (N : ℝ) ^ A * Y ^ (-A) = ((N : ℝ) ^ 4)⁻¹ := by
      rw [hYA, ← Real.rpow_add hN0, show A + (1 + η) * (-A) = -((4 : ℕ) : ℝ) by
        rw [hAdef]; field_simp; push_cast; ring, Real.rpow_neg hN0.le, Real.rpow_natCast]
    rw [← hNY']
    exact mul_le_mul_of_nonneg_right hmA (Real.rpow_nonneg hY0.le _)
  have hqc : ∀ j, |q j| ≤ |c j| := by
    intro j
    simp only [hq]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow,
      abs_of_pos hL0]
    exact div_le_self (abs_nonneg _) (one_le_pow₀ hL1)
  have hvb : ∀ m, 1 ≤ m → m ≤ N → ‖v m‖ ≤ δ := by
    intro m hm1 hmN
    rw [hv, norm_neg, ha, bdModDefect_sum_mul]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ j ∈ Finset.range m₀,
        ‖(q j : ℂ) * bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m‖ ≤
          |c j| * Cd * ((N : ℝ) ^ 4)⁻¹ := by
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hCd j (Finset.mem_range.mp hj) Y hY0 K hYK m hm1
      have h2 : Cd * (m : ℝ) ^ A * Y ^ (-A) ≤ Cd * ((N : ℝ) ^ 4)⁻¹ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hNA m hm1 hmN) hCd0
      calc |q j| * ‖bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m‖
          ≤ |c j| * (Cd * ((N : ℝ) ^ 4)⁻¹) :=
            mul_le_mul (hqc j) (h1.trans h2) (norm_nonneg _) (abs_nonneg _)
        _ = |c j| * Cd * ((N : ℝ) ^ 4)⁻¹ := by ring
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← hCc, hδ, hCs]
    ring
  have hδ0 : 0 ≤ δ := by positivity
  have hV : ∑ m ∈ Finset.Icc 2 N, ‖v m‖ ≤ N * δ := by
    refine (Finset.sum_le_sum fun m hm => hvb m (by simp only [Finset.mem_Icc] at hm; omega)
      (Finset.mem_Icc.mp hm).2).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hδ0
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hbB : ∀ k, ‖b k‖ ≤ ((N : ℝ) + 1) * (N * δ) := by
    intro k
    refine (norm_bdMoebiusCorrection_le N P v k).trans ?_
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hEb := bdDualEnergyC_le_of_bounded (K := K)
    (fun k hk => bdMoebiusCorrection_eq_zero hNP v hk) hbB
  have hEb' : bdDualEnergyC b K ≤ 1152 * Cs ^ 2 := by
    refine hEb.trans ?_
    have hPR : (P : ℝ) ≤ 2 * N := by exact_mod_cast hP2N
    have hP1 : (P : ℝ) + 1 ≤ 3 * N := by linarith
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    have hN1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    calc (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (2 * (((N : ℝ) + 1) * (N * δ))) ^ 2
        ≤ (2 * N) * (3 * N) ^ 2 * (2 * ((2 * N) * (N * δ))) ^ 2 := by
          gcongr
      _ = 1152 * Cs ^ 2 * (N : ℝ)⁻¹ := by
          rw [hδ]; field_simp; ring
      _ ≤ 1152 * Cs ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = 1152 * Cs ^ 2 := mul_one _
  have hEbre : bdDualEnergy (fun k => (b k).re) K ≤ 1152 * Cs ^ 2 :=
    (bdDualEnergy_re_le b K).trans hEb'
  have hEtot := bdDualEnergy_add_le (fun k => (a k).re) (fun k => (b k).re) K hη
  have hE : bdDualEnergy Aseq K ≤ (1 + η) ^ 2 * (‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2)) * Real.log N +
      ((1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2)) := by
    have h1 : (1 + η) * bdDualEnergy (fun k => (a k).re) K ≤
        (1 + η) * (‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2) * ((1 + η) * Real.log N) + KK) :=
      mul_le_mul_of_nonneg_left hEa (by positivity)
    have h2 : (1 + 1 / η) * bdDualEnergy (fun k => (b k).re) K ≤
        (1 + 1 / η) * (1152 * Cs ^ 2) :=
      mul_le_mul_of_nonneg_left hEbre (by positivity)
    have e : (1 + η) * (‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2) * ((1 + η) * Real.log N) + KK) =
        (1 + η) ^ 2 * (‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2)) * Real.log N + (1 + η) * KK := by ring
    have : bdDualEnergy Aseq K = bdDualEnergy (fun k => (a k).re + (b k).re) K := rfl
    rw [this]
    linarith only [hEtot, h1, h2, e]
  calc (1 : ℝ) ≤ bdDistDiscrete N ^ 2 * bdDualEnergy Aseq K := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- **Burnol's multiplicity-weighted lower bound.**  If `Re ρ = ½`, `Im ρ > 0` and
`ζ^{(i)}(ρ) = 0` for `i < m`, then `liminf_{N→∞} d_N² log N ≥ 2m²/|ρ|²`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZero {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hζ : ∀ i < m₀, iteratedDeriv i riemannZeta ρ = 0) {c : ℝ}
    (hc : c < 2 * (m₀ : ℝ) ^ 2 / ‖ρ‖ ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr fun h => by rw [h] at hre; simp at hre
  have hm0R : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  set β₀ : ℝ := ‖ρ‖ ^ 2 / (2 * (m₀ : ℝ) ^ 2) with hβ₀
  have hβ₀0 : 0 < β₀ := by positivity
  have hcβ : c < 1 / β₀ := by
    rw [hβ₀, one_div_div]; exact hc
  refine eventually_le_mul_log_of_forall_one_le (f := fun N => bdDistDiscrete N ^ 2)
    (fun N => sq_nonneg _) hβ₀0 (fun η hη => ?_) hcβ
  obtain ⟨K₁, hK₁⟩ :=
    exists_one_le_bdDistDiscrete_sq_mul_log_of_multipleZero hre him hm₀ hζ hη
  have hd2 := bdDistDiscrete_pos 2
  refine ⟨max K₁ (1 / bdDistDiscrete 2 ^ 2), fun N hN => ?_⟩
  have hlogN : 0 ≤ (1 + η) ^ 2 * β₀ * Real.log N :=
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  rcases eq_or_lt_of_le hN with h2 | h3
  · have hdN : bdDistDiscrete N = bdDistDiscrete 2 := by rw [← h2]
    have hd : 0 < bdDistDiscrete N ^ 2 := pow_pos (bdDistDiscrete_pos N) 2
    show 1 ≤ bdDistDiscrete N ^ 2 * ((1 + η) ^ 2 * β₀ * Real.log N +
      max K₁ (1 / bdDistDiscrete 2 ^ 2))
    rw [← hdN]
    calc (1 : ℝ) = bdDistDiscrete N ^ 2 * (1 / bdDistDiscrete N ^ 2) :=
          (mul_one_div_cancel hd.ne').symm
      _ ≤ bdDistDiscrete N ^ 2 * ((1 + η) ^ 2 * β₀ * Real.log N +
          max K₁ (1 / bdDistDiscrete N ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hd.le
          have := le_max_right K₁ (1 / bdDistDiscrete N ^ 2)
          linarith
  · have h := hK₁ N (by omega)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have := le_max_left K₁ (1 / bdDistDiscrete 2 ^ 2)
    rw [hβ₀]
    linarith

/-- **Burnol's bound in terms of the order of vanishing.**  If `Re ρ = ½`, `Im ρ > 0` and `ζ`
vanishes to order at least `m ≥ 1` at `ρ`, then `liminf_{N→∞} d_N² log N ≥ 2m²/|ρ|²`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_analyticOrderAt {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (him : 0 < ρ.im) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hord : (m₀ : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) {c : ℝ}
    (hc : c < 2 * (m₀ : ℝ) ^ 2 / ‖ρ‖ ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hdo : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta ρ := hdo.analyticAt (isOpen_ne.mem_nhds hρ1)
  exact eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZero hre him hm₀
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hord) hc

/-! ## Finitely many multiple zeros -/

/-- **The energy bound for finitely many multiple zeros.**  Let `Z` be a nonempty finite set of
points with `Re ρ = ½`, `Im ρ > 0`, at which `ζ, …, ζ^{(m(ρ)−1)}` vanish, `m(ρ) ≥ 1`, and
`S = Σ_{ρ ∈ Z} 2m(ρ)²/|ρ|²`.  For every `η > 0` there is `K₁` with
`1 ≤ d_N²((1 + η)²/S · log N + K₁)` for all `N ≥ 3`.  The dual is
`Σ_ρ λ_ρ p_{m(ρ)}(log k/L)Re(k^{−ρ})ψ(k/Y)` with `λ_ρ = (2m(ρ)²/|ρ|²)/S`, corrected over the
divisor lattice; the duals of distinct zeros are asymptotically orthogonal
(`exists_bdDualBilin_polyLogDual_le_of_ne`). -/
theorem exists_one_le_bdDistDiscrete_sq_mul_log_of_multipleZeros {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2 ∧ 0 < ρ.im) (hZne : Z.Nonempty) (m : ℂ → ℕ)
    (hm : ∀ ρ ∈ Z, 1 ≤ m ρ) (hζ : ∀ ρ ∈ Z, ∀ i < m ρ, iteratedDeriv i riemannZeta ρ = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K₁ : ℝ, ∀ N : ℕ, 3 ≤ N →
      1 ≤ bdDistDiscrete N ^ 2 *
        ((1 + η) ^ 2 / (∑ ρ ∈ Z, 2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2) * Real.log N + K₁) := by
  obtain ⟨ν, hνsmooth, hνnn, hνsupp, hνmass⟩ := SmoothExistence
  have hν : IsHalfTwoBump ν := ⟨hνsmooth, hνsupp⟩
  have νpos : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnn x
  have mass_one : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; norm_num
  have hε1 : ε < 1 := by rw [hεdef]; norm_num
  set A : ℝ := 4 / η with hAdef
  have hA0 : 0 < A := by positivity
  -- the defect constants
  have hdef : ∀ ρ ∈ Z, ∃ C : ℝ, 0 ≤ C ∧ ∀ j < m ρ, ∀ Y : ℝ, 0 < Y → ∀ K : ℕ, 3 * Y ≤ K →
      ∀ m' : ℕ, 1 ≤ m' →
        ‖bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m'‖ ≤ C * (m' : ℝ) ^ A * Y ^ (-A) := by
    intro ρ hρ
    have hball : ∀ z ∈ closedBall ρ (1 / 4), 0 < z.re ∧ z.re < 1 := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      have h := (Complex.abs_re_le_norm (z - ρ)).trans hz
      rw [Complex.sub_re, (hZ ρ hρ).1, abs_le] at h
      constructor <;> linarith [h.1, h.2]
    exact exists_norm_bdModDefect_logZeroSmoothDual_le hν νpos mass_one hε0 hε1
      (by norm_num : (0 : ℝ) < 1 / 4) hball (hζ ρ hρ) hA0
  choose! Cd hCd0 hCd using hdef
  -- the energies of each zero and each pair
  have hpair : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ∃ K₃ : ℝ, ∀ Y : ℝ, Real.exp 1 ≤ Y → ∀ K : ℕ,
      bdDualBilin
          (fun k => (endpointExtremalPoly (m ρ)).eval (Real.log k / Real.log Y) *
            (zeroSmoothDual ν ε ρ Y k).re)
          (fun k => (endpointExtremalPoly (m ρ')).eval (Real.log k / Real.log Y) *
            (zeroSmoothDual ν ε ρ' Y k).re) K ≤
        (if ρ = ρ' then ‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2) * Real.log Y else 0) + K₃ := by
    intro ρ hρ ρ' hρ'
    by_cases h : ρ = ρ'
    · subst h
      obtain ⟨K₀, hK₀⟩ := exists_bdDualEnergy_polyLogDual_le hν νpos mass_one hε0 hε1
        (hZ ρ hρ).1 (hZ ρ hρ).2.ne' (endpointExtremalPoly (m ρ))
      obtain ⟨C₄, hC₄⟩ := exists_sum_polyLog_sq_div_le (endpointExtremalPoly (m ρ))
      have hm0 : (0 : ℝ) < m ρ := by exact_mod_cast hm ρ hρ
      refine ⟨‖ρ‖ ^ 2 / 2 * C₄ + K₀, fun Y hY K => ?_⟩
      rw [if_pos rfl, ← bdDualEnergy_eq_bdDualBilin]
      refine (hK₀ Y hY K).trans ?_
      have hsum := hC₄ Y hY
      rw [integral_endpointExtremalPoly_sq (hm ρ hρ)] at hsum
      have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ ‖ρ‖ ^ 2 / 2)
      have e : ‖ρ‖ ^ 2 / 2 * (Real.log Y * (1 / (m ρ : ℝ) ^ 2) + C₄) =
          ‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2) * Real.log Y + ‖ρ‖ ^ 2 / 2 * C₄ := by
        field_simp
      linarith only [h1, e]
    · obtain ⟨K₃, hK₃⟩ := exists_bdDualBilin_polyLogDual_le_of_ne hν νpos mass_one hε0 hε1
        (hZ ρ hρ).1 (hZ ρ' hρ').1 (hZ ρ hρ).2 (hZ ρ' hρ').2 h (endpointExtremalPoly (m ρ))
        (endpointExtremalPoly (m ρ'))
      exact ⟨K₃, fun Y hY K => by rw [if_neg h, zero_add]; exact hK₃ Y hY K⟩
  choose! Kf hKf using hpair
  obtain ⟨c₁, _, hc₁, hbelow⟩ := Smooth1Properties_below hν.2 mass_one
  -- the weights
  have hnorm0 : ∀ ρ ∈ Z, 0 < ‖ρ‖ := fun ρ hρ =>
    norm_pos_iff.mpr fun h => by have := (hZ ρ hρ).1; rw [h] at this; simp at this
  have hmR : ∀ ρ ∈ Z, (0 : ℝ) < m ρ := fun ρ hρ => by exact_mod_cast hm ρ hρ
  set S : ℝ := ∑ ρ ∈ Z, 2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2 with hS
  have hS0 : 0 < S := Finset.sum_pos (fun ρ hρ => by
    have := hnorm0 ρ hρ; have := hmR ρ hρ; positivity) hZne
  set lam : ℂ → ℝ := fun ρ => 2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2 / S with hlam
  have hlam0 : ∀ ρ, 0 ≤ lam ρ := fun ρ => by positivity
  have hlam1 : ∑ ρ ∈ Z, lam ρ = 1 := by
    rw [hlam, ← Finset.sum_div, ← hS, div_self hS0.ne']
  have hlam2 : ∑ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2)) = 1 / S := by
    have : ∀ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2)) =
        (2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2) / S ^ 2 := by
      intro ρ hρ
      have := hnorm0 ρ hρ
      have := hmR ρ hρ
      rw [hlam]; field_simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← hS]
    field_simp
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = (∑ ρ ∈ Z, lam ρ *
      ((∑ j ∈ Finset.range (m ρ), |endpointExtremalCoeff (m ρ) j|) * Cd ρ)) / 2 := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by
    have : 0 ≤ ∑ ρ ∈ Z, lam ρ *
        ((∑ j ∈ Finset.range (m ρ), |endpointExtremalCoeff (m ρ) j|) * Cd ρ) :=
      Finset.sum_nonneg fun ρ hρ => mul_nonneg (hlam0 ρ) (mul_nonneg
        (Finset.sum_nonneg fun j _ => abs_nonneg _) (hCd0 ρ hρ))
    rw [hCs]; positivity
  set KK : ℝ := ∑ ρ ∈ Z, ∑ ρ' ∈ Z, lam ρ * lam ρ' * Kf ρ ρ' with hKK
  refine ⟨(1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2), fun N hN => ?_⟩
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set Y : ℝ := (N : ℝ) ^ (1 + η) with hYdef
  have hNY : (N : ℝ) ≤ Y := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
  have hY0 : 0 < Y := by linarith
  have hYe : Real.exp 1 ≤ Y := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hL1 : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hYe
  have hL0 : 0 < Real.log Y := by linarith
  set K : ℕ := ⌈3 * Y⌉₊ + 2 * N with hKdef
  have hYK : 3 * Y ≤ K := by
    have := Nat.le_ceil (3 * Y)
    have h2 : ((⌈3 * Y⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : ⌈3 * Y⌉₊ ≤ K)
    linarith
  obtain ⟨P, hP, hNP, hP2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hPK : P ≤ K := by omega
  set q : ℂ → ℕ → ℝ := fun ρ j =>
    endpointExtremalCoeff (m ρ) j * (-1) ^ j / Real.log Y ^ j with hq
  set a : ℕ → ℂ := fun k => ∑ ρ ∈ Z, (lam ρ : ℂ) *
    ∑ j ∈ Finset.range (m ρ), (q ρ j : ℂ) * logZeroSmoothDual ν ε ρ Y j k with ha
  have hare : ∀ k, (a k).re = ∑ ρ ∈ Z, lam ρ *
      ((endpointExtremalPoly (m ρ)).eval (Real.log k / Real.log Y) *
        (zeroSmoothDual ν ε ρ Y k).re) := by
    intro k
    simp only [ha, Complex.re_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [sum_logZeroSmoothDual_eq ν ε ρ Y (m ρ) (Real.log Y) k, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  set v : ℕ → ℂ := fun m' => -bdModDefect a K m' with hv
  set b : ℕ → ℂ := bdMoebiusCorrection N P v with hb
  set Aseq : ℕ → ℝ := fun k => (a k).re + (b k).re with hAseq
  -- support, value at one, constraints
  have hAsupp : ∀ k, K < k → Aseq k = 0 := by
    intro k hk
    have hk' : 3 * Y ≤ k := by
      have : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith
    simp only [hAseq, hare]
    rw [Finset.sum_eq_zero fun ρ _ => by rw [zeroSmoothDual_eq_zero hν hε0 hε1 ρ hY0 hk']; simp,
      hb, bdMoebiusCorrection_eq_zero hNP v (by omega)]
    simp
  have hψ : Smooth1 ν ε ((1 : ℕ) / Y) = 1 := by
    refine hbelow ε _ hε0 (by positivity) ?_
    rw [hc₁, hεdef]
    have hl := Real.log_two_lt_d9
    have : ((1 : ℕ) : ℝ) / Y ≤ 1 / 2 := by
      rw [Nat.cast_one, div_le_div_iff₀ hY0 (by norm_num)]; linarith
    norm_num at this hl ⊢
    linarith
  have hz1 : ∀ ρ : ℂ, (zeroSmoothDual ν ε ρ Y 1).re = 1 := by
    intro ρ
    unfold zeroSmoothDual zeroCoeff
    rw [if_neg one_ne_zero, hψ]
    simp
  have hA1 : Aseq 1 = 1 := by
    simp only [hAseq, hare, hb]
    rw [bdMoebiusCorrection_one hP.two_le]
    have h1 : ∀ ρ ∈ Z, lam ρ * ((endpointExtremalPoly (m ρ)).eval
        (Real.log ((1 : ℕ) : ℝ) / Real.log Y) * (zeroSmoothDual ν ε ρ Y 1).re) = lam ρ := by
      intro ρ hρ
      rw [Nat.cast_one, Real.log_one, zero_div, endpointExtremalPoly_eval_zero (hm ρ hρ), hz1]
      ring
    rw [Finset.sum_congr rfl h1, hlam1]
    simp
  have hC' : ∀ m', 2 ≤ m' → m' ≤ N →
      ∑ n ∈ (Finset.range K).filter (fun n => m' ∣ n + 1), Aseq (n + 1) =
        (1 / (m' : ℝ)) * ∑ n ∈ Finset.range K, Aseq (n + 1) := by
    intro m' hm2 hmN
    have h := dual_constraint_re (a := a + b) (K := K) (m := m') (by
      rw [bdModDefect_add, hb, bdModDefect_bdMoebiusCorrection hP hNP hPK v hm2 hmN, hv]
      ring)
    simpa only [Pi.add_apply, Complex.add_re, hAseq] using h
  have hmain := one_le_bdDistDiscrete_sq_mul_energy hAsupp hA1 hC'
  -- the energy of the combination
  have hlogY : Real.log Y = (1 + η) * Real.log N := by
    rw [hYdef, Real.log_rpow hN0]
  have hEa : bdDualEnergy (fun k => (a k).re) K ≤ (1 + η) * Real.log N / S + KK := by
    have hfun : (fun k : ℕ => (a k).re) = fun k : ℕ => ∑ ρ ∈ Z, lam ρ *
        (fun (ρ : ℂ) (k : ℕ) => (endpointExtremalPoly (m ρ)).eval (Real.log k / Real.log Y) *
          (zeroSmoothDual ν ε ρ Y k).re) ρ k := by
      funext k; exact hare k
    rw [hfun, bdDualEnergy_sum_eq]
    have hle : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, lam ρ * lam ρ' *
        bdDualBilin
          (fun k => (endpointExtremalPoly (m ρ)).eval (Real.log k / Real.log Y) *
            (zeroSmoothDual ν ε ρ Y k).re)
          (fun k => (endpointExtremalPoly (m ρ')).eval (Real.log k / Real.log Y) *
            (zeroSmoothDual ν ε ρ' Y k).re) K ≤
        (if ρ = ρ' then lam ρ ^ 2 * (‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2)) * Real.log Y else 0) +
          lam ρ * lam ρ' * Kf ρ ρ' := by
      intro ρ hρ ρ' hρ'
      have h := mul_le_mul_of_nonneg_left (hKf ρ hρ ρ' hρ' Y hYe K)
        (mul_nonneg (hlam0 ρ) (hlam0 ρ'))
      refine h.trans (le_of_eq ?_)
      split_ifs with he
      · subst he; ring
      · ring
    calc ∑ ρ ∈ Z, ∑ ρ' ∈ Z, lam ρ * lam ρ' *
          bdDualBilin
            (fun k => (endpointExtremalPoly (m ρ)).eval (Real.log k / Real.log Y) *
              (zeroSmoothDual ν ε ρ Y k).re)
            (fun k => (endpointExtremalPoly (m ρ')).eval (Real.log k / Real.log Y) *
              (zeroSmoothDual ν ε ρ' Y k).re) K
        ≤ ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
          ((if ρ = ρ' then lam ρ ^ 2 * (‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2)) * Real.log Y else 0) +
            lam ρ * lam ρ' * Kf ρ ρ') :=
          Finset.sum_le_sum fun ρ hρ => Finset.sum_le_sum fun ρ' hρ' => hle ρ hρ ρ' hρ'
      _ = (∑ ρ ∈ Z, lam ρ ^ 2 * (‖ρ‖ ^ 2 / (2 * (m ρ : ℝ) ^ 2))) * Real.log Y + KK := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_mul]
          rw [hKK]
          congr 1
          exact Finset.sum_congr rfl fun ρ hρ => by rw [if_pos hρ]
      _ = (1 + η) * Real.log N / S + KK := by
          rw [hlam2, hlogY]; field_simp
  -- the energy of the correction
  set δ : ℝ := 2 * Cs * ((N : ℝ) ^ 4)⁻¹ with hδ
  have hNA : ∀ m' : ℕ, 1 ≤ m' → m' ≤ N → (m' : ℝ) ^ A * Y ^ (-A) ≤ ((N : ℝ) ^ 4)⁻¹ := by
    intro m' hm1 hmN
    have hmA : (m' : ℝ) ^ A ≤ (N : ℝ) ^ A :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmN) hA0.le
    have hYA : Y ^ (-A) = (N : ℝ) ^ ((1 + η) * (-A)) := by
      rw [hYdef, ← Real.rpow_mul hN0.le]
    have hNY' : (N : ℝ) ^ A * Y ^ (-A) = ((N : ℝ) ^ 4)⁻¹ := by
      rw [hYA, ← Real.rpow_add hN0, show A + (1 + η) * (-A) = -((4 : ℕ) : ℝ) by
        rw [hAdef]; field_simp; push_cast; ring, Real.rpow_neg hN0.le, Real.rpow_natCast]
    rw [← hNY']
    exact mul_le_mul_of_nonneg_right hmA (Real.rpow_nonneg hY0.le _)
  have hqc : ∀ ρ j, |q ρ j| ≤ |endpointExtremalCoeff (m ρ) j| := by
    intro ρ j
    simp only [hq]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow,
      abs_of_pos hL0]
    exact div_le_self (abs_nonneg _) (one_le_pow₀ hL1)
  have hvb : ∀ m', 1 ≤ m' → m' ≤ N → ‖v m'‖ ≤ δ := by
    intro m' hm1 hmN
    have hsplit : bdModDefect a K m' = ∑ ρ ∈ Z, (lam ρ : ℂ) * bdModDefect
        (fun k => ∑ j ∈ Finset.range (m ρ), (q ρ j : ℂ) * logZeroSmoothDual ν ε ρ Y j k) K m' :=
      bdModDefect_sum_mul Z _ _ K m'
    rw [hv, norm_neg, hsplit]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ ρ ∈ Z, ‖(lam ρ : ℂ) * bdModDefect
        (fun k => ∑ j ∈ Finset.range (m ρ), (q ρ j : ℂ) * logZeroSmoothDual ν ε ρ Y j k) K m'‖ ≤
        lam ρ * (((∑ j ∈ Finset.range (m ρ), |endpointExtremalCoeff (m ρ) j|) * Cd ρ) *
          ((N : ℝ) ^ 4)⁻¹) := by
      intro ρ hρ
      have hinner : bdModDefect
          (fun k => ∑ j ∈ Finset.range (m ρ), (q ρ j : ℂ) * logZeroSmoothDual ν ε ρ Y j k) K m' =
          ∑ j ∈ Finset.range (m ρ), (q ρ j : ℂ) *
            bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m' :=
        bdModDefect_sum_mul _ _ (fun j => logZeroSmoothDual ν ε ρ Y j) K m'
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlam0 ρ), hinner]
      refine mul_le_mul_of_nonneg_left ?_ (hlam0 ρ)
      refine (norm_sum_le _ _).trans ?_
      have hle' : ∀ j ∈ Finset.range (m ρ),
          ‖(q ρ j : ℂ) * bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m'‖ ≤
            |endpointExtremalCoeff (m ρ) j| * Cd ρ * ((N : ℝ) ^ 4)⁻¹ := by
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := hCd ρ hρ j (Finset.mem_range.mp hj) Y hY0 K hYK m' hm1
        have h2 : Cd ρ * (m' : ℝ) ^ A * Y ^ (-A) ≤ Cd ρ * ((N : ℝ) ^ 4)⁻¹ := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hNA m' hm1 hmN) (hCd0 ρ hρ)
        calc |q ρ j| * ‖bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m'‖
            ≤ |endpointExtremalCoeff (m ρ) j| * (Cd ρ * ((N : ℝ) ^ 4)⁻¹) :=
              mul_le_mul (hqc ρ j) (h1.trans h2) (norm_nonneg _) (abs_nonneg _)
          _ = |endpointExtremalCoeff (m ρ) j| * Cd ρ * ((N : ℝ) ^ 4)⁻¹ := by ring
      refine (Finset.sum_le_sum hle').trans (le_of_eq ?_)
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    have e : ∑ ρ ∈ Z, lam ρ * (((∑ j ∈ Finset.range (m ρ), |endpointExtremalCoeff (m ρ) j|) *
        Cd ρ) * ((N : ℝ) ^ 4)⁻¹) = (∑ ρ ∈ Z, lam ρ *
          ((∑ j ∈ Finset.range (m ρ), |endpointExtremalCoeff (m ρ) j|) * Cd ρ)) *
          ((N : ℝ) ^ 4)⁻¹ := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ _ => by ring
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [e, hδ, hCs]
    ring
  have hδ0 : 0 ≤ δ := by positivity
  have hV : ∑ m' ∈ Finset.Icc 2 N, ‖v m'‖ ≤ N * δ := by
    refine (Finset.sum_le_sum fun m' hm => hvb m' (by simp only [Finset.mem_Icc] at hm; omega)
      (Finset.mem_Icc.mp hm).2).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hδ0
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hbB : ∀ k, ‖b k‖ ≤ ((N : ℝ) + 1) * (N * δ) := by
    intro k
    refine (norm_bdMoebiusCorrection_le N P v k).trans ?_
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hEb := bdDualEnergyC_le_of_bounded (K := K)
    (fun k hk => bdMoebiusCorrection_eq_zero hNP v hk) hbB
  have hEb' : bdDualEnergyC b K ≤ 1152 * Cs ^ 2 := by
    refine hEb.trans ?_
    have hPR : (P : ℝ) ≤ 2 * N := by exact_mod_cast hP2N
    have hP1 : (P : ℝ) + 1 ≤ 3 * N := by linarith
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    have hN1 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    calc (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (2 * (((N : ℝ) + 1) * (N * δ))) ^ 2
        ≤ (2 * N) * (3 * N) ^ 2 * (2 * ((2 * N) * (N * δ))) ^ 2 := by
          gcongr
      _ = 1152 * Cs ^ 2 * (N : ℝ)⁻¹ := by
          rw [hδ]; field_simp; ring
      _ ≤ 1152 * Cs ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = 1152 * Cs ^ 2 := mul_one _
  have hEbre : bdDualEnergy (fun k => (b k).re) K ≤ 1152 * Cs ^ 2 :=
    (bdDualEnergy_re_le b K).trans hEb'
  have hEtot := bdDualEnergy_add_le (fun k => (a k).re) (fun k => (b k).re) K hη
  have hE : bdDualEnergy Aseq K ≤ (1 + η) ^ 2 / S * Real.log N +
      ((1 + η) * KK + (1 + 1 / η) * (1152 * Cs ^ 2)) := by
    have h1 : (1 + η) * bdDualEnergy (fun k => (a k).re) K ≤
        (1 + η) * ((1 + η) * Real.log N / S + KK) :=
      mul_le_mul_of_nonneg_left hEa (by positivity)
    have h2 : (1 + 1 / η) * bdDualEnergy (fun k => (b k).re) K ≤
        (1 + 1 / η) * (1152 * Cs ^ 2) :=
      mul_le_mul_of_nonneg_left hEbre (by positivity)
    have e : (1 + η) * ((1 + η) * Real.log N / S + KK) =
        (1 + η) ^ 2 / S * Real.log N + (1 + η) * KK := by ring
    have : bdDualEnergy Aseq K = bdDualEnergy (fun k => (a k).re + (b k).re) K := rfl
    rw [this]
    linarith only [hEtot, h1, h2, e]
  calc (1 : ℝ) ≤ bdDistDiscrete N ^ 2 * bdDualEnergy Aseq K := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (sq_nonneg _)

/-- **Burnol's multiplicity-weighted bound for finitely many zeros.**  If `Re ρ = ½`, `Im ρ > 0`
and `ζ^{(i)}(ρ) = 0` for `i < m(ρ)` on a finite set `Z`, then
`liminf_{N→∞} d_N² log N ≥ Σ_{ρ ∈ Z} 2m(ρ)²/|ρ|²`. -/
theorem eventually_le_bdDistDiscrete_sq_mul_log_of_multipleZeros {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2 ∧ 0 < ρ.im) (m : ℂ → ℕ) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hζ : ∀ ρ ∈ Z, ∀ i < m ρ, iteratedDeriv i riemannZeta ρ = 0) {c : ℝ}
    (hc : c < ∑ ρ ∈ Z, 2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, c ≤ bdDistDiscrete N ^ 2 * Real.log N := by
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · rw [hZe, Finset.sum_empty] at hc
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have : 0 ≤ bdDistDiscrete N ^ 2 * Real.log N :=
      mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hN))
    linarith
  set S : ℝ := ∑ ρ ∈ Z, 2 * (m ρ : ℝ) ^ 2 / ‖ρ‖ ^ 2 with hS
  have hS0 : 0 < S := Finset.sum_pos (fun ρ hρ => by
    have h1 : 0 < ‖ρ‖ := norm_pos_iff.mpr fun h => by
      have := (hZ ρ hρ).1; rw [h] at this; simp at this
    have h2 : (0 : ℝ) < m ρ := by exact_mod_cast hm ρ hρ
    positivity) hZne
  have hβ₀0 : 0 < 1 / S := by positivity
  have hcβ : c < 1 / (1 / S) := by rw [one_div_one_div]; exact hc
  refine eventually_le_mul_log_of_forall_one_le (f := fun N => bdDistDiscrete N ^ 2)
    (fun N => sq_nonneg _) hβ₀0 (fun η hη => ?_) hcβ
  obtain ⟨K₁, hK₁⟩ :=
    exists_one_le_bdDistDiscrete_sq_mul_log_of_multipleZeros hZ hZne m hm hζ hη
  refine ⟨max K₁ (1 / bdDistDiscrete 2 ^ 2), fun N hN => ?_⟩
  have hlogN : 0 ≤ (1 + η) ^ 2 * (1 / S) * Real.log N :=
    mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
  rcases eq_or_lt_of_le hN with h2 | h3
  · have hdN : bdDistDiscrete N = bdDistDiscrete 2 := by rw [← h2]
    have hd : 0 < bdDistDiscrete N ^ 2 := pow_pos (bdDistDiscrete_pos N) 2
    show 1 ≤ bdDistDiscrete N ^ 2 * ((1 + η) ^ 2 * (1 / S) * Real.log N +
      max K₁ (1 / bdDistDiscrete 2 ^ 2))
    rw [← hdN]
    calc (1 : ℝ) = bdDistDiscrete N ^ 2 * (1 / bdDistDiscrete N ^ 2) :=
          (mul_one_div_cancel hd.ne').symm
      _ ≤ bdDistDiscrete N ^ 2 * ((1 + η) ^ 2 * (1 / S) * Real.log N +
          max K₁ (1 / bdDistDiscrete N ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hd.le
          have := le_max_right K₁ (1 / bdDistDiscrete N ^ 2)
          linarith
  · have h := hK₁ N (by omega)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have := le_max_left K₁ (1 / bdDistDiscrete 2 ^ 2)
    have e : (1 + η) ^ 2 / S = (1 + η) ^ 2 * (1 / S) := by ring
    rw [e]
    linarith

end

end RHTower
