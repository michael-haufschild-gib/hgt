import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralNegativeValues

/-!
# Von Koch's theorem for `π`: RH holds iff `π(x) - li(x) = O(√x log x)`

Under the Riemann hypothesis partial summation gives
`(ψ(x)-x)/log x - O(√x/log x) ≤ π(x) - li(x) ≤ (ψ(x)-x)/log x + O(√x/log²x) + O(1)`
(`exists_primeCounting_sub_logIntegral_ge_of_riemannHypothesis`,
`exists_primeCounting_sub_logIntegral_le_of_riemannHypothesis`), and von Koch's bound
`|ψ(x) - x| ≤ C√x log²x` finishes.  Conversely `π ≤ li + C√x log x` makes
`Π(e^t) ≤ L(t) + K e^{at} + M` for every `a > ½`, and the Landau receiver
`zetaResidueUnit_ne_zero_of_primePowerCount_le` clears every half-plane `Re s > a`.
-/

open Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **Von Koch for `π`.**  Under RH, `|π(x) - li(x)| ≤ C√x log x` for all large `x`. -/
theorem exists_abs_primeCounting_sub_logIntegral_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, Real.exp 8 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t|
        ≤ C * Real.sqrt x * Real.log x := by
  obtain ⟨C₁, K₁, K₂, hC₁, hK₁, hlow⟩ :=
    exists_primeCounting_sub_logIntegral_ge_of_riemannHypothesis hRH
  obtain ⟨K₃, K₄, hK₃, hup⟩ := exists_primeCounting_sub_logIntegral_le_of_riemannHypothesis hRH
  set V : ℝ := 200 * (xiLineTwoLogDerivConstant + 2) with hV
  have hV0 : 0 ≤ V := by have := xiLineTwoLogDerivConstant_nonneg; rw [hV]; positivity
  refine ⟨V + C₁ + K₁ + K₃ + |K₂| + |K₄|, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hL8 : 8 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hx16 : 16 ≤ x := by
    have : (16 : ℝ) ≤ Real.exp 8 := by
      have := Real.add_one_le_exp 8
      have h2 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
      have h3 := Real.add_one_le_exp 4
      nlinarith
    linarith
  set L := Real.log x with hLdef
  set u := Real.sqrt x with hu
  have hu1 : 1 ≤ u := by rw [hu, Real.le_sqrt (by norm_num) hx0.le]; linarith
  have hvk := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hx16
  rw [← hV, ← hLdef, ← hu] at hvk
  have hL0 : 0 < L := by linarith
  have hψ : |(Chebyshev.psi x - x) / L| ≤ V * u * L := by
    rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    calc |Chebyshev.psi x - x| ≤ V * u * L ^ 2 := hvk
      _ = V * u * L * L := by ring
  have hlow' := hlow x hx
  have hup' := hup x hx
  rw [← hLdef, ← hu] at hlow' hup'
  have hLL : 1 ≤ L * L := by nlinarith
  have e1 : C₁ * u / L ≤ C₁ * u * L := by
    rw [div_le_iff₀ hL0]
    have h0 : 0 ≤ C₁ * u := mul_nonneg hC₁ (by linarith)
    have := mul_le_mul_of_nonneg_left hLL h0
    linarith
  have e2 : K₁ * u / L ^ 2 ≤ K₁ * u * L := by
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ K₁ * u := mul_nonneg hK₁ (by linarith)
    nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ L) 3]
  have e3 : K₃ * u / L ^ 2 ≤ K₃ * u * L := by
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ K₃ * u := mul_nonneg hK₃ (by linarith)
    nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ L) 3]
  have e4 : |K₂| ≤ |K₂| * u * L := by
    have : 1 ≤ u * L := by nlinarith
    nlinarith [abs_nonneg K₂]
  have e5 : |K₄| ≤ |K₄| * u * L := by
    have : 1 ≤ u * L := by nlinarith
    nlinarith [abs_nonneg K₄]
  have hab := abs_le.mp hψ
  have hexp : (V + C₁ + K₁ + K₃ + |K₂| + |K₄|) * u * L = V * u * L + C₁ * u * L + K₁ * u * L
      + K₃ * u * L + |K₂| * u * L + |K₄| * u * L := by ring
  have hu0 : 0 ≤ u := by linarith
  have p1 : 0 ≤ C₁ * u * L := by positivity
  have p2 : 0 ≤ K₁ * u * L := by positivity
  have p3 : 0 ≤ K₃ * u * L := by positivity
  have p4 : 0 ≤ |K₂| * u * L := by positivity
  have p5 : 0 ≤ |K₄| * u * L := by positivity
  rw [abs_le, hexp]
  constructor
  · have := le_abs_self K₂
    linarith
  · have := le_abs_self K₄
    linarith

/-- **The converse: `π ≤ li + C√x log x` eventually implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt_log {C : ℝ}
    (h : ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ)
      ≤ (∫ t in (2 : ℝ)..x, 1 / Real.log t) + C * Real.sqrt x * Real.log x) :
    RiemannHypothesis := by
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp h
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set x₀ : ℝ := max x₁ 2 with hx₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : 0 ≤ x₀ + 1 := by rw [hx₀]; linarith [le_max_right x₁ 2]
  -- for each `a ∈ (½, 1]` the Landau receiver applies
  have hzero : ∀ a : ℝ, 1 / 2 < a → a ≤ 1 → ∀ s : ℂ, a < s.re → zetaResidueUnit s ≠ 0 := by
    intro a ha ha1 s hs
    set K : ℝ := |C| / (a - 1 / 2) + |C₀| / Real.log 2 + 2 with hK
    have hK0 : 0 ≤ K := by
      rw [hK]; have : 0 < a - 1 / 2 := by linarith
      positivity
    refine zetaResidueUnit_ne_zero_of_primePowerCount_le (by linarith) ha1 hK0 hM0 ?_ hs
    intro t ht
    have hE := Real.exp_pos (1 / 2 * t)
    have hEa := Real.exp_pos (a * t)
    have hL := logIntegralCompare_nonneg ht.le
    have hhalf : Real.exp (1 / 2 * t) ≤ Real.exp (a * t) := Real.exp_le_exp.mpr (by nlinarith)
    -- `t e^{t/2} ≤ e^{at}/(a - ½)`
    have hte : t * Real.exp (1 / 2 * t) ≤ Real.exp (a * t) / (a - 1 / 2) := by
      have hd : 0 < a - 1 / 2 := by linarith
      have h1 : (a - 1 / 2) * t ≤ Real.exp ((a - 1 / 2) * t) := by
        have := Real.add_one_le_exp ((a - 1 / 2) * t); linarith
      rw [le_div_iff₀ hd]
      have h2 : Real.exp ((a - 1 / 2) * t) * Real.exp (1 / 2 * t) = Real.exp (a * t) := by
        rw [← Real.exp_add]; ring_nf
      nlinarith
    by_cases hxt : x₀ ≤ Real.exp t
    · have hx2 : 2 ≤ Real.exp t := le_trans (le_max_right _ _) hxt
      have hpi := hx₁ (Real.exp t) (le_trans (le_max_left _ _) hxt)
      have hli := integral_inv_log_le_logIntegralCompare hx2
      rw [Real.log_exp] at hli
      have hpp := primePowerCount_le_primeCounting_add (Real.exp t)
      have hps := hC₀ (Real.exp t)
      rw [sqrt_exp_eq_exp_half_mul] at hpi hps
      rw [Real.log_exp] at hpi
      have hps' : (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)) / Real.log 2
          ≤ |C₀| / Real.log 2 * Real.exp (a * t) := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ hl2.le
        calc Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)
            ≤ C₀ * Real.exp (1 / 2 * t) := hps
          _ ≤ |C₀| * Real.exp (1 / 2 * t) := mul_le_mul_of_nonneg_right (le_abs_self C₀) hE.le
          _ ≤ |C₀| * Real.exp (a * t) := mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
      have hCC : C * Real.exp (1 / 2 * t) * t ≤ |C| / (a - 1 / 2) * Real.exp (a * t) := by
        calc C * Real.exp (1 / 2 * t) * t ≤ |C| * (t * Real.exp (1 / 2 * t)) := by
              have := le_abs_self C
              have h0 : 0 ≤ t * Real.exp (1 / 2 * t) := by positivity
              nlinarith
          _ ≤ |C| * (Real.exp (a * t) / (a - 1 / 2)) :=
              mul_le_mul_of_nonneg_left hte (abs_nonneg C)
          _ = |C| / (a - 1 / 2) * Real.exp (a * t) := by ring
      have hlog := log_le_two_mul_exp_half ht
      have hexp : K * Real.exp (a * t) = |C| / (a - 1 / 2) * Real.exp (a * t)
          + |C₀| / Real.log 2 * Real.exp (a * t) + 2 * Real.exp (a * t) := by
        rw [hK]; ring
      have hx02 : 2 ≤ x₀ := le_max_right _ _
      linarith
    · have h1 := primePowerCount_le (Real.exp t)
      have h2 := Nat.floor_le (Real.exp_pos t).le
      have h3 : 0 ≤ K * Real.exp (a * t) := mul_nonneg hK0 hEa.le
      have hxt' : Real.exp t < x₀ := not_le.mp hxt
      linarith
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs
  set a : ℝ := min ((1 / 2 + s.re) / 2) 1 with ha
  refine hzero a ?_ (min_le_right _ _) s ?_
  · rw [ha, lt_min_iff]; constructor <;> linarith
  · rw [ha]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- **Von Koch's equivalence for `π`.**  RH holds iff `π(x) - li(x) = O(√x log x)`. -/
theorem riemannHypothesis_iff_primeCounting_sub_logIntegral_isBigO :
    RiemannHypothesis ↔ (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)
      - ∫ t in (2 : ℝ)..x, 1 / Real.log t) =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) := by
  constructor
  · intro hRH
    obtain ⟨C, hC, hb⟩ := exists_abs_primeCounting_sub_logIntegral_le_of_riemannHypothesis hRH
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (Real.exp 8)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
    have hL : 0 ≤ Real.log x := Real.log_nonneg (by
      have := Real.add_one_le_exp 8; linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) hL), ← mul_assoc]
    exact hb x hx
  · intro hO
    obtain ⟨C, hC⟩ := hO.bound
    refine riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt_log (C := |C|) ?_
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) hL)] at hx
    have h1 := le_abs_self ((Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t)
    have h2 : C * (Real.sqrt x * Real.log x) ≤ |C| * Real.sqrt x * Real.log x := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg (Real.sqrt_nonneg x) hL)
    linarith

end

end RHTower
