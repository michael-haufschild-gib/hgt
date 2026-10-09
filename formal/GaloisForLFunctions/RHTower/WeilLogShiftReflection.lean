import GaloisForLFunctions.RHTower.WeilLogShiftLocalExcessDomain

/-!
# Coefficient reflection and the two one-sided probe domains

Reflection about von Mangoldt exchanges positive excess and deficit. Reflected
probes add to twice the zero-side functional, so local excess control and local
deficit control give opposite infinite limits outside the convergence domain.
An exponential majorant shows that even lower bounds at every nontrivial probe
cannot replace the local excess moment in the convergence criterion.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- Reflect arithmetic coefficients about the von Mangoldt sequence. -/
def weilCoefficientReflection (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℝ) - lam n

theorem weilCoefficientReflection_involutive (lam : ℕ → ℝ) :
    weilCoefficientReflection (weilCoefficientReflection lam) = lam := by
  funext n
  dsimp only [weilCoefficientReflection]
  ring

/-- Reflection negates normalized deviation, including its forced zero values
at indices zero and one. -/
theorem weilDeviation_reflection (lam : ℕ → ℝ) (n : ℕ) :
    weilDeviation (weilCoefficientReflection lam) n = -weilDeviation lam n := by
  simp only [weilDeviation, weilCoefficientReflection]
  split_ifs <;> ring

theorem deviationExcess_reflection (lam : ℕ → ℝ) (n : ℕ) :
    deviationExcess (weilCoefficientReflection lam) n = deviationDeficit lam n := by
  rw [deviationExcess, weilDeviation_reflection]
  rfl

theorem deviationDeficit_reflection (lam : ℕ → ℝ) (n : ℕ) :
    deviationDeficit (weilCoefficientReflection lam) n = deviationExcess lam n := by
  rw [deviationDeficit, weilDeviation_reflection, neg_neg]
  rfl

/-- Reflection negates every truncated potential without any convergence
assumption on the full potential. -/
theorem truncatedDeviationPotential_reflection (lam : ℕ → ℝ) (L y : ℝ) :
    truncatedDeviationPotential (weilCoefficientReflection lam) L y =
      -truncatedDeviationPotential lam L y := by
  unfold truncatedDeviationPotential
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [weilDeviation_reflection]
  ring

/-- The arithmetic parts of reflected probes cancel exactly at every real
cutoff and shift. -/
theorem logShift_probe_reflection_sum (lam : ℕ → ℝ) (L c : ℝ) :
    (weilFullFunctional lam (EF.weilTest (logShiftRiemannDifference L c)
      (logShiftRiemannDifference L c))).re +
    (weilFullFunctional (weilCoefficientReflection lam)
      (EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c))).re =
    2 * (zetaZeroConfig.W (logShiftRiemannDifference L c)
      (logShiftRiemannDifference L c)).re := by
  rw [logShift_probe_potential_identity, logShift_probe_potential_identity,
    truncatedDeviationPotential_reflection, truncatedDeviationPotential_reflection]
  ring

/-- Finite local deficit and nonsummable signed potential force the probe to
plus infinity, dual to the local-excess/minus-infinity theorem. -/
theorem tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit
    {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hdef : Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)))
    (hbad : ¬ Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) :
    Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference L (log m))
      (logShiftRiemannDifference L (log m)))).re) atTop atTop := by
  have hexc : Summable fun n => deviationExcess (weilCoefficientReflection lam) n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)) := by
    simpa only [deviationExcess_reflection] using hdef
  have hbadref : ¬ Summable fun n => weilDeviation (weilCoefficientReflection lam) n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)) := by
    intro hs
    apply hbad
    simpa only [weilDeviation_reflection, neg_mul, neg_neg] using hs.neg
  have href := tendsto_logShift_probe_atBot_of_nonsummable_sample_of_local_excess hm hexc hbadref
  have hW := (tendsto_order.mp (tendsto_logShift_zeroSide m)).1 (-1) (by norm_num)
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hW, href.eventually_le_atBot (-b - 2)] with L hWL hRL
  have hid := logShift_probe_reflection_sum lam L (log m)
  linarith only [hid, hWL, hRL]

/-- Exact dual local domain criterion: local deficit summability and one
eventual upper bound are jointly equivalent to signed-potential summability. -/
theorem summable_potential_iff_local_deficit_and_probe_upper_bound
    {lam : ℕ → ℝ} {m : ℕ} (hm : 2 ≤ m) :
    (Summable fun n => weilDeviation lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ↔
    (Summable fun n => deviationDeficit lam n *
      (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ∧
    ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (log m))
        (logShiftRiemannDifference k (log m)))).re ≤ b := by
  constructor
  · intro hs
    have hsref : Summable fun n => weilDeviation (weilCoefficientReflection lam) n *
        (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)) := by
      simpa only [weilDeviation_reflection, neg_mul] using hs.neg
    have hdef := summable_excess_potential_of_summable_potential hsref
    refine ⟨by simpa only [deviationExcess_reflection] using hdef, ?_⟩
    have ht := (tendsto_logShift_probe_of_summable_sample hm hs).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    let d := 2 * (deviationPotential lam (log m) - deviationPotential lam 0)
    have hev := (tendsto_order.mp ht).2 (d + 1) (by change d < d + 1; linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨d + 1, N, fun k hk => (hN k hk).le⟩
  · rintro ⟨hdef, b, N, hN⟩
    by_contra hbad
    have ht := tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit hm hdef hbad
    have hev := (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (b + 1)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    have hhi := hN (max N M) (le_max_left _ _)
    have hlo := hM (max N M) (le_max_right _ _)
    change b + 1 ≤ (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference (max N M : ℕ) (log m))
      (logShiftRiemannDifference (max N M : ℕ) (log m)))).re at hlo
    linarith only [hlo, hhi]

private theorem exponential_majorant_deviation (ρ : ℝ) (n : ℕ) :
    weilDeviation (fun j => (ArithmeticFunction.vonMangoldt j : ℝ) +
      sqrt j * exp (ρ * j)) n = if 2 ≤ n then exp (ρ * n) else 0 := by
  by_cases hn : 2 ≤ n
  · have hsqrt : sqrt (n : ℝ) ≠ 0 :=
      (sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))).ne'
    simp only [weilDeviation, if_pos hn]
    calc ((ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp (ρ * n) -
        ArithmeticFunction.vonMangoldt n) / sqrt n = exp (ρ * n) * (sqrt n / sqrt n) := by ring
      _ = exp (ρ * n) := by rw [div_self hsqrt, mul_one]
  · simp only [weilDeviation, if_neg hn]

private theorem exponential_majorant_deficit (ρ : ℝ) (n : ℕ) :
    deviationDeficit (fun j => (ArithmeticFunction.vonMangoldt j : ℝ) +
      sqrt j * exp (ρ * j)) n = 0 := by
  rw [deviationDeficit, exponential_majorant_deviation]
  split_ifs
  · exact max_eq_right (neg_nonpos.mpr (exp_pos _).le)
  · simp only [neg_zero, max_self]

private theorem not_summable_exponential_majorant_potential {m : ℕ} (hm : 2 ≤ m)
    {ρ : ℝ} (hρ : 2 * π / m < ρ) :
    ¬ Summable fun n => weilDeviation
      (fun j => (ArithmeticFunction.vonMangoldt j : ℝ) + sqrt j * exp (ρ * j)) n *
        (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n)) := by
  intro hs
  have hr : logKernelCriticalRate (log m) < ρ := by
    rwa [logKernelCriticalRate_log_nat (show 1 ≤ m by omega)]
  apply not_summable_exponential_kernelPotential_of_rate_lt hr
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [exponential_majorant_deviation, if_pos hn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (exp_pos _).le
      (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _)))]

/-- Positive exponential deviation strictly above the local critical rate
sends the actual probe to plus infinity. -/
theorem exponential_majorant_logShift_probe_atTop {m : ℕ} (hm : 2 ≤ m)
    {ρ : ℝ} (hρ : 2 * π / m < ρ) :
    Tendsto (fun L : ℝ => (weilFullFunctional
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp (ρ * n))
      (EF.weilTest (logShiftRiemannDifference L (log m))
        (logShiftRiemannDifference L (log m)))).re) atTop atTop := by
  apply tendsto_logShift_probe_atTop_of_nonsummable_sample_of_local_deficit hm
    _ (not_summable_exponential_majorant_potential hm hρ)
  simpa only [exponential_majorant_deficit, zero_mul] using
    (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

/-- Lower bounds at every nontrivial probe do not force any sampled potential
to converge. The same majorant `Λ(n)+sqrt(n)*exp(2πn)` makes every such probe
tend to plus infinity while its deficit vanishes identically. -/
theorem exists_majorant_all_logShift_probes_atTop_not_summable :
    ∃ lam : ℕ → ℝ,
      (∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (∀ n : ℕ, deviationDeficit lam n = 0) ∧
      ∀ m : ℕ, 2 ≤ m →
        (¬ Summable fun n => weilDeviation lam n *
          (riemannAutocorr (log m + log n) + riemannAutocorr (log m - log n))) ∧
        Tendsto (fun L : ℝ => (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference L (log m))
          (logShiftRiemannDifference L (log m)))).re) atTop atTop ∧
        ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          b ≤ (weilFullFunctional lam (EF.weilTest
            (logShiftRiemannDifference k (log m))
            (logShiftRiemannDifference k (log m)))).re := by
  let lam (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) + sqrt n * exp ((2 * π) * n)
  refine ⟨lam, fun n => ?_, exponential_majorant_deficit (2 * π), fun m hm => ?_⟩
  · have h := mul_nonneg (sqrt_nonneg (n : ℝ)) (exp_pos ((2 * π) * n)).le
    dsimp only [lam]
    linarith only [h]
  · have hρ : 2 * π / (m : ℝ) < 2 * π :=
      div_lt_self (by positivity) (by exact_mod_cast (show 1 < m by omega))
    have ht := exponential_majorant_logShift_probe_atTop hm hρ
    refine ⟨not_summable_exponential_majorant_potential hm hρ, ht, ?_⟩
    have hev := (ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨0, N, hN⟩

end RHTower
