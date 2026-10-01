import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction
import GaloisForLFunctions.RHTower.WeilFullConePNTErrorWiener
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitCounting
import GaloisForLFunctions.RHTower.XiZeroCountingFunction

/-!
# Square-root window rigidity of the Weil cone

For a Weil-positive `lam` and a test `K = f ⋆ f̃`, the **normalized window sum** at scale `x = e^y` is
`S_lam(y) = Σ_{n≥2} lam(n) n^{−1/2} K(log n − y)`, i.e. `x^{−1/2} Σ lam(n) ψ(n/x)` with
`ψ(v) = v^{−1/2}K(log v)`.

**Theorem** (`boundaryMeasure_real_singleton_eq_of_cesaro`).  If two full-cone producers `lam`,
`lam'` have translated Weil functionals with Cesàro-`L¹`-vanishing difference for every test
`f`, then `μ_lam` and `μ_lam'` have the same atoms.  Past the support of `K` this difference is
exactly `S_lam'(y) − S_lam(y)` (`weilFullFunctional_transl_sub_eq`): the pole and archimedean
parts cancel.

**Theorem** (`eq_vonMangoldt_of_window`).  Suppose `Λ` is Weil-positive (equivalently RH) and
`lam` is a full-cone producer whose window sums satisfy
`(1/Y)∫_{R₀}^{Y} |S_lam(y) − S_Λ(y)| dy → 0` for every test and every large `R₀`.  Then
`lam = Λ` on `n ≥ 2`.

So `Λ` is isolated in the Weil cone in the `√x`-window topology.  A second producer differs from
`Λ`, in Cesàro mean, by a constant times `√x` in some smoothed window sum.  The hypothesis
constrains only window cancellation at the exact `√x` scale, not the size of individual
coefficients.

**Proof.**
* `W_lam(K_y) = charFun ν_f(y)` with `ν_f = |f̂|²μ_lam`.
* The one-sided Cesàro mean of `charFun ν(y)e^{−iay}` is `ν({a})`
  (`HTGeometry.tendsto_oneSided_mean_charFun_mul`), so the hypothesis gives `ν_f{a} = ν'_f{a}`.
* Choosing `f` a mollifier with `f̂(a) ≠ 0` gives `μ_lam{a} = μ_lam'{a}`.
* For `lam' = Λ`, the atoms are the multiplicities of the critical zeros
  (`boundaryMeasure_vonMangoldt_real_singleton`).  Under RH every zero is critical, so every
  deficit weight vanishes, and the deficit law (`eq_vonMangoldt_of_deficitCount`) gives
  `lam = Λ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- The atom of the Bochner measure `|f̂|²μ_lam` at `a` is `|f̂(a)|² μ_lam({a})`. -/
theorem withDensity_specDensity_singleton {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (f : ℝ → ℂ) (a : ℝ) :
    ((boundaryMeasure hW).withDensity fun r => (specDensity f r : ℝ≥0∞)) {a} =
      (specDensity f a : ℝ≥0∞) * boundaryMeasure hW {a} := by
  rw [withDensity_apply _ (measurableSet_singleton a), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]

/-- **Atoms are determined by Cesàro-`L¹` limits of translated Weil functionals.** -/
theorem boundaryMeasure_real_singleton_eq_of_cesaro {lam lam' : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hW' : WeilPositiveFull lam')
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y,
        ‖weilFullFunctional lam (transl y (EF.weilTest f f)) -
          weilFullFunctional lam' (transl y (EF.weilTest f f))‖) atTop (𝓝 0))
    (a : ℝ) : (boundaryMeasure hW).real {a} = (boundaryMeasure hW').real {a} := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 4 * |a| ≤ j := exists_nat_ge _
  set f := mollC j with hfdef
  have hf := contDiff_mollC j
  have hfc := hasCompactSupport_mollC j
  obtain ⟨ν, hν, hνK⟩ := exists_spectralMeasure hW hf hfc
  obtain ⟨ν', hν', hνK'⟩ := exists_spectralMeasure hW' hf hfc
  have hm := GaloisForLFunctions.HTGeometry.tendsto_oneSided_mean_charFun_mul ν a
  have hm' := GaloisForLFunctions.HTGeometry.tendsto_oneSided_mean_charFun_mul ν' a
  -- the difference of the Cesàro means tends to 0
  have hcont : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → Continuous fun y : ℝ => charFun ρ y := by
    intro ρ _
    exact continuous_charFun
  have hdiff : Tendsto (fun Y : ℝ => (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y,
      (charFun ν y - charFun ν' y) * cexp (-(y * a * I))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _) ?_ (h f hf hfc)
    filter_upwards [eventually_gt_atTop 0] with Y hY
    rw [norm_mul, show ‖(1 / Y : ℂ)‖ = 1 / Y by
      rw [show (1 / Y : ℂ) = ((1 / Y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (intervalIntegral.norm_integral_le_integral_norm hY.le).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun y _ => ?_
    show ‖(charFun ν y - charFun ν' y) * cexp (-(↑y * ↑a * I))‖ = _
    rw [norm_mul, show -((y : ℂ) * a * I) = ((-(y * a) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, hνK y, hνK' y, spectralKernel, spectralKernel]
  have hsplit : ∀ Y : ℝ, (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y,
      (charFun ν y - charFun ν' y) * cexp (-(y * a * I)) =
      (1 / Y : ℂ) * (∫ y in (0 : ℝ)..Y, charFun ν y * cexp (-(y * a * I))) -
        (1 / Y : ℂ) * ∫ y in (0 : ℝ)..Y, charFun ν' y * cexp (-(y * a * I)) := by
    intro Y
    rw [← mul_sub, ← intervalIntegral.integral_sub]
    · congr 1
      refine intervalIntegral.integral_congr fun y _ => ?_
      show (charFun ν y - charFun ν' y) * cexp (-(↑y * ↑a * I)) = _
      ring
    · exact ((hcont ν hν).mul (by fun_prop)).intervalIntegrable _ _
    · exact ((hcont ν' hν').mul (by fun_prop)).intervalIntegrable _ _
  have hlim := hm.sub hm'
  simp_rw [← hsplit] at hlim
  have heq : ((ν.real {a} : ℝ) : ℂ) - (ν'.real {a} : ℂ) = 0 := tendsto_nhds_unique hlim hdiff
  have hνa : ν.real {a} = ν'.real {a} := by
    have := sub_eq_zero.mp heq
    exact_mod_cast this
  -- translate to the boundary measures
  have hdens : ν = (boundaryMeasure hW).withDensity fun r => (specDensity f r : ℝ≥0∞) :=
    eq_withDensity_boundaryMeasure hW hf hfc hνK
  have hdens' : ν' = (boundaryMeasure hW').withDensity fun r => (specDensity f r : ℝ≥0∞) :=
    eq_withDensity_boundaryMeasure hW' hf hfc hνK'
  have hspec : 0 < specDensity f a := by
    have hge := norm_paperFT_mollC_ge j (r := a) (by
      have : (j : ℝ) + 1 ≥ 4 * |a| := by linarith
      linarith)
    unfold specDensity
    have : 0 < ‖paperFT (mollC j) a‖₊ := by
      rw [← NNReal.coe_pos, coe_nnnorm]
      linarith
    positivity
  have hfinν : ν {a} ≠ ⊤ := measure_ne_top ν _
  have hfinν' : ν' {a} ≠ ⊤ := measure_ne_top ν' _
  rw [hdens, withDensity_specDensity_singleton] at hfinν
  rw [hdens', withDensity_specDensity_singleton] at hfinν'
  have hspec0 : (specDensity f a : ℝ≥0∞) ≠ 0 := by exact_mod_cast hspec.ne'
  have hμ : boundaryMeasure hW {a} ≠ ⊤ := fun ht => hfinν (by rw [ht, ENNReal.mul_top hspec0])
  have hμ' : boundaryMeasure hW' {a} ≠ ⊤ := fun ht => hfinν' (by rw [ht, ENNReal.mul_top hspec0])
  rw [measureReal_def, measureReal_def, hdens, hdens', withDensity_specDensity_singleton,
    withDensity_specDensity_singleton, ENNReal.toReal_mul, ENNReal.toReal_mul] at hνa
  have hs : (0 : ℝ) < (specDensity f a : ℝ≥0∞).toReal := by
    rw [ENNReal.coe_toReal]; exact_mod_cast hspec
  rw [measureReal_def, measureReal_def]
  exact mul_left_cancel₀ hs.ne' hνa

/-- Past the support, the difference of translated Weil functionals of two systems is the
difference of their window sums. -/
theorem weilFullFunctional_transl_sub_eq (lam lam' : ℕ → ℝ) {K : ℝ → ℂ} {R y : ℝ}
    (hR : ∀ u, K u ≠ 0 → |u| ≤ R) (hy : R < y) :
    weilFullFunctional lam (transl y K) - weilFullFunctional lam' (transl y K) =
      (∑' n : ℕ, ((if 2 ≤ n then lam' n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y)) -
        ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * K (Real.log n - y) := by
  have h := primeSum_transl_sub_main_eq lam hR hy
  have h' := primeSum_transl_sub_main_eq lam' hR hy
  linear_combination h - h'

/-- **Square-root window rigidity.**  If `Λ` is Weil-positive and the normalized window sums of a
full-cone producer `lam` agree with those of `Λ` in Cesàro-`L¹` mean, for every test and every
large starting point, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_window {lam : ℕ → ℝ}
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (hW : WeilPositiveFull lam)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ᶠ R₀ in atTop,
      Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in R₀..Y,
        ‖(∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
            EF.weilTest f f (Real.log n - y)) -
          ∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
            else 0 : ℝ) : ℂ) * EF.weilTest f f (Real.log n - y)‖) atTop (𝓝 0)) :
    ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  have hRH := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr hΛ
  -- step 1: Cesàro hypothesis for the Weil functionals
  have hces : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y,
        ‖weilFullFunctional lam (transl y (EF.weilTest f f)) -
          weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
            (transl y (EF.weilTest f f))‖) atTop (𝓝 0) := by
    intro f hf hfc
    have hK := admissible_weilTest hf hfc
    obtain ⟨R, hR⟩ := exists_abs_bound_of_hasCompactSupport hK.supp
    obtain ⟨R₀, hR₀, hR₀big⟩ := ((h f hf hfc).and (eventually_gt_atTop (max R 0))).exists
    have hR₀R : R < R₀ := lt_of_le_of_lt (le_max_left _ _) hR₀big
    have hR₀0 : 0 < R₀ := lt_of_le_of_lt (le_max_right _ _) hR₀big
    obtain ⟨ν, hν, hνK⟩ := exists_spectralMeasure hW hf hfc
    obtain ⟨ν', hν', hνK'⟩ := exists_spectralMeasure hΛ hf hfc
    set g : ℝ → ℝ := fun y => ‖weilFullFunctional lam (transl y (EF.weilTest f f)) -
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (transl y (EF.weilTest f f))‖ with hg
    have hgc : Continuous g := by
      have e : g = fun y => ‖charFun ν y - charFun ν' y‖ := by
        funext y; rw [hg]; simp only; rw [hνK y, hνK' y, spectralKernel, spectralKernel]
      rw [e]
      exact (continuous_charFun.sub continuous_charFun).norm
    have hgb : ∀ y, g y ≤ ν.real univ + ν'.real univ := by
      intro y
      have e : g y = ‖charFun ν y - charFun ν' y‖ := by
        rw [hg]; simp only; rw [hνK y, hνK' y, spectralKernel, spectralKernel]
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add (norm_charFun_le y) (norm_charFun_le y))
    -- on `[R₀, Y]` the integrand is the window difference
    have hwin : ∀ Y : ℝ, R₀ ≤ Y → ∫ y in R₀..Y, g y = ∫ y in R₀..Y,
        ‖(∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
            EF.weilTest f f (Real.log n - y)) -
          ∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
            else 0 : ℝ) : ℂ) * EF.weilTest f f (Real.log n - y)‖ := by
      intro Y hY
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
      rw [uIoc_of_le hY] at hy
      have hyR : R < y := lt_trans hR₀R hy.1
      rw [hg]
      simp only
      rw [weilFullFunctional_transl_sub_eq lam _ hR hyR, norm_sub_rev]
    have hhead : Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..R₀, g y) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∫ y in (0 : ℝ)..R₀, g y)).div_atTop tendsto_id
      simpa [div_eq_inv_mul, one_div] using this
    have hsum := hhead.add hR₀
    rw [add_zero] at hsum
    refine hsum.congr' ((eventually_ge_atTop R₀).mono fun Y hY => ?_)
    rw [← hwin Y hY, ← mul_add, intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  -- step 2: equal atoms
  have hatom : ∀ a : ℝ, (boundaryMeasure hW).real {a} =
      analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) := fun a => by
    rw [boundaryMeasure_real_singleton_eq_of_cesaro hW hΛ hces a,
      boundaryMeasure_vonMangoldt_real_singleton hΛ a]
  -- step 3: every deficit weight vanishes
  have hdef0 : ∀ q : XiZeroCopy, deficitWeight hW q = 0 := by
    intro q
    have hcrit : ((q.1 : ℂ)).re = 1 / 2 :=
      xi_zero_re_eq_half_of_RH hRH (xi_eq_zero_of_mem_divisor_support q.1)
    unfold deficitWeight
    rw [if_pos hcrit]
    have hq : ((q.1 : ℂ)) = (1 / 2 : ℂ) + (((q.1 : ℂ)).im : ℂ) * I := by
      apply Complex.ext <;> simp [hcrit]
    have hshare : atomShare hW q = 1 := by
      unfold atomShare
      have hmult : (xiDivisorMult q.1 : ℝ) = analyticOrderNatAt xi ((q.1 : ℂ)) := by
        unfold xiDivisorMult
        rw [xi_divisor_apply_of_mem (Set.mem_univ _)]
        simp [analyticOrderNatAt]
      have hm0 : (analyticOrderNatAt xi ((q.1 : ℂ)) : ℝ) ≠ 0 := by
        rw [← hmult]; exact_mod_cast (xiDivisorMult_pos q.1).ne'
      rw [← measureReal_def, hatom, ← hq, hmult]
      exact div_self hm0
    rw [hshare, sub_self, max_self]
  have hD : ∀ T : ℝ, deficitCount hW T = 0 := by
    intro T
    unfold deficitCount ordinateWindowWeight
    simp [hdef0]
  exact eq_vonMangoldt_of_deficitCount hW fun η hη =>
    Frequently.of_forall fun T => by rw [hD T, zero_div]; exact hη.le

end RHTower.WeilSpectral

end
