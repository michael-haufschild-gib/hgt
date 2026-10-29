import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsHaveGlobalContinuation
import GaloisForLFunctions.HeckeLFunctions.QuadraticHeckeProductsHavePositiveOccupationExpansions
import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau

/-!
# Nonvanishing on the line of absolute convergence

For a nontrivial quadratic character, a zero at one would cancel the trivial pole.
The product would be entire, while its positive occupation expansion and Landau
force a divergent sum of ones to converge. Combined with the three-four-one
inequality, this excludes every zero on `Re s ≥ 1`, away from the trivial pole.
-/

noncomputable section
open NumberField Filter Topology
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- A real nontrivial Hecke character cannot cancel the trivial character's pole: its positive
occupation series would then be entire and Landau would force a sum of ones to converge. -/
theorem heckeLFunction_one_ne_zero_of_sq_eq_one {ψ : HeckeCharacter 𝔪}
    (hψ : ψ ≠ 1) (hψ2 : ψ ^ 2 = 1) : heckeLFunction 𝔪 ψ 1 ≠ 0 := by
  intro hzero
  let a : (heckeQuadraticParticle 𝔪 ψ →₀ ℕ) → ℝ := fun _ => 1
  let lam := heckeQuadraticOccupationEnergy 𝔪 ψ
  have ha : ∀ ν, 0 ≤ a ν := fun _ => zero_le_one
  have hlam : ∀ ν, 0 ≤ lam ν := heckeQuadraticOccupationEnergy_nonneg 𝔪 ψ
  have hd := differentiable_heckeLFunction 𝔪 hψ
  have hdiv : Differentiable ℂ (dslope (heckeLFunction 𝔪 ψ) 1) := fun z =>
    (RHTower.analyticAt_dslope_of_analyticAt (hd.analyticAt 1) (hd.analyticAt z)).differentiableAt
  let F : ℂ → ℂ := fun s =>
    heckeEntireRegularPart 𝔪 1 s * heckeLFunction 𝔪 ψ s +
      (heckeDensity 𝔪 : ℂ) * dslope (heckeLFunction 𝔪 ψ) 1 s
  have hF : Differentiable ℂ F :=
    ((differentiable_heckeEntireRegularPart 𝔪 1).mul hd).add (hdiv.const_mul _)
  have hsum : Summable (gdTwistTerm a lam 2 0) := by
    have h := summable_norm_heckeQuadraticOccupation 𝔪 ψ (s := 2) (by norm_num)
    refine h.congr (fun ν => ?_)
    simpa [a, lam] using norm_gd_term ha hlam (2 : ℂ) ν
  have hagree (s : ℂ) (hs : 2 < s.re) : F s = gdSeries a lam s := by
    have hsR : 1 < s.re := (by norm_num : (1 : ℝ) < 2).trans hs
    have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re] at hs; linarith
    have hprod : F s = heckeL 𝔪 1 s * heckeL 𝔪 ψ s := by
      dsimp only [F]
      rw [dslope_of_ne _ hs1, slope_def_field, hzero, sub_zero,
        ← heckeLFunction_eq_heckeL 𝔪 1 hsR, ← heckeLFunction_eq_heckeL 𝔪 ψ hsR,
        heckeLFunction_one]
      ring
    rw [hprod, heckeL_mul_eq_positive_exponentialSeries 𝔪 ψ hψ2 hsR]
    simp only [gdSeries, a, lam, Complex.ofReal_one, one_mul]
  have hall : Summable (gdTwistTerm a lam 0 0) :=
    general_landau_summable_transfer ha hlam hsum (h := 1) zero_lt_one
      (R := 4) hF.differentiableOn hagree (by norm_num)
  change Summable (fun ν => gdTwistTerm a lam 0 0 ν) at hall
  simp only [gdTwistTerm, a, zero_mul, neg_zero, Real.exp_zero, pow_zero, mul_one] at hall
  obtain ⟨j⟩ := nonempty_heckeQuadraticParticle 𝔪 hψ2
  have hinj : Function.Injective (fun n : ℕ => Finsupp.single j n) := by
    intro m n h
    simpa only [Finsupp.single_eq_same] using congrArg (fun ν => ν j) h
  have hnat : Summable (fun _ : ℕ => (1 : ℝ)) := hall.comp_injective hinj
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnat.tendsto_atTop_zero)

/-- Every nontrivial finite-order ray class character has nonzero Hecke L-value at one. -/
theorem heckeLFunction_one_ne_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeLFunction 𝔪 ψ 1 ≠ 0 := by
  by_cases hψ2 : ψ ^ 2 = 1
  · exact heckeLFunction_one_ne_zero_of_sq_eq_one 𝔪 hψ hψ2
  · exact heckeLFunction_ne_zero_of_sq_ne_one 𝔪 hψ2 (by simp)

/-- The original ideal-counting continuation has the same nonzero value at one. -/
theorem heckeLCont_one_ne_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeLCont 𝔪 ψ 1 ≠ 0 := by
  rw [← heckeLFunction_eq_heckeLCont 𝔪 hψ (errExp_lt_one (K := K))]
  exact heckeLFunction_one_ne_zero 𝔪 hψ

/-- Away from the real point, the three-four-one inequality excludes every boundary zero. -/
theorem heckeLFunction_line_one_ne_zero (ψ : HeckeCharacter 𝔪) (t : ℝ) (ht : t ≠ 0) :
    heckeLFunction 𝔪 ψ (1 + Complex.I * t) ≠ 0 := by
  intro hzero
  have hp : (1 : ℂ) + Complex.I * t ≠ 1 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hp2 : (1 : ℂ) + 2 * Complex.I * t ≠ 1 := by
    intro h
    have h2 : 2 * t = 0 := by simpa using congrArg Complex.im h
    exact ht ((mul_eq_zero.mp h2).resolve_left two_ne_zero)
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hc' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    change (σ : ℂ) ≠ 1
    exact_mod_cast (show 1 < σ from hσ).ne'
  have hdiff : DifferentiableAt ℂ (fun s : ℂ => heckeLFunction 𝔪 ψ (s + Complex.I * t)) 1 :=
    (differentiableAt_heckeLFunction 𝔪 ψ hp).comp 1 (differentiableAt_id.add_const _)
  have hquot : Tendsto (fun σ : ℝ => heckeL 𝔪 ψ (σ + Complex.I * t) / ((σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ))
      (𝓝 (deriv (fun s : ℂ => heckeLFunction 𝔪 ψ (s + Complex.I * t)) 1)) := by
    have h := (HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero hdiff hzero).comp hc'
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact congrArg (fun z : ℂ => z / ((σ : ℂ) - 1))
      (heckeLFunction_eq_heckeL 𝔪 ψ (by simpa using (show 1 < σ from hσ)))
  have hsq : Tendsto (fun σ : ℝ => heckeL 𝔪 (ψ ^ 2) (σ + 2 * Complex.I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (heckeLFunction 𝔪 (ψ ^ 2) (1 + 2 * Complex.I * t))) := by
    have hd := differentiableAt_heckeLFunction 𝔪 (ψ ^ 2) hp2
    refine (hd.continuousAt.tendsto.comp (hc.add_const (2 * Complex.I * t))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact heckeLFunction_eq_heckeL 𝔪 (ψ ^ 2) (by simpa using (show 1 < σ from hσ))
  have hsub : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using hc.sub_const 1
  have hprod := (((tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪)).pow 3).mul
    (hquot.pow 4)).mul hsq |>.mul hsub
  simp only [mul_zero] at hprod
  have hlim : Tendsto (fun σ : ℝ =>
      heckeL 𝔪 1 σ ^ 3 * heckeL 𝔪 ψ (σ + Complex.I * t) ^ 4 *
        heckeL 𝔪 (ψ ^ 2) (σ + 2 * Complex.I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hs : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast (show 1 < σ from hσ).ne')
    field_simp [hs]
  have hge : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      1 ≤ ‖heckeL 𝔪 1 σ ^ 3 * heckeL 𝔪 ψ (σ + Complex.I * t) ^ 4 *
        heckeL 𝔪 (ψ ^ 2) (σ + 2 * Complex.I * t)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact one_le_norm_heckeL_three_four_one 𝔪 ψ (show 1 < σ from hσ) t
  have hcontr : (1 : ℝ) ≤ 0 := by simpa only [norm_zero] using ge_of_tendsto hlim.norm hge
  exact (not_le_of_gt zero_lt_one) hcontr

/-- Every finite-order Hecke L-function is nonzero on `Re s >= 1`, apart from the trivial pole. -/
theorem heckeLFunction_ne_zero_of_one_le_re (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 1 ≤ s.re) (h : ψ ≠ 1 ∨ s ≠ 1) : heckeLFunction 𝔪 ψ s ≠ 0 := by
  rcases hs.eq_or_lt with hs | hs
  · have hsform : s = 1 + Complex.I * s.im := by
      apply Complex.ext
      · simpa using hs.symm
      · simp
    by_cases ht : s.im = 0
    · have hs1 : s = 1 := by rw [hsform, ht]; simp
      have hψ : ψ ≠ 1 := h.resolve_right (not_not_intro hs1)
      rw [hs1]
      exact heckeLFunction_one_ne_zero 𝔪 hψ
    · rw [hsform]
      exact heckeLFunction_line_one_ne_zero 𝔪 ψ s.im ht
  · rw [heckeLFunction_eq_heckeL 𝔪 ψ hs]
    exact heckeL_ne_zero 𝔪 ψ hs

/-- The counting continuation of every nontrivial character is nonzero on the closed right half-plane. -/
theorem heckeLCont_ne_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : heckeLCont 𝔪 ψ s ≠ 0 := by
  rw [← heckeLFunction_eq_heckeLCont 𝔪 hψ ((errExp_lt_one (K := K)).trans_le hs)]
  exact heckeLFunction_ne_zero_of_one_le_re 𝔪 ψ hs (Or.inl hψ)

end GaloisForLFunctions.HeckeLFunctions
