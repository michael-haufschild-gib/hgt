import GaloisForLFunctions.BiarithmeticGaugeGeometry.CentralExcessForcesASquareRootPrimeDeficit

/-!
# The Deficit Residue Bounds the Central Excess

For an arithmetic member `−F'/F = Σ b(n) n^{−s}` (`b ≥ 0`) of `HeightCoupledSystem 2 1 1 γ`, the
square-root deficit law says that a central excess forces the deficit series
`D(s) = Σ d(n) n^{−s}`, `d(n) = (b_γ(n) − b(n))⁺`, to have abscissa at least `1/2`. This module
proves the quantitative form at the threshold.

**Deficit–excess law (`deficit_residue_ge_centralExcess`).** If `ξ` has no off-critical zero at
ordinate `γ` and `D` converges absolutely on `Re s > 1/2`, then

`liminf_{σ ↓ 1/2} (σ − 1/2) D(σ) ≥ ord_{1/2} Λ − ord_{1/2} Λ_γ`.

The excess central vanishing order is bounded by the Abelian residue of the prime deficit at the
centre. Proof: with the abscissa of the surplus measure at or left of `1/2`, the relation
`Λ_γ'/Λ_γ − Λ'/Λ = 𝓛(surplus) + b(1) − D` holds on the real segment right of `1/2`; multiplying by
`σ − 1/2`, the left side tends to `ord_{1/2} Λ_γ − ord_{1/2} Λ`, the surplus term is nonnegative and
`(σ − 1/2) b(1) → 0`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace_ofReal)

/-- **Deficit–excess law.** If `ξ` has no off-critical zero at ordinate `γ`, `F` is an arithmetic
member of `HeightCoupledSystem 2 1 1 γ` and its deficit series `D` converges absolutely on
`Re s > 1/2`, then for every `ε > 0`, eventually as `σ ↓ 1/2`,
`ord_{1/2} Λ − ord_{1/2} Λ_γ − ε ≤ (σ − 1/2) D(σ)`. -/
theorem deficit_residue_ge_centralExcess {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) ≤ (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
      ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) -
          (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat - ε ≤
        (σ - 1 / 2) * (LSeries (fun n => (latticeDeficit γ b n : ℂ)) (σ : ℂ)).re := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ with hΛγ
  set D : ℂ → ℂ := LSeries (fun n => (latticeDeficit γ b n : ℂ)) with hDdef
  set E : ℂ → ℂ := fun s => (b 1 : ℂ) - D s with hEdef
  have hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_of_le_of_lt hdef
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := latticeMember_primeMass_split (γ := γ) hb habs hL
  obtain ⟨c, hc0, -, hanchor, hrel, -⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hmass hE hsplit
  have hc : c ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have hz := (hanchor (by linarith) hgt).1
    have := hoff c (xi_add_eq_zero_of_heightCoupledΛ_real_zero hz)
    linarith
  have hmax : max c (1 / 2) = 1 / 2 := max_eq_right hc
  -- orders at the centre and the punctured relation on the real segment
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top (1 / 2))
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hHC0.orderAt_ne_top (1 / 2))
  have hΛan : AnalyticAt ℂ Λ (1 / 2) := hHC.analyticOnNhd_univ _ (Set.mem_univ _)
  have hΛγan : AnalyticAt ℂ Λγ (1 / 2) := hHC0.analyticOnNhd_univ _ (Set.mem_univ _)
  obtain ⟨gA, δA, hδA, hA⟩ := exists_logDeriv_cofactor hΛan ha.symm
  obtain ⟨gB, δB, hδB, hB⟩ := exists_logDeriv_cofactor hΛγan hk.symm
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro h
      have h' : (σ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simpa using h
      have := Complex.ofReal_injective h'
      have hσ' : 1 / 2 < σ := hσ
      linarith
  have hta := (tendsto_sub_mul_logDeriv hΛan ha.symm).comp hmap
  have htb := (tendsto_sub_mul_logDeriv hΛγan hk.symm).comp hmap
  have hb1 : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1 / 2) * (b 1 : ℂ)) (𝓝[>] (1 / 2 : ℝ))
      (𝓝 0) := by
    have h : Continuous fun σ : ℝ => ((σ : ℂ) - 1 / 2) * (b 1 : ℂ) := by fun_prop
    have h' := (h.tendsto (1 / 2 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))
    simpa using h'
  -- `g(σ) = Re[(σ − ½) b(1)] − Re[(σ − ½)(Λ_γ'/Λ_γ − Λ'/Λ)(σ)] → ord Λ − ord Λ_γ`
  have hg := (Complex.continuous_re.tendsto _).comp (hb1.sub (htb.sub hta))
  simp only [Function.comp_def, zero_sub, Complex.neg_re, Complex.sub_re,
    Complex.natCast_re] at hg
  have hev := hg.eventually (lt_mem_nhds (show ((a : ℝ) - k) - ε < -((k : ℝ) - a) by linarith))
  have hδ : 0 < min δA δB := lt_min hδA hδB
  filter_upwards [hev, Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 / 2 + min δA δB by
    linarith)] with σ hσg hσI
  have hball : ∀ δ' : ℝ, min δA δB ≤ δ' → (σ : ℂ) ∈ Metric.ball (1 / 2 : ℂ) δ' := by
    intro δ' hδ'
    rw [Metric.mem_ball, Complex.dist_eq, show (σ : ℂ) - 1 / 2 = ((σ - 1 / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hσI.1])]
    linarith [hσI.2]
  have hσne : (σ : ℂ) ≠ 1 / 2 := by
    intro h
    have h' : (σ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simpa using h
    have := Complex.ofReal_injective h'
    linarith [hσI.1]
  have hAσ := (hA σ (hball δA (min_le_left _ _))).2.2.2 hσne
  have hBσ := (hB σ (hball δB (min_le_right _ _))).2.2.2 hσne
  have hσre : max c (1 / 2) < (σ : ℂ).re := by rw [hmax]; simpa using hσI.1
  have hr := hrel σ hσre hAσ.1 hBσ.1
  rw [complexLaplace_ofReal] at hr
  have hlap : 0 ≤ laplaceReal (latticeMeasure (latticeSurplus γ b)) σ :=
    setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le
  -- `(σ − ½) Re D(σ) = (σ − ½)·𝓛(σ) + Re[(σ − ½) b(1)] − Re[(σ − ½)(Λ_γ'/Λ_γ − Λ'/Λ)(σ)]`
  have hD : (σ - 1 / 2) * (D σ).re =
      (σ - 1 / 2) * laplaceReal (latticeMeasure (latticeSurplus γ b)) σ +
        ((((σ : ℂ) - 1 / 2) * (b 1 : ℂ)).re -
          ((((σ : ℂ) - 1 / 2) * logDeriv Λγ σ).re - (((σ : ℂ) - 1 / 2) * logDeriv Λ σ).re)) := by
    have hDσ : D σ = ((laplaceReal (latticeMeasure (latticeSurplus γ b)) σ : ℝ) : ℂ) + (b 1 : ℂ) -
        (logDeriv Λγ σ - logDeriv Λ σ) := by
      rw [hr]; simp only [hEdef]; ring
    have hcast : ((σ : ℂ) - 1 / 2) = ((σ - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hDσ, hcast]
    simp only [Complex.re_ofReal_mul, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    ring
  rw [hD, ← ha, ← hk, ENat.toNat_coe, ENat.toNat_coe]
  have hσpos : 0 ≤ σ - 1 / 2 := by linarith [hσI.1]
  have h1 := mul_nonneg hσpos hlap
  linarith [hσg]

end GaloisForLFunctions.BiarithmeticGaugeGeometry
