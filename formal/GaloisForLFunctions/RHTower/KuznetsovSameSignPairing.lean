import GaloisForLFunctions.RHTower.KuznetsovSameSignRows

/-!
# The geometric side of the same-sign Kuznetsov formula

For `Re s₁, Re s₂ > 1`, `μ, ν > 0`, `ρ(T)v = e(μ)v`, `ρ(T)w = e(ν)w`:

`∫_𝒟 ⟨U(·|s₁, μ, v), U(·|s₂, ν, w)⟩
   = 2 [μ = ν] (4πμ)^{1−s̄₁−s₂} Γ(s̄₁+s₂−1) ⟨v, w + ρ(−1)⁻¹w⟩
     + 2 Σ_{(c,d) reduced} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) (c²)^{−s₂} V⁺(s̄₁, s₂; μ, ν, c²)`

(`integral_inner_poincSeries_poincProfile`), with the same-sign double integral `V⁺ = kuzValuePlus`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Integrals of series -/

/-- A series of integrable functions with summable `L¹` norms is integrable. -/
theorem integrable_tsum_of_summable_integral_norm {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} {F : ι → α → ℂ} (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) : Integrable (fun a => ∑' i, F i a) μ := by
  have hlint : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := fun i => by
    rw [ofReal_integral_eq_lintegral_ofReal (hF i).norm
      (Filter.Eventually.of_forall fun a => norm_nonneg _)]
    congr 1; funext a; rw [ofReal_norm]
  have hfin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hlt : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ < ⊤ := by
    rw [lintegral_tsum fun i => (hF i).1.enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hae : ∀ᵐ a ∂μ, ∑' i, ‖F i a‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum fun i => (hF i).1.enorm) hlt.ne
  have hsum : ∀ᵐ a ∂μ, Summable fun i => F i a := by
    filter_upwards [hae] with a ha
    refine Summable.of_norm ?_
    have := ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm] using ha.ne)
    exact NNReal.summable_coe.2 this
  refine ⟨?_, ?_⟩
  · exact aestronglyMeasurable_of_tendsto_ae (u := (Filter.atTop : Filter (Finset ι)))
      (f := fun s a => ∑ i ∈ s, F i a)
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => (hF i).1)
      (by filter_upwards [hsum] with a ha; exact ha.hasSum)
  · unfold HasFiniteIntegral
    calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ < ⊤ := hlt

theorem integrableOn_cpow_mul_exp {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * y))) (Ioi 0) := by
  refine (HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := a.re - 1) (by linarith) hr).mono'
    ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (ContinuousOn.mul (fun y hy =>
      (Complex.continuousAt_ofReal_cpow_const y _
        (Or.inr (ne_of_gt (show (0 : ℝ) < y from hy)))).continuousWithinAt) (by fun_prop))
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      show -((r : ℂ) * y) = ((-(r * y) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    simp

/-! ## The pairing -/

/-- The diagonal contribution `[μ = ν] (4πμ)^{1−a₁−s₂} Γ(a₁+s₂−1) ⟨v, w + ρ(−1)⁻¹w⟩`. -/
def diagPlus (a₁ s₂ : ℂ) (μ ν : ℝ) (v w : DeckSpace N) : ℂ :=
  if μ = ν then (1 / ((4 * Real.pi * μ : ℝ) : ℂ)) ^ (a₁ + s₂ - 1) * Complex.Gamma (a₁ + s₂ - 1) *
    ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ else 0

/-- **The geometric side of the same-sign Kuznetsov formula.** -/
theorem integral_inner_poincSeries_poincProfile {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen ν w) :
    ∫ z in fd, ⟪poincSeries (poincProfile s₁ μ) v z, poincSeries (poincProfile s₂ ν) w z⟫_ℂ =
      2 * diagPlus (conj s₁) s₂ μ ν v w +
      2 * ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) *
        kuzValuePlus (conj s₁) s₂ μ ν ((r.1.1 0 : ℝ) ^ 2) := by
  have hGc := continuous_poincSeries_profile hs₂ hν.le w
  have hGe := deckEquivariant_poincSeries (cuspCompatible_poincProfile s₂ hw)
  have hGL := memLp_poincSeries_profile hs₂ hν w
  rw [integral_inner_poincSeries_eq_deckCuspCoeff hs₁ hμ hv hGc hGe hGL, ← mul_add]
  congr 1
  have ha₁ : (conj s₁).re = s₁.re := Complex.conj_re s₁
  -- the exponent `δ`
  set δ := (max 0 (s₂.re - s₁.re) + (s₂.re - 1)) / 2 with hδdef
  have hm0 := le_max_left 0 (s₂.re - s₁.re)
  have hm1 := le_max_right 0 (s₂.re - s₁.re)
  have hm2 : max 0 (s₂.re - s₁.re) < s₂.re - 1 := max_lt (by linarith) (by linarith)
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ₁ : s₂.re - (conj s₁).re < δ := by rw [ha₁, hδdef]; linarith
  have hδ₂ : δ < s₂.re - 1 / 2 := by rw [hδdef]; linarith
  have hδ₃ : 1 < s₂.re - δ := by rw [hδdef]; linarith
  have hc2 : ∀ r : ReducedRow, 0 < ((r.1.1 0 : ℝ)) ^ 2 := fun r => by
    have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
    positivity
  set c₀ : ℂ := ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ
  set D : ℝ → ℂ := fun y => if μ = ν then c₀ * ((y : ℂ) ^ ((conj s₁ + s₂ - 1) - 1) *
    cexp (-(((4 * Real.pi * μ : ℝ) : ℂ) * y))) else 0 with hDdef
  set F : ReducedRow → ℝ → ℂ := fun r y => rowWeightPlus μ ν v w r.1 *
    (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) *
      ∫ ξ, kuzKernelPlus (conj s₁) s₂ μ ν ((r.1.1 0 : ℝ) ^ 2) (y, ξ) with hFdef
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ((y : ℂ) ^ (conj s₁) *
      (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
        deckCuspCoeff μ v (poincSeries (poincProfile s₂ ν) w) y) = D y + ∑' r, F r y := by
    intro y (hy : 0 < y)
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [deckCuspCoeff_poincSeries hy (cuspCompatible_poincProfile s₂ hw) hv
      (continuous_poincProfile s₂ ν) (summable_norm_poincProfile hs₂ hν.le)
      (continuous_tsum_norm_poincProfile hs₂ hν.le), diagonal_poincProfile s₂ hv hw hy,
      mul_add, smul_add]
    congr 1
    · simp only [hDdef]
      split_ifs with h
      · subst h
        rw [Complex.real_smul, show ((y ^ 2)⁻¹ : ℝ) = y ^ (-2 : ℤ) by rw [zpow_neg]; norm_cast,
          Complex.ofReal_zpow]
        have hpow : (y : ℂ) ^ (conj s₁ + s₂ - 1 - 1) =
            (y : ℂ) ^ (-2 : ℤ) * ((y : ℂ) ^ conj s₁ * (y : ℂ) ^ s₂) := by
          rw [← Complex.cpow_add _ _ hy', ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hy']
          congr 1; push_cast; ring
        have hexp : cexp (-(((4 * Real.pi * μ : ℝ) : ℂ) * y)) =
            (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) := by
          rw [← Complex.ofReal_mul (Real.exp (-(2 * Real.pi * μ * y))), ← Real.exp_add,
            Complex.ofReal_exp]; congr 1; push_cast; ring
        rw [hpow, hexp]; ring
      · simp
    · rw [Complex.real_smul, ← tsum_mul_left, ← tsum_mul_left]
      refine tsum_congr fun r => ?_
      rw [← Complex.real_smul, integral_coeffTerm_poincProfile s₁ s₂ v w r.2.1 hy]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  -- integrability of the pieces
  have hre : 0 < (conj s₁ + s₂ - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; rw [ha₁]; linarith
  have hDint : IntegrableOn D (Ioi 0) := by
    simp only [hDdef]
    split_ifs
    · exact (integrableOn_cpow_mul_exp hre (by positivity)).const_mul c₀
    · exact integrableOn_zero
  have hker : ∀ r : ReducedRow, Integrable
      (kuzKernelPlus (conj s₁) s₂ μ ν ((r.1.1 0 : ℝ) ^ 2))
      ((volume.restrict (Ioi 0)).prod volume) := fun r =>
    integrable_kuzKernelPlus hμ hν (hc2 r) hδ hδ₁ hδ₂
  have hint : ∀ r, Integrable (F r) (volume.restrict (Ioi 0)) := fun r =>
    (hker r).integral_prod_left.const_mul _
  set B := δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
    ((∫ y in Ioi (0 : ℝ), y ^ ((conj s₁ - s₂).re + δ - 1) *
      Real.exp (-(2 * Real.pi * μ * y))) * ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - s₂.re)) with hB
  have hbound : ∀ r : ReducedRow, ∫ y in Ioi (0 : ℝ), ‖F r y‖ ≤
      ‖v‖ * ‖w‖ * B * (((r.1.1 0 : ℝ)) ^ 2) ^ (-(s₂.re - δ)) := fun r => by
    have hq := hc2 r
    set q := ((r.1.1 0 : ℝ)) ^ 2
    have hcp : ‖((q : ℝ) : ℂ) ^ (-s₂)‖ = q ^ (-s₂.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re]
    have hle : ∀ y, ‖F r y‖ ≤ ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
        ∫ ξ, ‖kuzKernelPlus (conj s₁) s₂ μ ν q (y, ξ)‖ := fun y => by
      rw [hFdef, norm_mul, norm_mul, hcp]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (norm_rowWeightPlus_le μ ν v w r.1)
        (Real.rpow_nonneg hq.le _)) (norm_integral_le_integral_norm _) (norm_nonneg _)
        (by positivity)
    calc ∫ y in Ioi (0 : ℝ), ‖F r y‖
        ≤ ∫ y in Ioi (0 : ℝ), ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
            ∫ ξ, ‖kuzKernelPlus (conj s₁) s₂ μ ν q (y, ξ)‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            ((hker r).integral_norm_prod_left.const_mul _) (Filter.Eventually.of_forall hle)
      _ = ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
            ∫ p, ‖kuzKernelPlus (conj s₁) s₂ μ ν q p‖
              ∂((volume.restrict (Ioi 0)).prod volume) := by
          rw [integral_const_mul, integral_prod _ (hker r).norm]
      _ ≤ ‖v‖ * ‖w‖ * q ^ (-s₂.re) * (B * q ^ δ) :=
          mul_le_mul_of_nonneg_left (integral_norm_kuzKernelPlus_le hμ hν hq hδ hδ₁ hδ₂)
            (by positivity)
      _ = ‖v‖ * ‖w‖ * B * q ^ (-(s₂.re - δ)) := by
          rw [show -(s₂.re - δ) = -s₂.re + δ by ring, Real.rpow_add hq]
          ring
  have hsum : Summable fun r => ∫ y in Ioi (0 : ℝ), ‖F r y‖ :=
    ((summable_reducedRow_rpow hδ₃).mul_left (‖v‖ * ‖w‖ * B)).of_nonneg_of_le
      (fun r => integral_nonneg fun y => norm_nonneg _) hbound
  rw [integral_add hDint (integrable_tsum_of_summable_integral_norm hint hsum),
    ← integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  · simp only [hDdef, diagPlus]
    split_ifs with h
    · subst h
      rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hre (by positivity)]
      push_cast; ring
    · simp
  · refine tsum_congr fun r => ?_
    rw [hFdef, integral_const_mul]
    rfl

end

end GaloisForLFunctions.RHTower.DeckPointPair
