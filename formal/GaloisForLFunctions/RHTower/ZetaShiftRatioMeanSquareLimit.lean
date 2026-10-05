import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.RHTower.XiVerticalMonotoneCriterion
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.ZetaMollifiedCriticalLineJensen
import GaloisForLFunctions.RHTower.XiHorizontalStripComparison
import GaloisForLFunctions.RHTower.ZetaChiStripGrowth

/-!
# The shift limit for the zeta ratio under RH

For `s = ½ + it` and `δ > 0` the quotient `ζ(s)/ζ(s + δ)` is the natural Nyman--Beurling
approximant to the constant `1`.  Under RH it converges in the weighted mean:

`∫ |1 − ζ(½ + it)/ζ(½ + δ + it)|² dt/(¼ + t²) → 0`   as `δ ↓ 0`

(`tendsto_integral_one_sub_riemannZeta_ratio_of_rh`).

**Mechanism.**  Under RH `|ξ(σ + it)|` is nondecreasing in `σ ≥ ½`
(`norm_xi_half_le_of_rh`).  Writing `ζ = 2ξ/(s(s − 1)Γ_ℝ(s))` and bounding the vertical Gamma
ratio `|Γ(¼ + d + iτ)/Γ(¼ + iτ)| ≤ K(1 + |τ|)^{1/8}` for `0 ≤ d ≤ 1/8`
(`exists_norm_Gamma_quarter_add_le`, from `log|Γ|' = Re ψ ≤ log|z| + 3/|z|`) gives

`|ζ(½ + it)| ≤ K (1 + |t|)^{1/8} |ζ(½ + δ + it)|`,   `0 ≤ δ ≤ 1/4`

(`exists_norm_riemannZeta_half_le_of_rh`).  This dominates the integrand by
`O((1 + |t|)^{−7/4})`, and the ratio tends to `1` off the null set of critical zeros.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- **Uniform vertical Gamma growth to the right.**  For `a > 0`, `δ ≥ 0`, `τ ≥ 2`:
`|Γ(a+δ+iτ)| ≤ e^{3δ/2}(a + δ + τ)^δ |Γ(a+iτ)|`, from `log|Γ|' = Re ψ ≤ log|z| + 3/|z|`. -/
theorem norm_Gamma_add_le_rpow_mul {a δ τ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hτ : 2 ≤ τ) :
    ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.exp (3 * δ / 2) * (a + δ + τ) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
  have hτ0 : 0 < τ := by linarith
  have hint := integral_re_digamma_vertical (a := a) (δ := δ) hτ0
  have hbound : ∀ x ∈ Icc a (a + δ), (Complex.digamma ((x : ℂ) + (τ : ℂ) * I)).re ≤
      Real.log (a + δ + τ) + 3 / 2 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    set z : ℂ := (x : ℂ) + (τ : ℂ) * I with hz
    have hzre : 0 < z.re := by simp [hz, hx0]
    have hznorm : τ ≤ ‖z‖ := by
      have := Complex.abs_im_le_norm z
      simp [hz] at this
      rw [abs_of_pos hτ0] at this
      exact this
    have hznorm2 : 2 ≤ ‖z‖ := le_trans hτ hznorm
    have hzle : ‖z‖ ≤ x + τ := by
      calc ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = x + τ := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hτ0]
    have hd := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hznorm2
    have hre : (Complex.digamma z).re ≤ (Complex.log z).re + 3 / ‖z‖ := by
      have := (Complex.re_le_norm (Complex.digamma z - Complex.log z)).trans hd
      simp only [Complex.sub_re] at this
      linarith
    rw [Complex.log_re] at hre
    have hlog : Real.log ‖z‖ ≤ Real.log (a + δ + τ) :=
      Real.log_le_log (by linarith) (by linarith [hx.2])
    have h3 : 3 / ‖z‖ ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hle : ∫ x in a..(a + δ), (Complex.digamma ((x : ℂ) + (τ : ℂ) * I)).re ≤
      δ * (Real.log (a + δ + τ) + 3 / 2) := by
    have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + δ)
      ((continuous_re_digamma_line hτ0).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hbound
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    linarith
  rw [hint] at hle
  have hG0 : 0 < ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ0 a)
  have hG1 : 0 < ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ0 (a + δ))
  have hlog' : Real.log ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.log (Real.exp (3 * δ / 2) * (a + δ + τ) ^ δ *
        ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖) := by
    rw [Real.log_mul (by positivity) hG0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_rpow (by linarith)]
    nlinarith
  exact (Real.log_le_log_iff hG1 (by positivity)).mp hlog'

theorem Gamma_ofReal_add_mul_I_ne_zero {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

/-- **The vertical Gamma ratio, uniformly in the shift.**  There is `K` with
`|Γ(¼ + d + iτ)| ≤ K (1 + |τ|)^{1/8} |Γ(¼ + iτ)|` for all `0 ≤ d ≤ 1/8` and real `τ`. -/
theorem exists_norm_Gamma_quarter_add_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 8 → ∀ τ : ℝ,
      ‖Complex.Gamma (((1 / 4 + d : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
        K * (1 + |τ|) ^ (1 / 8 : ℝ) * ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  -- the compact part
  set R : Set (ℝ × ℝ) := Icc (0 : ℝ) (1 / 8) ×ˢ Icc (-2 : ℝ) 2 with hR
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  set g : ℝ × ℝ → ℝ := fun p => ‖Complex.Gamma (((1 / 4 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)‖ /
    ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (p.2 : ℂ) * I)‖ with hg
  have hgc : ContinuousOn g R := by
    intro p hp
    have hp1 : 0 ≤ p.1 := hp.1.1
    refine ContinuousAt.continuousWithinAt ?_
    have hΓc : ∀ σ : ℝ, 0 < σ → ∀ τ : ℝ,
        ContinuousAt Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I) := fun σ hσ τ =>
      (Complex.differentiableAt_Gamma _ fun m hm => by
        have := congrArg Complex.re hm; simp at this
        linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]).continuousAt
    refine ContinuousAt.div ?_ ?_ (norm_ne_zero_iff.mpr (Gamma_ofReal_add_mul_I_ne_zero
      (by norm_num) _))
    · refine ContinuousAt.norm ?_
      refine ContinuousAt.comp (g := Complex.Gamma) (hΓc _ (by linarith) _) ?_
      fun_prop
    · refine ContinuousAt.norm ?_
      refine ContinuousAt.comp (g := Complex.Gamma) (hΓc _ (by norm_num) _) ?_
      fun_prop
  obtain ⟨M, hM⟩ := (hRc.bddAbove_image hgc)
  refine ⟨max M (Real.exp (3 / 16) * 2), le_max_of_le_right (by positivity), ?_⟩
  intro d hd0 hd1 τ
  have hG0 : 0 < ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (Gamma_ofReal_add_mul_I_ne_zero (by norm_num) τ)
  have hpow1 : 1 ≤ (1 + |τ|) ^ (1 / 8 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg τ])
    (by norm_num)
  rcases le_or_gt |τ| 2 with hτ | hτ
  · have hmem : (d, τ) ∈ R := ⟨⟨hd0, hd1⟩, abs_le.mp hτ⟩
    have hle : g (d, τ) ≤ M := hM ⟨(d, τ), hmem, rfl⟩
    simp only [hg] at hle
    rw [div_le_iff₀ hG0] at hle
    calc ‖Complex.Gamma (((1 / 4 + d : ℝ) : ℂ) + (τ : ℂ) * I)‖
        ≤ M * ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := hle
      _ ≤ max M (Real.exp (3 / 16) * 2) * (1 + |τ|) ^ (1 / 8 : ℝ) *
          ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hG0.le
          calc M ≤ max M (Real.exp (3 / 16) * 2) := le_max_left _ _
            _ = max M (Real.exp (3 / 16) * 2) * 1 := (mul_one _).symm
            _ ≤ max M (Real.exp (3 / 16) * 2) * (1 + |τ|) ^ (1 / 8 : ℝ) :=
                mul_le_mul_of_nonneg_left hpow1 (le_max_of_le_right (by positivity))
  · -- the asymptotic part, reduced to `τ ≥ 2` by conjugation
    have hpos : ∀ y : ℝ, 2 ≤ y → ‖Complex.Gamma (((1 / 4 + d : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        Real.exp (3 / 16) * 2 * (1 + y) ^ (1 / 8 : ℝ) *
          ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
      intro y hy
      have h := norm_Gamma_add_le_rpow_mul (a := 1 / 4) (δ := d) (by norm_num) hd0 hy
      have hG := norm_pos_iff.mpr (Gamma_ofReal_add_mul_I_ne_zero (σ := 1 / 4) (by norm_num) y)
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hG.le)
      have he : Real.exp (3 * d / 2) ≤ Real.exp (3 / 16) := Real.exp_le_exp.mpr (by linarith)
      have hb : (1 / 4 + d + y) ^ d ≤ 2 * (1 + y) ^ (1 / 8 : ℝ) := by
        have h1 : 1 / 4 + d + y ≤ 1 + y := by linarith
        have h2 : (1 / 4 + d + y) ^ d ≤ (1 + y) ^ d :=
          Real.rpow_le_rpow (by linarith) h1 hd0
        have h3 : (1 + y) ^ d ≤ (1 + y) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hd1
        linarith [Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + y) (1 / 8 : ℝ)]
      calc Real.exp (3 * d / 2) * (1 / 4 + d + y) ^ d
          ≤ Real.exp (3 / 16) * (2 * (1 + y) ^ (1 / 8 : ℝ)) :=
            mul_le_mul he hb (Real.rpow_nonneg (by linarith) _) (by positivity)
        _ = Real.exp (3 / 16) * 2 * (1 + y) ^ (1 / 8 : ℝ) := by ring
    have hconj : ∀ σ : ℝ, ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * I)‖ =
        ‖Complex.Gamma ((σ : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ := by
      intro σ
      rw [← norm_Gamma_conj]
      congr 2
      simp
    rcases le_or_gt 0 τ with hτ0 | hτ0
    · rw [abs_of_nonneg hτ0] at hτ ⊢
      refine (hpos τ hτ.le).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (by linarith) _)) hG0.le
    · rw [abs_of_neg hτ0] at hτ ⊢
      rw [hconj (1 / 4 + d), hconj (1 / 4)]
      refine (hpos (-τ) hτ.le).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (by linarith) _)) ?_
      exact norm_nonneg _

/-! ## Monotonicity of `|ξ|` and the zeta ratio under RH -/

/-- **Under RH, `|ξ|` does not decrease to the right of the critical line.** -/
theorem norm_xi_half_le_of_rh (hRH : RiemannHypothesis) (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖xi (1 / 2 + (t : ℂ) * I)‖ ≤ ‖xi (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ := by
  have hmono := norm_XiC_vertical_monotoneOn_of_rh hRH t
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hδ) hδ
  simp only at h
  have e0 : XiC ((t : ℂ) + ((0 : ℝ) : ℂ) * I) = xi (1 / 2 + (t : ℂ) * I) := by
    rw [XiC]; congr 1; push_cast; ring
  have e1 : ‖XiC ((t : ℂ) + (δ : ℂ) * I)‖ = ‖xi (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ := by
    rw [XiC, ← xi_one_sub]
    have hc : (1 : ℂ) - (1 / 2 + ((t : ℂ) + (δ : ℂ) * I) * I) =
        (starRingEnd ℂ) (1 / 2 + (δ : ℂ) + (t : ℂ) * I) := by
      simp [Complex.ext_iff]; ring
    rw [hc, xi_conj, Complex.norm_conj]
  rw [e0] at h
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  rw [← e1]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The zeta ratio under RH.**  There is `K` with
`|ζ(½ + it)| ≤ K (1 + |t|)^{1/8} |ζ(½ + δ + it)|` for all `0 ≤ δ ≤ 1/4` and real `t`: write
`ζ = 2ξ/(s(s − 1)Γ_ℝ(s))`, use `|ξ(½ + it)| ≤ |ξ(½ + δ + it)|` and the vertical Gamma ratio. -/
theorem exists_norm_riemannZeta_half_le_of_rh (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ t : ℝ,
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤
        K * (1 + |t|) ^ (1 / 8 : ℝ) * ‖riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_Gamma_quarter_add_le
  refine ⟨4 * K, by positivity, ?_⟩
  intro δ hδ0 hδ1 t
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  set u : ℂ := 1 / 2 + (δ : ℂ) + (t : ℂ) * I with hu
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hure : u.re = 1 / 2 + δ := by simp [hu]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hsre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; norm_num at hsre
  have hu0 : u ≠ 0 := fun h => by rw [h] at hure; simp at hure; linarith
  have hu1 : u ≠ 1 := fun h => by rw [h] at hure; simp at hure; linarith
  have hxs := xi_eq_mul_Gammaℝ_mul_riemannZeta hs0 hs1 (by rw [hsre]; norm_num)
  have hxu := xi_eq_mul_Gammaℝ_mul_riemannZeta hu0 hu1 (by rw [hure]; linarith)
  have hmono := norm_xi_half_le_of_rh hRH t hδ0
  rw [← hs, ← hu, hxs, hxu] at hmono
  simp only [norm_mul, norm_div] at hmono
  -- the factors
  have hns : ‖s‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring_nf
  have hns1 : ‖s - 1‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring_nf
  have hsn : 1 / 2 ≤ ‖s‖ := by
    have : (1 / 2 : ℝ) ^ 2 ≤ ‖s‖ ^ 2 := by rw [hns]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).mp this
  have hs1n : ‖s - 1‖ = ‖s‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hns, hns1]
  have hun : ‖u‖ ≤ ‖s‖ + δ := by
    calc ‖u‖ = ‖s + (δ : ℂ)‖ := by rw [hu, hs]; ring_nf
      _ ≤ ‖s‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ + δ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
  have hun1 : ‖u - 1‖ ≤ ‖s‖ + δ := by
    calc ‖u - 1‖ = ‖(s - 1) + (δ : ℂ)‖ := by rw [hu, hs]; ring_nf
      _ ≤ ‖s - 1‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ + δ := by rw [hs1n, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
  have hpoly : ‖u‖ * ‖u - 1‖ ≤ 4 * (‖s‖ * ‖s - 1‖) := by
    rw [hs1n]
    have h2 : ‖s‖ + δ ≤ 2 * ‖s‖ := by linarith
    calc ‖u‖ * ‖u - 1‖ ≤ (‖s‖ + δ) * (‖s‖ + δ) :=
          mul_le_mul hun hun1 (norm_nonneg _) (by positivity)
      _ ≤ (2 * ‖s‖) * (2 * ‖s‖) := mul_le_mul h2 h2 (by positivity) (by positivity)
      _ = 4 * (‖s‖ * ‖s‖) := by ring
  have hGs : ‖Complex.Gammaℝ s‖ = Real.pi ^ (-(1 / 4 : ℝ)) *
      ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    rw [norm_Gammaℝ_eq, hsre]
    congr 2
    · norm_num
    · rw [hs]; push_cast; ring_nf
  have hGu : ‖Complex.Gammaℝ u‖ = Real.pi ^ (-(1 / 2 + δ) / 2) *
      ‖Complex.Gamma (((1 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    rw [norm_Gammaℝ_eq, hure]
    congr 2
    rw [hu]; push_cast; ring_nf
  have hGam := hK (δ / 2) (by linarith) (by linarith) (t / 2)
  have hpi : Real.pi ^ (-(1 / 2 + δ) / 2) ≤ Real.pi ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have htpow : (1 + |t / 2|) ^ (1 / 8 : ℝ) ≤ (1 + |t|) ^ (1 / 8 : ℝ) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  rw [hGs, hGu] at hmono
  set g0 := ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ with hg0
  set g1 := ‖Complex.Gamma (((1 / 4 + δ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ with hg1
  have hg0pos : 0 < g0 := norm_pos_iff.mpr (Gamma_ofReal_add_mul_I_ne_zero (by norm_num) _)
  set P := Real.pi ^ (-(1 / 4 : ℝ)) with hP
  have hPpos : 0 < P := by positivity
  set Q := Real.pi ^ (-(1 / 2 + δ) / 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set zs := ‖riemannZeta s‖
  set zu := ‖riemannZeta u‖
  have hss : 0 < ‖s‖ * ‖s - 1‖ := by rw [hs1n]; nlinarith
  -- `|s(s-1)|/2 · P g0 zs ≤ |u(u-1)|/2 · Q g1 zu`
  have hmono' : ‖s‖ * ‖s - 1‖ * (P * g0 * zs) ≤ ‖u‖ * ‖u - 1‖ * (Q * g1 * zu) := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at hmono
    nlinarith [hmono]
  have hrhs : ‖u‖ * ‖u - 1‖ * (Q * g1 * zu) ≤
      4 * (‖s‖ * ‖s - 1‖) * (P * (K * (1 + |t|) ^ (1 / 8 : ℝ) * g0) * zu) := by
    have hg1' : g1 ≤ K * (1 + |t|) ^ (1 / 8 : ℝ) * g0 :=
      hGam.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htpow hK0) hg0pos.le)
    refine mul_le_mul hpoly ?_ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul hpi hg1' (norm_nonneg _) hPpos.le)
      (norm_nonneg _)
  have key : (‖s‖ * ‖s - 1‖ * P * g0) * zs ≤
      (‖s‖ * ‖s - 1‖ * P * g0) * (4 * K * (1 + |t|) ^ (1 / 8 : ℝ) * zu) := by
    have := hmono'.trans hrhs
    linarith [this]
  exact le_of_mul_le_mul_left key (by positivity)

/-! ## The shift limit -/

theorem continuous_riemannZeta_vertical {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := fun h => hσ (by simpa using congrArg Complex.re h)
  exact ((differentiableAt_riemannZeta hne).continuousAt).comp
    (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) (by fun_prop)

theorem one_div_quarter_add_sq_le (t : ℝ) : 1 / (1 / 4 + t ^ 2) ≤ 8 * (1 + |t|) ^ (-2 : ℝ) := by
  have h1 : 0 < 1 + |t| := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_two, div_le_iff₀ (by positivity)]
  have hsq : (1 + |t|) ^ 2 ≤ 8 * (1 / 4 + t ^ 2) := by
    nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 1)]
  rw [mul_comm 8, mul_assoc, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [hsq]

/-- **The shift limit under RH.**
`∫ |1 - ζ(½ + it)/ζ(½ + δ + it)|² dt/(¼ + t²) → 0` as `δ ↓ 0`, by dominated convergence: the
ratio is `O((1 + |t|)^{1/8})` uniformly in `0 < δ ≤ 1/4`, and it tends to `1` off the null set of
critical zeros. -/
theorem tendsto_integral_one_sub_riemannZeta_ratio_of_rh (hRH : RiemannHypothesis) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ, ‖1 - riemannZeta (1 / 2 + (t : ℂ) * I) /
        riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_riemannZeta_half_le_of_rh hRH
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝[>] (0 : ℝ)) (f := fun _ : ℝ => (0 : ℝ))
    (F := fun (δ : ℝ) (t : ℝ) => ‖1 - riemannZeta (1 / 2 + (t : ℂ) * I) /
        riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2))
    (fun t : ℝ => 8 * (1 + K) ^ 2 * (1 + |t|) ^ (-(7 / 4 : ℝ))) ?_ ?_ ?_ ?_
  · simpa using hlim
  · -- measurability
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with δ hδ
    have h1 : Continuous fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I) := by
      have := continuous_riemannZeta_vertical (σ := 1 / 2) (by norm_num)
      simpa using this
    have h2 : Continuous fun t : ℝ => riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I) := by
      have := continuous_riemannZeta_vertical (σ := 1 / 2 + δ) (by linarith [hδ.2])
      simpa using this
    exact ((((measurable_const.sub (h1.measurable.div h2.measurable)).norm).pow_const 2).div
      (by fun_prop)).aestronglyMeasurable
  · -- domination
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with δ hδ
    refine Eventually.of_forall fun t => ?_
    have hr : ‖riemannZeta (1 / 2 + (t : ℂ) * I) / riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖
        ≤ K * (1 + |t|) ^ (1 / 8 : ℝ) := by
      rw [norm_div]
      by_cases hz : ‖riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ = 0
      · rw [hz, div_zero]; positivity
      · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
        exact hK δ hδ.1.le hδ.2 t
    have hp1 : 1 ≤ (1 + |t|) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
    have hn : ‖1 - riemannZeta (1 / 2 + (t : ℂ) * I) /
        riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ ≤ (1 + K) * (1 + |t|) ^ (1 / 8 : ℝ) := by
      calc _ ≤ ‖(1 : ℂ)‖ + _ := norm_sub_le _ _
        _ ≤ 1 + K * (1 + |t|) ^ (1 / 8 : ℝ) := by rw [norm_one]; linarith
        _ ≤ (1 + K) * (1 + |t|) ^ (1 / 8 : ℝ) := by nlinarith
    have hq : 0 < 1 / 4 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_one_div]
    have hpos : 0 < 1 + |t| := by positivity
    calc _ ≤ ((1 + K) * (1 + |t|) ^ (1 / 8 : ℝ)) ^ 2 * (8 * (1 + |t|) ^ (-2 : ℝ)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn 2) (one_div_quarter_add_sq_le t)
            (by positivity) (by positivity)
      _ = 8 * (1 + K) ^ 2 * (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |t|) ^ (1 / 8 : ℝ)), ← Real.rpow_mul hpos.le]
          have : (1 + |t|) ^ (-(7 / 4 : ℝ)) = (1 + |t|) ^ ((1 / 8 : ℝ) * ((2 : ℕ) : ℝ)) *
              (1 + |t|) ^ (-2 : ℝ) := by
            rw [← Real.rpow_add hpos]; norm_num
          rw [this]; ring
  · -- integrability of the bound
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 7 / 4) (by norm_num)
    simpa [Real.norm_eq_abs] using h.const_mul (8 * (1 + K) ^ 2)
  · -- pointwise limit off the critical zeros
    have hae := ae_riemannZeta_mul_ne_zero (M := fun _ => (1 : ℂ)) (differentiable_const _)
      one_ne_zero
    filter_upwards [hae] with t ht
    simp only [mul_one] at ht
    have hne : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    have hc : Tendsto (fun δ : ℝ => riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)) (𝓝[>] 0)
        (𝓝 (riemannZeta (1 / 2 + (t : ℂ) * I))) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hcont : ContinuousAt (fun δ : ℝ => riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)) 0 :=
        ((differentiableAt_riemannZeta (by simpa using hne)).continuousAt).comp
          (f := fun δ : ℝ => 1 / 2 + (δ : ℂ) + (t : ℂ) * I) (by fun_prop)
      simpa using hcont.tendsto
    have hr := (tendsto_const_nhds (x := riemannZeta (1 / 2 + (t : ℂ) * I))).div hc ht
    rw [div_self ht] at hr
    have h0 := ((tendsto_const_nhds (x := (1 : ℂ))).sub hr).norm.pow 2
    simp only [sub_self, norm_zero] at h0
    simpa using h0.div_const (1 / 4 + t ^ 2)

end

end RHTower
