import GaloisForLFunctions.RHTower.KuznetsovSameSignGaussKernel

/-!
# The same-sign Kuznetsov identity integrated against the Gaussian weight

For `σ > 1` the geometric side of `⟨U(σ−it, μ, v), U(σ−it, ν, w)⟩` is
`2 [μ = ν] (4πμ)^{1−2σ} Γ(2σ−1) ⟨v, w + ρ(−1)⁻¹w⟩ + 2 (ν/μ)^{it} R_σ(t)`,
`R_σ(t) = Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) c^{−2σ} Ξ_σ(t, 4π√(μν)/|c|)`
(`integral_inner_poincSeries_line`).  The row sum is absolutely integrable against
`g_K(t) = t² e^{−(t/K)²}` because `|Ξ_σ(t, X_q)| ≤ ∫∫ |K⁺| ≪ q^δ` uniformly in `t`, and

`∫ g_K(t) R_σ(t) dt = Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) c^{−2σ} Ψ_σ(4π√(μν)/|c|)`

(`integral_gaussWeight_mul_rowSum`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ}

theorem norm_ofReal_cpow_mul_I {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖((x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- **`|Ξ_σ(t, X_q)| ≤ ∫∫ |K⁺|`, uniformly in `t`.** -/
theorem norm_sameSignKernel_le {μ ν q σ δ : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hq : 0 < q)
    (hσ : 1 < σ) (hδ : 0 < δ) (hδσ : δ < σ - 1 / 2) (t : ℝ) :
    ‖sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / q))‖ ≤
      δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
        ((∫ y in Ioi (0 : ℝ), y ^ (δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
          ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - σ)) * q ^ δ := by
  have hre1 : ((σ : ℂ) + t * Complex.I).re = σ := by simp
  have hre2 : ((σ : ℂ) - t * Complex.I).re = σ := by simp
  have hdiff : ((σ : ℂ) + t * Complex.I - ((σ : ℂ) - t * Complex.I)).re = 0 := by simp
  have hint := integrable_kuzKernelPlus (a₁ := (σ : ℂ) + t * Complex.I)
    (a₂ := (σ : ℂ) - t * Complex.I) hμ hν hq hδ (by rw [hre1, hre2]; linarith) (by rw [hre2]; linarith)
  have hval := kuzValuePlus_line hμ hν hq hσ t
  have hnorm : ‖sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / q))‖ =
      ‖kuzValuePlus ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν q‖ := by
    rw [hval, norm_mul, norm_ofReal_cpow_mul_I (by positivity), one_mul]
  rw [hnorm]
  have hle := integral_norm_kuzKernelPlus_le hμ hν hq hδ (by rw [hre1, hre2]; linarith)
    (by rw [hre2]; linarith) (a₁ := (σ : ℂ) + t * Complex.I) (a₂ := (σ : ℂ) - t * Complex.I)
  rw [hdiff, hre2, zero_add] at hle
  refine le_trans ?_ hle
  rw [kuzValuePlus, ← integral_prod (kuzKernelPlus _ _ μ ν q) hint]
  exact norm_integral_le_integral_norm _

theorem continuous_sameSign_integrand (σ X : ℝ) :
    Continuous fun p : (ℝ × ℝ) × ℝ => (((1 + p.1.2 ^ 2) ^ (-σ) : ℝ) : ℂ) *
      (cexp (2 * p.1.1 * p.2 * Complex.I) * cexp (-(X * cayleyUnit p.1.2 * Real.cosh p.2))) := by
  have h1 : Continuous fun p : (ℝ × ℝ) × ℝ => (((1 + p.1.2 ^ 2) ^ (-σ) : ℝ) : ℂ) :=
    (continuous_one_add_sq_rpow σ).comp (continuous_snd.comp continuous_fst)
  have h2 : Continuous fun p : (ℝ × ℝ) × ℝ => cexp (2 * p.1.1 * p.2 * Complex.I) := by fun_prop
  have h3 : Continuous fun p : (ℝ × ℝ) × ℝ => cexp (-(X * cayleyUnit p.1.2 * Real.cosh p.2)) :=
    ((continuous_const.mul (continuous_cayleyUnit.comp (continuous_snd.comp continuous_fst))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp continuous_snd))).neg.cexp
  exact h1.mul (h2.mul h3)

theorem aestronglyMeasurable_sameSignKernel (σ X : ℝ) :
    AEStronglyMeasurable (fun t => sameSignKernel σ t X) volume := by
  have h1 : StronglyMeasurable fun p : ℝ × ℝ => ∫ w : ℝ, (((1 + p.2 ^ 2) ^ (-σ) : ℝ) : ℂ) *
      (cexp (2 * p.1 * w * Complex.I) * cexp (-(X * cayleyUnit p.2 * Real.cosh w))) :=
    (continuous_sameSign_integrand σ X).stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ))
  have h2 : StronglyMeasurable fun t : ℝ => ∫ ξ : ℝ, ∫ w : ℝ, (((1 + ξ ^ 2) ^ (-σ) : ℝ) : ℂ) *
      (cexp (2 * t * w * Complex.I) * cexp (-(X * cayleyUnit ξ * Real.cosh w))) :=
    h1.integral_prod_right' (ν := (volume : Measure ℝ))
  refine h2.aestronglyMeasurable.congr (Eventually.of_forall fun t => ?_)
  simp only [sameSignKernel]
  congr 1; funext ξ
  rw [integral_const_mul]

/-! ## The geometric pairing on the line -/

/-- The modulus `q = c²` of a reduced row. -/
abbrev rowSq (r : ReducedRow) : ℝ := ((r.1.1 0 : ℝ)) ^ 2

theorem rowSq_pos (r : ReducedRow) : 0 < rowSq r := by
  have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
  positivity

theorem rowTerm_line {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (v w : DeckSpace N) (r : ReducedRow) :
    rowWeightPlus μ ν v w r.1 * ((rowSq r : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) *
      kuzValuePlus ((σ : ℂ) + t * Complex.I) ((σ : ℂ) - t * Complex.I) μ ν (rowSq r) =
      (((ν / μ : ℝ)) : ℂ) ^ (t * Complex.I) * (rowWeightPlus μ ν v w r.1 *
        ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := by
  have hq := rowSq_pos r
  rw [kuzValuePlus_line hμ hν hq hσ t]
  have hsplit : ((rowSq r : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I)) =
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * ((rowSq r : ℝ) : ℂ) ^ (t * Complex.I) := by
    rw [show -((σ : ℂ) - t * Complex.I) = ((-σ : ℝ) : ℂ) + t * Complex.I by push_cast; ring,
      Complex.cpow_add _ _ (by exact_mod_cast hq.ne'), Complex.ofReal_cpow hq.le]
  have hcomb : ((rowSq r : ℝ) : ℂ) ^ (t * Complex.I) *
      (((ν / (μ * rowSq r)) : ℝ) : ℂ) ^ (t * Complex.I) = (((ν / μ : ℝ)) : ℂ) ^ (t * Complex.I) := by
    rw [show ν / (μ * rowSq r) = (ν / μ) / rowSq r by field_simp,
      ofReal_cpow_mul_ofReal_div_cpow hq (div_pos hν hμ).le]
  rw [hsplit, ← hcomb]
  ring

/-- **The geometric side on the line** `s = σ − it`:
`∫_𝒟 ⟨U(s, μ, v), U(s, ν, w)⟩ = 2 diag + 2 (ν/μ)^{it} R_σ(t)`. -/
theorem integral_inner_poincSeries_line {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen ν w) :
    ∫ z in fd, ⟪poincSeries (poincProfile ((σ : ℂ) - t * Complex.I) μ) v z,
        poincSeries (poincProfile ((σ : ℂ) - t * Complex.I) ν) w z⟫_ℂ =
      2 * diagPlus (σ : ℂ) σ μ ν v w + 2 * ((((ν / μ : ℝ)) : ℂ) ^ (t * Complex.I) *
        ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
          sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := by
  have hs : 1 < ((σ : ℂ) - t * Complex.I).re := by simp [hσ]
  have hconj : conj ((σ : ℂ) - t * Complex.I) = (σ : ℂ) + t * Complex.I := by
    simp [map_sub, Complex.conj_ofReal]
  rw [integral_inner_poincSeries_poincProfile hs hs hμ hν hv hw, hconj,
    diagPlus_congr (b₁ := (σ : ℂ)) (b₂ := (σ : ℂ)) (by ring)]
  congr 2
  rw [← tsum_mul_left]
  exact tsum_congr fun r => rowTerm_line hσ t hμ hν v w r

/-! ## Integration of the row sum against `g_K` -/

theorem integrable_gaussWeight_mul_rowTerm {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K) {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) (v w : DeckSpace N) (r : ReducedRow) :
    Integrable (fun t : ℝ => (gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))))
    ∧ ∫ t : ℝ, ‖(gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ ≤
      (∫ t : ℝ, gaussWeight K t) * (‖v‖ * ‖w‖ *
        ((σ - 1) / 2) ^ ((σ - 1) / 2) * (2 * Real.pi * ν)⁻¹ ^ ((σ - 1) / 2) *
        ((∫ y in Ioi (0 : ℝ), y ^ ((σ - 1) / 2 - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
          ∫ ξ : ℝ, (1 + ξ ^ 2) ^ ((σ - 1) / 2 - σ))) * rowSq r ^ (-(σ - (σ - 1) / 2)) := by
  set δ := (σ - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hδσ : δ < σ - 1 / 2 := by simp only [δ]; linarith
  have hq := rowSq_pos r
  set B := δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
    ((∫ y in Ioi (0 : ℝ), y ^ (δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
      ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - σ))
  have hB : 0 ≤ B := by
    have h1 : 0 ≤ ∫ y in Ioi (0 : ℝ), y ^ (δ - 1) * Real.exp (-(2 * Real.pi * μ * y)) :=
      setIntegral_nonneg measurableSet_Ioi fun y (hy : 0 < y) => by positivity
    have h2 : 0 ≤ ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - σ) := integral_nonneg fun ξ => by positivity
    positivity
  have hpt : ∀ t : ℝ, ‖(gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ ≤
      gaussWeight K t * (‖v‖ * ‖w‖ * B * rowSq r ^ (-(σ - δ))) := fun t => by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (gaussWeight_nonneg K t), Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (gaussWeight_nonneg K t)
    have h1 := norm_rowWeightPlus_le μ ν v w r.1
    have h2 := norm_sameSignKernel_le hμ hν hq hσ hδ hδσ t
    have h3 : rowSq r ^ (-σ) * rowSq r ^ δ = rowSq r ^ (-(σ - δ)) := by
      rw [← Real.rpow_add hq]; congr 1; ring
    calc ‖rowWeightPlus μ ν v w r.1‖ * rowSq r ^ (-σ) *
          ‖sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))‖
        ≤ ‖v‖ * ‖w‖ * rowSq r ^ (-σ) * (B * rowSq r ^ δ) := by gcongr
      _ = _ := by rw [← h3]; ring
  have hint : Integrable (fun t : ℝ => (gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))) :=
    ((integrable_gaussWeight hK).mul_const _).mono'
      (((by unfold gaussWeight; fun_prop : Continuous fun t : ℝ => (gaussWeight K t : ℂ)).aestronglyMeasurable).mul
        (aestronglyMeasurable_const.mul (aestronglyMeasurable_sameSignKernel σ _)))
      (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  calc ∫ t : ℝ, ‖(gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
        ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖
      ≤ ∫ t : ℝ, gaussWeight K t * (‖v‖ * ‖w‖ * B * rowSq r ^ (-(σ - δ))) :=
        integral_mono hint.norm ((integrable_gaussWeight hK).mul_const _) hpt
    _ = _ := by rw [integral_mul_const]; ring

/-- **The row sum integrated against `g_K`.** -/
theorem integral_gaussWeight_mul_rowSum {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K) {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) (v w : DeckSpace N) :
    Integrable (fun t : ℝ => (gaussWeight K t : ℂ) *
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) ∧
    ∫ t : ℝ, (gaussWeight K t : ℂ) *
        ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
          sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) =
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        gaussKernel σ K (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) := by
  have hrow := fun r => integrable_gaussWeight_mul_rowTerm hσ hK hμ hν v w r
  have hsum : Summable fun r : ReducedRow => ∫ t : ℝ, ‖(gaussWeight K t : ℂ) *
      (rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ :=
    ((summable_reducedRow_rpow (τ := σ - (σ - 1) / 2) (by linarith)).mul_left _).of_nonneg_of_le
      (fun r => integral_nonneg fun t => norm_nonneg _) fun r => (hrow r).2
  have heq : ∀ t : ℝ, (gaussWeight K t : ℂ) *
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) =
      ∑' r : ReducedRow, (gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
        ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) :=
    fun t => (tsum_mul_left).symm
  simp_rw [heq]
  refine ⟨integrable_tsum_of_summable_integral_norm (fun r => (hrow r).1) hsum, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm (fun r => (hrow r).1) hsum]
  refine tsum_congr fun r => ?_
  have hX : 0 < 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by
    have := Real.sqrt_pos.2 (show 0 < μ * ν / rowSq r by have := rowSq_pos r; positivity)
    positivity
  have hpt : ∀ t : ℝ, (gaussWeight K t : ℂ) * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) =
      (rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ)) * ((gaussWeight K t : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := fun t => by ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussWeight_mul_sameSignKernel hσ hK hX]

end

end GaloisForLFunctions.RHTower.DeckPointPair
