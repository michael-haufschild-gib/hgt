import GaloisForLFunctions.RHTower.KuznetsovSpectralIdentity
import GaloisForLFunctions.RHTower.DeckIncompleteEisensteinMellin
import GaloisForLFunctions.RHTower.DeckMaassSelbergBounds

/-!
# Unfolding deck Poincaré series against fields of moderate growth

The unfolding `∫_𝒟 ⟨P(·|h,v), G⟩ = 2 ∫_{strip} conj h ⟨v, G⟩` needs only the integrability on `𝒟` of
the majorant `(Σ_p |h(M_p z)|) ‖G(z)‖` (`integral_inner_poincSeries_of_majorant`); square
integrability of `G` is not needed.  For the Selberg profile `y^{s₁}e(μz)` and fields of growth
`Σ_p Im(M_p z)^σ` with `1 < σ < Re s₁` (the deck Eisenstein series `Ẽ(·, σ+it; w)`), the majorant is
`≪ y^{1−Re s₁+σ} + 1` on `𝒟` (`integrable_tsum_norm_poincProfile_mul_rowSum`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries Complex
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The unfolded integrand is integrable on the strip as soon as the majorant is integrable on `𝒟`. -/
theorem integrableOn_poincIntegrand_strip_of_majorant {h : ℍ → ℂ} {v : DeckSpace N}
    (hc : CuspCompatible h v) (hhc : Continuous h) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hmaj : Integrable (fun z => (∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * ‖G z‖)
      cellMeasure) :
    IntegrableOn (poincIntegrand h v G) modularStrip volume := by
  set f := poincIntegrand h v G
  have hT : ∀ (n : ℤ) (w : ℍ), f (ModularGroup.T ^ n • w) = f w := poincIntegrand_T_zpow hc hGe
  have hfc : Continuous f :=
    (Complex.continuous_conj.comp hhc).mul (continuous_const.inner hGc)
  refine ⟨hfc.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hg : ∀ (n : ℤ) (z : ℍ), ‖f (ModularGroup.T ^ n • z)‖ₑ = ‖f z‖ₑ := fun n z => by rw [hT]
  have hunf := tsum_lintegral_fd_eq_two_mul_lintegral_strip (g := fun z => ‖f z‖ₑ) hg
  have hswap : ∑' p : gammaSet 1 1 0, ∫⁻ z in fd, ‖f (gammaSetMatrix p • z)‖ₑ =
      ∫⁻ z in fd, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ :=
    (lintegral_tsum fun p => (hfc.comp (continuous_modular_smul _)).enorm.aemeasurable).symm
  have hpt : ∀ z, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ ≤
      ENNReal.ofReal (‖v‖ * ((∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * ‖G z‖)) := by
    intro z
    rw [show ‖v‖ * ((∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * ‖G z‖) =
        (∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * (‖v‖ * ‖G z‖) by ring,
      ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum z), ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun p => ?_
    show ‖poincIntegrand h v G (gammaSetMatrix p • z)‖ₑ ≤ _
    rw [← inner_poincTerm hGe, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
    rw [norm_poincTerm, mul_assoc]
  have hfin : ∫⁻ z in fd, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ < ∞ :=
    (lintegral_mono hpt).trans_lt ((hmaj.const_mul ‖v‖).lintegral_lt_top)
  rw [← hswap, hunf] at hfin
  exact lt_of_le_of_lt (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hfin

/-- **Unfolding against fields of moderate growth.** -/
theorem integral_inner_poincSeries_of_majorant {h : ℍ → ℂ} {v : DeckSpace N}
    (hc : CuspCompatible h v) (hhc : Continuous h) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hmaj : Integrable (fun z => (∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * ‖G z‖)
      cellMeasure) :
    ∫ z in fd, ⟪poincSeries h v z, G z⟫_ℂ = 2 * ∫ w in modularStrip, poincIntegrand h v G w := by
  set f := poincIntegrand h v G
  have hT : ∀ (n : ℤ) (w : ℍ), f (ModularGroup.T ^ n • w) = f w := poincIntegrand_T_zpow hc hGe
  have hstrip : IntegrableOn f modularStrip volume :=
    integrableOn_poincIntegrand_strip_of_majorant hc hhc hGc hGe hsum hmaj
  have hsum' : Summable fun p : gammaSet 1 1 0 => ∫ z in fd, ‖f (gammaSetMatrix p • z)‖ := by
    have hφ : ∀ (n : ℤ) (z : ℍ), ((‖f (ModularGroup.T ^ n • z)‖ : ℝ) : ℂ) = ((‖f z‖ : ℝ) : ℂ) :=
      fun n z => by rw [hT]
    have h := summable_fdUnfoldTerm hφ hstrip.norm.ofReal
    refine Complex.summable_ofReal.1 (h.congr fun p => ?_)
    exact integral_complex_ofReal
  have hterm : ∀ p : gammaSet 1 1 0, IntegrableOn (fun z => f (gammaSetMatrix p • z)) fd volume :=
    fun p => (integrableOn_smul_set_iff _ _ _).1 (integrableOn_smul_fd_of_periodic hT hstrip _)
  have hmain := (integral_fd_tsum_eq_two_mul_strip hT hterm hsum').2
  rw [← hmain]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  have hs : Summable fun p => poincTerm h v p z :=
    Summable.of_norm ((hsum z).mul_right ‖v‖ |>.congr fun p => (norm_poincTerm h v p z).symm)
  rw [poincSeries, inner_tsum_left hs]
  exact tsum_congr fun p => inner_poincTerm hGe h v p z

/-- **Unfolding the Selberg–Poincaré series against fields of moderate growth**, in coordinates. -/
theorem integral_inner_poincSeries_eq_deckCuspCoeff_of_majorant {s : ℂ} (hs : 1 < s.re) {μ : ℝ}
    (hμ : 0 ≤ μ) {v : DeckSpace N} (hv : IsCuspEigen μ v) {G : ℍ → DeckSpace N}
    (hGc : Continuous G) (hGe : deckEquivariant N G)
    (hmaj : Integrable (fun z => (∑' p : gammaSet 1 1 0,
      ‖poincProfile s μ (gammaSetMatrix p • z)‖) * ‖G z‖) cellMeasure) :
    ∫ z in fd, ⟪poincSeries (poincProfile s μ) v z, G z⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ •
        ((y : ℂ) ^ (conj s) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) * deckCuspCoeff μ v G y) := by
  have hc := cuspCompatible_poincProfile s hv
  have hint := integrableOn_poincIntegrand_strip_of_majorant hc (continuous_poincProfile s μ) hGc
    hGe (summable_norm_poincProfile hs hμ) hmaj
  rw [integral_inner_poincSeries_of_majorant hc (continuous_poincProfile s μ) hGc hGe
    (summable_norm_poincProfile hs hμ) hmaj, setIntegral_modularStrip_eq_iterated _ hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  congr 1
  rw [deckCuspCoeff, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [ofComplex_eq_hLine hy, poincIntegrand, conj_poincProfile_hLine]
  ring

/-! ## The majorant against Eisenstein growth -/

/-- For `1 < σ < Re s` and `μ > 0`, `(Σ_p |h_{s,μ}(M_p z)|)(Σ_p Im(M_p z)^σ)` is integrable on `𝒟`. -/
theorem integrable_tsum_norm_poincProfile_mul_rowSum {s : ℂ} (hs : 1 < s.re) {μ : ℝ}
    (hμ : 0 < μ) {σ : ℝ} (hσ : 1 < σ) (hσs : σ < s.re) :
    Integrable (fun z => (∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖) *
      ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ) cellMeasure := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_tsum_norm_poincProfile_le_fd hs hμ.le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_tsum_norm_poincProfile_le_fd (s := (σ : ℂ))
    (by simpa using hσ) (μ := 0) le_rfl
  have hk : 0 < 2 * Real.pi * μ := by positivity
  have hdec : ∀ (a : ℝ), 0 < a → ∀ y : ℝ, 0 < y →
      y ^ a * Real.exp (-(2 * Real.pi * μ * y)) ≤ (a / (2 * Real.pi * μ)) ^ a := fun a ha y hy => by
    have h := SelbergPoincareBounded.rpow_mul_exp_le ha hk hy.le
    rwa [show -(2 * Real.pi * μ) * y = -(2 * Real.pi * μ * y) by ring] at h
  set K₂ := ((s.re + σ) / (2 * Real.pi * μ)) ^ (s.re + σ)
  set K₃ := ((s.re + 1 - σ) / (2 * Real.pi * μ)) ^ (s.re + 1 - σ)
  set D₁ : ℝ := (1 / 2) ^ (2 - s.re - σ)
  have hK₂ : 0 ≤ K₂ := Real.rpow_nonneg (by positivity) _
  have hK₃ : 0 ≤ K₃ := Real.rpow_nonneg (div_nonneg (by linarith) hk.le) _
  have hD₁ : 0 ≤ D₁ := Real.rpow_nonneg (by norm_num) _
  have hcont : Continuous fun z : ℍ => (∑' p : gammaSet 1 1 0,
      ‖poincProfile s μ (gammaSetMatrix p • z)‖) * ∑' p : gammaSet 1 1 0,
        RHTower.rowHeight p z ^ σ :=
    (continuous_tsum_norm_poincProfile hs hμ.le).mul (continuous_tsum_rowHeight_rpow hσ)
  set C : ℝ := 2 * C₁ + C₁ * C₂ * D₁ + 2 * C₂ * K₃ + 4 * K₂
  have hint := integrableOn_fd_of_norm_le_two (g := fun z : ℍ => (((∑' p : gammaSet 1 1 0,
      ‖poincProfile s μ (gammaSetMatrix p • z)‖) * ∑' p : gammaSet 1 1 0,
        RHTower.rowHeight p z ^ σ : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp hcont).aestronglyMeasurable)
    (β₁ := 1 - s.re + σ) (β₂ := 0) (C := C) (by linarith) (by norm_num) fun z hz => by
      have hy : 1 / 2 < z.im := RHTower.half_lt_im_of_mem_fd' hz
      have hy0 : 0 < z.im := z.im_pos
      have h1 := hC₁ z hz
      have h2 := hC₂ z hz
      have hR : ∀ p : gammaSet 1 1 0, ‖poincProfile (σ : ℂ) 0 (gammaSetMatrix p • z)‖ =
          RHTower.rowHeight p z ^ σ := fun p => by
        rw [norm_poincProfile]; simp [RHTower.rowHeight]
      simp only [hR, Complex.ofReal_re, mul_zero, zero_mul, neg_zero, Real.exp_zero,
        mul_one] at h2
      have hA0 : 0 ≤ ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖ :=
        tsum_nonneg fun _ => norm_nonneg _
      have hB0 : 0 ≤ ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ :=
        tsum_rowHeight_rpow_nonneg σ z
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 hB0),
        Real.rpow_zero]
      set y := z.im
      set e := Real.exp (-(2 * Real.pi * μ * y))
      have he0 : 0 ≤ e := (Real.exp_pos _).le
      have p1 : y ^ (1 - s.re) * y ^ (1 - σ) ≤ D₁ := by
        rw [← Real.rpow_add hy0, show 1 - s.re + (1 - σ) = 2 - s.re - σ by ring]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hy.le (by linarith)
      have p2 : y ^ (1 - s.re) * y ^ σ = y ^ (1 - s.re + σ) := by
        rw [← Real.rpow_add hy0]
      have p3 : y ^ s.re * e * y ^ (1 - σ) ≤ K₃ := by
        rw [mul_right_comm, ← Real.rpow_add hy0, show s.re + (1 - σ) = s.re + 1 - σ by ring]
        exact hdec _ (by linarith) y hy0
      have p4 : y ^ s.re * e * y ^ σ ≤ K₂ := by
        rw [mul_right_comm, ← Real.rpow_add hy0]
        exact hdec _ (by linarith) y hy0
      have hyβ : 0 ≤ y ^ (1 - s.re + σ) := Real.rpow_nonneg hy0.le _
      have hy1 : 0 ≤ y ^ (1 - s.re) := Real.rpow_nonneg hy0.le _
      have hy2 : 0 ≤ y ^ (1 - σ) := Real.rpow_nonneg hy0.le _
      have hy3 : 0 ≤ y ^ s.re := Real.rpow_nonneg hy0.le _
      have hy4 : 0 ≤ y ^ σ := Real.rpow_nonneg hy0.le _
      calc (∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖) *
            ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ
          ≤ (C₁ * y ^ (1 - s.re) + 2 * (y ^ s.re * e)) * (C₂ * y ^ (1 - σ) + 2 * y ^ σ) :=
            mul_le_mul h1 h2 hB0 (by positivity)
        _ = C₁ * C₂ * (y ^ (1 - s.re) * y ^ (1 - σ)) + 2 * C₁ * (y ^ (1 - s.re) * y ^ σ) +
            2 * C₂ * (y ^ s.re * e * y ^ (1 - σ)) + 4 * (y ^ s.re * e * y ^ σ) := by ring
        _ ≤ C₁ * C₂ * D₁ + 2 * C₁ * y ^ (1 - s.re + σ) + 2 * C₂ * K₃ + 4 * K₂ := by
            rw [p2]
            have q1 := mul_le_mul_of_nonneg_left p1 (mul_nonneg hC₁0 hC₂0)
            have q3 := mul_le_mul_of_nonneg_left p3 (by positivity : (0 : ℝ) ≤ 2 * C₂)
            linarith
        _ ≤ C * (y ^ (1 - s.re + σ) + 1) := by
            have : 0 ≤ C₁ * C₂ * D₁ + 2 * C₂ * K₃ + 4 * K₂ := by positivity
            nlinarith
  exact hint.re.congr (Eventually.of_forall fun z => Complex.ofReal_re _)

theorem norm_poincSeries_le (h : ℍ → ℂ) (v : DeckSpace N) {z : ℍ}
    (hsum : Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖) :
    ‖poincSeries h v z‖ ≤ ‖v‖ * ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖ := by
  calc ‖poincSeries h v z‖ ≤ ∑' p, ‖poincTerm h v p z‖ :=
        norm_tsum_le_tsum_norm ((hsum.mul_right ‖v‖).congr fun p => (norm_poincTerm h v p z).symm)
    _ = ‖v‖ * ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖ := by
        simp_rw [norm_poincTerm]
        rw [tsum_mul_right, mul_comm]

/-- **A field dominated by a Selberg–Poincaré majorant against an incomplete Eisenstein series**:
if `‖U‖ ≤ C Σ_p |h_{s₁,μ}(M_p ·)|`, then
`⟨U, E(·|φ,w)⟩ = π⁻¹ ∫ φ̂(σ+it) ∫_𝒟 ⟨U, Ẽ(·, σ+it; w)⟩ dt` for `1 < σ < Re s₁`. -/
theorem inner_toDeckL2_incEisL2_eq_integral_line (hN : 2 ≤ N) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ}
    (hμ : 0 < μ) {U : ℍ → DeckSpace N} (hUc : Continuous U) (hUL : MemLp U 2 cellMeasure) {C : ℝ}
    (hU : ∀ z, ‖U z‖ ≤ C * ∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖)
    (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun) {w : DeckSpace N} (hw : IsCuspVec w) {σ : ℝ}
    (hσ : 1 < σ) (hσs : σ < s₁.re) :
    ⟪toDeckL2 U hUL, incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
        ∫ z in fd, ⟪U z, eisVec ((σ : ℂ) + t * Complex.I) w z⟫_ℂ := by
  set h : ℝ → ℂ := fun t => hMellin φ.toFun ((σ : ℂ) + t * Complex.I)
  set E : ℝ → ℍ → DeckSpace N := fun t z => eisVec ((σ : ℂ) + t * Complex.I) w z
  set f : ℍ → ℝ → ℂ := fun z t => h t * ⟪U z, E t z⟫_ℂ
  have hh : Integrable h := φ.integrable_hMellin_line hφ σ
  have hre : ∀ t : ℝ, 1 < ((σ : ℂ) + t * Complex.I).re := fun t => by simpa using hσ
  set R : ℍ → ℝ := fun z => ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ σ
  have hE : ∀ t z, ‖E t z‖ ≤ 1 / 2 * (R z * ‖w‖) := fun t z => by
    have := norm_eisVec_le (hre t) w z
    simpa using this
  have hEc : ∀ z, Continuous fun t => E t z := fun z => continuous_eisVec_line hN hw z hσ
  have hintz : ∀ z, Integrable fun t => h t • E t z := fun z => by
    refine (hh.norm.mul_const (1 / 2 * (R z * ‖w‖))).mono'
      ((hh.aestronglyMeasurable).smul (hEc z).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hE t z) (norm_nonneg _)
  set A : ℍ → ℝ := fun z => ∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖
  set B : ℍ → ℝ := fun z => C * ‖w‖ / 2 * (A z * R z)
  have hB : Integrable B cellMeasure :=
    (integrable_tsum_norm_poincProfile_mul_rowSum hs₁ hμ hσ hσs).const_mul _
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (cellMeasure.prod volume) := by
    have hs : StronglyMeasurable (Function.uncurry fun (t : ℝ) (z : ℍ) => f z t) := by
      refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => ?_)
        (fun t => ?_)
      · exact (φ.continuous_hMellin_line σ).mul (continuous_const.inner (hEc z))
      · exact (continuous_const.mul (hUc.inner (continuous_eisVec (hre t) hw.1))).stronglyMeasurable
    exact (hs.comp_measurable measurable_swap).aestronglyMeasurable
  have hint : Integrable (Function.uncurry f) (cellMeasure.prod volume) := by
    refine (hB.mul_prod hh.norm).mono' hmeas (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, f, norm_mul]
    rw [mul_comm (‖h p.2‖)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖U p.1‖ * ‖E p.2 p.1‖ ≤ (C * A p.1) * (1 / 2 * (R p.1 * ‖w‖)) :=
          mul_le_mul (hU p.1) (hE _ _) (norm_nonneg _) ((norm_nonneg _).trans (hU p.1))
      _ = B p.1 := by simp only [B]; ring
  have hinner : ⟪toDeckL2 U hUL, incEisL2 φ w⟫_ℂ = ∫ z in fd, ⟪U z, incEis φ.toFun w z⟫_ℂ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hUL, incEisL2_coeFn φ w] with z h1 h2
    change ⟪(hUL.toLp U) z, (incEisL2 φ w) z⟫_ℂ = _
    rw [h1, h2]
  have hpt : ∀ z, ⟪U z, incEis φ.toFun w z⟫_ℂ = (Real.pi : ℂ)⁻¹ * ∫ t, f z t := fun z => by
    rw [incEis_eq_integral_eisVec φ hφ hσ w z, inner_smul_right, ← integral_inner (hintz z)]
    simp_rw [inner_smul_right]
    rfl
  rw [hinner, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [f]
  rw [integral_const_mul]

/-- **The Poincaré series against an incomplete Eisenstein series as a line integral**:
`⟨U, E(·|φ,w)⟩ = π⁻¹ ∫ φ̂(σ+it) ∫_𝒟 ⟨U, Ẽ(·, σ+it; w)⟩ dt` for `1 < σ < Re s₁`. -/
theorem inner_poincL2_incEisL2_eq_integral_line (hN : 2 ≤ N) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ}
    (hμ : 0 < μ) (v : DeckSpace N) (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun)
    {w : DeckSpace N} (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 < σ) (hσs : σ < s₁.re) :
    ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
        ∫ z in fd, ⟪poincSeries (poincProfile s₁ μ) v z,
          eisVec ((σ : ℂ) + t * Complex.I) w z⟫_ℂ :=
  inner_toDeckL2_incEisL2_eq_integral_line hN hs₁ hμ (continuous_poincSeries_profile hs₁ hμ.le v)
    _ (C := ‖v‖) (fun z => norm_poincSeries_le _ v (summable_norm_poincProfile hs₁ hμ.le z)) φ hφ hw
    hσ hσs

/-- **The conjugate series against an incomplete Eisenstein series as a line integral.** -/
theorem inner_conjL2_incEisL2_eq_integral_line (hN : 2 ≤ N) {s₂ : ℂ} (hs₂ : 1 < s₂.re) {ν : ℝ}
    (hν : 0 < ν) (w₂ : DeckSpace N) (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun)
    {w : DeckSpace N} (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 < σ) (hσs : σ < s₂.re) :
    ⟪toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w₂), incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
        ∫ z in fd, ⟪poincSeries (conjProfile s₂ ν) w₂ z,
          eisVec ((σ : ℂ) + t * Complex.I) w z⟫_ℂ :=
  inner_toDeckL2_incEisL2_eq_integral_line hN hs₂ hν
    (continuous_poincSeries_conjProfile hs₂ hν.le w₂) _ (C := ‖w₂‖) (fun z => by
      refine (norm_poincSeries_le _ w₂ (summable_norm_conjProfile hs₂ hν.le z)).trans_eq ?_
      simp_rw [norm_conjProfile]) φ hφ hw hσ hσs

/-- **Unfolding the conjugate series against fields of moderate growth**, in coordinates. -/
theorem integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff_of_majorant {s : ℂ}
    (hs : 1 < s.re) {ν : ℝ} (hν : 0 ≤ ν) {w : DeckSpace N} (hw : IsCuspEigen (-ν) w)
    {G : ℍ → DeckSpace N} (hGc : Continuous G) (hGe : deckEquivariant N G)
    (hmaj : Integrable (fun z => (∑' p : gammaSet 1 1 0,
      ‖poincProfile s ν (gammaSetMatrix p • z)‖) * ‖G z‖) cellMeasure) :
    ∫ z in fd, ⟪poincSeries (conjProfile s ν) w z, G z⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ •
        ((y : ℂ) ^ s * (Real.exp (-(2 * Real.pi * ν * y)) : ℂ) * deckCuspCoeff (-ν) w G y) := by
  have hc := cuspCompatible_conjProfile s hw
  have hmaj' : Integrable (fun z => (∑' p : gammaSet 1 1 0,
      ‖conjProfile s ν (gammaSetMatrix p • z)‖) * ‖G z‖) cellMeasure := by
    simp_rw [norm_conjProfile]
    exact hmaj
  have hint := integrableOn_poincIntegrand_strip_of_majorant hc (continuous_conjProfile s ν) hGc
    hGe (summable_norm_conjProfile hs hν) hmaj'
  rw [integral_inner_poincSeries_of_majorant hc (continuous_conjProfile s ν) hGc hGe
    (summable_norm_conjProfile hs hν) hmaj', setIntegral_modularStrip_eq_iterated _ hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  congr 1
  rw [deckCuspCoeff, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [ofComplex_eq_hLine hy, poincIntegrand, conjProfile, Complex.conj_conj, poincProfile_hLine]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
