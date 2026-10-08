import GaloisForLFunctions.RHTower.WeilWorkQuantizationLaurentFinitePart
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# The actual source after matching the zeta pole

The divided difference of the source pole numerator removes its singularity
at one. Subtracting the regularized zeta function then gives a holomorphic
function whose literal critical trace is the source trace minus its residue
times zeta. Its Dirichlet coefficients and growth are supplied by full positivity.
-/

open Complex Set Filter MeasureTheory Topology GaloisForLFunctions
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial WeilWorkSettledPhase WeilSingularArithmetic
variable {lam : ℕ → ℝ}

/-- The holomorphic numerator of the source's simple pole. -/
def quantizationPoleNumerator (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  sourceCompletion hW s / (s * Gammaℝ s)

@[simp] theorem quantizationPoleNumerator_one (hW : WeilPositiveFull lam) :
    quantizationPoleNumerator hW 1 = sourceCompletion hW 1 := by
  simp [quantizationPoleNumerator, Gammaℝ_one]

theorem differentiableOn_quantizationPoleNumerator (hW : WeilPositiveFull lam) :
    DifferentiableOn ℂ (quantizationPoleNumerator hW) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  change 1 / 2 < s.re at hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  exact ((hasDerivAt_sourceCompletion hW hs).differentiableAt.div
    (differentiableAt_id.mul (differentiableAt_Gammaℝ (by linarith)))
    (mul_ne_zero hs0 (Gammaℝ_ne_zero_of_re_pos (by linarith)))).differentiableWithinAt

/-- The source with the same polar zeta contribution removed, filled at one. -/
def quantizationCenteredProdF (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  dslope (quantizationPoleNumerator hW) 1 s - sourceCompletion hW 1 * riemannZeta₀ s

theorem differentiableOn_quantizationCenteredProdF (hW : WeilPositiveFull lam) :
    DifferentiableOn ℂ (quantizationCenteredProdF hW) {s : ℂ | 1 / 2 < s.re} := by
  have hd := (Complex.differentiableOn_dslope
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re}))).mpr
        (differentiableOn_quantizationPoleNumerator hW)
  exact hd.sub ((differentiable_riemannZeta₀.differentiableOn).const_mul _)

theorem quantizationCenteredProdF_eq (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : s ≠ 1) :
    quantizationCenteredProdF hW s = prodF (quantizationCompletion hW) s -
      sourceCompletion hW 1 * riemannZeta s := by
  rw [quantizationCenteredProdF, dslope_of_ne _ hs, slope_def_module,
    quantizationPoleNumerator_one, riemannZeta_eq_inv_sub_add hs]
  change (s - 1)⁻¹ * (sourceCompletion hW s / (s * Gammaℝ s) - sourceCompletion hW 1) - _ =
    sourceCompletion hW s / (s * (s - 1) * Gammaℝ s) - _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Literal centered coefficients, with the unused zero coefficient normalized to zero. -/
def quantizationCenteredCoeff (hW : WeilPositiveFull lam) (n : ℕ) : ℂ :=
  if n = 0 then 0 else sourceCoeff lam n - sourceCompletion hW 1

@[simp] theorem quantizationCenteredCoeff_zero (hW : WeilPositiveFull lam) :
    quantizationCenteredCoeff hW 0 = 0 := by simp [quantizationCenteredCoeff]

theorem quantizationCenteredCoeff_summable (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (quantizationCenteredCoeff hW) s := by
  have hc := (LSeriesSummable_one_iff.mpr hs).smul (sourceCompletion hW 1)
  have hh := (sourceCoeff_LSeries hW hs).1.sub hc
  refine (LSeriesSummable_congr s ?_).mpr hh
  intro n hn
  simp [quantizationCenteredCoeff, hn]

theorem quantizationCenteredCoeff_LSeries (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (quantizationCenteredCoeff hW) s = quantizationCenteredProdF hW s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hc := (LSeriesSummable_one_iff.mpr hs).smul (sourceCompletion hW 1)
  rw [quantizationCenteredProdF_eq hW hs1, quantization_prodF_eq_zetaOf hW hs,
    ← (sourceCoeff_LSeries hW hs).2]
  calc
    _ = LSeries (sourceCoeff lam - sourceCompletion hW 1 • (1 : ℕ → ℂ)) s :=
      LSeries_congr (fun {n} hn => by simp [quantizationCenteredCoeff, hn]) s
    _ = _ := by rw [LSeries_sub (sourceCoeff_LSeries hW hs).1 hc,
      LSeries_smul, LSeries_one_eq_riemannZeta hs]

/-- The centered physical trace retains the actual measurable source boundary. -/
def quantizationCenteredTrace (hW : WeilPositiveFull lam) (t : ℝ) : ℂ :=
  quantizationTraceF hW t - sourceCompletion hW 1 * riemannZeta (tracePoint 0 t)

theorem tendsto_quantizationCenteredTrace (hW : WeilPositiveFull lam) (t : ℝ) :
    Tendsto (fun η : ℝ => quantizationCenteredProdF hW (tracePoint η t))
      (𝓝[>] 0) (𝓝 (quantizationCenteredTrace hW t)) := by
  have hs1 : tracePoint 0 t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [tracePoint] at this
  have hp : Continuous (fun η : ℝ => tracePoint η t) := by unfold tracePoint; fun_prop
  have hz : Tendsto (fun η : ℝ => riemannZeta (tracePoint η t))
      (𝓝[>] 0) (𝓝 (riemannZeta (tracePoint 0 t))) :=
    (differentiableAt_riemannZeta hs1).continuousAt.tendsto.comp
    ((hp.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hf := (tendsto_quantizationTraceF hW t).sub (hz.const_mul (sourceCompletion hW 1))
  refine hf.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
  have hne : tracePoint η t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [tracePoint] at this
    linarith [hη.2]
  exact (quantizationCenteredProdF_eq hW hne).symm

/-- The actual pole-centered source has uniform linear growth on the critical strip tails. -/
theorem exists_quantizationCenteredProdF_tail (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 < σ → σ ≤ 3 / 2 → 2 ≤ |t| →
      ‖quantizationCenteredProdF hW ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨A, hA, hF⟩ := exists_quantizationProdF_subpolynomial hW (p := 1) (by norm_num)
  refine ⟨A + ‖sourceCompletion hW 1‖ * (5 * Real.sqrt (3 / 2 + 3)), by positivity,
    fun σ t hσ hσ' ht => ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    norm_num [hi] at ht
  have hf := hF σ t hσ hσ' ht
  rw [Real.rpow_one] at hf
  have hz := norm_riemannZeta_le_linear_of_re_ge_half hσ.le
    (B := 3 / 2) (abs_le.mpr ⟨by linarith, hσ'⟩) (by linarith)
  rw [quantizationCenteredProdF_eq hW hs1]
  calc
    _ ≤ ‖prodF (quantizationCompletion hW) ((σ : ℂ) + t * I)‖ +
        ‖sourceCompletion hW 1‖ * ‖riemannZeta ((σ : ℂ) + t * I)‖ := by
      simpa only [norm_mul] using norm_sub_le
        (prodF (quantizationCompletion hW) ((σ : ℂ) + t * I))
        (sourceCompletion hW 1 * riemannZeta ((σ : ℂ) + t * I))
    _ ≤ A * (1 + |t|) + ‖sourceCompletion hW 1‖ *
        (5 * Real.sqrt (3 / 2 + 3) * |t|) := by gcongr
    _ ≤ _ := by nlinarith [norm_nonneg (sourceCompletion hW 1),
      Real.sqrt_nonneg (3 / 2 + 3)]

/-- One linear bound works down to the actual critical trace on every radial slice. -/
theorem exists_quantizationCenteredProdF_radial_bound (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η ∈ Ioo (0 : ℝ) (1 / 4), ∀ t : ℝ,
      ‖quantizationCenteredProdF hW (tracePoint η t)‖ ≤ C * (1 + |t|) := by
  obtain ⟨C, hC, htail⟩ := exists_quantizationCenteredProdF_tail hW
  let K : Set ℂ := Icc (1 / 2 : ℝ) (3 / 4) ×ℂ Icc (-2 : ℝ) 2
  let H (s : ℂ) : ℝ := ‖quantizationRightMajorant hW s‖ +
    ‖sourceCompletion hW 1‖ * ‖riemannZeta s‖
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn H K := by
    intro s hs
    have hs' := Complex.mem_reProdIm.mp hs
    have hs1 : s ≠ 1 := by
      intro h
      have hi := hs'.1.2
      norm_num [h] at hi
    exact ((continuousAt_quantizationRightMajorant hW hs'.1.1 hs'.1.2).norm.add
      ((differentiableAt_riemannZeta hs1).continuousAt.norm.const_mul _)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C (max B 0), hC.trans (le_max_left _ _), fun η hη t => ?_⟩
  by_cases ht : 2 ≤ |t|
  · exact (htail (1 / 2 + η) t (by linarith [hη.1]) (by linarith [hη.2]) ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have ht' : |t| ≤ 2 := (lt_of_not_ge ht).le
  have hs : tracePoint η t ∈ K := by
    apply Complex.mem_reProdIm.mpr
    simp only [tracePoint, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, sub_self, add_zero, add_im, mul_im, mul_one, zero_add]
    exact ⟨⟨by linarith [hη.1], by linarith [hη.2]⟩, abs_le.mp ht'⟩
  have hs1 : tracePoint η t ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [tracePoint] at he
    linarith [hη.2]
  have hb : ‖quantizationCenteredProdF hW (tracePoint η t)‖ ≤ B := by
    apply le_trans _ ((le_abs_self (H (tracePoint η t))).trans (hB _ hs))
    rw [quantizationCenteredProdF_eq hW hs1]
    calc
      _ ≤ ‖prodF (quantizationCompletion hW) (tracePoint η t)‖ +
          ‖sourceCompletion hW 1‖ * ‖riemannZeta (tracePoint η t)‖ := by
        simpa only [norm_mul] using norm_sub_le
          (prodF (quantizationCompletion hW) (tracePoint η t))
          (sourceCompletion hW 1 * riemannZeta (tracePoint η t))
      _ ≤ H (tracePoint η t) := add_le_add
        (norm_quantizationProdF_le_rightMajorant hW (s := tracePoint η t)
          (by simp [tracePoint]; linarith [hη.1]) (by simp [tracePoint]; linarith [hη.2])) le_rfl
  exact hb.trans ((le_max_left B 0).trans ((le_max_right C _).trans
    (le_mul_of_one_le_right (le_max_of_le_right (le_max_right B 0))
      (by linarith [abs_nonneg t]))))

theorem exists_quantizationCenteredTrace_bound (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖quantizationCenteredTrace hW t‖ ≤ C * (1 + |t|) := by
  obtain ⟨C, hC, hb⟩ := exists_quantizationCenteredProdF_radial_bound hW
  refine ⟨C, hC, fun t => le_of_tendsto (tendsto_quantizationCenteredTrace hW t).norm ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with η hη
  exact hb η hη t

end RHTower.WeilSpectral
