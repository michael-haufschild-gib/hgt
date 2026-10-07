import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialContour
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseMellinTrace

/-!
# Arithmetic Mellin inversion on the canonical radial trace

Identify the two normalized source constructions and reuse the checked weighted
boundary shift. The actual Dirichlet-exponential coefficients then have their
inverse-Mellin and theta representations on the measurable critical trace,
including the polar normalization. No reflected functional equation or continuous
critical-edge extension is assumed.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  WeilWorkSettledPhase GaloisForLFunctions.HTGeometry HamburgerStability

theorem quantizationCompletion_eq_sourceCompletion {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationCompletion hW = sourceCompletion hW := rfl

theorem quantizationCompletedTrace_ae_eq_sourceTrace {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) : quantizationCompletedTrace hW =ᵐ[volume] sourceTrace hW := by
  filter_upwards [tendsto_sourceTrace_ae hW] with y hy
  exact tendsto_nhds_unique (tendsto_quantizationCompletedTrace hW y) hy

/-- The actual radial trace after the removable pole subtraction. -/
def quantizationRemainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℂ :=
  quantizationCompletedTrace hW y / (tracePoint 0 y * (tracePoint 0 y - 1)) -
    betaG (quantizationCompletion hW) * Gammaℝ (tracePoint 0 y - 1)

theorem quantizationRemainderTrace_ae_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationRemainderTrace hW =ᵐ[volume] remainderTrace hW := by
  filter_upwards [quantizationCompletedTrace_ae_eq_sourceTrace hW] with y hy
  simp only [quantizationRemainderTrace, remainderTrace, hy,
    quantizationCompletion_eq_sourceCompletion]

theorem integrable_quantizationRemainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (quantizationRemainderTrace hW) :=
  (integrable_remainderTrace hW).congr (quantizationRemainderTrace_ae_eq hW).symm

theorem integral_quantizationRemainder_eq_boundary {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ, (x : ℂ) ^ (-tracePoint 1 y / 2) * sourceRemainder hW (tracePoint 1 y)) =
      ∫ y : ℝ, (x : ℂ) ^ (-tracePoint 0 y / 2) * quantizationRemainderTrace hW y := by
  rw [integral_sourceRemainder_eq_boundary hW hx]
  apply integral_congr_ae
  filter_upwards [quantizationRemainderTrace_ae_eq hW] with y hy
  rw [hy]

theorem quantization_dirichletExp_spec {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (dirichletExp (lamLog lam)) s ∧
      LSeries (dirichletExp (lamLog lam)) s = zetaOf lam s :=
  LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
    (lseriesSummable_of_le (norm_lamLog_le lam)
      (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ) hs)

theorem quantization_coeff_summable {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖dirichletExp (lamLog lam) (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
  summable_coeff_of_LSeriesSummable
    (quantization_dirichletExp_spec hW (s := (σ : ℂ)) (by simpa using hσ)).1

theorem quantization_mellin_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : s.re = 3 / 2) :
    mellin (coeffTheta (dirichletExp (lamLog lam))) (s / 2) =
      sourceRemainder hW s + betaG (quantizationCompletion hW) * Gammaℝ (s - 1) := by
  have h1 : 1 < s.re := by rw [hs]; norm_num
  have h0 : s ≠ 0 := by intro h; simp [h] at h1; linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at h1
  rw [mellin_coeffTheta _ (fun _ hσ => quantization_coeff_summable hW hσ) h1,
    coeffDirichlet_eq_LSeries, (quantization_dirichletExp_spec hW h1).2]
  simp only [sourceRemainder, ← quantizationCompletion_eq_sourceCompletion,
    bigEG_eq h0 hs1, quantizationCompletion_eq_bigG hW h1]
  unfold bigG
  field_simp
  ring

/-- The canonical coefficient theta series is the inverse Mellin transform of
its actual measurable radial trace, with the polar normalization retained. -/
theorem quantization_radial_inverse_mellin {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    coeffTheta (dirichletExp (lamLog lam)) x - betaG (quantizationCompletion hW) *
        ((x : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ,
        (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * quantizationRemainderTrace hW (2 * t) := by
  have ha := fun σ hσ => quantization_coeff_summable hW (σ := σ) hσ
  have hθc := continuousOn_coeffTheta (dirichletExp (lamLog lam)) (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta (dirichletExp (lamLog lam))) (3 / 4 : ℂ) :=
    mellinConvergent_coeffTheta (dirichletExp (lamLog lam)) ha (by norm_num) (by norm_num)
  obtain ⟨C, _, hC⟩ := exists_decay_sourceRemainder hW
  have hcont : ContinuousOn (sourceRemainder hW) (verticalStrip (2 * (3 / 4)) (3 / 2)) := by
    intro s hs
    rw [mem_verticalStrip] at hs
    exact ((differentiableOn_sourceRemainder hW).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        change (1 / 2 : ℝ) < s.re; linarith [hs.1]))).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℂ (sourceRemainder hW)
      {s : ℂ | 2 * (3 / 4) < s.re ∧ s.re < 3 / 2} :=
    (differentiableOn_sourceRemainder hW).mono (fun s hs => by
      change (1 / 2 : ℝ) < s.re; linarith [hs.1])
  have hdecay : ∀ s ∈ verticalStrip (2 * (3 / 4)) (3 / 2),
      ‖sourceRemainder hW s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hs
    rw [mem_verticalStrip] at hs
    exact hC s (by linarith [hs.1]) hs.2
  have hi := inverse_mellin_shift (σ := 3 / 4) (by norm_num) hθc hθm hcont hd hdecay
    (fun s hs => quantization_mellin_right hW hs) hx
  rw [hi]
  congr 1
  let R : ℝ → ℂ := fun y => (x : ℂ) ^ (-tracePoint 1 y / 2) * sourceRemainder hW (tracePoint 1 y)
  let L : ℝ → ℂ := fun y => (x : ℂ) ^ (-tracePoint 0 y / 2) * quantizationRemainderTrace hW y
  have hR : ∀ t : ℝ, (x : ℂ) ^ (-(((3 / 4 : ℝ) : ℂ) + t * I)) *
      sourceRemainder hW (2 * (((3 / 4 : ℝ) : ℂ) + t * I)) = R (2 * t) := by
    intro t
    have hp : tracePoint 1 (2 * t) = 2 * (((3 / 4 : ℝ) : ℂ) + t * I) := by
      unfold tracePoint; push_cast; ring
    simp only [R, hp]
    congr 2
    ring
  have hL : ∀ t : ℝ, L (2 * t) = (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      quantizationRemainderTrace hW (2 * t) := by
    intro t
    simp only [L]
    congr 2
    unfold tracePoint; push_cast; ring
  calc (∫ t : ℝ, (x : ℂ) ^ (-(((3 / 4 : ℝ) : ℂ) + t * I)) *
        sourceRemainder hW (2 * (((3 / 4 : ℝ) : ℂ) + t * I))) = ∫ t : ℝ, R (2 * t) :=
          integral_congr_ae (Eventually.of_forall hR)
    _ = |(2 : ℝ)⁻¹| • ∫ y : ℝ, R y := Measure.integral_comp_mul_left R 2
    _ = |(2 : ℝ)⁻¹| • ∫ y : ℝ, L y := by
        rw [show (∫ y : ℝ, R y) = ∫ y : ℝ, L y from integral_quantizationRemainder_eq_boundary hW hx]
    _ = ∫ t : ℝ, L (2 * t) := (Measure.integral_comp_mul_left L 2).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hL)

theorem integrable_quantizationMellin_integrand {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      quantizationRemainderTrace hW (2 * t) := by
  have hi := (integrable_quantizationRemainderTrace hW).comp_mul_left' (two_ne_zero' ℝ)
  have hm : AEStronglyMeasurable (fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))).aestronglyMeasurable
  apply hi.bdd_mul hm
  refine Eventually.of_forall fun t => ?_
  show ‖(x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I))‖ ≤ x ^ (-(1 / 4 : ℝ))
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem quantizationRemainderTrace_add {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    quantizationRemainderTrace hW (2 * t) + betaG (quantizationCompletion hW) *
      Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) =
        Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * quantizationTraceF hW (2 * t) := by
  have hp : 2 * (((1 / 4 : ℝ) : ℂ) + t * I) = tracePoint 0 (2 * t) := by
    unfold tracePoint; push_cast; ring
  rw [hp]
  have hsre : (tracePoint 0 (2 * t)).re = 1 / 2 := by simp
  have h0 : tracePoint 0 (2 * t) ≠ 0 := by intro h; rw [h] at hsre; norm_num at hsre
  have h1 : tracePoint 0 (2 * t) ≠ 1 := by intro h; rw [h] at hsre; norm_num at hsre
  have hΓ : Gammaℝ (tracePoint 0 (2 * t)) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have he : quantizationTraceF hW (2 * t) = quantizationCompletedTrace hW (2 * t) /
      (tracePoint 0 (2 * t) * (tracePoint 0 (2 * t) - 1) * Gammaℝ (tracePoint 0 (2 * t))) := by
    simp only [quantizationTraceF, tracePoint, add_zero]
  rw [quantizationRemainderTrace, sub_add_cancel, he]
  field_simp

/-- The source theta series, expressed by its actual boundary quotient. -/
theorem quantization_coeffTheta_eq_defectKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    coeffTheta (dirichletExp (lamLog lam)) x =
      betaG (quantizationCompletion hW) * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel (fun t => quantizationTraceF hW (2 * t)) x := by
  set β := betaG (quantizationCompletion hW)
  have h1 := quantization_radial_inverse_mellin hW hx
  rw [Complex.real_smul] at h1
  set f₀ : ℝ → ℂ := fun y => (y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * y) with hf₀
  have hM : ∀ t : ℝ, HasMellin f₀ (((1 / 4 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    intro t
    have h := hasMellin_halfPow_expNegSubOne_pi (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by simp; norm_num) (by simp; norm_num)
    rwa [show 2 * (((1 / 4 : ℝ) : ℂ) + t * I) / 2 = ((1 / 4 : ℝ) : ℂ) + t * I by ring] at h
  have hconv : MellinConvergent f₀ ((1 / 4 : ℝ) : ℂ) := by
    have := (hM 0).1
    simpa using this
  have hGint : ∀ {y : ℝ}, 0 < y → ∀ σ : ℝ, Integrable fun t : ℝ =>
      (y : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) := by
    intro y hy σ
    have h := integrable_cpow_mul_Gammaℝ_line (σ := σ) (a := -(1 / 2)) (c := 2) (x := y)
      hy two_ne_zero (fun k hk => by
        have h4 : (4 * k : ℝ) = 1 := by linarith
        have : (4 * k : ℕ) = 1 := by exact_mod_cast h4
        omega)
    have e : ∀ t : ℝ, (((-(1 / 2) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) =
        2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1 := fun t => by push_cast; ring
    simp only [e] at h
    exact h
  have hvert : VerticalIntegrable (mellin f₀) (1 / 4) volume := by
    unfold VerticalIntegrable
    have h := hGint one_pos 0
    simp only [ofReal_one, one_cpow, one_mul] at h
    refine h.congr (Eventually.of_forall fun t => ?_)
    exact ((hM t).2).symm
  have hcont : ContinuousAt f₀ x := by
    refine ContinuousAt.mul ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx)).comp
      Complex.continuous_ofReal.continuousAt) ?_
    unfold expNegSubOne
    fun_prop
  have h2 := mellinInv_mellin_eq (1 / 4) f₀ hx hconv hvert hcont
  unfold mellinInv at h2
  rw [Complex.real_smul] at h2
  have h2' : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) = f₀ x := by
    rw [← h2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [(hM t).2]
  have hIE := integrable_quantizationMellin_integrand hW hx
  have hIG := hGint hx (1 / 4)
  have hpt : ∀ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * quantizationTraceF hW (2 * t)) =
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * quantizationRemainderTrace hW (2 * t) +
        β * ((x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
          Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    intro t
    rw [← quantizationRemainderTrace_add hW t]
    ring
  have hsplit : defectKernel (fun t => quantizationTraceF hW (2 * t)) x =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * quantizationRemainderTrace hW (2 * t)) +
      β * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
          Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1)) := by
    unfold defectKernel
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hIE (hIG.const_mul β),
      integral_const_mul]
    ring
  have hexp : expNegSubOne (Real.pi * x) = expNegPi x - 1 := by
    unfold expNegSubOne expNegPi; push_cast; ring
  rw [hsplit, h2']
  simp only [hf₀, hexp]
  linear_combination h1

end RHTower.WeilSpectral
