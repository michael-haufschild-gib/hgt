import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseMellinTrace

/-!
# The actual source theta function is recovered from its critical trace

Right-line Mellin inversion and the actual-source contour passage give an exact
identity with the canonical measurable trace. No atomic representation, support
gap, boundary continuity, or extra coefficient estimate is assumed.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open GaloisForLFunctions.HTGeometry WeilSpectral IntegerMassRigidity PhaseLockRigidity
  FractionalMassRigidity HamburgerStability

/-- Dirichlet coefficients of the actual producer, before any rigidity claim. -/
def sourceCoeff (lam : ℕ → ℝ) : ℕ → ℂ := dirichletExp (lamLog lam)

theorem sourceCoeff_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (sourceCoeff lam) s ∧ LSeries (sourceCoeff lam) s = zetaOf lam s :=
  LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
    (lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hs)

theorem summable_sourceCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖sourceCoeff lam (n + 1)‖ / ((n : ℝ) + 1) ^ σ) :=
  summable_coeff_of_LSeriesSummable (sourceCoeff_LSeries hW (by simpa using hσ)).1

theorem mellin_sourceCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (coeffTheta (sourceCoeff lam)) (s / 2) =
      sourceRemainder hW s + betaG (sourceCompletion hW) * Gammaℝ (s - 1) := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [mellin_coeffTheta _ (fun σ hσ => summable_sourceCoeff hW hσ) hs,
    coeffDirichlet_eq_LSeries, (sourceCoeff_LSeries hW hs).2,
    sourceRemainder, bigEG_eq h0 h1, sourceCompletion_eq_bigG hW hs]
  unfold bigG
  field_simp
  ring

/-- Actual theta inversion on the full canonical critical trace. The factor
`1/(4*pi)` includes the height substitution in the half-argument Mellin transform. -/
theorem coeffTheta_eq_remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    coeffTheta (sourceCoeff lam) r -
        betaG (sourceCompletion hW) * ((r : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi r) =
      (1 / (4 * Real.pi)) •
        ∫ y : ℝ, (r : ℂ) ^ (-tracePoint 0 y / 2) * remainderTrace hW y := by
  obtain ⟨C, _, hC⟩ := exists_decay_sourceRemainder hW
  have hmem : ∀ s ∈ verticalStrip (2 * (3 / 4 : ℝ)) (3 / 2), 1 / 2 < s.re := by
    intro s hs
    change 2 * (3 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 3 / 2 at hs
    linarith [hs.1]
  have hc : ContinuousOn (sourceRemainder hW) (verticalStrip (2 * (3 / 4 : ℝ)) (3 / 2)) :=
    (differentiableOn_sourceRemainder hW).continuousOn.mono (fun s hs => hmem s hs)
  have hd : DifferentiableOn ℂ (sourceRemainder hW)
      {s : ℂ | 2 * (3 / 4 : ℝ) < s.re ∧ s.re < 3 / 2} :=
    (differentiableOn_sourceRemainder hW).mono (fun s hs => by
      change 1 / 2 < s.re
      linarith [hs.1])
  have hb : ∀ s ∈ verticalStrip (2 * (3 / 4 : ℝ)) (3 / 2),
      ‖sourceRemainder hW s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hs
    exact hC s (hmem s hs) hs.2
  have hi := inverse_mellin_shift (θ := coeffTheta (sourceCoeff lam))
    (β := betaG (sourceCompletion hW)) (σ := 3 / 4) (by rfl)
    (continuousOn_coeffTheta _ (summable_sourceCoeff hW (by norm_num : (1 : ℝ) < 2)))
    (mellinConvergent_coeffTheta _ (fun σ hσ => summable_sourceCoeff hW hσ)
      (by norm_num) (by norm_num)) hc hd hb
    (fun s hs => mellin_sourceCoeff hW (by rw [hs]; norm_num)) hr
  let F : ℝ → ℂ := fun y =>
    (r : ℂ) ^ (-tracePoint 1 y / 2) * sourceRemainder hW (tracePoint 1 y)
  have hp : ∀ t : ℝ, tracePoint 1 (2 * t) = 2 * (((3 / 4 : ℝ) : ℂ) + t * I) := by
    intro t
    unfold tracePoint
    push_cast
    ring
  have he : ∀ t : ℝ, -tracePoint 1 (2 * t) / 2 = -(((3 / 4 : ℝ) : ℂ) + t * I) := by
    intro t
    rw [hp]
    ring
  have hint : (∫ t : ℝ, (r : ℂ) ^ (-(((3 / 4 : ℝ) : ℂ) + t * I)) *
      sourceRemainder hW (2 * (((3 / 4 : ℝ) : ℂ) + t * I))) =
      (1 / 2 : ℝ) • ∫ y : ℝ, F y := by
    calc
      _ = ∫ t : ℝ, F (2 * t) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by dsimp [F]; rw [he, hp])
      _ = _ := by simpa using Measure.integral_comp_mul_left F 2
  rw [hint, smul_smul] at hi
  have hfactor : (1 / (2 * Real.pi)) * (1 / 2 : ℝ) = 1 / (4 * Real.pi) := by ring
  rw [hfactor] at hi
  exact hi.trans (congrArg (fun z : ℂ => (1 / (4 * Real.pi)) • z)
    (integral_sourceRemainder_eq_boundary hW hr))

theorem tracePoint_zero_two (t : ℝ) : tracePoint 0 (2 * t) = lineS t := by
  unfold tracePoint lineS
  push_cast
  ring

private theorem tracePoint_zero_half (t : ℝ) :
    -tracePoint 0 (2 * t) / 2 = -(((1 / 4 : ℝ) : ℂ) + t * I) := by
  rw [tracePoint_zero_two]
  unfold lineS
  ring

/-- Boundary value of the uncompleted Dirichlet producer. -/
def sourcePhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℂ :=
  sourceTrace hW (2 * t) / (lineS t * (lineS t - 1) * Gammaℝ (lineS t))

theorem remainderTrace_add_eq_sourcePhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (t : ℝ) :
    remainderTrace hW (2 * t) + betaG (sourceCompletion hW) * Gammaℝ (lineS t - 1) =
      Gammaℝ (lineS t) * sourcePhi hW t := by
  rw [remainderTrace, tracePoint_zero_two]
  unfold sourcePhi
  have h0 := lineS_ne_zero t
  have h1 := sub_ne_zero.mpr (lineS_ne_one t)
  have hΓ := Gammaℝ_lineS_ne_zero t
  field_simp
  ring

theorem integrable_weighted_remainderTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : ℝ => (r : ℂ) ^ (-tracePoint 0 y / 2) * remainderTrace hW y) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hw : Continuous (fun y : ℝ => (r : ℂ) ^ (-tracePoint 0 y / 2)) :=
    Continuous.const_cpow (by unfold tracePoint; fun_prop) (Or.inl hr0)
  refine (integrable_remainderTrace hW).bdd_mul (c := r ^ (-(1 / 4 : ℝ))) hw.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  exact le_of_eq (by rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; norm_num [tracePoint])

private theorem coeffTheta_eq_half_remainderTrace {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {r : ℝ} (hr : 0 < r) :
    coeffTheta (sourceCoeff lam) r -
        betaG (sourceCompletion hW) * ((r : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi r) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ,
        (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * remainderTrace hW (2 * t) := by
  simp_rw [← tracePoint_zero_half]
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => (r : ℂ) ^ (-tracePoint 0 y / 2) * remainderTrace hW y) 2
  rw [show |(2 : ℝ)⁻¹| = 1 / 2 by norm_num] at h
  rw [h, smul_smul]
  convert coeffTheta_eq_remainderTrace hW hr using 1
  congr 1
  ring

private theorem integrable_polar_weight {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    Integrable (fun t : ℝ => (r : ℂ) ^ (-((σ : ℂ) + t * I)) * Gammaℝ (lineS t - 1)) := by
  have h := integrable_cpow_mul_Gammaℝ_line (σ := σ) (a := -(1 / 2)) (c := 2)
    hr two_ne_zero (fun k hk => by
      have h4 : (4 * k : ℝ) = 1 := by linarith
      have : (4 * k : ℕ) = 1 := by exact_mod_cast h4
      omega)
  have e : ∀ t : ℝ, (((-(1 / 2) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) = lineS t - 1 :=
    fun t => by unfold lineS; push_cast; ring
  simpa only [e] using h

private theorem polar_boundary_inverse {r : ℝ} (hr : 0 < r) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * Gammaℝ (lineS t - 1) =
        (r : ℂ) ^ (-(1 / 2 : ℂ)) * (expNegPi r - 1) := by
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * y)
  have hM : ∀ t : ℝ, HasMellin f (((1 / 4 : ℝ) : ℂ) + t * I) (Gammaℝ (lineS t - 1)) := by
    intro t
    have h := hasMellin_halfPow_expNegSubOne_pi (s := lineS t)
      (by rw [lineS_re]; norm_num) (by rw [lineS_re]; norm_num)
    rwa [show lineS t / 2 = ((1 / 4 : ℝ) : ℂ) + t * I by unfold lineS; ring] at h
  have hm : MellinConvergent f ((1 / 4 : ℝ) : ℂ) := by simpa using (hM 0).1
  have hv : VerticalIntegrable (mellin f) (1 / 4) volume := by
    unfold VerticalIntegrable
    have h := integrable_polar_weight one_pos 0
    simp only [ofReal_one, one_cpow, one_mul] at h
    exact h.congr (Eventually.of_forall fun t => ((hM t).2).symm)
  have hc : ContinuousAt f r := by
    refine ContinuousAt.mul ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hr)).comp
      Complex.continuous_ofReal.continuousAt) ?_
    unfold expNegSubOne
    fun_prop
  have hi := mellinInv_mellin_eq (1 / 4) f hr hm hv hc
  unfold mellinInv at hi
  rw [Complex.real_smul] at hi
  have he : expNegSubOne (Real.pi * r) = expNegPi r - 1 := by
    unfold expNegSubOne expNegPi
    push_cast
    ring
  change _ = (r : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * r) at hi
  rw [he] at hi
  convert hi using 1
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by
    simp only [smul_eq_mul]
    rw [(hM t).2])

/-- The actual-source input for the corpus theta-defect calculus, with the polar
part restored. All regularity needed here follows from the original source. -/
theorem coeffTheta_eq_sourcePhi_kernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    coeffTheta (sourceCoeff lam) r = betaG (sourceCompletion hW) * (r : ℂ) ^ (-(1 / 2 : ℂ)) +
      defectKernel (sourcePhi hW) r := by
  have h1 := coeffTheta_eq_half_remainderTrace hW hr
  rw [Complex.real_smul] at h1
  have h2 := polar_boundary_inverse hr
  have hIE : Integrable (fun t : ℝ => (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      remainderTrace hW (2 * t)) := by
    simpa only [tracePoint_zero_half] using
      (integrable_weighted_remainderTrace hW hr).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
  have hIG := integrable_polar_weight hr (1 / 4)
  have hpt : ∀ t : ℝ, (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Gammaℝ (lineS t) * sourcePhi hW t) =
      (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * remainderTrace hW (2 * t) +
        betaG (sourceCompletion hW) *
          ((r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * Gammaℝ (lineS t - 1)) := by
    intro t
    rw [← remainderTrace_add_eq_sourcePhi]
    ring
  unfold defectKernel
  change _ = _ + ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * (Gammaℝ (lineS t) * sourcePhi hW t)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hIE
    (hIG.const_mul (betaG (sourceCompletion hW))), integral_const_mul]
  linear_combination h1 - betaG (sourceCompletion hW) * h2

/-- The full reflected defect, with no mass removed from the canonical trace. -/
def sourceDefect {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℂ :=
  (sourceTrace hW (2 * t) - sourceTrace hW (-(2 * t))) /
    (lineS t * (lineS t - 1) * Gammaℝ (lineS t))

theorem Gamma_mul_sourcePhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    Gammaℝ (lineS t) * sourcePhi hW t = sourceTrace hW (2 * t) / (lineS t * (lineS t - 1)) := by
  unfold sourcePhi
  have h0 := lineS_ne_zero t
  have h1 := sub_ne_zero.mpr (lineS_ne_one t)
  have hΓ := Gammaℝ_lineS_ne_zero t
  field_simp

theorem Gamma_mul_sourceDefect {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    Gammaℝ (lineS t) * sourceDefect hW t =
      Gammaℝ (lineS t) * sourcePhi hW t - Gammaℝ (lineS (-t)) * sourcePhi hW (-t) := by
  rw [Gamma_mul_sourcePhi, Gamma_mul_sourcePhi]
  have hq : lineS (-t) * (lineS (-t) - 1) = lineS t * (lineS t - 1) := by
    rw [← one_sub_lineS]
    ring
  rw [hq, show 2 * -t = -(2 * t) by ring]
  unfold sourceDefect
  have h0 := lineS_ne_zero t
  have h1 := sub_ne_zero.mpr (lineS_ne_one t)
  have hΓ := Gammaℝ_lineS_ne_zero t
  field_simp

theorem integrable_weighted_sourcePhi {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Gammaℝ (lineS t) * sourcePhi hW t)) := by
  have hIE : Integrable (fun t : ℝ => (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      remainderTrace hW (2 * t)) := by
    simpa only [tracePoint_zero_half] using
      (integrable_weighted_remainderTrace hW hr).comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)
  have hIG := integrable_polar_weight hr (1 / 4)
  exact (hIE.add (hIG.const_mul (betaG (sourceCompletion hW)))).congr
    (Eventually.of_forall fun t => by dsimp only [Pi.add_apply]; rw [← remainderTrace_add_eq_sourcePhi]; ring)

theorem sourceDefect_kernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    defectKernel (sourceDefect hW) r = defectKernel (sourcePhi hW) r -
      (r : ℂ) ^ (-(1 / 2 : ℂ)) * defectKernel (sourcePhi hW) r⁻¹ := by
  have hpt : ∀ t : ℝ, (r : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((r⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) *
        (Gammaℝ (lineS (-t)) * sourcePhi hW (-t))) =
      (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        (Gammaℝ (lineS (-t)) * sourcePhi hW (-t)) := by
    intro t
    rw [ofReal_inv_cpow_eq hr, ← mul_assoc, ofReal_cpow_mul_ofReal_cpow hr]
    congr 2
    push_cast
    ring
  have hi := ((integrable_weighted_sourcePhi hW (inv_pos.mpr hr)).comp_neg.const_mul
    ((r : ℂ) ^ (-(1 / 2 : ℂ)))).congr (Eventually.of_forall hpt)
  have hreflect : (r : ℂ) ^ (-(1 / 2 : ℂ)) * (∫ t : ℝ,
      ((r⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        (Gammaℝ (lineS t) * sourcePhi hW t)) =
      ∫ t : ℝ, (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        (Gammaℝ (lineS (-t)) * sourcePhi hW (-t)) := by
    rw [← integral_const_mul, ← integral_neg_eq_self]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hg : ∀ t : ℝ, (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Gammaℝ (lineS t) * sourceDefect hW t) =
      (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * (Gammaℝ (lineS t) * sourcePhi hW t) -
      (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        (Gammaℝ (lineS (-t)) * sourcePhi hW (-t)) := by
    intro t
    rw [Gamma_mul_sourceDefect, mul_sub]
  unfold defectKernel
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (r : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * (Gammaℝ (lineS t) * sourceDefect hW t)) = _
  rw [integral_congr_ae (Eventually.of_forall hg),
    integral_sub (integrable_weighted_sourcePhi hW hr) hi, ← hreflect]
  unfold lineS
  ring

/-- The reflected theta equation is available for the original full measure,
before atomicity or phase settlement is known. -/
theorem coeffTheta_source_reflection {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    coeffTheta (sourceCoeff lam) r =
      (r : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta (sourceCoeff lam) r⁻¹ -
        betaG (sourceCompletion hW) + betaG (sourceCompletion hW) * (r : ℂ) ^ (-(1 / 2 : ℂ)) +
          defectKernel (sourceDefect hW) r := by
  have hhalf : (r : ℂ) ^ (-(1 / 2 : ℂ)) * ((r⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [ofReal_inv_cpow_eq hr, ofReal_cpow_mul_ofReal_cpow hr]
    norm_num
  rw [coeffTheta_eq_sourcePhi_kernel hW hr,
    coeffTheta_eq_sourcePhi_kernel hW (inv_pos.mpr hr), sourceDefect_kernel hW hr]
  linear_combination -betaG (sourceCompletion hW) * hhalf

end RHTower.WeilWorkSettledPhase
