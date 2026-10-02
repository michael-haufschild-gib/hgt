import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationContinuation
import GaloisForLFunctions.RHTower.LaplaceNegativeRealResidue

/-!
# Negative actual source correlations occur beyond every lag cutoff

The source-specific continued transform has a negative real pole. Landau
excludes an eventually nonnegative correlation without dropping its compact
head or presuming admission at a negative real frequency.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower

private theorem shifted_ray_kernel (a : ℝ → ℝ) (σ u : ℝ) :
    ((Real.exp ((5 / 4 : ℝ) * u) * a u *
      Real.exp (-σ * u) : ℝ) : ℂ) =
    expRay ((σ : ℂ) - 5 / 4) u * (a u : ℂ) := by
  unfold expRay
  push_cast
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  ring

private theorem not_eventually_nonneg_of_continued_ray
    {a : ℝ → ℝ} (hac : Continuous a) (hai : IntegrableOn a (Ioi 0)) {F : ℂ → ℂ}
    (hFa : ∀ x : ℝ, -1 < x → AnalyticAt ℂ F (x : ℂ))
    (hFt : ∀ σ : ℝ, 0 < σ → bochnerLaplaceRay (fun u => (a u : ℂ)) (σ : ℂ) = F (σ : ℂ))
    {κ : ℝ} (hκ : 0 < κ)
    (hFr : Tendsto (fun x : ℝ => (x + 1) * (F (x : ℂ)).re)
      (𝓝[>] (-1 : ℝ)) (𝓝 (-κ))) :
    ¬ ∃ H : ℝ, ∀ u : ℝ, H < u → 0 ≤ a u := by
  let g : ℝ → ℝ := fun u => Real.exp ((5 / 4 : ℝ) * u) * a u
  let G : ℂ → ℂ := fun s => F (s - 5 / 4)
  have hgc : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      hac
  have hk (σ : ℝ) (hσ : 3 / 2 < σ) :
      IntegrableOn (fun u : ℝ => expRay ((σ : ℂ) - 5 / 4) u *
        (a u : ℂ)) (Ioi 0) := by
    apply bochnerLaplaceRay_integrable
      (Complex.continuous_ofReal.comp hac).aestronglyMeasurable
      (c := 0) _ _ (by simp; linarith)
    convert (hai.ofReal (𝕜 := ℂ)) using 1
    simp [expRay, IntegrableOn]
  have hgi (σ : ℝ) (hσ : 3 / 2 < σ) :
      IntegrableOn (fun u : ℝ => g u * Real.exp (-σ * u)) (Ioi 0) := by
    apply (hk σ hσ).re.congr
    filter_upwards with u
    change (expRay ((σ : ℂ) - 5 / 4) u * (a u : ℂ)).re = _
    rw [← shifted_ray_kernel]
    rfl
  have htrans (σ : ℝ) (hσ : 3 / 2 < σ) :
      ((∫ u in Ioi (0 : ℝ), g u * Real.exp (-σ * u) : ℝ) : ℂ) = G (σ : ℂ) := by
    change _ = F ((σ : ℂ) - 5 / 4)
    have hc : (((σ - 5 / 4 : ℝ) : ℂ)) = (σ : ℂ) - 5 / 4 := by push_cast; rfl
    rw [← hc, ← hFt (σ - 5 / 4) (by linarith)]
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only [bochnerLaplaceRay]
    rw [hc]
    exact shifted_ray_kernel a σ u
  have hGan (σ : ℝ) (hσ : 1 / 4 < σ) : AnalyticAt ℂ G (σ : ℂ) := by
    have h := hFa (σ - 5 / 4) (by linarith)
    have hc : (((σ - 5 / 4 : ℝ) : ℂ)) = (σ : ℂ) - 5 / 4 := by push_cast; rfl
    rw [hc] at h
    exact AnalyticAt.comp (x := (σ : ℂ)) (g := F) (f := fun z : ℂ => z - 5 / 4)
      h (analyticAt_id.sub analyticAt_const)
  have hshift : Tendsto (fun σ : ℝ => σ - 5 / 4) (𝓝[>] (1 / 4 : ℝ))
      (𝓝[>] (-1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun σ : ℝ => σ - 5 / 4) := continuous_id.sub continuous_const
      convert (hc.tendsto (1 / 4 : ℝ)).mono_left
        (show 𝓝[>] (1 / 4 : ℝ) ≤ 𝓝 (1 / 4 : ℝ) from nhdsWithin_le_nhds) using 1
      norm_num
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change -1 < σ - 5 / 4
      change 1 / 4 < σ at hσ
      linarith
  have hres : Tendsto (fun σ : ℝ => (σ - 1 / 4) * (G (σ : ℂ)).re)
      (𝓝[>] (1 / 4 : ℝ)) (𝓝 (-κ)) := by
    have h := hFr.comp hshift
    convert h using 1
    funext σ
    dsimp [G]
    rw [show σ - 5 / 4 + 1 = σ - 1 / 4 by ring]
    push_cast
    rfl
  have hno := not_eventually_nonneg_of_negative_real_laplace_residue hgc hgi htrans hGan
    hκ hres
  rintro ⟨H, hH⟩
  apply hno
  exact ⟨H, fun u hu => mul_nonneg (Real.exp_pos _).le (hH u hu)⟩

/-- No finite head removal makes the literal critical source correlation nonnegative. -/
theorem criticalAbelLogAutocorrelation_not_eventually_nonneg :
    ¬ ∃ H : ℝ, ∀ u : ℝ, H < u → 0 ≤ criticalAbelLogAutocorrelation u := by
  exact not_eventually_nonneg_of_continued_ray continuous_criticalAbelLogAutocorrelation
    integrable_criticalAbelLogAutocorrelation.integrableOn
    (fun _ hx => analyticAt_criticalAbelCorrelationContinuation_real hx)
    (fun σ hσ => (criticalAbelCorrelationContinuation_eq_right (s := (σ : ℂ))
      (by simpa using hσ.le)).symm)
    criticalCorrelationNegativeResidue_pos criticalAbelCorrelationContinuation_left_residue

/-- Unconditional cofinal negativity of the actual critical Abel autocorrelation. -/
theorem criticalAbelLogAutocorrelation_negative_beyond (H : ℝ) :
    ∃ u : ℝ, H < u ∧ criticalAbelLogAutocorrelation u < 0 := by
  by_contra hn
  push Not at hn
  exact criticalAbelLogAutocorrelation_not_eventually_nonneg ⟨H, hn⟩

/-- The negative part has infinite exponential mass at the real source pole. -/
theorem not_integrableOn_criticalAbelLogAutocorrelation_negative_exp :
    ¬ IntegrableOn (fun u : ℝ => Real.exp u *
      max (-criticalAbelLogAutocorrelation u) 0) (Ioi 0) := by
  intro hi
  let N : ℝ → ℝ := fun u => max (-criticalAbelLogAutocorrelation u) 0
  let P : ℝ → ℝ := fun u => max (criticalAbelLogAutocorrelation u) 0
  let W : ℂ → ℂ := bochnerLaplaceRay (fun u => (N u : ℂ))
  let F : ℂ → ℂ := fun s => criticalAbelCorrelationContinuation s + W s
  have hNc : Continuous N := continuous_criticalAbelLogAutocorrelation.neg.max continuous_const
  have hPc : Continuous P := continuous_criticalAbelLogAutocorrelation.max continuous_const
  have hPi : Integrable P := by
    apply integrable_criticalAbelLogAutocorrelation.norm.mono' hPc.aestronglyMeasurable
    filter_upwards with u
    dsimp only [P]
    by_cases hu : 0 ≤ criticalAbelLogAutocorrelation u
    · simp [max_eq_left hu, Real.norm_eq_abs, abs_of_nonneg hu]
    · simp [max_eq_right (le_of_not_ge hu)]
  have hNin : IntegrableOn (fun u : ℝ => expRay ((-1 : ℝ) : ℂ) u • (N u : ℂ)) (Ioi 0) := by
    apply (hi.ofReal (𝕜 := ℂ)).congr
    filter_upwards with u
    change ((Real.exp u * N u : ℝ) : ℂ) = expRay ((-1 : ℝ) : ℂ) u • (N u : ℂ)
    simp [expRay, Complex.ofReal_mul, Complex.ofReal_exp]
  have hNa : AEStronglyMeasurable (fun u => (N u : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hNc).aestronglyMeasurable
  have hWa (x : ℝ) (hx : -1 < x) : AnalyticAt ℂ W (x : ℂ) := by
    have hdiff : DifferentiableOn ℂ W {s : ℂ | -1 < s.re} := by
      intro s hs
      exact (bochnerLaplaceRay_differentiableAt (S := fun u => (N u : ℂ)) hNa
        (c := (-1 : ℝ)) hNin s hs).differentiableWithinAt
    exact hdiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
  have hC0 : IntegrableOn (fun u : ℝ => expRay (0 : ℂ) u •
      (criticalAbelLogAutocorrelation u : ℂ)) (Ioi 0) := by
    convert (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).integrableOn
      (s := Ioi (0 : ℝ)) using 1
    simp [expRay]
  have hsplit (u : ℝ) : P u = criticalAbelLogAutocorrelation u + N u := by
    dsimp only [P, N]
    by_cases hu : 0 ≤ criticalAbelLogAutocorrelation u
    · simp [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu)]
    · have hn := le_of_not_ge hu
      simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
  have hFt (σ : ℝ) (hσ : 0 < σ) :
      bochnerLaplaceRay (fun u => (P u : ℂ)) (σ : ℂ) = F (σ : ℂ) := by
    have hCi := bochnerLaplaceRay_integrable
      (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).aestronglyMeasurable
      hC0 (σ : ℂ) hσ.le
    have hNi := bochnerLaplaceRay_integrable hNa hNin (σ : ℂ) (by simp; linarith)
    change (∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u • (P u : ℂ)) =
      criticalAbelCorrelationContinuation (σ : ℂ) +
        ∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u • (N u : ℂ)
    rw [criticalAbelCorrelationContinuation_eq_right (s := (σ : ℂ)) hσ.le]
    change _ = (∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u •
      (criticalAbelLogAutocorrelation u : ℂ)) + _
    rw [← integral_add
      (f := fun u : ℝ => expRay (σ : ℂ) u • (criticalAbelLogAutocorrelation u : ℂ))
      (g := fun u : ℝ => expRay (σ : ℂ) u • (N u : ℂ)) hCi hNi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [hsplit, Complex.ofReal_add, smul_add]
  let M : ℝ := ∫ u in Ioi (0 : ℝ), ‖expRay ((-1 : ℝ) : ℂ) u • (N u : ℂ)‖
  have hWzero : Tendsto (fun x : ℝ => (x + 1) * (W (x : ℂ)).re)
      (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have hx : Tendsto (fun x : ℝ => x + 1) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_id.mono_left
        (show 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ) from nhdsWithin_le_nhds)).add_const 1
    apply squeeze_zero_norm' _ (by simpa using hx.mul_const M)
    filter_upwards [self_mem_nhdsWithin] with x hx
    change -1 < x at hx
    have hd : 0 ≤ x + 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm (W (x : ℂ))).trans
      (bochnerLaplaceRay_norm_le hNin (x : ℂ) hx.le)) hd
  have hFr : Tendsto (fun x : ℝ => (x + 1) * (F (x : ℂ)).re)
      (𝓝[>] (-1 : ℝ)) (𝓝 (-criticalCorrelationNegativeResidue)) := by
    have h := criticalAbelCorrelationContinuation_left_residue.add hWzero
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards with x
    dsimp only [F]
    rw [Complex.add_re, mul_add]
  have hno := not_eventually_nonneg_of_continued_ray hPc hPi.integrableOn
    (fun x hx => (analyticAt_criticalAbelCorrelationContinuation_real hx).add (hWa x hx))
    hFt criticalCorrelationNegativeResidue_pos hFr
  exact hno ⟨0, fun u _ => le_max_right _ _⟩

private theorem expRay_mul_exp_neg (s : ℂ) (u : ℝ) :
    expRay s u * (Real.exp (-u) : ℂ) = Complex.exp (-(s + 1) * (u : ℂ)) := by
  unfold expRay
  rw [Complex.ofReal_exp, Complex.ofReal_neg, ← Complex.exp_add]
  congr 1
  ring

private theorem laplace_exp_neg {s : ℂ} (hs : 0 < s.re) :
    bochnerLaplaceRay (fun u : ℝ => (Real.exp (-u) : ℂ)) s = 1 / (s + 1) := by
  unfold bochnerLaplaceRay
  simp_rw [smul_eq_mul, expRay_mul_exp_neg]
  rw [integral_exp_mul_complex_Ioi (by simp; linarith)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]

/-- Every eventual exponential lower envelope below the actual residue fails. -/
theorem criticalAbelLogAutocorrelation_below_residue_envelope
    {k : ℝ} (hk : k < criticalCorrelationNegativeResidue) (H : ℝ) :
    ∃ u : ℝ, H < u ∧ criticalAbelLogAutocorrelation u < -k * Real.exp (-u) := by
  let a : ℝ → ℝ := fun u => criticalAbelLogAutocorrelation u + k * Real.exp (-u)
  let F : ℂ → ℂ := fun s => criticalAbelCorrelationContinuation s + (k : ℂ) / (s + 1)
  have hac : Continuous a := continuous_criticalAbelLogAutocorrelation.add
    (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg))
  have hai : IntegrableOn a (Ioi 0) :=
    integrable_criticalAbelLogAutocorrelation.integrableOn.add
      ((integrableOn_exp_neg_Ioi 0).const_mul k)
  have hFa (x : ℝ) (hx : -1 < x) : AnalyticAt ℂ F (x : ℂ) := by
    exact (analyticAt_criticalAbelCorrelationContinuation_real hx).add
      (analyticAt_const.div (analyticAt_id.add analyticAt_const)
        (Complex.ne_zero_of_re_pos (by simp; linarith)))
  have hC0 : IntegrableOn (fun u : ℝ => expRay (0 : ℂ) u •
      (criticalAbelLogAutocorrelation u : ℂ)) (Ioi 0) := by
    convert (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).integrableOn
      (s := Ioi (0 : ℝ)) using 1
    simp [expRay]
  have hFt (σ : ℝ) (hσ : 0 < σ) :
      bochnerLaplaceRay (fun u => (a u : ℂ)) (σ : ℂ) = F (σ : ℂ) := by
    have hCi := bochnerLaplaceRay_integrable
      (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).aestronglyMeasurable
      hC0 (σ : ℂ) hσ.le
    have hEi : IntegrableOn (fun u : ℝ => expRay (σ : ℂ) u •
        (Real.exp (-u) : ℂ)) (Ioi 0) := by
      apply (integrableOn_exp_mul_complex_Ioi (a := -((σ : ℂ) + 1))
        (by simp; linarith) 0).congr_fun _ measurableSet_Ioi
      intro u _
      exact (expRay_mul_exp_neg (σ : ℂ) u).symm
    calc
      _ = criticalAbelCorrelationLaplace (σ : ℂ) + (k : ℂ) *
          bochnerLaplaceRay (fun u : ℝ => (Real.exp (-u) : ℂ)) (σ : ℂ) := by
        change (∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u • (a u : ℂ)) =
          (∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u • (criticalAbelLogAutocorrelation u : ℂ)) +
            (k : ℂ) * ∫ u in Ioi (0 : ℝ), expRay (σ : ℂ) u • (Real.exp (-u) : ℂ)
        rw [← integral_const_mul, ← integral_add
          (f := fun u : ℝ => expRay (σ : ℂ) u • (criticalAbelLogAutocorrelation u : ℂ))
          (g := fun u : ℝ => (k : ℂ) * (expRay (σ : ℂ) u • (Real.exp (-u) : ℂ)))
          hCi (hEi.const_mul (k : ℂ))]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        dsimp only [a]
        push_cast
        simp only [smul_eq_mul]
        ring
      _ = _ := by
        dsimp only [F]
        rw [criticalAbelCorrelationContinuation_eq_right (s := (σ : ℂ)) hσ.le,
          laplace_exp_neg hσ, mul_one_div]
  have hFr : Tendsto (fun x : ℝ => (x + 1) * (F (x : ℂ)).re)
      (𝓝[>] (-1 : ℝ)) (𝓝 (-(criticalCorrelationNegativeResidue - k))) := by
    have h := criticalAbelCorrelationContinuation_left_residue.add_const k
    rw [show -criticalCorrelationNegativeResidue + k =
      -(criticalCorrelationNegativeResidue - k) by ring] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change -1 < x at hx
    dsimp only [F]
    rw [Complex.add_re, mul_add]
    have he : (k : ℂ) / ((x : ℂ) + 1) = ((k / (x + 1) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [he, Complex.ofReal_re]
    have hd : x + 1 ≠ 0 := by linarith
    have hcancel : (x + 1) * (k / (x + 1)) = k := by field_simp [hd]
    rw [hcancel]
  have hno := not_eventually_nonneg_of_continued_ray hac hai hFa hFt (sub_pos.mpr hk) hFr
  by_contra hn
  push Not at hn
  apply hno
  refine ⟨H, fun u hu => ?_⟩
  dsimp only [a]
  linarith [hn u hu]

end RHTower
