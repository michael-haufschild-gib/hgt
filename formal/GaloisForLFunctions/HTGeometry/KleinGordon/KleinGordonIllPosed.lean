import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPotentialUniqueness
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFreqInvNotSurjective
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimePotential

/-!
# The inverse problem is ill-posed

The field determines the perturbation, and depends on it Lipschitz-continuously. The remaining
question is whether the *inverse* correspondence is continuous — whether a small change in the
observed field forces a small change in the equation. It does not, and the obstruction is visible in
the symbol.

The half-order propagator `sin(τ⟨ξ⟩)/⟨ξ⟩` decays like `⟨ξ⟩⁻¹`. A perturbation that lives entirely
above frequency `R` therefore enters the Duhamel term damped by `⟨R⟩⁻¹`, however large its operator
norm. So the high-pass multiplier of height `c` has operator norm exactly `c` — it acts as
multiplication by `c` on any function with spectrum above `R` — while the field it produces differs
from the free field by `O(c/⟨R⟩)` uniformly over all Cauchy data on any fixed observation window.

Letting `R` grow gives, for every tolerance and every window, a perturbation of fixed size that is
invisible to that tolerance. The forward map is not bounded below, so its inverse admits no modulus
of continuity: the inverse problem is ill-posed in the classical sense, and the exponential factor in
the stability estimate is not an artefact of the proof.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The high-pass perturbation -/

/-- The symbol of the high-pass perturbation: the constant `c` above frequency `R`, zero below. -/
def kgHighPass (c R : ℝ) (ξ : E) : ℂ := if R ≤ ‖ξ‖ then (c : ℂ) else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgHighPass (c R : ℝ) : Measurable (kgHighPass (E := E) c R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgHighPass_le {c : ℝ} (hc0 : 0 ≤ c) (R : ℝ) (ξ : E) :
    ‖kgHighPass c R ξ‖ ≤ c := by
  rw [kgHighPass]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  · simpa using hc0

/-- **The high-pass perturbation**: multiplication by `c` on the frequencies above `R`. -/
def kgHighPassOp {c : ℝ} (hc0 : 0 ≤ c) (R : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgHighPass (E := E) c R) hc0 (norm_kgHighPass_le hc0 R)

theorem norm_kgHighPassOp_le {c : ℝ} (hc0 : 0 ≤ c) (R : ℝ) :
    ‖kgHighPassOp (E := E) hc0 R‖ ≤ c :=
  norm_fourierMulCLM_le _ _ _

/-- **The high-pass perturbation has the full norm of its height.** It acts as multiplication by `c`
on any function whose spectrum lies above `R`, and such functions exist once the space is
nontrivial. -/
theorem le_norm_kgHighPassOp (hd : 0 < Module.finrank ℝ E) {c : ℝ} (hc0 : 0 ≤ c) (R : ℝ) :
    c ≤ ‖kgHighPassOp (E := E) hc0 R‖ := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_norm_eq (E := E) hd (by positivity : (0 : ℝ) ≤ |R| + 1)
  have hfar : ∀ ξ ∈ ball ξ₀ (1 : ℝ), R ≤ ‖ξ‖ := by
    intro ξ hξ
    have hd1 : ‖ξ₀ - ξ‖ < 1 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using hξ
    have hsub := norm_sub_norm_le ξ₀ ξ
    rw [hξ₀] at hsub
    have habs : R ≤ |R| := le_abs_self R
    linarith
  set g := kgBallFun ξ₀ (1 : ℝ) with hg
  set f := fourierL2inv E g with hf
  have hgf : fourierL2 E f = g := by rw [hf, fourierL2_fourierL2inv]
  have hnf : ‖f‖ = ‖g‖ := by rw [hf, norm_fourierL2inv_apply]
  have hgpos : 0 < ‖g‖ := by
    rw [norm_pos_iff, hg]
    exact kgBallFun_ne_zero ξ₀ one_pos
  have hmul : lpBoundedMulCLM (p := 2) (μ := (volume : Measure E))
      (measurable_kgHighPass (E := E) c R) hc0 (norm_kgHighPass_le hc0 R) g = (c : ℂ) • g := by
    refine Lp.ext ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure E))
      (measurable_kgHighPass (E := E) c R) hc0 (norm_kgHighPass_le hc0 R) g,
      kgBallFun_coeFn ξ₀ (1 : ℝ), Lp.coeFn_smul (c : ℂ) g] with ξ h1 h2 h3
    rw [h1, h3, Pi.smul_apply, smul_eq_mul]
    by_cases hmem : ξ ∈ ball ξ₀ (1 : ℝ)
    · rw [kgHighPass, if_pos (hfar ξ hmem)]
    · have hzero : (g : E → ℂ) ξ = 0 := by
        rw [hg, h2, Set.indicator_of_notMem hmem]
      rw [hzero, mul_zero, mul_zero]
  have hval : ‖kgHighPassOp (E := E) hc0 R f‖ = c * ‖f‖ := by
    rw [kgHighPassOp, fourierMulCLM_apply, hgf, hmul, norm_fourierL2inv_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0, hnf]
  have hle := (kgHighPassOp (E := E) hc0 R).le_opNorm f
  rw [hval] at hle
  have hfpos : 0 < ‖f‖ := by rw [hnf]; exact hgpos
  exact le_of_mul_le_mul_right (by linarith) hfpos

theorem norm_kgHighPassOp (hd : 0 < Module.finrank ℝ E) {c : ℝ} (hc0 : 0 ≤ c) (R : ℝ) :
    ‖kgHighPassOp (E := E) hc0 R‖ = c :=
  le_antisymm (norm_kgHighPassOp_le hc0 R) (le_norm_kgHighPassOp hd hc0 R)

/-! ## The perturbation is damped by the propagator -/

/-- **A perturbation living above frequency `R` enters the Duhamel term damped by `⟨R⟩⁻¹`.** -/
theorem norm_kgSinFreqOp_comp_kgHighPassOp {c : ℝ} (hc0 : 0 ≤ c) {R : ℝ} (hR : 0 ≤ R) (τ : ℝ) :
    ‖(kgSinFreqOp (E := E) τ).comp (kgHighPassOp hc0 R)‖ ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) := by
  have hSpos : 0 < Real.sqrt (1 + R ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by nlinarith)
  have hB0 : (0 : ℝ) ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) := by positivity
  have hmeas : Measurable fun ξ : E => kgSinOverFreq τ ξ * kgHighPass c R ξ :=
    (measurable_kgSinOverFreq τ).mul (measurable_kgHighPass c R)
  have hbound : ∀ ξ : E, ‖kgSinOverFreq τ ξ * kgHighPass c R ξ‖ ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) := by
    intro ξ
    rw [norm_mul, kgHighPass]
    by_cases hmem : R ≤ ‖ξ‖
    · rw [if_pos hmem, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
      have hsin : ‖kgSinOverFreq τ ξ‖ ≤ (kgFreq ξ)⁻¹ := by
        have hpos := kgFreq_pos ξ
        rw [kgSinOverFreq, Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_pos hpos, div_le_iff₀ hpos, inv_mul_cancel₀ hpos.ne']
        exact Real.abs_sin_le_one _
      have hfr : Real.sqrt (1 + R ^ (2 : ℕ)) ≤ kgFreq ξ := by
        rw [kgFreq]
        refine Real.sqrt_le_sqrt ?_
        nlinarith [norm_nonneg ξ]
      have hinv : (kgFreq ξ)⁻¹ ≤ (Real.sqrt (1 + R ^ (2 : ℕ)))⁻¹ := by
        gcongr
      calc ‖kgSinOverFreq τ ξ‖ * c ≤ (kgFreq ξ)⁻¹ * c :=
            mul_le_mul_of_nonneg_right hsin hc0
        _ ≤ (Real.sqrt (1 + R ^ (2 : ℕ)))⁻¹ * c := mul_le_mul_of_nonneg_right hinv hc0
        _ = c / Real.sqrt (1 + R ^ (2 : ℕ)) := by
            rw [inv_mul_eq_div, div_eq_div_iff hSpos.ne' hSpos.ne']
    · rw [if_neg hmem]
      simpa using hB0
  rw [kgSinFreqOp_eq, kgHighPassOp,
    fourierMulCLM_comp _ _ hmeas _ _ _ _ hB0 hbound (Filter.Eventually.of_forall fun _ => rfl)]
  exact norm_fourierMulCLM_le _ _ _

/-- **The field of a high-pass perturbation is close to the free field**, uniformly over all Cauchy
data. -/
theorem norm_kgFieldMild_kgHighPassOp_sub_free_le {c : ℝ} (hc0 : 0 ≤ c) {R : ℝ} (hR : 0 ≤ R)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild (kgHighPassOp hc0 R) f h t - kgFieldFree f h t‖
      ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) * (|t| * ((‖f‖ + ‖h‖) * Real.exp (c * |t|))) := by
  have hSpos : 0 < Real.sqrt (1 + R ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by nlinarith)
  have hB0 : (0 : ℝ) ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) := by positivity
  set W := kgHighPassOp (E := E) hc0 R with hW
  have hWb : ‖W‖ ≤ c := norm_kgHighPassOp_le hc0 R
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖kgFieldKernel W t s (kgFieldMild W f h s)‖
        ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) * ((‖f‖ + ‖h‖) * Real.exp (c * |t|)) := by
    intro s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖kgFieldKernel W t s (kgFieldMild W f h s)‖
        ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) * ‖kgFieldMild W f h s‖ := by
      have hcomp : kgFieldKernel W t s (kgFieldMild W f h s)
          = ((kgSinFreqOp (E := E) (t - s)).comp W) (kgFieldMild W f h s) :=
        kgFieldKernel_apply W t s _
      rw [hcomp]
      exact ((kgSinFreqOp (E := E) (t - s)).comp W).le_of_opNorm_le
        (norm_kgSinFreqOp_comp_kgHighPassOp hc0 hR (t - s)) _
    have h2 : ‖kgFieldMild W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (c * |s|) :=
      norm_kgFieldMild_le hc0 hWb f h s
    have h3 : Real.exp (c * |s|) ≤ Real.exp (c * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hc0)
    have h4 : ‖kgFieldMild W f h s‖ ≤ (‖f‖ + ‖h‖) * Real.exp (c * |t|) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 hD0)
    exact h1.trans (mul_le_mul_of_nonneg_left h4 hB0)
  have hEq := kgFieldMild_eq hc0 hWb f h t
  have hsub : kgFieldMild W f h t - kgFieldFree f h t
      = ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (kgFieldMild W f h s) := by
    rw [hEq]
    abel
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  simpa [mul_comm, mul_left_comm, mul_assoc] using hle

/-! ## Ill-posedness -/

/-- **The forward map is not bounded below.** For every tolerance `ε` and every observation window
`[-T, T]` there is a perturbation of norm exactly `c` whose field is `ε`-indistinguishable from the
free field, uniformly over all Cauchy data. -/
theorem exists_norm_eq_and_kgFieldMild_close (hd : 0 < Module.finrank ℝ E) {c : ℝ} (hc : 0 < c)
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    ∃ W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ‖W‖ = c ∧
      ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        ‖kgFieldMild W f h t - kgFieldMild 0 f h t‖ ≤ ε * (‖f‖ + ‖h‖) := by
  have hc0 : (0 : ℝ) ≤ c := hc.le
  set R : ℝ := c * T * Real.exp (c * T) / ε with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hSpos : 0 < Real.sqrt (1 + R ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by nlinarith)
  have hRlt : R < Real.sqrt (1 + R ^ (2 : ℕ)) := by
    have h1 : R ^ (2 : ℕ) < 1 + R ^ (2 : ℕ) := by linarith
    have h2 : Real.sqrt (R ^ (2 : ℕ)) < Real.sqrt (1 + R ^ (2 : ℕ)) := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq hR0] at h2
  have hkey : c * T * Real.exp (c * T) / Real.sqrt (1 + R ^ (2 : ℕ)) ≤ ε := by
    rw [div_le_iff₀ hSpos]
    have hmul : c * T * Real.exp (c * T) = ε * R := by
      rw [hRdef]
      field_simp
    rw [hmul]
    exact mul_le_mul_of_nonneg_left hRlt.le hε.le
  refine ⟨kgHighPassOp (E := E) hc0 R, norm_kgHighPassOp hd hc0 R, fun f h t htT => ?_⟩
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  have hfree : kgFieldMild (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
      f h t = kgFieldFree f h t := kgFieldMild_zero_op f h t
  rw [hfree]
  refine (norm_kgFieldMild_kgHighPassOp_sub_free_le hc0 hR0 f h t).trans ?_
  have hexp : Real.exp (c * |t|) ≤ Real.exp (c * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hc0)
  have hstep : |t| * ((‖f‖ + ‖h‖) * Real.exp (c * |t|))
      ≤ T * ((‖f‖ + ‖h‖) * Real.exp (c * T)) := by
    have h1 : (‖f‖ + ‖h‖) * Real.exp (c * |t|) ≤ (‖f‖ + ‖h‖) * Real.exp (c * T) :=
      mul_le_mul_of_nonneg_left hexp hD0
    have h2 : (0 : ℝ) ≤ (‖f‖ + ‖h‖) * Real.exp (c * T) := by positivity
    exact mul_le_mul htT h1 (by positivity) (by linarith [abs_nonneg t])
  have hB0 : (0 : ℝ) ≤ c / Real.sqrt (1 + R ^ (2 : ℕ)) := by positivity
  refine (mul_le_mul_of_nonneg_left hstep hB0).trans ?_
  have hfac : c / Real.sqrt (1 + R ^ (2 : ℕ)) * (T * ((‖f‖ + ‖h‖) * Real.exp (c * T)))
      = (c * T * Real.exp (c * T) / Real.sqrt (1 + R ^ (2 : ℕ))) * (‖f‖ + ‖h‖) := by
    field_simp
  rw [hfac]
  exact mul_le_mul_of_nonneg_right hkey hD0

/-- **The inverse problem is ill-posed.** For every factor `κ` and every observation window there are
two admissible perturbations whose fields are `κ` times closer than the perturbations themselves,
uniformly over all Cauchy data. So the inverse of the forward map admits no modulus of continuity,
and the exponential factor in the stability estimate cannot be removed by any argument that would
also make the inverse continuous. -/
theorem exists_potentials_field_closer_than (hd : 0 < Module.finrank ℝ E) {c : ℝ} (hc : 0 < c)
    {T : ℝ} (hT : 0 ≤ T) {κ : ℝ} (hκ : 0 < κ) :
    ∃ W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ‖W₁‖ ≤ c ∧ ‖W₂‖ ≤ c ∧ ‖W₁ - W₂‖ = c ∧
      ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        κ * ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖ ≤ ‖W₁ - W₂‖ * (‖f‖ + ‖h‖) := by
  obtain ⟨W, hWnorm, hWclose⟩ :=
    exists_norm_eq_and_kgFieldMild_close hd hc (by positivity : (0 : ℝ) < c / κ) hT
  refine ⟨W, 0, le_of_eq hWnorm, by simpa using hc.le, by simpa using hWnorm, ?_⟩
  intro f h t htT
  have hbd := hWclose f h t htT
  have hD0 : (0 : ℝ) ≤ ‖f‖ + ‖h‖ := by positivity
  rw [sub_zero, hWnorm]
  have hstep : κ * ‖kgFieldMild W f h t - kgFieldMild 0 f h t‖
      ≤ κ * (c / κ * (‖f‖ + ‖h‖)) := mul_le_mul_of_nonneg_left hbd hκ.le
  refine hstep.trans ?_
  rw [le_iff_eq_or_lt]
  left
  field_simp

/-- **Ill-posedness for moving backgrounds.** A constant family is a moving background, so the same
witness shows the non-autonomous forward map is not bounded below either. -/
theorem exists_norm_eq_and_kgFieldMildT_close (hd : 0 < Module.finrank ℝ E) {c : ℝ} (hc : 0 < c)
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    ∃ W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)),
      (∀ r : ℝ, ‖W r‖ = c) ∧
      (∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) ∧
      ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        ‖kgFieldMildT W f h t
            - kgFieldMildT (fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ]
              Lp ℂ 2 (volume : Measure E))) f h t‖ ≤ ε * (‖f‖ + ‖h‖) := by
  obtain ⟨W₀, hnorm, hclose⟩ := exists_norm_eq_and_kgFieldMild_close hd hc hε hT
  exact ⟨fun _ => W₀, fun _ => hnorm, fun _ => continuous_const, hclose⟩

end GaloisForLFunctions.HTGeometry
