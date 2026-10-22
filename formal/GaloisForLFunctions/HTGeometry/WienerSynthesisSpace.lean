import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSynthesisField

/-!
# Differentiating the synthesis in space

A derivative of the synthesis in a spatial direction costs one factor `2πi⟪ξ,v⟫` under the integral,
and that factor is dominated by `2π‖v‖⟨ξ⟩`. So the same weight that pays for the time derivatives
pays for the space derivatives, and with two spare powers the synthesis of a weighted datum is twice
differentiable in every direction.

Unlike the time derivatives, the bound here is global: it does not depend on the point of space, so
the dominating function works on the whole line of the parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The character along a line -/

/-- The synthesis of a frequency density. -/
noncomputable def kgSynthesis (f : E → ℂ) (x : E) : ℂ := ∫ ξ, kgChar x ξ * f ξ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgChar_add_smul (x v ξ : E) (r : ℝ) :
    kgChar (x + r • v) ξ = ((𝐞 (⟪ξ, x⟫ + r * ⟪ξ, v⟫) : Circle) : ℂ) := by
  rw [kgChar, inner_add_right, real_inner_smul_right]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kgChar_eq_cexp (x ξ : E) :
    kgChar x ξ = Complex.exp (((2 * Real.pi * ⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) := by
  rw [kgChar, Real.fourierChar_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The character is differentiable along a line**, with the frequency appearing as a factor. -/
theorem hasDerivAt_kgChar_dir (x v ξ : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => kgChar (x + s • v) ξ)
      (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + r • v) ξ) r := by
  have hfun : (fun s : ℝ => kgChar (x + s • v) ξ)
      = fun s : ℝ =>
        Complex.exp (((2 * Real.pi * (⟪ξ, x⟫ + s * ⟪ξ, v⟫) : ℝ) : ℂ) * Complex.I) := by
    funext s
    rw [kgChar_eq_cexp, inner_add_right, real_inner_smul_right]
  have hlin : HasDerivAt
      (fun s : ℝ => ((2 * Real.pi * (⟪ξ, x⟫ + s * ⟪ξ, v⟫) : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * ⟪ξ, v⟫ : ℝ) : ℂ) * Complex.I) r := by
    have hre : HasDerivAt (fun s : ℝ => 2 * Real.pi * (⟪ξ, x⟫ + s * ⟪ξ, v⟫))
        (2 * Real.pi * ⟪ξ, v⟫) r := by
      have h := ((hasDerivAt_id r).mul_const (⟪ξ, v⟫ : ℝ)).const_add (⟪ξ, x⟫ : ℝ)
      have h2 := h.const_mul (2 * Real.pi)
      simpa using h2
    exact (hre.ofReal_comp).mul_const Complex.I
  have hexp := hlin.cexp
  rw [hfun]
  refine hexp.congr_deriv ?_
  have hval : kgChar (x + r • v) ξ
      = Complex.exp (((2 * Real.pi * (⟪ξ, x⟫ + r * ⟪ξ, v⟫) : ℝ) : ℂ) * Complex.I) := by
    rw [kgChar_eq_cexp, inner_add_right, real_inner_smul_right]
  rw [hval]
  push_cast
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_inner_le_kgFreq (v ξ : E) : |⟪ξ, v⟫| ≤ ‖v‖ * kgFreq ξ := by
  have h1 : |⟪ξ, v⟫| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
  have h2 : ‖ξ‖ ≤ kgFreq ξ := by
    rw [kgFreq]
    have hle : ‖ξ‖ ^ (2 : ℕ) ≤ 1 + ‖ξ‖ ^ (2 : ℕ) := by nlinarith
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg ξ)] at this
  nlinarith [norm_nonneg v, norm_nonneg ξ]

/-! ## The first derivative -/

/-- **The synthesis is differentiable in every spatial direction.** -/
theorem hasDerivAt_kgSynthesis_dir {f : E → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hint : Integrable f (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E)) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => kgSynthesis f (x + s • v))
      (∫ ξ, 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + r • v) ξ * f ξ) r := by
  have hmeasF : ∀ s : ℝ, AEStronglyMeasurable
      (fun ξ : E => kgChar (x + s • v) ξ * f ξ) (volume : Measure E) := fun s =>
    ((continuous_kgChar' (x + s • v)).aestronglyMeasurable).mul hmeas
  have hmeasF' : ∀ s : ℝ, AEStronglyMeasurable
      (fun ξ : E => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ)
      (volume : Measure E) := by
    intro s
    have hinner : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
    exact (((continuous_const.mul hinner).mul
      (continuous_kgChar' (x + s • v))).aestronglyMeasurable).mul hmeas
  have hbound : ∀ (s : ℝ) (ξ : E),
      ‖2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ‖
        ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖) := by
    intro s ξ
    have hchar := norm_kgChar (x + s • v) ξ
    have hpi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [norm_mul, norm_mul, norm_mul, hchar, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hpi' : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := hpi
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from rfl]
    rw [hpi']
    have hinner := norm_inner_le_kgFreq v ξ
    have hf : (0 : ℝ) ≤ ‖f ξ‖ := norm_nonneg _
    have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hstep : |(⟪ξ, v⟫ : ℝ)| * ‖f ξ‖ ≤ ‖v‖ * kgFreq ξ * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right hinner hf
    nlinarith [hstep, hpipos]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := r) (s := Set.univ)
    (F := fun s ξ => kgChar (x + s • v) ξ * f ξ)
    (F' := fun s ξ => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ)
    (bound := fun ξ => 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖)) Filter.univ_mem
    (Filter.Eventually.of_forall hmeasF)
    (hint.bdd_mul (c := 1) ((continuous_kgChar' (x + r • v)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => le_of_eq (norm_kgChar (x + r • v) ξ)))
    (hmeasF' r) ?_ (h1.const_mul _) ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro s _
    exact hbound s ξ
  · filter_upwards with ξ
    intro s _
    exact (hasDerivAt_kgChar_dir x v ξ s).mul_const (f ξ)

/-! ## The second derivative -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_two_pi_I_inner (v ξ : E) :
    ‖2 * (Real.pi : ℂ) * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)‖ = 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

/-- **The synthesis is twice differentiable in every spatial direction**, and the second derivative
brings down the square of the frequency. -/
theorem hasDerivAt_deriv_kgSynthesis_dir {f : E → ℂ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hint : Integrable f (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E)) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (fun q : ℝ => kgSynthesis f (x + q • v)) s)
      (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar (x + r • v) ξ * f ξ) r := by
  have hfun : (fun s : ℝ => deriv (fun q : ℝ => kgSynthesis f (x + q • v)) s)
      = fun s : ℝ =>
        ∫ ξ, 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ := by
    funext s
    exact (hasDerivAt_kgSynthesis_dir hmeas hint h1 x v s).deriv
  rw [hfun]
  have hinnerCont : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
  have hmeasF : ∀ s : ℝ, AEStronglyMeasurable
      (fun ξ : E => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ)
      (volume : Measure E) := fun s =>
    (((continuous_const.mul hinnerCont).mul
      (continuous_kgChar' (x + s • v))).aestronglyMeasurable).mul hmeas
  have hmeasF' : ∀ s : ℝ, AEStronglyMeasurable
      (fun ξ : E => (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ)
        * kgChar (x + s • v) ξ * f ξ) (volume : Measure E) := fun s =>
    ((((continuous_const.mul hinnerCont).pow 2).mul
      (continuous_kgChar' (x + s • v))).aestronglyMeasurable).mul hmeas
  have hb1 : ∀ (s : ℝ) (ξ : E),
      ‖2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ‖
        ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖) := by
    intro s ξ
    rw [norm_mul, norm_mul, norm_kgChar, mul_one, norm_two_pi_I_inner]
    have hinner := norm_inner_le_kgFreq v ξ
    have hf : (0 : ℝ) ≤ ‖f ξ‖ := norm_nonneg _
    have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hstep : |(⟪ξ, v⟫ : ℝ)| * ‖f ξ‖ ≤ ‖v‖ * kgFreq ξ * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right hinner hf
    nlinarith [hstep, hpipos]
  have hb2 : ∀ (s : ℝ) (ξ : E),
      ‖(2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar (x + s • v) ξ * f ξ‖
        ≤ (2 * Real.pi * ‖v‖) ^ (2 : ℕ) * (kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) := by
    intro s ξ
    rw [norm_mul, norm_mul, norm_kgChar, mul_one, norm_pow, norm_two_pi_I_inner]
    have hinner := norm_inner_le_kgFreq v ξ
    have hf : (0 : ℝ) ≤ ‖f ξ‖ := norm_nonneg _
    have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hsq : (2 * Real.pi * |(⟪ξ, v⟫ : ℝ)|) ^ (2 : ℕ) ≤ (2 * Real.pi * (‖v‖ * kgFreq ξ)) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| := by positivity
      have hmono : 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| ≤ 2 * Real.pi * (‖v‖ * kgFreq ξ) :=
        mul_le_mul_of_nonneg_left hinner hpipos.le
      exact pow_le_pow_left₀ hnn hmono 2
    nlinarith [hsq, hf]
  have hF_int : Integrable
      (fun ξ : E => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + r • v) ξ * f ξ)
      (volume : Measure E) := by
    refine Integrable.mono' (h1.const_mul (2 * Real.pi * ‖v‖)) (hmeasF r) ?_
    filter_upwards with ξ
    exact hb1 r ξ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := r) (s := Set.univ)
    (F := fun s ξ => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + s • v) ξ * f ξ)
    (F' := fun s ξ => (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ)
      * kgChar (x + s • v) ξ * f ξ)
    (bound := fun ξ => (2 * Real.pi * ‖v‖) ^ (2 : ℕ) * (kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖)) Filter.univ_mem
    (Filter.Eventually.of_forall hmeasF) hF_int (hmeasF' r) ?_ (h2.const_mul _) ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro s _
    exact hb2 s ξ
  · filter_upwards with ξ
    intro s _
    have hbase := ((hasDerivAt_kgChar_dir x v ξ s).const_mul
      (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ))).mul_const (f ξ)
    refine hbase.congr_deriv ?_
    ring

end GaloisForLFunctions.HTGeometry
