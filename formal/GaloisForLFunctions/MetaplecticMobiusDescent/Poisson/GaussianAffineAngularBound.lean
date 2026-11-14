import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AnnularAngularSchwartz

/-!
# Uniform angular cancellation on translated Gaussian lattices

Complex affine Poisson summation isolates the zero Fourier mode with its exact
covolume factor. The remaining modes are controlled by four physical derivatives,
uniformly in the complex dilation and translation. Annular angular kernels in
nontrivial quarter-turn sectors have no zero mode, so their full physical lattice
sums satisfy this uniform bound.
-/

noncomputable section
open Complex MeasureTheory
open scoped Classical SchwartzMap FourierTransform RealInnerProductSpace

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
open CubicEisenstein.SchwartzPlanePoisson

/-- Gaussian integers identified with their two integral coordinates. -/
def gaussianPairEquiv : GaussianInt ≃ ℤ × ℤ where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

private theorem gaussianPoint_coordinates (z : GaussianInt) :
    complexPoint (z.re : ℝ) (z.im : ℝ) = (z : ℂ) :=
  (GaussianInt.toComplex_def₂ z).symm

/-- Complex Gaussian lattice sums agree exactly with sums over integer coordinates. -/
theorem gaussian_tsum_eq_pair (F : ℂ → ℂ) :
    (∑' z : GaussianInt, F (z : ℂ)) =
      ∑' p : ℤ × ℤ, F (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  have h := gaussianPairEquiv.tsum_eq
    (fun p : ℤ × ℤ => F (complexPoint (p.1 : ℝ) (p.2 : ℝ)))
  change (∑' z : GaussianInt, F (complexPoint (z.re : ℝ) (z.im : ℝ))) = _ at h
  simpa only [gaussianPoint_coordinates] using h

private theorem gaussian_summable_of_pair (F : ℂ → ℂ)
    (h : Summable (fun p : ℤ × ℤ => F (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) :
    Summable (fun z : GaussianInt => F (z : ℂ)) := by
  have hg := (gaussianPairEquiv.summable_iff
    (f := fun p : ℤ × ℤ => F (complexPoint (p.1 : ℝ) (p.2 : ℝ)))).mpr h
  change Summable (fun z : GaussianInt => F (complexPoint (z.re : ℝ) (z.im : ℝ))) at hg
  simpa only [gaussianPoint_coordinates] using hg

/-- A quarter turn is a permutation of the entire Gaussian lattice. -/
def gaussianQuarterTurn : GaussianInt ≃ GaussianInt where
  toFun z := ⟨-z.im, z.re⟩
  invFun z := ⟨z.im, -z.re⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

/-- Integral quarter turns agree with complex multiplication by `i`. -/
theorem gaussianQuarterTurn_complex (z : GaussianInt) :
    (gaussianQuarterTurn z : ℂ) = I * (z : ℂ) := by
  change ((⟨-z.im, z.re⟩ : GaussianInt) : ℂ) = _
  simp only [GaussianInt.toComplex_def, Int.cast_neg]
  calc
    -(z.im : ℂ) + (z.re : ℂ) * I =
        I * (z.re : ℂ) + (z.im : ℂ) * I ^ 2 := by rw [I_sq]; ring
    _ = _ := by ring

/-- The physical Schwartz sum on an arbitrary translated square lattice. -/
def gaussianAffineSum (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) : ℂ :=
  ∑' z : GaussianInt, f ((c : ℂ) * (z : ℂ) + b)

/-- Every affine Gaussian Schwartz series converges. -/
theorem summable_gaussianAffine (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    Summable (fun z : GaussianInt => f ((c : ℂ) * (z : ℂ) + b)) := by
  apply gaussian_summable_of_pair (fun w => f ((c : ℂ) * w + b))
  simpa only [affinePullback_apply, complexMulEquiv_apply] using
    plane_lattice_summable (affinePullback f (complexMulEquiv (c : ℂ) c.ne_zero) b)

/-- Rotating the translation multiplies an angular lattice sum by its angular character. -/
theorem gaussian_affine_annular_quarter_turn (k : ℕ) (W : 𝓢(ℝ, ℂ)) (c : ℂˣ) (b : ℂ) :
    gaussianAffineSum (annularAngularCLM k W) c (I * b) =
      I ^ k * gaussianAffineSum (annularAngularCLM k W) c b := by
  have h := gaussianQuarterTurn.tsum_eq
    (fun z : GaussianInt => annularAngularCLM k W ((c : ℂ) * (z : ℂ) + I * b))
  have hterm (z : GaussianInt) :
      annularAngularCLM k W ((c : ℂ) * (gaussianQuarterTurn z : ℂ) + I * b) =
        I ^ k * annularAngularCLM k W ((c : ℂ) * (z : ℂ) + b) := by
    rw [gaussianQuarterTurn_complex,
      show (c : ℂ) * (I * (z : ℂ)) + I * b = I * ((c : ℂ) * (z : ℂ) + b) by ring]
    simp only [annularAngularCLM_apply, angularRadial_quarter_turn]
  simp_rw [hterm] at h
  rw [tsum_mul_left] at h
  exact h.symm

private theorem nontrivialQuarterTurn (n : ℕ) (j : Fin 3) :
    I ^ (4 * n + (j.val + 1)) ≠ 1 := by
  have h4 : I ^ (4 * n) = 1 := by
    rw [pow_mul, show I ^ 4 = 1 by
      norm_num [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq], one_pow]
  rw [pow_add, h4, one_mul]
  fin_cases j <;> intro h
  · have hi := congrArg Complex.im h
    norm_num at hi
  · have hr := congrArg Complex.re h
    norm_num [I_sq] at hr
  · have hi := congrArg Complex.im h
    norm_num [pow_succ, I_sq] at hi

/-- On a centered Gaussian lattice the full angular sum is zero in every
nontrivial quarter-turn sector, before any Poisson estimate is needed. -/
theorem gaussian_centered_annular_sum_zero (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ)) (c : ℂˣ) :
    gaussianAffineSum (annularAngularCLM (4 * n + (j.val + 1)) W) c 0 = 0 := by
  have h := gaussian_affine_annular_quarter_turn (4 * n + (j.val + 1)) W c 0
  rw [mul_zero] at h
  have hz : (I ^ (4 * n + (j.val + 1)) - 1) *
      gaussianAffineSum (annularAngularCLM (4 * n + (j.val + 1)) W) c 0 = 0 := by
    linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left (by
    intro he
    exact nontrivialQuarterTurn n j (sub_eq_zero.mp he))

private def inverseNormScale (c : ℂˣ) : PositiveScale :=
  ⟨‖(c : ℂ)‖⁻¹, inv_pos.mpr (norm_pos_iff.mpr c.ne_zero)⟩

private theorem inverseJacobian_mul_unit (c : ℂˣ) :
    inverseJacobian (complexMulEquiv (c : ℂ) c.ne_zero) = (inverseNormScale c).val ^ 2 := by
  rw [inverseJacobian, complexMulEquiv_det, abs_inv,
    abs_of_nonneg (Complex.normSq_nonneg (c : ℂ))]
  simp only [inverseNormScale, inv_pow, Complex.sq_norm]

/-- The reciprocal conjugate dilation gives the dual Gaussian lattice. -/
def gaussianDualPoint (c : ℂˣ) (z : GaussianInt) : ℂ :=
  (starRingEnd ℂ (c : ℂ))⁻¹ * (z : ℂ)

private theorem norm_gaussianDualPoint (c : ℂˣ) (z : GaussianInt) :
    ‖gaussianDualPoint c z‖ = (inverseNormScale c).val * ‖(z : ℂ)‖ := by
  simp only [gaussianDualPoint, norm_mul, norm_inv, Complex.norm_conj, inverseNormScale]

/-- A translated dual Fourier sample, including its unit-modulus phase. -/
def gaussianDualTerm (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) (z : GaussianInt) : ℂ :=
  (Real.fourierChar (inner ℝ b (gaussianDualPoint c z)) : ℂ) * (𝓕 f) (gaussianDualPoint c z)

private theorem norm_gaussianDualTerm (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) (z : GaussianInt) :
    ‖gaussianDualTerm f c b z‖ = ‖(𝓕 f) (gaussianDualPoint c z)‖ := by
  simp only [gaussianDualTerm, norm_mul, Circle.norm_coe, one_mul]

/-- Poisson summation on the actual Gaussian lattice, with the exact covolume and dual phase. -/
theorem gaussian_affine_poisson (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    gaussianAffineSum f c b = (‖(c : ℂ)‖⁻¹ ^ 2 : ℝ) •
      ∑' z : GaussianInt, gaussianDualTerm f c b z := by
  have h := affine_lattice_poisson f (complexMulEquiv (c : ℂ) c.ne_zero) b
  rw [inverseJacobian_mul_unit] at h
  simp only [complexMulEquiv_apply, dual_mul_apply, Circle.smul_def, smul_eq_mul] at h
  have hl := gaussian_tsum_eq_pair (fun w => f ((c : ℂ) * w + b))
  have hr := gaussian_tsum_eq_pair (fun w =>
    (Real.fourierChar (inner ℝ b ((starRingEnd ℂ (c : ℂ))⁻¹ * w)) : ℂ) *
      (𝓕 f) ((starRingEnd ℂ (c : ℂ))⁻¹ * w))
  change gaussianAffineSum f c b = _ at hl
  change (∑' z : GaussianInt, gaussianDualTerm f c b z) = _ at hr
  exact hl.trans (h.trans (congrArg (fun u : ℂ => (‖(c : ℂ)‖⁻¹ ^ 2 : ℝ) • u) hr.symm))

/-- The dual Fourier sample with its zero mode removed. -/
def gaussianDualTail (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) (z : GaussianInt) : ℂ :=
  if z = 0 then 0 else gaussianDualTerm f c b z

private theorem norm_gaussianDualTail_le (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) (z : GaussianInt) :
    ‖gaussianDualTail f c b z‖ ≤
      136 * derivativeMass 4 f * gaussianTail (inverseNormScale c) z := by
  by_cases hz : z = 0
  · simp [gaussianDualTail, gaussianTail, hz]
  · rw [gaussianDualTail, if_neg hz, norm_gaussianDualTerm, gaussianTail, if_neg hz]
    have h := one_add_fourier_fourth_le f (gaussianDualPoint c z)
    rw [norm_gaussianDualPoint] at h
    have hd : 0 < (1 + (inverseNormScale c).val * ‖(z : ℂ)‖) ^ 4 := by
      have hs : 0 < (inverseNormScale c).val := (inverseNormScale c).property
      positivity
    rw [mul_one_div, le_div_iff₀ hd]
    simpa only [mul_comm] using h

private theorem summable_norm_gaussianDualTail (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    Summable (fun z : GaussianInt => ‖gaussianDualTail f c b z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_gaussianDualTail_le f c b)
    ((summable_gaussianTail (inverseNormScale c)).mul_left (136 * derivativeMass 4 f))

private theorem summable_gaussianDualTail (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    Summable (gaussianDualTail f c b) :=
  Summable.of_norm (f := gaussianDualTail f c b) (summable_norm_gaussianDualTail f c b)

private theorem gaussianDualTerm_eq (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    gaussianDualTerm f c b = fun z =>
      (if z = 0 then (𝓕 f) 0 else 0) + gaussianDualTail f c b z := by
  funext z
  by_cases hz : z = 0 <;> simp [gaussianDualTail, gaussianDualTerm, gaussianDualPoint, hz]

/-- Absolute convergence of the complete dual series is established before splitting its zero mode. -/
theorem summable_gaussianDualTerm (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    Summable (gaussianDualTerm f c b) := by
  have hd : Summable (fun z : GaussianInt =>
      if z = 0 then (𝓕 f : 𝓢(ℂ, ℂ)) 0 else (0 : ℂ)) :=
    (hasSum_ite_eq (0 : GaussianInt) ((𝓕 f : 𝓢(ℂ, ℂ)) 0)).summable
  rw [gaussianDualTerm_eq]
  exact hd.add (summable_gaussianDualTail f c b)

private theorem gaussianDualSum_eq (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    (∑' z : GaussianInt, gaussianDualTerm f c b z) =
      (𝓕 f) 0 + ∑' z : GaussianInt, gaussianDualTail f c b z := by
  have hd := hasSum_ite_eq (0 : GaussianInt) ((𝓕 f : 𝓢(ℂ, ℂ)) 0)
  rw [gaussianDualTerm_eq, hd.summable.tsum_add (summable_gaussianDualTail f c b),
    hd.tsum_eq]

private theorem scaled_gaussianDualTail_mass_le (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    (inverseNormScale c).val ^ 2 * (∑' z : GaussianInt, ‖gaussianDualTail f c b z‖) ≤
      1632 * derivativeMass 4 f := by
  have hm := (summable_gaussianTail (inverseNormScale c)).mul_left (136 * derivativeMass 4 f)
  have hsum := Summable.tsum_le_tsum (norm_gaussianDualTail_le f c b)
    (summable_norm_gaussianDualTail f c b) hm
  rw [tsum_mul_left] at hsum
  have hC : 0 ≤ 136 * derivativeMass 4 f := mul_nonneg (by norm_num) (derivativeMass_nonneg 4 f)
  calc
    _ ≤ (inverseNormScale c).val ^ 2 *
        (136 * derivativeMass 4 f * ∑' z : GaussianInt, gaussianTail (inverseNormScale c) z) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (136 * derivativeMass 4 f) * ((inverseNormScale c).val ^ 2 *
        ∑' z : GaussianInt, gaussianTail (inverseNormScale c) z) := by ring
    _ ≤ (136 * derivativeMass 4 f) * 12 :=
      mul_le_mul_of_nonneg_left (scaled_gaussianTail_le (inverseNormScale c)) hC
    _ = _ := by ring

/-- After its exact mean term is removed, every translated Gaussian sum is bounded
independently of both complex dilation and translation. -/
theorem gaussian_affine_sum_sub_mean_le (f : 𝓢(ℂ, ℂ)) (c : ℂˣ) (b : ℂ) :
    ‖gaussianAffineSum f c b - (‖(c : ℂ)‖⁻¹ ^ 2 : ℝ) • (𝓕 f) 0‖ ≤
      1632 * derivativeMass 4 f := by
  rw [gaussian_affine_poisson, gaussianDualSum_eq, smul_add, add_sub_cancel_left,
    norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left
    (norm_tsum_le_tsum_norm (summable_norm_gaussianDualTail f c b)) (sq_nonneg _)).trans
      (scaled_gaussianDualTail_mass_le f c b)

/-- Nontrivial angular sectors have uniformly bounded physical lattice sums at all
scales, rotations, and translations, because their zero Fourier mode vanishes. -/
theorem gaussian_affine_annular_sum_le (n : ℕ) (j : Fin 3) (W : 𝓢(ℝ, ℂ))
    (c : ℂˣ) (b : ℂ) :
    ‖gaussianAffineSum (annularAngularCLM (4 * n + (j.val + 1)) W) c b‖ ≤
      1632 * derivativeMass 4 (annularAngularCLM (4 * n + (j.val + 1)) W) := by
  have hz := annularFourier_zero n j W
  change (𝓕 (annularAngularCLM (4 * n + (j.val + 1)) W)) 0 = 0 at hz
  have h := gaussian_affine_sum_sub_mean_le (annularAngularCLM (4 * n + (j.val + 1)) W) c b
  simpa only [hz, smul_zero, sub_zero] using h

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
