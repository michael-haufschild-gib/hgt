import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodKernel

/-!
# Reciprocal and pairwise likelihood moments

On the spectral interval the reciprocal prime likelihood is affine in
`x²`. Hence every ratio of two prime likelihoods is affine in the first
likelihood. The covariance resolvent then gives exact first and second
moments of all directed likelihood ratios.
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Reciprocal likelihoods are continuous because the clamped weights stay positive. -/
theorem continuous_kestenLikelihood_inv (p : Nat.Primes) :
    Continuous (fun x => (kestenLikelihood p x)⁻¹) :=
  (continuous_kestenLikelihood p).inv₀ (fun x => (kestenLikelihood_pos p x).ne')

/-- Every pairwise likelihood ratio is continuous. -/
theorem continuous_kestenLikelihood_ratio (p q : Nat.Primes) :
    Continuous (fun x => kestenLikelihood p x / kestenLikelihood q x) :=
  (continuous_kestenLikelihood p).div (continuous_kestenLikelihood q)
    (fun x => (kestenLikelihood_pos q x).ne')

/-- On the spectral interval the reciprocal likelihood is affine in the squared coordinate. -/
theorem kestenLikelihood_inv_on_interval (p : Nat.Primes) (x : Icc (-2 : ℝ) 2) :
    (kestenLikelihood p x)⁻¹ = ((p : ℝ) + 1) / (p : ℝ) - (x : ℝ) ^ 2 / ((p : ℝ) + 1) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  have hp2 : (p : ℝ) + 1 ≠ 0 := by positivity
  unfold kestenLikelihood
  rw [kestenBetaWeight_on_unit p ⟨_, heckeSquareCoordinate_mem x⟩]
  unfold kestenEdgeScale kestenEdgeSlope heckeSquareCoordinate
  field_simp [hp0, hp1, hp2]
  ring

/-- The semicircle expectation of the reciprocal likelihood is explicit. -/
theorem integral_semicircleLikelihood_inv (p : Nat.Primes) :
    (∫ x, (kestenLikelihood p x)⁻¹ ∂(semicircleSpectralLaw : Measure ℝ)) =
      1 + ((p : ℝ) * ((p : ℝ) + 1))⁻¹ := by
  have ha : ∀ᵐ x ∂(semicircleSpectralLaw : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact semicircleSpectralLaw_carried
  have he : (fun x => (kestenLikelihood p x)⁻¹) =ᵐ[(semicircleSpectralLaw : Measure ℝ)]
      (fun x => ((p : ℝ) + 1) / (p : ℝ) - x ^ 2 / ((p : ℝ) + 1)) := by
    filter_upwards [ha] with x hx
    exact kestenLikelihood_inv_on_interval p ⟨x, hx⟩
  have hm : (∫ x : ℝ, x ^ 2 ∂(semicircleSpectralLaw : Measure ℝ)) = 1 := by
    rw [(semicircleSpectralLaw_hasMoments 2).2,
      show semicircleMoment 2 = (catalan 1 : ℝ) from semicircleMoment_even 1]
    norm_num
  rw [integral_congr_ae he,
    integral_sub (integrable_const _) ((semicircleSpectralLaw_hasMoments 2).1.div_const _)]
  simp only [integral_div, hm, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hp0, hp1]
  ring

/-- Under its own prime law the reciprocal likelihood has mean one. -/
theorem integral_kestenLikelihood_inv (p : Nat.Primes) :
    (∫ x, (kestenLikelihood p x)⁻¹ ∂(kestenSpectralLaw p : Measure ℝ)) = 1 := by
  have h := integral_semicircleLikelihood_mul p ⟨_, continuous_kestenLikelihood_inv p⟩
  change (∫ x, kestenLikelihood p x * (kestenLikelihood p x)⁻¹
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, (kestenLikelihood p x)⁻¹ ∂(kestenSpectralLaw p : Measure ℝ) at h
  rw [← h]
  have he (x : ℝ) : kestenLikelihood p x * (kestenLikelihood p x)⁻¹ = 1 :=
    mul_inv_cancel₀ (kestenLikelihood_pos p x).ne'
  simp only [he, integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- The second reciprocal-likelihood moment is the semicircle reciprocal mean. -/
theorem integral_kestenLikelihood_inv_sq (p : Nat.Primes) :
    (∫ x, ((kestenLikelihood p x)⁻¹) ^ 2 ∂(kestenSpectralLaw p : Measure ℝ)) =
      1 + ((p : ℝ) * ((p : ℝ) + 1))⁻¹ := by
  have h := integral_semicircleLikelihood_mul p ⟨_, (continuous_kestenLikelihood_inv p).pow 2⟩
  change (∫ x, kestenLikelihood p x * ((kestenLikelihood p x)⁻¹) ^ 2
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, ((kestenLikelihood p x)⁻¹) ^ 2 ∂(kestenSpectralLaw p : Measure ℝ) at h
  rw [← h]
  have he (x : ℝ) : kestenLikelihood p x * ((kestenLikelihood p x)⁻¹) ^ 2 =
      (kestenLikelihood p x)⁻¹ := by
    field_simp [(kestenLikelihood_pos p x).ne']
  simp only [he]
  exact integral_semicircleLikelihood_inv p

/-- A ratio of two prime likelihoods is affine in the first likelihood on the spectral interval. -/
theorem kestenLikelihood_ratio_on_interval (p q : Nat.Primes) (x : Icc (-2 : ℝ) 2) :
    kestenLikelihood p x / kestenLikelihood q x =
      (((q : ℝ) - (p : ℝ)) * ((p : ℝ) * (q : ℝ) - 1) /
        ((p : ℝ) * (q : ℝ) * ((q : ℝ) + 1))) * kestenLikelihood p x +
          ((p : ℝ) + 1) / ((q : ℝ) + 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have he : (kestenLikelihood q x)⁻¹ =
      (((q : ℝ) - (p : ℝ)) * ((p : ℝ) * (q : ℝ) - 1) /
        ((p : ℝ) * (q : ℝ) * ((q : ℝ) + 1))) +
          (((p : ℝ) + 1) / ((q : ℝ) + 1)) * (kestenLikelihood p x)⁻¹ := by
    rw [kestenLikelihood_inv_on_interval, kestenLikelihood_inv_on_interval]
    field_simp [hp0, hq0, hp1, hq1]
    ring
  rw [div_eq_mul_inv, he, mul_add]
  have hc := mul_inv_cancel₀ (kestenLikelihood_pos p x).ne'
  linear_combination (((p : ℝ) + 1) / ((q : ℝ) + 1)) * hc

/-- The self-law expectation of a pairwise likelihood ratio is one plus an explicit positive square. -/
theorem integral_kestenLikelihood_ratio_self (p q : Nat.Primes) :
    (∫ x, kestenLikelihood p x / kestenLikelihood q x ∂(kestenSpectralLaw p : Measure ℝ)) =
      1 + ((p : ℝ) - (q : ℝ)) ^ 2 /
        ((q : ℝ) * ((q : ℝ) + 1) * ((p : ℝ) ^ 2 - 1)) := by
  have ha : ∀ᵐ x ∂(kestenSpectralLaw p : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact kestenSpectralLaw_carried p
  have he : (fun x => kestenLikelihood p x / kestenLikelihood q x) =ᵐ[
      (kestenSpectralLaw p : Measure ℝ)] (fun x =>
      (((q : ℝ) - (p : ℝ)) * ((p : ℝ) * (q : ℝ) - 1) /
        ((p : ℝ) * (q : ℝ) * ((q : ℝ) + 1))) * kestenLikelihood p x +
          ((p : ℝ) + 1) / ((q : ℝ) + 1)) := by
    filter_upwards [ha] with x hx
    exact kestenLikelihood_ratio_on_interval p q ⟨x, hx⟩
  rw [integral_congr_ae he,
    integral_add ((integrable_kestenLikelihood p p).const_mul _) (integrable_const _),
    integral_const_mul, integral_kestenLikelihood_cross]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hpd : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp, sq_nonneg ((p : ℝ) - 1)]
  rw [← pow_two]
  field_simp [hp0, hq0, hq1, hpd]
  ring

/-- Every pairwise likelihood ratio has mean one under its denominator law. -/
theorem integral_kestenLikelihood_ratio (p q : Nat.Primes) :
    (∫ x, kestenLikelihood p x / kestenLikelihood q x ∂(kestenSpectralLaw q : Measure ℝ)) = 1 := by
  have h := integral_semicircleLikelihood_mul q ⟨_, continuous_kestenLikelihood_ratio p q⟩
  change (∫ x, kestenLikelihood q x * (kestenLikelihood p x / kestenLikelihood q x)
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, kestenLikelihood p x / kestenLikelihood q x ∂(kestenSpectralLaw q : Measure ℝ) at h
  rw [← h]
  have he (x : ℝ) : kestenLikelihood q x * (kestenLikelihood p x / kestenLikelihood q x) =
      kestenLikelihood p x := by
    field_simp [(kestenLikelihood_pos q x).ne']
  simp only [he]
  exact integral_semicircleLikelihood p

/-- The second pairwise likelihood moment equals its self-law expectation. -/
theorem integral_kestenLikelihood_ratio_sq (p q : Nat.Primes) :
    (∫ x, (kestenLikelihood p x / kestenLikelihood q x) ^ 2
      ∂(kestenSpectralLaw q : Measure ℝ)) =
      1 + ((p : ℝ) - (q : ℝ)) ^ 2 /
        ((q : ℝ) * ((q : ℝ) + 1) * ((p : ℝ) ^ 2 - 1)) := by
  have h := integral_semicircleLikelihood_mul q ⟨_, (continuous_kestenLikelihood_ratio p q).pow 2⟩
  change (∫ x, kestenLikelihood q x * (kestenLikelihood p x / kestenLikelihood q x) ^ 2
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, (kestenLikelihood p x / kestenLikelihood q x) ^ 2
        ∂(kestenSpectralLaw q : Measure ℝ) at h
  rw [← h]
  have he (x : ℝ) : kestenLikelihood q x * (kestenLikelihood p x / kestenLikelihood q x) ^ 2 =
      kestenLikelihood p x * (kestenLikelihood p x / kestenLikelihood q x) := by
    field_simp [(kestenLikelihood_pos q x).ne']
  simp only [he]
  have hj := integral_semicircleLikelihood_mul p ⟨_, continuous_kestenLikelihood_ratio p q⟩
  change (∫ x, kestenLikelihood p x * (kestenLikelihood p x / kestenLikelihood q x)
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, kestenLikelihood p x / kestenLikelihood q x ∂(kestenSpectralLaw p : Measure ℝ) at hj
  rw [hj]
  exact integral_kestenLikelihood_ratio_self p q

end
end GaloisForLFunctions.SelbergClass.Primon
