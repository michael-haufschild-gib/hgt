import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactMean
import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactStability

open Complex Set Metric Filter Topology
noncomputable section
namespace RHTower

/-- The literal full cofactor with the coherent scale and nonzero prefix mean removed. -/
def relativeFullGaussianCofactorScalarMode (s : ℂ) (t : ℝ) (A : ℂ)
    (R : ℝ) (ω : SteinhausModel.Omega) : ℂ :=
  A⁻¹ * (steinhausFullGaussianCofactor s R ω * (R : ℂ) ^ (-(s + (t : ℂ) * I)))

private theorem norm_inv_mul_error_lt (A : ℂ) {ε x : ℝ} (hε : 0 < ε)
    (hx : x < ε / (‖A⁻¹‖ + 1)) : ‖A⁻¹‖ * x < ε := by
  have hd : 0 < ε / (‖A⁻¹‖ + 1) := by positivity
  have hden : 0 < ‖A⁻¹‖ + 1 := by positivity
  calc
    _ ≤ ‖A⁻¹‖ * (ε / (‖A⁻¹‖ + 1)) := mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    _ < (‖A⁻¹‖ + 1) * (ε / (‖A⁻¹‖ + 1)) :=
      mul_lt_mul_of_pos_right (lt_add_one _) hd
    _ = ε := by field_simp [hden.ne']

/-- Coherent normalized modes converge on the whole disc in the uniform topology. -/
theorem tendstoUniformlyOn_relativeFullGaussianCofactor_extension
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1) :
    TendstoUniformlyOn (fun R s => relativeFullGaussianCofactorScalarMode s t
      (finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)))
      R (finitePrimeTwistExtension S ω t))
      (fun s => smoothAFEGaussianKernel (s + (t : ℂ) * I)) atTop (closedBall c r) := by
  let A := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  have hlim := tendstoUniformlyOn_finitePrimeTwistExtension_gaussian_mean S ω t hρ hrρ hc0 hc1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hd : 0 < ε / (‖A⁻¹‖ + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim _ hd] with R hR s hs
  have hnear := hR s hs
  rw [dist_comm, dist_eq_norm] at hnear ⊢
  let F := steinhausFullGaussianCofactor s R (finitePrimeTwistExtension S ω t) *
    (R : ℂ) ^ (-(s + (t : ℂ) * I))
  let G := smoothAFEGaussianKernel (s + (t : ℂ) * I)
  change ‖F - A * G‖ < ε / (‖A⁻¹‖ + 1) at hnear
  change ‖A⁻¹ * F - G‖ < ε
  have heq : A⁻¹ * (F - A * G) = A⁻¹ * F - G := by
    have hcancel : A⁻¹ * (A * G) = G := by
      rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    rw [mul_sub, hcancel]
  rw [← heq, norm_mul]
  exact norm_inv_mul_error_lt A hε hnear

/-- One coherent extension realizes a whole-disc mode with any minimum block scale
and any prescribed mean-weighted length budget. -/
theorem exists_fullGaussianCofactor_compact_mode_block
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ) (B : ℕ) (K ε : ℝ)
    (hε : 0 < ε) {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1) :
    ∃ ω' : SteinhausModel.Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ M : ℕ, B ≤ M ∧ 1 ≤ M ∧ ∃ A : ℂ, A ≠ 0 ∧ K ≤ (M : ℝ) * ‖A‖ ^ 2 ∧
        ∀ R : ℝ, (M : ℝ) ≤ R → ∀ s ∈ closedBall c r,
          ‖relativeFullGaussianCofactorScalarMode s t A R ω' -
            smoothAFEGaussianKernel (s + (t : ℂ) * I)‖ < ε := by
  let A := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  have hApos : 0 < ‖A‖ ^ 2 := pow_pos (norm_pos_iff.mpr hA) 2
  have hlim := tendstoUniformlyOn_relativeFullGaussianCofactor_extension S ω t hρ hrρ hc0 hc1
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hlim ε hε)
  obtain ⟨C, hC⟩ := exists_nat_gt (max R0 (K / ‖A‖ ^ 2))
  let M := B + C + 1
  have hCM : (C : ℝ) ≤ M := by exact_mod_cast (show C ≤ M by omega)
  have hRC : R0 < (C : ℝ) := lt_of_le_of_lt (le_max_left _ _) hC
  refine ⟨finitePrimeTwistExtension S ω t,
    fun _ hp => finitePrimeTwistExtension_eq_on_prefix S ω t hp,
    M, by omega, by omega, A, hA, ?_, ?_⟩
  · have hc : K < (C : ℝ) * ‖A‖ ^ 2 :=
      (div_lt_iff₀ hApos).mp (lt_of_le_of_lt (le_max_right _ _) hC)
    exact hc.le.trans (mul_le_mul_of_nonneg_right hCM hApos.le)
  · intro R hR s hs
    have h := hR0 R (hRC.le.trans (hCM.trans hR)) s hs
    rwa [dist_comm, dist_eq_norm] at h

/-- Fixed finite characters preserve the normalized mode throughout a whole
bounded scale interval and a nonnegative abscissa band. -/
theorem exists_relativeFullGaussianCofactor_compact_character_tolerance
    (b U : ℝ) (t : ℝ) (A : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ R : ℝ, 1 ≤ R → R ≤ U →
        ∀ ω η : SteinhausModel.Omega,
          (∀ n ∈ Finset.Icc 1 B, ‖SteinhausModel.X n η - SteinhausModel.X n ω‖ < δ) →
          ‖relativeFullGaussianCofactorScalarMode s t A R η -
            relativeFullGaussianCofactorScalarMode s t A R ω‖ < ε := by
  obtain ⟨B, hB, δ, hδ, htol⟩ :=
    exists_fullGaussianCofactor_uniform_abscissa_character_tolerance b U
      (by positivity : 0 < ε / (‖A⁻¹‖ + 1))
  refine ⟨B, hB, δ, hδ, fun s hs0 hsb R hR hRU ω η hcell => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h := htol s hsb R hR0 hRU ω η hcell
  have hp : ‖(R : ℂ) ^ (-(s + (t : ℂ) * I))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hR0]
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hR (neg_nonpos.mpr hs0)
  have heq : relativeFullGaussianCofactorScalarMode s t A R η -
      relativeFullGaussianCofactorScalarMode s t A R ω =
      (A⁻¹ * (steinhausFullGaussianCofactor s R η - steinhausFullGaussianCofactor s R ω)) *
        (R : ℂ) ^ (-(s + (t : ℂ) * I)) := by
    unfold relativeFullGaussianCofactorScalarMode
    ring
  rw [heq, norm_mul, norm_mul]
  calc
    _ ≤ (‖A⁻¹‖ * ‖steinhausFullGaussianCofactor s R η -
        steinhausFullGaussianCofactor s R ω‖) * 1 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ < ε := by rw [mul_one]; exact norm_inv_mul_error_lt A hε h

end RHTower
