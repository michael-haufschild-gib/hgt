import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuarticHarmonicJets

/-!
# An asymptotic spectral differential equation for actual Gibbs energy

The operator D(D^2+4)(D^2+16) annihilates the critical profile.
Applied to the actual aligned Gibbs potential, every derivative of
its residual is uniformly o(d), where d is phase asymmetry. This
transfers the two nonconstant critical frequencies to an observable
built directly from the actual energy derivatives. The residual is
not asserted to vanish at finite coexistence states.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsSpectralResidual (w φ τ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ) : ℝ :=
  iteratedDeriv (n + 5) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ +
    20 * iteratedDeriv (n + 3) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ +
    64 * iteratedDeriv (n + 1) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ

theorem egbFixedChargeAGibbsSpectralResidual_error_decomposition (w φ τ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ) :
    egbFixedChargeAGibbsSpectralResidual w φ τ l₁ l₂ n ψ / egbCoexistenceASymmetricRatio τ =
      (iteratedDeriv (n + 5) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
        iteratedDeriv (n + 5) (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ +
      20 * ((iteratedDeriv (n + 3) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
        iteratedDeriv (n + 3) (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ) +
      64 * ((iteratedDeriv (n + 1) (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
        iteratedDeriv (n + 1) (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ) := by
  have hr := egbFixedChargeAQuarticProfile_differential_recurrence n ψ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsSpectralResidual
  field_simp [hd.ne']
  nlinarith

theorem egbFixedChargeAGibbsSpectralResidual_uniform_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => egbFixedChargeAGibbsSpectralResidual w φ τ l₁ l₂ n ψ /
      egbCoexistenceASymmetricRatio τ) (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε / 85 := by positivity
  have h₅ := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ (n + 5))) (ε / 85) he
  have h₃ := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ (n + 3))) (ε / 85) he
  have h₁ := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAPeakNormalizedGibbs_iteratedDeriv_uniform_first_zero_limit w φ l₁ l₂ (n + 1))) (ε / 85) he
  filter_upwards [h₅, h₃, h₁] with τ h₅ h₃ h₁
  intro ψ
  have h₅ := h₅ ψ
  have h₃ := h₃ ψ
  have h₁ := h₁ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg] at h₅ h₃ h₁ ⊢
  rw [egbFixedChargeAGibbsSpectralResidual_error_decomposition]
  let e := fun j : ℕ => (iteratedDeriv j (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ -
    iteratedDeriv j (fun x : ℝ => cos x ^ 4) ψ) / egbCoexistenceASymmetricRatio τ
  change |e (n + 5) + 20 * e (n + 3) + 64 * e (n + 1)| < ε
  change |e (n + 5)| < ε / 85 at h₅
  change |e (n + 3)| < ε / 85 at h₃
  change |e (n + 1)| < ε / 85 at h₁
  have ha := abs_add_le (e (n + 5) + 20 * e (n + 3)) (64 * e (n + 1))
  have hb := abs_add_le (e (n + 5)) (20 * e (n + 3))
  norm_num [abs_mul] at ha hb
  linarith

theorem egbFixedChargeAGibbsSpectralResidual_uniform_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => egbFixedChargeAGibbsSpectralResidual w φ τ l₁ l₂ n ψ)
      (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAGibbsSpectralResidual_uniform_first_zero_limit w φ l₁ l₂ n)) 1 (by norm_num)
  have hd := egbCoexistenceASymmetricRatio_critical_limit.eventually_lt_const hε
  filter_upwards [he, hd] with τ hτ hδ
  intro ψ
  have hp := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := hτ ψ
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_div, abs_of_pos hp] at h
  have hx := (div_lt_iff₀ hp).mp h
  simp only [one_mul] at hx
  simpa only [Real.dist_eq, zero_sub, abs_neg] using hx.trans hδ

theorem egbFixedChargeAGibbsSpectralResidual_moving_first_zero_limit (w φ l₁ l₂ : ℝ) (n : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsSpectralResidual w φ τ l₁ l₂ n (ψ τ) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAGibbsSpectralResidual_uniform_first_zero_limit w φ l₁ l₂ n)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

end GaloisForLFunctions.HTGeometry
