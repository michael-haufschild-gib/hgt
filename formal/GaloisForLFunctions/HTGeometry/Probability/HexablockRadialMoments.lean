import GaloisForLFunctions.HTGeometry.Probability.ComplexSphereMonomialNorm
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments

/-!
# Radial moments of the two hexablock boundary models

The normalized coordinate moments on the unit sphere in complex dimension two and the flat
quarter-circle parameter are respectively `1/(n+1)` and `centralBinom n/4^n`.
The angular density `π cos(t) sin(t)` transforms every moment into its
spherical counterpart. Spherical moments admit the sharp upper comparison
with constant one, but no reverse comparison: their ratio is asymptotic to
`sqrt(π/n)`. These are statements about actual sphere and angular integrals;
they do not assume a Haar-measure identification for the full boundary.
-/

noncomputable section
open MeasureTheory Set Metric Filter Topology
namespace GaloisForLFunctions.HTGeometry

/-- The radial coordinate monomial moment for the sphere in complex dimension two. -/
def hexablockSphereMoment (n : ℕ) : ℝ := complexSphereMellin 1 n

/-- The corresponding angular moment under the flat quarter-circle parameter. -/
def hexablockAngleMoment (n : ℕ) : ℝ :=
  (2 / Real.pi) * ∫ t in (0 : ℝ)..Real.pi / 2, Real.cos t ^ (2 * n)

theorem hexablockSphereMoment_eq (n : ℕ) :
    hexablockSphereMoment n = 1 / ((n : ℝ) + 1) := by
  rw [hexablockSphereMoment, complexSphereMellin_eq_prod 1 (by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hn])]
  simp

theorem hexablockAngleMoment_eq (n : ℕ) :
    hexablockAngleMoment n = normalizedCentralBinom n := by
  rw [hexablockAngleMoment, integral_cos_pow_even_zero_pi_div_two]
  field_simp

theorem hexablockAngleMoment_pos (n : ℕ) : 0 < hexablockAngleMoment n := by
  rw [hexablockAngleMoment_eq, normalizedCentralBinom]
  exact div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos n)) (by positivity)

/-- The radial density converting the flat angle parameter to the spherical model. -/
def hexablockRadialDensity (t : ℝ) : ℝ := Real.pi * Real.cos t * Real.sin t

private theorem weighted_cos_moment (n : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 2,
      2 * Real.sin t * Real.cos t * Real.cos t ^ (2 * n)) = 1 / ((n : ℝ) + 1) := by
  let F : ℝ → ℝ := fun t => -(Real.cos t ^ (2 * n + 2)) / ((n : ℝ) + 1)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hd (t : ℝ) : HasDerivAt F
      (2 * Real.sin t * Real.cos t * Real.cos t ^ (2 * n)) t := by
    apply (((Real.hasDerivAt_cos t).pow (2 * n + 2)).neg.div_const ((n : ℝ) + 1)).congr_deriv
    rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega, pow_succ]
    push_cast
    field_simp
  have hi : IntervalIntegrable
      (fun t => 2 * Real.sin t * Real.cos t * Real.cos t ^ (2 * n)) volume
      (0 : ℝ) (Real.pi / 2) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp [F]
  ring

/-- Every coordinate moment transforms by the paper's radial density. -/
theorem hexablockSphereMoment_eq_weightedAngleIntegral (n : ℕ) :
    hexablockSphereMoment n = (2 / Real.pi) *
      ∫ t in (0 : ℝ)..Real.pi / 2,
        hexablockRadialDensity t * Real.cos t ^ (2 * n) := by
  have he (t : ℝ) : hexablockRadialDensity t * Real.cos t ^ (2 * n) =
      (Real.pi / 2) * (2 * Real.sin t * Real.cos t * Real.cos t ^ (2 * n)) := by
    unfold hexablockRadialDensity
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, weighted_cos_moment, hexablockSphereMoment_eq]
  field_simp

/-- Spherical coordinate moments are bounded by flat-angle moments, with optimal constant one. -/
theorem hexablockSphereMoment_le_angle (n : ℕ) :
    hexablockSphereMoment n ≤ hexablockAngleMoment n := by
  simp only [hexablockSphereMoment_eq, hexablockAngleMoment_eq]
  induction n with
  | zero => simp [normalizedCentralBinom]
  | succ n ih =>
    rw [normalizedCentralBinom_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h₂ : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h₃ : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
    calc
      1 / ((n + 1 : ℕ) + 1 : ℝ) ≤
          (1 / ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
        push_cast
        rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
        rw [le_div_iff₀ h₃, div_mul_eq_mul_div, div_mul_eq_mul_div,
          div_le_div_iff₀ h₂ h₁]
        nlinarith only [hn]
      _ ≤ normalizedCentralBinom n * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
        gcongr

/-- Constant one is forced already by the constant monomial. -/
theorem hexablockMoment_domination_iff (C : ℝ) :
    (∀ n : ℕ, hexablockSphereMoment n ≤ C * hexablockAngleMoment n) ↔ 1 ≤ C := by
  constructor
  · intro h
    have h₀ := h 0
    simpa [hexablockSphereMoment_eq, hexablockAngleMoment_eq, normalizedCentralBinom] using h₀
  · intro h n
    exact (hexablockSphereMoment_le_angle n).trans
      (by nlinarith only [hexablockAngleMoment_pos n, h])

/-- The squared-norm ratio has sharp half-order decay. -/
theorem tendsto_hexablockMomentRatio_scaled :
    Tendsto (fun n : ℕ => Real.sqrt n *
      (hexablockSphereMoment n / hexablockAngleMoment n)) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).div
    tendsto_sqrtNat_mul_normalizedCentralBinom (by positivity : 1 / Real.sqrt Real.pi ≠ 0)
  have he : (fun n : ℕ => Real.sqrt n *
      (hexablockSphereMoment n / hexablockAngleMoment n)) =ᶠ[atTop]
        fun n => ((n : ℝ) / ((n : ℝ) + 1)) / (Real.sqrt n * normalizedCentralBinom n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
    have hc : normalizedCentralBinom n ≠ 0 :=
      (hexablockAngleMoment_eq n ▸ hexablockAngleMoment_pos n).ne'
    have hn' : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [hexablockSphereMoment_eq, hexablockAngleMoment_eq]
    field_simp [hs, hc, hn']
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg n)]
  apply Filter.Tendsto.congr' he.symm
  change Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) /
    (Real.sqrt n * normalizedCentralBinom n)) atTop (𝓝 (1 / (1 / Real.sqrt Real.pi))) at h
  simpa only [one_div_one_div] using h

/-- Sphere and flat-angle moments separate asymptotically. -/
theorem tendsto_hexablockMomentRatio_zero :
    Tendsto (fun n : ℕ => hexablockSphereMoment n / hexablockAngleMoment n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h := tendsto_hexablockMomentRatio_scaled.div_atTop hs
  apply Filter.Tendsto.congr' _ h
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  exact mul_div_cancel_left₀ _ hn'

/-- No fixed constant bounds all flat-angle monomial moments by spherical ones. -/
theorem hexablockMoments_not_equivalent :
    ¬ ∃ C : ℝ, ∀ n : ℕ, hexablockAngleMoment n ≤ C * hexablockSphereMoment n := by
  rintro ⟨C, hC⟩
  have hlim := tendsto_hexablockMomentRatio_zero.const_mul C
  rw [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)).exists
  have hle : (1 : ℝ) ≤ C * (hexablockSphereMoment n / hexablockAngleMoment n) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (hexablockAngleMoment_pos n)).2 (by simpa using hC n)
  exact (not_le_of_gt hn) hle

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.hexablockSphereMoment_eq_weightedAngleIntegral
#print axioms GaloisForLFunctions.HTGeometry.tendsto_hexablockMomentRatio_scaled
#print axioms GaloisForLFunctions.HTGeometry.hexablockMoments_not_equivalent

#print axioms GaloisForLFunctions.HTGeometry.hexablockMoment_domination_iff
