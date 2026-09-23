import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedCoordinate

/-!
# Moving-peak alignment removes the first asymmetric profile correction

An endpoint-preserving fractional linear change of radius absorbs the
entire first odd correction of the actual barrier-normalized Gibbs
profile. The corrected reference profile is bounded by one, has exactly
the physical phase zeros, and places its maximum at the true stationary
barrier. The proved residual is little-o of phase asymmetry, pointwise
in the original interior coordinate.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakAlignedProfile (τ φ ψ : ℝ) : ℝ :=
  (1 - egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ)) ^ (2 : ℕ)

theorem egbFixedChargeAPeakAlignedProfile_bounds (τ φ ψ : ℝ) :
    0 ≤ egbFixedChargeAPeakAlignedProfile τ φ ψ ∧ egbFixedChargeAPeakAlignedProfile τ φ ψ ≤ 1 := by
  have hx := egbFixedChargeAPeakAlignedCoordinate_bounds τ φ ψ
  have hx2 : egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - egbFixedChargeAPeakAlignedCoordinate τ φ ψ)
      (by linarith : 0 ≤ 1 + egbFixedChargeAPeakAlignedCoordinate τ φ ψ)]
  unfold egbFixedChargeAPeakAlignedProfile
  constructor
  · positivity
  · nlinarith [sq_nonneg (egbFixedChargeAPeakAlignedCoordinate τ φ ψ),
      sq_nonneg (egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ))]

theorem egbFixedChargeAPeakAlignedProfile_zero_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedProfile τ φ ψ = 0 ↔ cos ψ = 0 := by
  have hx := egbFixedChargeAPeakAlignedCoordinate_bounds τ φ ψ
  constructor
  · intro hz
    unfold egbFixedChargeAPeakAlignedProfile at hz
    have hx2 : egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ) = 1 := by nlinarith
    have hp : (egbFixedChargeAPeakAlignedCoordinate τ φ ψ - 1) *
        (egbFixedChargeAPeakAlignedCoordinate τ φ ψ + 1) = 0 := by nlinarith [hx2]
    rcases mul_eq_zero.mp hp with h | h
    · have hs := (egbFixedChargeAPeakAlignedCoordinate_large_iff τ φ ψ).mp (by linarith)
      nlinarith [sin_sq_add_cos_sq ψ]
    · have hs := (egbFixedChargeAPeakAlignedCoordinate_small_iff τ φ ψ).mp (by linarith)
      nlinarith [sin_sq_add_cos_sq ψ]
  · intro hz
    have hs2 : sin ψ ^ (2 : ℕ) = 1 := by nlinarith [sin_sq_add_cos_sq ψ]
    have hp : (sin ψ - 1) * (sin ψ + 1) = 0 := by nlinarith [hs2]
    rcases mul_eq_zero.mp hp with h | h
    · have he := (egbFixedChargeAPeakAlignedCoordinate_large_iff τ φ ψ).mpr (by linarith)
      simp only [egbFixedChargeAPeakAlignedProfile, he, one_pow, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · have he := (egbFixedChargeAPeakAlignedCoordinate_small_iff τ φ ψ).mpr (by linarith)
      norm_num only [egbFixedChargeAPeakAlignedProfile, he, neg_sq, one_pow, sub_self, zero_pow]

theorem egbFixedChargeAPeakAlignedProfile_one_iff (τ φ ψ : ℝ) :
    egbFixedChargeAPeakAlignedProfile τ φ ψ = 1 ↔ sin ψ = egbFixedChargeAMiddleGapCoordinate τ φ := by
  rw [← egbFixedChargeAPeakAlignedCoordinate_zero_iff τ φ ψ]
  have hx := egbFixedChargeAPeakAlignedCoordinate_bounds τ φ ψ
  have hx2 : egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - egbFixedChargeAPeakAlignedCoordinate τ φ ψ)
      (by linarith : 0 ≤ 1 + egbFixedChargeAPeakAlignedCoordinate τ φ ψ)]
  unfold egbFixedChargeAPeakAlignedProfile
  constructor
  · intro he
    have hnon : 0 ≤ egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ) := sq_nonneg _
    nlinarith [mul_nonneg hnon (by linarith : 0 ≤ 1 - egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ))]
  · intro he
    rw [he]
    norm_num

theorem egbFixedChargeAPeakAlignedProfile_critical_limit (φ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPeakAlignedProfile τ φ ψ) atBot (𝓝 (cos ψ ^ (4 : ℕ))) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub ((egbFixedChargeAPeakAlignedCoordinate_critical_limit φ ψ).pow 2)).pow 2
  have hs : 1 - sin ψ ^ (2 : ℕ) = cos ψ ^ (2 : ℕ) := by linarith [sin_sq_add_cos_sq ψ]
  have he : (1 - sin ψ ^ (2 : ℕ)) ^ (2 : ℕ) = cos ψ ^ (4 : ℕ) := by rw [hs]; ring
  rw [he] at h
  exact h

theorem egbFixedChargeAPeakAlignedProfile_linear_formula (τ φ ψ : ℝ) :
    (egbFixedChargeAPeakAlignedProfile τ φ ψ - cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ =
      ((egbFixedChargeAPeakAlignedCoordinate τ φ ψ - sin ψ) / egbCoexistenceASymmetricRatio τ) *
        (egbFixedChargeAPeakAlignedCoordinate τ φ ψ + sin ψ) *
        (egbFixedChargeAPeakAlignedCoordinate τ φ ψ ^ (2 : ℕ) + sin ψ ^ (2 : ℕ) - 2) := by
  have hs : cos ψ ^ (2 : ℕ) = 1 - sin ψ ^ (2 : ℕ) := by linarith [sin_sq_add_cos_sq ψ]
  have he : cos ψ ^ (4 : ℕ) = (1 - sin ψ ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [← hs]; ring
  unfold egbFixedChargeAPeakAlignedProfile
  rw [he]
  ring

theorem egbFixedChargeAPeakAlignedProfile_first_correction_limit (φ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAPeakAlignedProfile τ φ ψ - cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ))) := by
  have hx := egbFixedChargeAPeakAlignedCoordinate_critical_limit φ ψ
  have h := ((egbFixedChargeAPeakAlignedCoordinate_linear_limit φ ψ).mul
    (hx.add (tendsto_const_nhds (x := sin ψ)))).mul
    (((hx.pow 2).add (tendsto_const_nhds (x := sin ψ ^ (2 : ℕ)))).sub (tendsto_const_nhds (x := (2 : ℝ))))
  have hs : sin ψ ^ (2 : ℕ) = 1 - cos ψ ^ (2 : ℕ) := by linarith [sin_sq_add_cos_sq ψ]
  have he : (-egbFixedChargeAMiddleMeanCorrection φ * cos ψ ^ (2 : ℕ)) * (sin ψ + sin ψ) *
      (sin ψ ^ (2 : ℕ) + sin ψ ^ (2 : ℕ) - 2) = 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ) := by
    rw [hs]
    ring
  rw [he] at h
  simpa only [egbFixedChargeAPeakAlignedProfile_linear_formula] using h

theorem egbFixedChargeAInteriorGibbsGap_aligned_first_zero_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      egbFixedChargeAPeakAlignedProfile τ φ ψ) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_normalized_first_correction_limit w φ l₁ l₂ ψ).sub
    (egbFixedChargeAPeakAlignedProfile_first_correction_limit φ ψ)
  simp only [sub_self] at h
  convert h using 1
  funext τ
  ring

theorem egbFixedChargeAInteriorGibbsGap_aligned_peak_zero_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      egbFixedChargeAPeakAlignedProfile τ φ ψ) / egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAInteriorGibbsGap_aligned_first_zero_limit w φ l₁ l₂ ψ).div
    (egbFixedChargeAMiddleGapCoordinate_linear_limit φ) hc.ne
  simp only [zero_div, Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
