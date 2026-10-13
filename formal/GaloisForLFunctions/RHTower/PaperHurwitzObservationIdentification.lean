import GaloisForLFunctions.RHTower.PaperHurwitzExactObservation
import GaloisForLFunctions.HTGeometry.LpObservationModulus

/-! # The exact source parameter visible to Hurwitz observations

All full-history norm observations determine exactly absolute distance from the
critical line. One literal dyadic level already determines that entire profile.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

def paperHurwitzWallDistance (rho : ℂ) : ℝ := |rho.re - 1 / 2|

theorem paperHurwitzWallDistance_nonneg (rho : ℂ) : 0 ≤ paperHurwitzWallDistance rho := abs_nonneg _

theorem paperHurwitzPowerEnergy_eq_sinh_distance (rho : ℂ) (k : ℕ) :
    paperHurwitzPowerEnergy rho k =
      Real.sinh ((k : ℝ) * paperHurwitzWallDistance rho * Real.log 2) ^ 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha : |(k : ℝ) * ((rho.re - 1 / 2) * Real.log 2)| =
      (k : ℝ) * paperHurwitzWallDistance rho * Real.log 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hl]
    simp only [paperHurwitzWallDistance, mul_assoc]
  rw [paperHurwitzPowerEnergy_eq_sinh]
  apply (sq_eq_sq_iff_abs_eq_abs _ _).mpr
  rw [Real.abs_sinh, Real.abs_sinh, ha,
    abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (paperHurwitzWallDistance_nonneg rho)) hl)]

theorem paperHurwitzRegularizer_eq_distance (rho : ℂ) (k : ℕ) :
    paperHurwitzRegularizer rho k =
      (1 + Real.sinh ((k : ℝ) * paperHurwitzWallDistance rho * Real.log 2) ^ 2)⁻¹ := by
  rw [paperHurwitzRegularizer, paperHurwitzPowerEnergy_eq_sinh_distance]

theorem paperHurwitzRegularizer_complex_norm (rho : ℂ) (k : ℕ) :
    ‖(paperHurwitzRegularizer rho k : ℂ)‖ = paperHurwitzRegularizer rho k := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (paperHurwitzRegularizer_pos rho k)]

theorem paperHurwitzResolvent_singleObservation (rho : ℂ) (k : ℕ) :
    lpSolidObservation (paperHurwitzResolvent rho) (lp.single 2 k (1 : ℂ)) =
      paperHurwitzRegularizer rho k := by
  rw [lpSolidObservation_coordinate_single _ _ (paperHurwitzResolvent_apply rho),
    paperHurwitzRegularizer_complex_norm]

theorem paperHurwitzRegularizer_one_eq_iff_distance (rho sigma : ℂ) :
    paperHurwitzRegularizer rho 1 = paperHurwitzRegularizer sigma 1 ↔
      paperHurwitzWallDistance rho = paperHurwitzWallDistance sigma := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs (z : ℂ) : 0 ≤ Real.sinh (paperHurwitzWallDistance z * Real.log 2) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg (paperHurwitzWallDistance_nonneg z) hl.le)
  simp only [paperHurwitzRegularizer_eq_distance, Nat.cast_one, one_mul, inv_inj, add_left_cancel_iff]
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (hs rho), abs_of_nonneg (hs sigma), Real.sinh_inj]
  constructor
  · exact mul_right_cancel₀ hl.ne'
  · intro h
    rw [h]

theorem paperHurwitz_observations_eq_iff_distance (rho sigma : ℂ) :
    (∀ x, lpSolidObservation (paperHurwitzResolvent rho) x =
      lpSolidObservation (paperHurwitzResolvent sigma) x) ↔
        paperHurwitzWallDistance rho = paperHurwitzWallDistance sigma := by
  constructor
  · intro h
    apply (paperHurwitzRegularizer_one_eq_iff_distance rho sigma).mp
    simpa only [paperHurwitzResolvent_singleObservation] using h (lp.single 2 1 (1 : ℂ))
  · intro h
    apply (forall_lpSolidObservation_eq_iff _ _ _ _
      (paperHurwitzResolvent_apply rho) (paperHurwitzResolvent_apply sigma)).mpr
    intro k
    rw [paperHurwitzRegularizer_complex_norm, paperHurwitzRegularizer_complex_norm,
      paperHurwitzRegularizer_eq_distance, paperHurwitzRegularizer_eq_distance, h]

theorem paperHurwitzResolvent_eq_iff_distance (rho sigma : ℂ) :
    paperHurwitzResolvent rho = paperHurwitzResolvent sigma ↔
      paperHurwitzWallDistance rho = paperHurwitzWallDistance sigma := by
  constructor
  · intro h
    exact (paperHurwitz_observations_eq_iff_distance rho sigma).mp (fun x => by rw [h])
  · intro h
    ext x k
    simp only [paperHurwitzResolvent_apply, paperHurwitzRegularizer_eq_distance, h]

theorem paperHurwitz_observations_eq_iff_single (rho sigma : ℂ) :
    (∀ x, lpSolidObservation (paperHurwitzResolvent rho) x =
      lpSolidObservation (paperHurwitzResolvent sigma) x) ↔
    lpSolidObservation (paperHurwitzResolvent rho) (lp.single 2 1 (1 : ℂ)) =
      lpSolidObservation (paperHurwitzResolvent sigma) (lp.single 2 1 (1 : ℂ)) := by
  rw [paperHurwitz_observations_eq_iff_distance, paperHurwitzResolvent_singleObservation,
    paperHurwitzResolvent_singleObservation, paperHurwitzRegularizer_one_eq_iff_distance]

theorem paperHurwitz_observations_eq_iff_reflection (rho sigma : ℂ) :
    (∀ x, lpSolidObservation (paperHurwitzResolvent rho) x =
      lpSolidObservation (paperHurwitzResolvent sigma) x) ↔
        rho.re = sigma.re ∨ rho.re + sigma.re = 1 := by
  rw [paperHurwitz_observations_eq_iff_distance]
  change |rho.re - 1 / 2| = |sigma.re - 1 / 2| ↔ _
  rw [abs_eq_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

end
end RHTower
