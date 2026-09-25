import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# Mellin transform of the literal theta Euler atom

The factor `a - 1/2` is exact, before any Euler summation. The critical
zero of every finite atom therefore does not determine the completed
source's nonzero critical charge; any completion theorem must retain the
failure of uniform integrability at that boundary.
-/

open MeasureTheory Set

namespace RHTower

private theorem thetaEulerRadialIntegrable (sig : ℝ) (hsig : -1 < sig) :
    IntegrableOn (fun t : ℝ => t ^ sig * Real.exp (-Real.pi * t ^ 2)) (Ioi 0) := by
  exact (integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos hsig).integrableOn

/-- Radial Mellin transform of the normalized theta-cusp seed. -/
theorem integral_rpow_mul_thetaCuspSeed_Ioi (a : ℝ) (ha : -(5 / 2) < a) :
    (∫ t : ℝ in Ioi 0, t ^ (a - 1 / 2) * thetaCuspSeed t) =
      (a - 1 / 2) * Real.Gamma (a / 2 + 5 / 4) *
        Real.pi ^ (-(a / 2 + 1 / 4)) := by
  have hs2 : -1 < a + 3 / 2 := by linarith
  have hs4 : -1 < a + 7 / 2 := by linarith
  have hform : ∀ t : ℝ, 0 < t →
      t ^ (a - 1 / 2) * thetaCuspSeed t =
        (4 * Real.pi ^ 2) * (t ^ (a + 7 / 2) * Real.exp (-Real.pi * t ^ 2)) -
          (6 * Real.pi) * (t ^ (a + 3 / 2) * Real.exp (-Real.pi * t ^ 2)) := by
    intro t ht
    have h4 : t ^ (a + 7 / 2) = t ^ (a - 1 / 2) * t ^ 4 := by
      rw [show a + 7 / 2 = (a - 1 / 2) + 4 by ring, Real.rpow_add ht]
      norm_num
    have h2 : t ^ (a + 3 / 2) = t ^ (a - 1 / 2) * t ^ 2 := by
      rw [show a + 3 / 2 = (a - 1 / 2) + 2 by ring, Real.rpow_add ht]
      norm_num
    rw [h4, h2]
    unfold thetaCuspSeed
    ring
  rw [show (∫ t : ℝ in Ioi 0, t ^ (a - 1 / 2) * thetaCuspSeed t) =
      ∫ t : ℝ in Ioi 0,
        (4 * Real.pi ^ 2) * (t ^ (a + 7 / 2) * Real.exp (-Real.pi * t ^ 2)) -
          (6 * Real.pi) * (t ^ (a + 3 / 2) * Real.exp (-Real.pi * t ^ 2)) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hform t ht]
  rw [integral_sub ((thetaEulerRadialIntegrable _ hs4).const_mul _)
      ((thetaEulerRadialIntegrable _ hs2).const_mul _), integral_const_mul,
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_sq_Ioi hs4 Real.pi_pos,
    integral_rpow_mul_exp_neg_mul_sq_Ioi hs2 Real.pi_pos]
  have hv : a / 2 + 5 / 4 ≠ 0 := by linarith
  have hgamma : Real.Gamma (a / 2 + 9 / 4) =
      (a / 2 + 5 / 4) * Real.Gamma (a / 2 + 5 / 4) := by
    convert Real.Gamma_add_one hv using 1 <;> ring
  rw [show (a + 7 / 2 + 1) / 2 = a / 2 + 9 / 4 by ring,
    show (a + 3 / 2 + 1) / 2 = a / 2 + 5 / 4 by ring,
    hgamma]
  have hpow2 : (1 / Real.pi) ^ (a / 2 + 9 / 4) =
      (1 / Real.pi) ^ (a / 2 + 1 / 4) / Real.pi ^ 2 := by
    rw [show a / 2 + 9 / 4 = (a / 2 + 1 / 4) + 2 by ring,
      Real.rpow_add (by positivity)]
    have htw : (1 / Real.pi : ℝ) ^ (2 : ℝ) = (Real.pi ^ 2)⁻¹ := by
      rw [Real.rpow_two, one_div, inv_pow]
    rw [htw]
    exact (div_eq_mul_inv _ _).symm
  have hpow1 : (1 / Real.pi) ^ (a / 2 + 5 / 4) =
      (1 / Real.pi) ^ (a / 2 + 1 / 4) / Real.pi := by
    rw [show a / 2 + 5 / 4 = (a / 2 + 1 / 4) + 1 by ring,
      Real.rpow_add (by positivity), Real.rpow_one]
    rw [one_div]
    ring
  rw [hpow2, hpow1]
  have hinv : (1 / Real.pi) ^ (a / 2 + 1 / 4) =
      Real.pi ^ (-(a / 2 + 1 / 4)) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]
    ring
  rw [hinv]
  field_simp [Real.pi_ne_zero]
  ring

/-- Log-coordinate Mellin transform, valid across the critical parameter. -/
theorem integral_exp_mul_thetaCuspLogSeed (a : ℝ) (ha : -(5 / 2) < a) :
    (∫ x : ℝ, Real.exp (a * x) * thetaCuspLogSeed x) =
      (a - 1 / 2) * Real.Gamma (a / 2 + 5 / 4) *
        Real.pi ^ (-(a / 2 + 1 / 4)) := by
  rw [← integral_rpow_mul_thetaCuspSeed_Ioi a ha,
    GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [thetaCuspLogSeed]
  rw [← Real.exp_mul]
  rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- Exact real Mellin transform of each positive integer theta-source atom. -/
theorem integral_exp_mul_thetaCuspSourceTerm (a : ℝ) (ha : -(5 / 2) < a)
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ, Real.exp (a * x) * thetaCuspSourceTerm x n) =
      Real.exp (-(a + 1 / 2) * Real.log n) *
        ((a - 1 / 2) * Real.Gamma (a / 2 + 5 / 4) *
          Real.pi ^ (-(a / 2 + 1 / 4))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hseed (x : ℝ) : Real.exp (x + Real.log n) = n * Real.exp x := by
    rw [Real.exp_add, Real.exp_log hnR]
    ring
  have hfun (x : ℝ) :
      Real.exp (a * x) * thetaCuspSourceTerm x n =
        Real.exp (-(a + 1 / 2) * Real.log n) *
          (Real.exp (a * (x + Real.log n)) *
            thetaCuspLogSeed (x + Real.log n)) := by
    dsimp [thetaCuspSourceTerm, thetaCuspLogSeed]
    rw [hseed]
    repeat rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∫ x : ℝ, Real.exp (-(a + 1 / 2) * Real.log n) *
          (Real.exp (a * (x + Real.log n)) *
            thetaCuspLogSeed (x + Real.log n)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hfun x
    _ = Real.exp (-(a + 1 / 2) * Real.log n) *
          ∫ x : ℝ, Real.exp (a * (x + Real.log n)) *
            thetaCuspLogSeed (x + Real.log n) := by rw [integral_const_mul]
    _ = Real.exp (-(a + 1 / 2) * Real.log n) *
          ∫ y : ℝ, Real.exp (a * y) * thetaCuspLogSeed y := by
          congr 1
          exact integral_add_right_eq_self
            (fun y : ℝ => Real.exp (a * y) * thetaCuspLogSeed y) (Real.log n)
    _ = _ := by rw [integral_exp_mul_thetaCuspLogSeed a ha]

end RHTower
