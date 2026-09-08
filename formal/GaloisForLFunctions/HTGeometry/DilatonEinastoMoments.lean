import GaloisForLFunctions.HTGeometry.DilatonGroundStates
import GaloisForLFunctions.HTGeometry.EinastoGammaMoments

/-!
# The quartic dilaton ground-state density is an Einasto profile

Connects the half-density Hamiltonian mechanism of arXiv:2608.21406v1 with
the Einasto density and Gamma moments of arXiv:2608.23600v1. The squared
amplitude of the constructed quartic ground state equals an Einasto profile
of index `1/4`, with a coupling-dependent length scale. This exact functional
identity transfers every natural radial moment, every absolute moment,
integrability, total norm-density integral, and enclosed-mass construction.
It identifies functions, not the two papers' physical systems.
-/

noncomputable section
open Real Polynomial MeasureTheory Set
open scoped SchwartzMap Topology
namespace GaloisForLFunctions.HTGeometry

theorem quarticDilatonGroundState_norm_sq (k x : ℝ) :
    ‖quarticDilatonGroundState k x‖ ^ 2 = exp (-exp k * x ^ 4) := by
  rw [quarticDilatonGroundState_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (exp_pos _), ← Real.exp_nat_mul _ 2]
  congr 1
  ring

/-- The ground-state density is exactly an Einasto profile with index `1/4`. -/
theorem quarticDilatonGroundState_einasto_density (k x : ℝ) :
    ‖quarticDilatonGroundState k x‖ ^ 2 = einastoDensity 0 (-k / 4) (-log 4) x := by
  rw [quarticDilatonGroundState_norm_sq]
  simp only [einastoDensity, exp_zero, one_mul, neg_neg, exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [show (x / exp (-k / 4)) ^ (4 : ℝ) = (x / exp (-k / 4)) ^ (4 : ℕ) from rpow_natCast _ 4,
    div_pow]
  have he : exp (-k / 4) ^ 4 = exp (-k) := by
    rw [← Real.exp_nat_mul _ 4]
    congr 1
    ring
  rw [he, exp_neg k, div_inv_eq_mul]
  congr 1
  ring

/-- All radial moments of the exact ground state follow from the Einasto Gamma formula. -/
theorem quarticDilatonGroundState_radial_moments (n : ℕ) (k : ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ n * ‖quarticDilatonGroundState k x‖ ^ 2) =
      exp (-k / 4) ^ (n + 1) / 4 * Gamma (((n : ℝ) + 1) / 4) := by
  simp only [quarticDilatonGroundState_einasto_density]
  change einastoMoment n 0 (-k / 4) (-log 4) = _
  rw [einastoMoment_eq]
  simp only [exp_zero, one_mul, exp_neg, exp_log (by norm_num : (0 : ℝ) < 4), div_eq_mul_inv]

theorem quarticDilatonGroundState_radial_moments_integrable (n : ℕ) (k : ℝ) :
    IntegrableOn (fun x => x ^ n * ‖quarticDilatonGroundState k x‖ ^ 2) (Ioi (0 : ℝ)) := by
  simp only [quarticDilatonGroundState_einasto_density]
  exact einastoMoment_integrable n 0 (-k / 4) (-log 4)

/-- The same squared field supplies the already-verified finite enclosed-mass source. -/
theorem quarticDilatonGroundState_enclosed_mass (k r : ℝ) :
    4 * Real.pi * (∫ x in 0..r, x ^ 2 * ‖quarticDilatonGroundState k x‖ ^ 2) =
      einastoMass 0 (-k / 4) (-log 4) r := by
  simp only [quarticDilatonGroundState_einasto_density]
  rfl

theorem quarticDilatonGroundState_absolute_moments (n : ℕ) (k : ℝ) :
    (∫ x : ℝ, |x| ^ n * ‖quarticDilatonGroundState k x‖ ^ 2) =
      exp (-k / 4) ^ (n + 1) / 2 * Gamma (((n : ℝ) + 1) / 4) := by
  calc
    _ = ∫ x : ℝ, |x| ^ n * ‖quarticDilatonGroundState k |x|‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      rw [quarticDilatonGroundState_norm_sq, quarticDilatonGroundState_norm_sq,
        ← abs_pow x 4, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    _ = 2 * ∫ x in Ioi (0 : ℝ), x ^ n * ‖quarticDilatonGroundState k x‖ ^ 2 :=
      integral_comp_abs (f := fun x : ℝ => x ^ n * ‖quarticDilatonGroundState k x‖ ^ 2)
    _ = _ := by
      rw [quarticDilatonGroundState_radial_moments]
      ring

theorem quarticDilatonGroundState_absolute_moments_integrable (n : ℕ) (k : ℝ) :
    Integrable (fun x : ℝ => |x| ^ n * ‖quarticDilatonGroundState k x‖ ^ 2) := by
  have h := (mulS (SchwartzMap.conjSLM (quarticDilatonGroundState k))
    (quarticDilatonGroundState k)).integrable_pow_mul volume n
  convert h using 1
  funext x
  simp only [Real.norm_eq_abs, mulS_apply, norm_mul, SchwartzMap.conjSLM_apply, RCLike.norm_conj, pow_two]

theorem quarticDilatonGroundState_total_norm_density (k : ℝ) :
    (∫ x : ℝ, ‖quarticDilatonGroundState k x‖ ^ 2) = exp (-k / 4) / 2 * Gamma (1 / 4) := by
  simpa only [pow_zero, one_mul, Nat.cast_zero, zero_add, pow_one] using
    quarticDilatonGroundState_absolute_moments 0 k

end GaloisForLFunctions.HTGeometry
