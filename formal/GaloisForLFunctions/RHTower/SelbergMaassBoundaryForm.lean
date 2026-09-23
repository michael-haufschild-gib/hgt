import GaloisForLFunctions.RHTower.SelbergMaassBesselRemainder
import GaloisForLFunctions.RHTower.SelbergMaassBoundaryTrace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual Maass cusp energy as a Bessel boundary form plus squares

The signed modal quarter-energy is dominated by its two nonnegative derivative
energies plus quarter hyperbolic mass. Their actual Parseval sum is integrable
on the entire cusp, which justifies the countable mode/height interchange.

The exact complex Bessel identity for each nonzero mode, and the proved vanishing
constant channel, therefore sum to the actual boundary form on the literal
Maass trace plus a convergent series of nonnegative square integrals. The source
flux identity identifies the same total with the lower flux and actual tail mass.
The compact quotient-core quarter-energy estimate is not asserted.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm
open SelbergMaassBessel SelbergMaassFourier SelbergMaassParseval SelbergMaassFlux
open SelbergMaassTailEnergy SelbergMaassTrace SelbergBoundaryOperator
noncomputable section

private def majorant (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (y : ℝ) (n : ℤ) : ℝ :=
  signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) * Complex.normSq (maassCoefficient N f n y) +
    Complex.normSq (deriv (maassCoefficient N f n) y) +
      (1 / (4 * y ^ (2 : ℕ))) * Complex.normSq (maassCoefficient N f n y)

private theorem majorant_hasSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasSum (majorant N f y) (gradientEnergy N f y + (1 / (4 * y ^ (2 : ℕ))) * mass N f y) :=
  (gradientEnergy_hasSum N f hy).add ((mass_hasSum N f hy).mul_left (1 / (4 * y ^ (2 : ℕ))))

private theorem energy_norm_le_majorant (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    ‖energy (modeRate N n) (maassCoefficient N f n) y‖ ≤ majorant N f y n := by
  rw [energy, modeRate_sq, Real.norm_eq_abs, abs_le]
  unfold majorant
  have hD := Complex.normSq_nonneg (deriv (maassCoefficient N f n) y)
  have hk := mul_nonneg (sq_nonneg (signedFrequency (N + 1 : ℕ) n))
    (Complex.normSq_nonneg (maassCoefficient N f n y))
  have hm := mul_nonneg (by positivity : 0 ≤ 1 / (4 * y ^ (2 : ℕ)))
    (Complex.normSq_nonneg (maassCoefficient N f n y))
  constructor <;> nlinarith

private theorem majorant_tsum_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ∑' n : ℤ, majorant N f y n) (Ioi Y) := by
  apply ((gradientEnergy_tail_integrable N lam f hY).add
    ((hyperbolicMass_tail_integrable N lam f hY).const_mul (1 / 4 : ℝ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [(majorant_hasSum N f (hY.trans hy)).tsum_eq]
  simp only [Pi.add_apply]
  ring

/-- The actual signed modal tail integrals sum to the full physical quarter-energy tail. -/
theorem maass_energy_tail_hasSum (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun n : ℤ => ∫ y in Ioi Y, energy (modeRate N n) (maassCoefficient N f n) y)
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∫ y in Ioi Y, quarterSlice N f y) := by
  rw [← integral_const_mul]
  apply hasSum_integral_of_dominated_convergence (fun n y => majorant N f y n)
    (fun n => (mode_energy_integrable N lam f n hY).aestronglyMeasurable) ?_ ?_
    (majorant_tsum_integrable N lam f hY) ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact energy_norm_le_majorant N f n (hY.trans hy)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (majorant_hasSum N f (hY.trans hy)).summable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply (maass_quarter_hasSum N f (hY.trans hy)).congr_fun
    intro n
    exact mode_energy_eq_modalQuarter N f n y

/-- The physical-height response equals the existing Bessel seam at the actual mode frequency. -/
theorem response_eq_seam (N : ℕ) {n : ℤ} (hn : n ≠ 0) (T : ℝ) :
    response (modeRate N n) (Real.exp T) = SelbergBesselModes.seam (Real.log (N + 1 : ℕ)) T n := by
  have hf : Real.exp (SelbergBesselModes.modeLog (Real.log (N + 1 : ℕ)) n) = modeRate N n := by
    rw [SelbergBesselModes.mode_frequency _ ⟨n, hn⟩,
      Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
    unfold modeRate signedFrequency
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
  rw [SelbergBesselModes.seam, if_neg hn, response_eq_outgoing (modeRate_pos N hn) (Real.exp_pos T),
    Real.log_exp]
  congr 1
  rw [← hf, Real.log_exp]

/-- The literal nonzero-mode complex square integral, with the absent constant channel assigned zero. -/
def modeSquareTail (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (T : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else ∫ y in Ioi (Real.exp T), remainder (modeRate N n) (maassCoefficient N f n) y

/-- Every actual integrated mode square is nonnegative. -/
theorem modeSquareTail_nonneg (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (T : ℝ) (n : ℤ) : 0 ≤ modeSquareTail N f T n := by
  unfold modeSquareTail
  split_ifs
  · exact le_rfl
  · exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

private theorem mode_tail_trace_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (T : ℝ) (n : ℤ) :
    (∫ y in Ioi (Real.exp T), energy (modeRate N n) (maassCoefficient N f n) y) =
      modeSquareTail N f T n + SelbergBesselModes.seam (Real.log (N + 1 : ℕ)) T n *
        Complex.normSq (maassCoefficient N f n (Real.exp T)) := by
  by_cases hn : n = 0
  · subst n
    simp only [modeSquareTail, SelbergBesselModes.seam, if_true, zero_mul, add_zero]
    have he : ∀ᵐ y ∂volume.restrict (Ioi (Real.exp T)),
        energy (modeRate N 0) (maassCoefficient N f 0) y = 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact constant_mode_energy_zero N lam f ((Real.exp_pos T).trans hy)
    rw [integral_congr_ae he, integral_zero]
  · rw [modeSquareTail, if_neg hn, ← response_eq_seam N hn T]
    exact mode_boundary_identity N lam f n hn (Real.exp_pos T)

/-- The full series of actual mode square integrals converges to physical tail energy minus boundary form. -/
theorem maass_square_tail_hasSum (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    HasSum (modeSquareTail N f T)
      (((N + 1 : ℕ) : ℝ)⁻¹ * (∫ y in Ioi (Real.exp T), quarterSlice N f y) -
        boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N f T)) := by
  have hB : HasSum (fun n : ℤ => SelbergBesselModes.seam (Real.log (N + 1 : ℕ)) T n *
      Complex.normSq (maassCoefficient N f n (Real.exp T)))
      (boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N f T)) :=
    (maass_seam_summable N f T).hasSum
  apply ((maass_energy_tail_hasSum N lam f (Real.exp_pos T)).sub hB).congr_fun
  intro n
  have h := mode_tail_trace_identity N lam f T n
  linarith

/-- Exact full-cusp decomposition on the actual Maass boundary trace, retaining every square remainder. -/
theorem maass_boundary_square_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    ((N + 1 : ℕ) : ℝ)⁻¹ * (∫ y in Ioi (Real.exp T), quarterSlice N f y) =
      boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N f T) +
        ∑' n : ℤ, modeSquareTail N f T n := by
  rw [(maass_square_tail_hasSum N lam f T).tsum_eq]
  ring

/-- The actual Bessel boundary form is a lower bound for the full physical cusp quarter-energy. -/
theorem maass_boundary_form_lower_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N f T) ≤
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ y in Ioi (Real.exp T), quarterSlice N f y := by
  rw [maass_boundary_square_identity N lam f T]
  exact le_add_of_nonneg_right (tsum_nonneg (modeSquareTail_nonneg N f T))

/-- The actual outgoing flux and spectral tail mass equal the Bessel boundary form plus convergent squares. -/
theorem maass_flux_boundary_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    -flux N f (Real.exp T) + ((lam : ℝ) - 1 / 4) *
        (∫ y in Ioi (Real.exp T), mass N f y / y ^ (2 : ℕ)) =
      boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N f T) +
        ∑' n : ℤ, modeSquareTail N f T n := by
  rw [← quarterSlice_tail_identity N lam f (Real.exp_pos T)]
  exact maass_boundary_square_identity N lam f T

end
end GaloisForLFunctions.RHTower.SelbergMaassBoundaryForm
