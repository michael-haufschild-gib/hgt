import GaloisForLFunctions.HTGeometry.TraceDynamicsSusceptibility

/-!
# Thermal clock matching and heat-trace dimension

Matched energy and temperature rescalings preserve Gibbs probabilities, susceptibility
and Wightman half-densities. The heat-trace version of the spectral-dimension diagnostic
has an exact slope governed by the thermal energy covariance.

Source: Singh, arXiv:2609.10571, sections 4.2 and 9, equations (24), (79) and (80).
-/

set_option autoImplicit false

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
open _root_.HTGeometry
noncomputable section
variable {α ι : Type*} [Fintype α]

/-- The clock-matched energy and inverse temperature define exactly the same Gibbs law. -/
theorem finiteGibbsStateWeight_clock_match (β z : ℝ) (E : α → ℝ) (a : α) :
    finiteGibbsStateWeight (Real.exp z*β) (fun i => E i/Real.exp z) a =
      finiteGibbsStateWeight β E a := by
  have h (i : α) : -(Real.exp z*β)*(E i/Real.exp z) = -β*E i := by
    field_simp [(Real.exp_pos z).ne']
  simp only [finiteGibbsStateWeight, finiteGibbsPartition, h]

/-- Static means and connected susceptibilities are invariant under a matched clock change. -/
theorem gibbsMean_clock_match (β z : ℝ) (E f : α → ℝ) :
    gibbsMean (Real.exp z*β) (fun i => E i/Real.exp z) f = gibbsMean β E f := by
  simp only [gibbsMean, finiteGibbsStateWeight_clock_match]

theorem susceptibility_clock_match (β z : ℝ) (E : α → ℝ) (O : ι → α → ℝ) :
    susceptibility (Real.exp z*β) (fun i => E i/Real.exp z) O = susceptibility β E O := by
  ext i j
  simp only [susceptibility, gibbsCovariance, gibbsMean_clock_match,
    finiteGibbsStateWeight_clock_match]

/-- The entire quantum half-density, not just its diagonal probability, is clock invariant. -/
theorem finiteKMSWightmanWeight_clock_match (β z : ℝ) (E : α → ℝ) (a b : α) :
    finiteKMSWightmanWeight (Real.exp z*β) (fun i => E i/Real.exp z) a b =
      finiteKMSWightmanWeight β E a b := by
  have h (i : α) : -(Real.exp z*β)*(E i/Real.exp z) = -β*E i := by
    field_simp [(Real.exp_pos z).ne']
  have hpair : -(Real.exp z*β)*((E a/Real.exp z+E b/Real.exp z)/2) =
      -β*((E a+E b)/2) := by field_simp [(Real.exp_pos z).ne']
  simp only [finiteKMSWightmanWeight, finiteGibbsPartition, h, hpair]

theorem gibbsMean_neg (β : ℝ) (E f : α → ℝ) :
    gibbsMean β E (fun a => -f a) = -gibbsMean β E f := by
  simp [gibbsMean]

theorem gibbsCovariance_neg_right (β : ℝ) (E f g : α → ℝ) :
    gibbsCovariance β E f (fun a => -g a) = -gibbsCovariance β E f g := by
  simp only [gibbsCovariance, gibbsMean_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gibbsMean_temperature_one (β : ℝ) (E f : α → ℝ) :
    gibbsMean 1 (fun a => β*E a) f = gibbsMean β E f := by
  simp [gibbsMean, finiteGibbsStateWeight, finiteGibbsPartition]

theorem gibbsCovariance_temperature_one (β : ℝ) (E f g : α → ℝ) :
    gibbsCovariance 1 (fun a => β*E a) f g = gibbsCovariance β E f g := by
  simp [gibbsCovariance, gibbsMean_temperature_one, finiteGibbsStateWeight,
    finiteGibbsPartition]

variable [Nonempty α]

/-- Temperature response is minus the connected energy covariance. -/
theorem hasDerivAt_gibbsMean_temperature (E f : α → ℝ) (β : ℝ) :
    HasDerivAt (fun t => gibbsMean t E f) (-gibbsCovariance β E f E) β := by
  have h := hasDerivAt_gibbsMean_source (fun _ => 0) (fun a => -E a) f β
  simpa only [mul_neg, sub_neg_eq_add, zero_add, gibbsMean_temperature_one,
    gibbsCovariance_temperature_one, gibbsCovariance_neg_right] using h


/-- The logarithmic heat-trace derivative is minus the Gibbs mean energy. -/
theorem hasDerivAt_log_finiteGibbsPartition (E : α → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.log (finiteGibbsPartition s E)) (-gibbsMean t E E) t := by
  have hZ : HasDerivAt (fun s => finiteGibbsPartition s E)
      (∑ a, Real.exp (-t*E a)*(-E a)) t := by
    apply HasDerivAt.fun_sum
    intro a _
    apply ((((hasDerivAt_id t).neg).mul_const (E a)).exp).congr_deriv
    dsimp
    ring
  apply (hZ.log (finiteGibbsPartition_pos t E).ne').congr_deriv
  simp only [gibbsMean, finiteGibbsStateWeight, div_mul_eq_mul_div,
    Finset.sum_div, ← Finset.sum_neg_distrib, mul_neg, neg_div]

/-- Heat-trace spectral dimension for a finite energy spectrum. -/
def finiteHeatSpectralDimension (E : α → ℝ) (t : ℝ) : ℝ :=
  2*t*gibbsMean t E E

/-- The spectral-dimension slope is governed by the thermal energy variance. -/
theorem hasDerivAt_finiteHeatSpectralDimension (E : α → ℝ) (t : ℝ) :
    HasDerivAt (finiteHeatSpectralDimension E)
      (2*gibbsMean t E E-2*t*gibbsCovariance t E E E) t := by
  apply (((hasDerivAt_id t).const_mul 2).mul
    (hasDerivAt_gibbsMean_temperature E E t)).congr_deriv
  dsimp
  ring

/-- Squared Dirac spectra have a nonnegative heat-trace dimension at every forward square time. -/
theorem finiteHeatSpectralDimension_dirac_nonnegative (spectrum : α → ℝ) (s : ℝ) :
    0 ≤ finiteHeatSpectralDimension (fun a => (spectrum a)^(2 : ℕ)) (s^(2 : ℕ)) := by
  unfold finiteHeatSpectralDimension gibbsMean
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (finiteGibbsStateWeight_pos _ _ _).le (sq_nonneg _)

omit [Nonempty α] in
/-- At zero diffusion time every finite spectrum has dimension zero. -/
theorem finiteHeatSpectralDimension_zero (E : α → ℝ) : finiteHeatSpectralDimension E 0 = 0 := by
  simp [finiteHeatSpectralDimension]

/-- The mean-energy definition is exactly minus twice the logarithmic heat-trace slope. -/
theorem finiteHeatSpectralDimension_log_derivative (E : α → ℝ) (t : ℝ) :
    finiteHeatSpectralDimension E t =
      -2*t*deriv (fun s => Real.log (finiteGibbsPartition s E)) t := by
  rw [(hasDerivAt_log_finiteGibbsPartition E t).deriv]
  unfold finiteHeatSpectralDimension
  ring

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
