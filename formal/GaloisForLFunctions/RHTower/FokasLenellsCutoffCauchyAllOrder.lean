import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffAllOrderStability
import GaloisForLFunctions.RHTower.FokasLenellsCutoffCauchyPhase
import GaloisForLFunctions.RHTower.FokasLenellsCauchyMatrixNorm

/-!
# All actual cutoff derivatives survive Cauchy compression exactly

Each generator power is realized by an actual L-infinity symbol. The
existing isometric Cauchy multiplier representation preserves every
operator derivative norm, every cross-order distance, and every optimal
time stability constant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual L-infinity symbol for each cutoff time derivative. -/
def cutoffDerivativeLinfty (a : ℝ) : ℕ → ℝ → Lp ℂ ∞ (volume : Measure ℝ)
  | 0,t => cutoffPhaseLinfty a t
  | n+1,t => lineLinftyProduct (cutoffPhaseTimeLinfty a 0) (cutoffDerivativeLinfty a n t)

/-- Every generator power is the multiplier of the actual derivative symbol. -/
theorem cutoffEvolutionDerivative_eq_lineLinftyMultiplier (a t : ℝ) (n : ℕ) :
    cutoffEvolutionDerivative a n t = lineLinftyMultiplier (cutoffDerivativeLinfty a n t) := by
  induction n with
  | zero => exact (cutoffEvolutionDerivative_zero a t).trans (cutoffEvolution_eq_lineLinftyMultiplier a t)
  | succ n ih =>
    rw [cutoffDerivativeLinfty,← lineLinftyMultiplier_comp,← ih]
    change cutoffEvolutionTimeOperator a 0 ^ (n+1) * cutoffEvolution a t =
      cutoffEvolutionTimeOperator a 0 * (cutoffEvolutionTimeOperator a 0 ^ n * cutoffEvolution a t)
    rw [pow_succ',mul_assoc]

/-- The essential norm of each actual derivative symbol is the exact generator-power norm. -/
theorem norm_cutoffDerivativeLinfty (a t : ℝ) (n : ℕ) :
    ‖cutoffDerivativeLinfty a n t‖ = cutoffPhaseBudget a ^ n := by
  rw [← norm_lineLinftyMultiplier,← cutoffEvolutionDerivative_eq_lineLinftyMultiplier,
    norm_cutoffEvolutionDerivative]

/-- The actual signed Cauchy compression of each cutoff operator derivative. -/
def cutoffCauchyDerivative (a : ℝ) (n : ℕ) (t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (cutoffEvolutionDerivative a n t)

/-- Zeroth compressed derivative is the existing Cauchy evolution. -/
theorem cutoffCauchyDerivative_zero (a t : ℝ) :
    cutoffCauchyDerivative a 0 t = cutoffCauchyEvolution a t := by
  rw [cutoffCauchyDerivative,cutoffEvolutionDerivative_zero]
  rfl

/-- First compressed derivative is the existing Cauchy time operator. -/
theorem cutoffCauchyDerivative_one (a t : ℝ) :
    cutoffCauchyDerivative a 1 t = cutoffCauchyTimeOperator a t := by
  rw [cutoffCauchyDerivative,cutoffEvolutionDerivative_one]
  rfl

/-- The compressed derivative uses the actual isometric Cauchy representation. -/
theorem cutoffCauchyDerivative_eq_cauchyLinftyMultiplier (a t : ℝ) (n : ℕ) :
    cutoffCauchyDerivative a n t = cauchyLinftyMultiplier (cutoffDerivativeLinfty a n t) := by
  rw [cutoffCauchyDerivative,cutoffEvolutionDerivative_eq_lineLinftyMultiplier,cauchyLinftyMultiplier_apply]

/-- Cauchy compression preserves every derivative norm exactly. -/
theorem norm_cutoffCauchyDerivative (a t : ℝ) (n : ℕ) :
    ‖cutoffCauchyDerivative a n t‖ = cutoffPhaseBudget a ^ n := by
  rw [cutoffCauchyDerivative_eq_cauchyLinftyMultiplier,norm_cauchyLinftyMultiplier,norm_cutoffDerivativeLinfty]

/-- Cauchy compression preserves distances across all derivative orders, times, and cutoffs. -/
theorem norm_cutoffCauchyDerivative_sub_eq_uncompressed (a b s t : ℝ) (m n : ℕ) :
    ‖cutoffCauchyDerivative a m s - cutoffCauchyDerivative b n t‖ =
      ‖cutoffEvolutionDerivative a m s - cutoffEvolutionDerivative b n t‖ := by
  rw [cutoffCauchyDerivative_eq_cauchyLinftyMultiplier,cutoffCauchyDerivative_eq_cauchyLinftyMultiplier,
    cutoffEvolutionDerivative_eq_lineLinftyMultiplier,cutoffEvolutionDerivative_eq_lineLinftyMultiplier,
    ← map_sub,← map_sub,norm_cauchyLinftyMultiplier,norm_lineLinftyMultiplier]

/-- Every compressed derivative differentiates to its next order in operator norm. -/
theorem cutoffCauchyDerivative_hasDerivAt (a t : ℝ) (n : ℕ) :
    HasDerivAt (cutoffCauchyDerivative a n) (cutoffCauchyDerivative a (n+1) t) t :=
  ((ContinuousLinearMap.compL ℂ SoninL2 SoninL2 SoninL2 negativeCauchy).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (cutoffEvolutionDerivative_hasDerivAt a t n)

/-- Every compressed derivative is real analytic in operator norm. -/
theorem cutoffCauchyDerivative_analyticAt (a t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (cutoffCauchyDerivative a n) t :=
  (((ContinuousLinearMap.compL ℂ SoninL2 SoninL2 SoninL2 negativeCauchy).restrictScalars ℝ).analyticAt _).comp
    (cutoffEvolutionDerivative_analyticAt a t n)

/-- The actual Cauchy evolution is real analytic in operator norm. -/
theorem cutoffCauchyEvolution_analyticAt (a t : ℝ) :
    AnalyticAt ℝ (cutoffCauchyEvolution a) t := by
  have h := cutoffCauchyDerivative_analyticAt a t 0
  simpa only [show cutoffCauchyDerivative a 0 = cutoffCauchyEvolution a from funext (cutoffCauchyDerivative_zero a)] using h

/-- All iterated derivatives of the actual Cauchy evolution are the compressed powers. -/
theorem iteratedDeriv_cutoffCauchyEvolution (a : ℝ) (n : ℕ) :
    iteratedDeriv n (cutoffCauchyEvolution a) = cutoffCauchyDerivative a n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact funext fun t => (cutoffCauchyDerivative_zero a t).symm
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (cutoffCauchyDerivative_hasDerivAt a t n).deriv

/-- The exact norm law holds for actual iterated Cauchy derivatives. -/
theorem norm_iteratedDeriv_cutoffCauchyEvolution (a t : ℝ) (n : ℕ) :
    ‖iteratedDeriv n (cutoffCauchyEvolution a) t‖ = cutoffPhaseBudget a ^ n := by
  rw [iteratedDeriv_cutoffCauchyEvolution,norm_cutoffCauchyDerivative]

/-- Every compressed derivative has exactly the same optimal Lipschitz constant. -/
theorem cutoffCauchyDerivative_lipschitz_iff (a L : ℝ) (n : ℕ) :
    (∀ s t, ‖cutoffCauchyDerivative a n s - cutoffCauchyDerivative a n t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ^ (n+1) ≤ L := by
  simp_rw [norm_cutoffCauchyDerivative_sub_eq_uncompressed]
  exact cutoffEvolutionDerivative_lipschitz_iff a L n

/-- Cauchy compression retains the blow-up of every positive derivative norm. -/
theorem cutoffCauchyDerivative_norm_tendsto_atBot (t : ℝ) (n : ℕ) :
    Tendsto (fun a => ‖cutoffCauchyDerivative a (n+1) t‖) atBot atTop := by
  simpa only [norm_cutoffEvolutionDerivative,norm_cutoffCauchyDerivative] using
    cutoffEvolutionDerivative_norm_tendsto_atBot t n

/-- No derivative order regains uniform cutoff stability after Cauchy compression. -/
theorem cutoffCauchyDerivative_no_uniform_lipschitz_constant (L : ℝ) (n : ℕ) :
    ¬ ∀ a s t : ℝ, ‖cutoffCauchyDerivative a n s - cutoffCauchyDerivative a n t‖ ≤ L * ‖s-t‖ := by
  simpa only [norm_cutoffCauchyDerivative_sub_eq_uncompressed] using
    cutoffEvolutionDerivative_no_uniform_lipschitz_constant L n

end
end RHTower.FokasLenells
