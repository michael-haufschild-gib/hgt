import GaloisForLFunctions.HTGeometry.Thermofield.KMSAutocorrelation
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# KMS overlap bounds for finite Gibbs spectra

The finite Gibbs probabilities turn the scalar KMS kernels into a normalized
positive spectral mixture. The mixed-kernel estimate gives a dimension-free
bound on its integrated square, with quadratic coefficient one half.
-/

noncomputable section
open MeasureTheory intervalIntegral
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.Thermofield
open _root_.HTGeometry

variable {α : Type*} [Fintype α] [Nonempty α]

/-- A finite Gibbs mixture of KMS kernels with spectral gaps `2 * gap a`. -/
def gibbsKMSAutocorrelation (β : ℝ) (energy gap : α → ℝ) (u : ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β energy a * kmsKernel (gap a) u

/-- Its integrated susceptibility. -/
def gibbsKMSSusceptibility (β : ℝ) (energy gap : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β energy a * kmsMean (gap a)

omit [Nonempty α] in
theorem continuous_gibbsKMSAutocorrelation (β : ℝ) (energy gap : α → ℝ) :
    Continuous (gibbsKMSAutocorrelation β energy gap) := by
  apply continuous_finsetSum
  intro a _
  exact continuous_const.mul (continuous_kmsKernel (gap a))

theorem gibbsKMSSusceptibility_nonneg (β : ℝ) (energy gap : α → ℝ) :
    0 ≤ gibbsKMSSusceptibility β energy gap :=
  Finset.sum_nonneg fun a _ => mul_nonneg
    (finiteGibbsStateWeight_pos β energy a).le (kmsMean_nonneg (gap a))

/-- Integration reads the susceptibility of every spectral gap. -/
theorem integral_gibbsKMSAutocorrelation (β : ℝ) (energy gap : α → ℝ) :
    (∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u) =
      gibbsKMSSusceptibility β energy gap := by
  have hi (a : α) : IntervalIntegrable
      (fun u => finiteGibbsStateWeight β energy a * kmsKernel (gap a) u) volume 0 1 :=
    (continuous_const.mul (continuous_kmsKernel (gap a))).intervalIntegrable _ _
  simp only [gibbsKMSAutocorrelation]
  rw [intervalIntegral.integral_finsetSum (fun a _ => hi a)]
  simp only [intervalIntegral.integral_const_mul, integral_kmsKernel, gibbsKMSSusceptibility]

omit [Nonempty α] in
private theorem square_expansion (β : ℝ) (energy gap : α → ℝ) (u : ℝ) :
    gibbsKMSAutocorrelation β energy gap u ^ 2 =
      ∑ a, ∑ b, (finiteGibbsStateWeight β energy a * finiteGibbsStateWeight β energy b) *
        (kmsKernel (gap a) u * kmsKernel (gap b) u) := by
  rw [gibbsKMSAutocorrelation, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The finite Gibbs mixture satisfies the improved KMS square bound. -/
theorem integral_gibbsKMSAutocorrelation_sq_le (β : ℝ) (energy gap : α → ℝ) :
    (∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u ^ 2) ≤
      gibbsKMSSusceptibility β energy gap / 2 +
        gibbsKMSSusceptibility β energy gap ^ 2 / 2 := by
  let w := finiteGibbsStateWeight β energy
  let c := fun a => kmsMean (gap a)
  have hw : ∑ a, w a = 1 := sum_finiteGibbsStateWeight_eq_one β energy
  have hcont (a b : α) : Continuous (fun u =>
      (w a*w b) * (kmsKernel (gap a) u * kmsKernel (gap b) u)) :=
    continuous_const.mul ((continuous_kmsKernel _).mul (continuous_kmsKernel _))
  have hexpand : (∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u ^ 2) =
      ∑ a, ∑ b, (w a*w b) * (∫ u in (0:ℝ)..1, kmsKernel (gap a) u * kmsKernel (gap b) u) := by
    simp_rw [square_expansion]
    rw [intervalIntegral.integral_finsetSum (fun a _ =>
      (continuous_finsetSum _ (fun b _ => hcont a b)).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [intervalIntegral.integral_finsetSum (fun b _ => (hcont a b).intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hexpand]
  calc
    _ ≤ ∑ a, ∑ b, (w a*w b) * ((c a+c b)/4+c a*c b/2) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (integral_kmsKernel_mul_le _ _)
        (mul_nonneg (finiteGibbsStateWeight_pos β energy a).le
          (finiteGibbsStateWeight_pos β energy b).le)
    _ = _ := by
      have hpoint (a b : α) : (w a*w b) * ((c a+c b)/4+c a*c b/2) =
          ((w a*c a)*w b)/4 + (w a*(w b*c b))/4 +
            ((w a*c a)*(w b*c b))/2 := by ring
      simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hw]
      change _ = (∑ a, w a*c a)/2+(∑ a, w a*c a)^2/2
      ring

/-- The bound can be stated using only the literal integrated autocorrelation. -/
theorem gibbsKMS_overlap_bound (β : ℝ) (energy gap : α → ℝ) :
    (∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u ^ 2) ≤
      ((∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u) +
        (∫ u in (0:ℝ)..1, gibbsKMSAutocorrelation β energy gap u)^2) / 2 := by
  rw [integral_gibbsKMSAutocorrelation]
  convert integral_gibbsKMSAutocorrelation_sq_le β energy gap using 1
  ring

end GaloisForLFunctions.HTGeometry.Thermofield
