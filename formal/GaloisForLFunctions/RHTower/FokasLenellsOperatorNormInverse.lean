import GaloisForLFunctions.RHTower.FokasLenellsOperatorNormCauchy
import GaloisForLFunctions.RHTower.FokasLenellsTimeInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Operator-norm differentiation of the constructed Cauchy inverse

Inversion in the actual Banach algebra transports the Cauchy derivative
into R C' R. The inverse and Cauchy families have equivalent operator-norm
regularity. Together with the full jump, their exact gate is compatibility.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual inverse derivative as a bounded operator. -/
def directResolventTimeOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((directResolventUnit q t x)⁻¹).val * directCauchyTimeOperator q t x * ((directResolventUnit q t x)⁻¹).val

theorem directResolventTimeOperator_apply (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    directResolventTimeOperator q t x d = directTimeSolution q t x d := rfl

theorem directResolventTimeOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directResolventTimeOperator q t x‖ ≤ (81/50 : ℝ)*regularReflectionFrequencyBudget q := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
  exact directTimeSolution_bound q t x

private theorem inverse_operator_derivative_of_cauchy (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (hC : HasDerivAt (fun s => directCauchyOperator q s x) (directCauchyTimeOperator q t x) t) :
    HasDerivAt (fun s => ((directResolventUnit q s x)⁻¹).val) (directResolventTimeOperator q t x) t := by
  have hA := (hasDerivAt_const t (1 : Boundary →L[ℂ] Boundary)).fun_sub hC
  simp only [zero_sub] at hA
  change HasDerivAt (fun s => (directResolventUnit q s x).val) (-directCauchyTimeOperator q t x) t at hA
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) (directResolventUnit q t x)).comp_hasDerivAt t hA
  change HasDerivAt (fun s => Ring.inverse (directResolventUnit q s x).val)
    (-(((directResolventUnit q t x)⁻¹).val * (-directCauchyTimeOperator q t x) * ((directResolventUnit q t x)⁻¹).val)) t at hd
  have he : -(((directResolventUnit q t x)⁻¹).val * (-directCauchyTimeOperator q t x) *
      ((directResolventUnit q t x)⁻¹).val) = directResolventTimeOperator q t x := by
    apply ContinuousLinearMap.ext
    intro u
    change -(((directResolventUnit q t x)⁻¹).val (-directCauchyTimeOperator q t x (((directResolventUnit q t x)⁻¹).val u))) =
      ((directResolventUnit q t x)⁻¹).val (directCauchyTimeOperator q t x (((directResolventUnit q t x)⁻¹).val u))
    rw [map_neg,neg_neg]
  rw [he] at hd
  simp only [Ring.inverse_unit] at hd
  exact hd

private theorem inverse_unit_curve_differentiableAt
    (U : ℝ → (Boundary →L[ℂ] Boundary)ˣ) (t : ℝ)
    (hU : DifferentiableAt ℝ (fun s => (U s).val) t) :
    DifferentiableAt ℝ (fun s => ((U s)⁻¹).val) t := by
  have hh := (hasFDerivAt_ringInverse (𝕜 := ℝ) (U t)).differentiableAt.comp t hU
  change DifferentiableAt ℝ (fun s => Ring.inverse (U s).val) t at hh
  simpa only [Ring.inverse_unit] using hh

private theorem inverse_unit_curve_contDiff
    (U : ℝ → (Boundary →L[ℂ] Boundary)ˣ)
    (hU : ContDiff ℝ 1 (fun s => (U s).val)) :
    ContDiff ℝ 1 (fun s => ((U s)⁻¹).val) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hh := (contDiffAt_ringInverse ℝ (U t)).comp t hU.contDiffAt
  change ContDiffAt ℝ 1 (fun s => Ring.inverse (U s).val) t at hh
  simpa only [Ring.inverse_unit] using hh

/-- Operator-norm differentiability of the actual inverse is equivalent to that of its Cauchy operator. -/
theorem directResolventInverse_operator_differentiableAt_iff_cauchy (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => ((directResolventUnit q s x)⁻¹).val) t ↔
      DifferentiableAt ℝ (fun s => directCauchyOperator q s x) t := by
  constructor
  · intro h
    have hh := inverse_unit_curve_differentiableAt (fun s => (directResolventUnit q s x)⁻¹) t h
    simp only [inv_inv] at hh
    have hc := (differentiableAt_const (c := (1 : Boundary →L[ℂ] Boundary))).sub hh
    change DifferentiableAt ℝ (fun s => 1-(1-directCauchyOperator q s x)) t at hc
    simpa only [sub_sub_cancel] using hc
  · intro h
    have hh := (differentiableAt_const (c := (1 : Boundary →L[ℂ] Boundary))).sub h
    exact inverse_unit_curve_differentiableAt (fun s => directResolventUnit q s x) t hh

/-- Global C1 operator-norm regularity is transported in both directions by the constructed inverse. -/
theorem directResolventInverse_operator_contDiff_iff_cauchy (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => ((directResolventUnit q t x)⁻¹).val) ↔
      ContDiff ℝ 1 (fun t => directCauchyOperator q t x) := by
  constructor
  · intro h
    have hh := inverse_unit_curve_contDiff (fun t => (directResolventUnit q t x)⁻¹) h
    simp only [inv_inv] at hh
    have hc := (contDiff_const (c := (1 : Boundary →L[ℂ] Boundary))).sub hh
    change ContDiff ℝ 1 (fun t => 1-(1-directCauchyOperator q t x)) at hc
    simpa only [sub_sub_cancel] using hc
  · intro h
    have hh := (contDiff_const (c := (1 : Boundary →L[ℂ] Boundary))).sub h
    exact inverse_unit_curve_contDiff (fun t => directResolventUnit q t x) hh

/-- The actual jump and resolvent both have their expected operator-norm derivatives exactly at compatibility. -/
theorem directJumpResolvent_operator_hasDerivAt_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    (HasDerivAt (fun s => directJumpPerturbation q s x) (directJumpTimeOperator q t x) t ∧
      HasDerivAt (fun s => ((directResolventUnit q s x)⁻¹).val) (directResolventTimeOperator q t x) t) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  constructor
  · exact fun h => (directJumpPerturbation_operator_hasDerivAt_iff q t x).1 h.1
  · intro hm
    have h := (directJumpCauchy_operator_hasDerivAt_iff q t x).2 hm
    exact ⟨h.1,inverse_operator_derivative_of_cauchy q t x h.2⟩

/-- Global C1 regularity of the jump together with its actual inverse has the same exact nonlinear gate. -/
theorem directJumpResolvent_operator_contDiff_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (ContDiff ℝ 1 (fun t => directJumpPerturbation q t x) ∧
      ContDiff ℝ 1 (fun t => ((directResolventUnit q t x)⁻¹).val)) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [directResolventInverse_operator_contDiff_iff_cauchy]
  exact directJumpCauchy_operator_contDiff_iff q x

theorem directResolventInverse_oddInitialPart_operator_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    HasDerivAt (fun s => ((directResolventUnit (oddInitialPart q) s x)⁻¹).val)
      (directResolventTimeOperator (oddInitialPart q) t x) t :=
  inverse_operator_derivative_of_cauchy _ t x (directCauchyOperator_oddInitialPart_operator_hasDerivAt q t x)

theorem directResolventInverse_oddInitialPart_operator_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContDiff ℝ 1 (fun t => ((directResolventUnit (oddInitialPart q) t x)⁻¹).val) :=
  (directResolventInverse_operator_contDiff_iff_cauchy _ x).2 (directCauchyOperator_oddInitialPart_operator_contDiff q x)

end
end RHTower.FokasLenells
