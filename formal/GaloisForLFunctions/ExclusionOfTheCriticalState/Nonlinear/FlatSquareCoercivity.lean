import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatEvenIntegralEnergy
import Mathlib.Analysis.Convex.Integral

/-!
# Sharp nonlinear norm coercivity on probability spaces

The flat potential becomes strictly convex as a function of squared
amplitude: `s ↦ χ(√s)`. Its derivative is half the secant slope of the
strictly convex gradient through zero. Jensen's inequality therefore
gives `χ(‖f‖₂) ≤ ∫ χ(|f|)`, with equality exactly for constant absolute
amplitude. Finite-volume normalization retains the precise measure
factor. Infinite flatness removes quadratic coercivity, but does not
remove this sharp nonlinear control.
-/

open MeasureTheory Set Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

private theorem curvature_strictMono : StrictMonoOn expNegInvGlue (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  rw [expNegInvGlue, if_neg (not_le_of_gt hx), expNegInvGlue, if_neg (not_le_of_gt hy),
    Real.exp_lt_exp]
  exact neg_lt_neg ((inv_lt_inv₀ hy hx).mpr hxy)

/-- The flat gradient is strictly convex on the nonnegative half-line. -/
theorem gradient_strictConvex_nonneg : StrictConvexOn ℝ (Ici 0) gradient := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0)
    (gradient_contDiff 0).continuous.continuousOn
  intro x hx y hy hxy
  rw [interior_Ici] at hx hy
  rw [(gradient_hasDerivAt x).deriv, (gradient_hasDerivAt y).deriv]
  exact curvature_strictMono hx hy hxy

/-- The potential viewed as a function of squared amplitude. -/
def squarePotential (s : ℝ) : ℝ := potential (Real.sqrt s)

theorem squarePotential_continuous : Continuous squarePotential :=
  (potential_contDiff 0).continuous.comp Real.continuous_sqrt

theorem squarePotential_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt squarePotential (gradient (Real.sqrt s) / (2 * Real.sqrt s)) s := by
  have h : HasDerivAt squarePotential
      (gradient (Real.sqrt s) * (1 / (2 * Real.sqrt s))) s :=
    (potential_hasDerivAt (Real.sqrt s)).comp s (Real.hasDerivAt_sqrt hs.ne')
  simpa only [div_eq_mul_inv, one_mul] using h

/-- Increasing gradient secants give strict convexity in squared amplitude. -/
theorem squarePotential_strictConvex : StrictConvexOn ℝ (Ici 0) squarePotential := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) squarePotential_continuous.continuousOn
  intro x hx y hy hxy
  rw [interior_Ici, mem_Ioi] at hx hy
  rw [(squarePotential_hasDerivAt hx).deriv, (squarePotential_hasDerivAt hy).deriv]
  have hs := gradient_strictConvex_nonneg.secant_strict_mono
    (show (0 : ℝ) ∈ Ici 0 by simp only [mem_Ici, le_refl])
    (show Real.sqrt x ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using Real.sqrt_nonneg x)
    (show Real.sqrt y ∈ Ici (0 : ℝ) by simpa only [mem_Ici] using Real.sqrt_nonneg y)
    (Real.sqrt_pos.mpr hx).ne' (Real.sqrt_pos.mpr hy).ne' (Real.sqrt_lt_sqrt hx.le hxy)
  rw [gradient_zero, sub_zero, sub_zero, sub_zero, sub_zero] at hs
  have h := mul_lt_mul_of_pos_right hs (by norm_num : (0 : ℝ) < 1 / 2)
  convert h using 1 <;> ring

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem evenIntegralEnergy_integral (f : Lp ℝ 2 μ) :
    evenIntegralEnergy f = ∫ x, evenPotential (f x) ∂μ := by
  rw [evenIntegralEnergy, integralEnergy, integralEnergy,
    ← integral_add (integrable_potential f) (integrable_potential (-f))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg f] with x hx
  rw [hx]
  rfl

theorem integrable_evenPotential (f : Lp ℝ 2 μ) : Integrable (fun x => evenPotential (f x)) μ := by
  apply ((integrable_potential f).add (integrable_potential (-f))).congr
  filter_upwards [Lp.coeFn_neg f] with x hx
  simp only [Pi.add_apply]
  rw [hx]
  rfl

private theorem integral_square_norm (f : Lp ℝ 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by change f x ^ 2 = f x * f x; ring

private theorem squarePotential_square (t : ℝ) : squarePotential (t ^ 2) = evenPotential t := by
  rw [squarePotential, Real.sqrt_sq_eq_abs, evenPotential_eq_potential_abs]

private theorem evenPotential_norm (f : Lp ℝ 2 μ) :
    evenPotential ‖f‖ = potential ‖f‖ := by
  rw [evenPotential_eq_potential_abs, abs_of_nonneg (norm_nonneg f)]

private theorem integrable_squarePotential (f : Lp ℝ 2 μ) :
    Integrable (squarePotential ∘ fun x => f x ^ 2) μ := by
  change Integrable (fun x => squarePotential (f x ^ 2)) μ
  simpa only [squarePotential_square] using integrable_evenPotential f

/-- Sharp nonlinear coercivity on every probability space, without boundedness assumptions on f. -/
theorem evenIntegralEnergy_probability_coercivity [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    potential ‖f‖ ≤ evenIntegralEnergy f := by
  have h := squarePotential_strictConvex.convexOn.map_integral_le
    squarePotential_continuous.continuousOn isClosed_Ici
    (Eventually.of_forall fun x => show f x ^ 2 ∈ Ici 0 by
      simpa only [mem_Ici] using sq_nonneg (f x))
    (Lp.memLp f).integrable_sq (integrable_squarePotential f)
  simpa only [integral_square_norm, squarePotential_square, evenPotential_norm,
    ← evenIntegralEnergy_integral] using h

/-- Equality in the sharp bound occurs precisely at constant absolute amplitude. -/
theorem evenIntegralEnergy_probability_eq_iff [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    evenIntegralEnergy f = potential ‖f‖ ↔ ∀ᵐ x ∂μ, |f x| = ‖f‖ := by
  constructor
  · intro he
    have h := squarePotential_strictConvex.ae_eq_const_or_map_average_lt
      squarePotential_continuous.continuousOn isClosed_Ici
      (Eventually.of_forall fun x => show f x ^ 2 ∈ Ici 0 by
        simpa only [mem_Ici] using sq_nonneg (f x))
      (Lp.memLp f).integrable_sq (integrable_squarePotential f)
    simp only [average_eq_integral, integral_square_norm, squarePotential_square,
      evenPotential_norm] at h
    rcases h with h | h
    · filter_upwards [h] with x hx
      have hh := congrArg Real.sqrt hx
      simpa only [Function.const, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)] using hh
    · rw [← evenIntegralEnergy_integral, he] at h
      exact False.elim (lt_irrefl _ h)
  · intro he
    rw [evenIntegralEnergy_integral]
    calc
      (∫ x, evenPotential (f x) ∂μ) = ∫ _, potential ‖f‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [evenPotential_eq_potential_abs, hx]
      _ = potential ‖f‖ := by simp

/-- Finite-volume normalization gives the exact mass-dependent coercivity law. -/
theorem evenIntegralEnergy_finite_coercivity [IsFiniteMeasure μ] [NeZero μ] (f : Lp ℝ 2 μ) :
    potential (Real.sqrt ((μ.real univ)⁻¹ * ‖f‖ ^ 2)) ≤
      (μ.real univ)⁻¹ * evenIntegralEnergy f := by
  have h := squarePotential_strictConvex.convexOn.map_average_le
    squarePotential_continuous.continuousOn isClosed_Ici
    (Eventually.of_forall fun x => show f x ^ 2 ∈ Ici 0 by
      simpa only [mem_Ici] using sq_nonneg (f x))
    (Lp.memLp f).integrable_sq (integrable_squarePotential f)
  simp only [average_eq, smul_eq_mul, integral_square_norm, squarePotential_square,
    ← evenIntegralEnergy_integral] at h
  exact h

#print axioms squarePotential_strictConvex
#print axioms evenIntegralEnergy_probability_coercivity
#print axioms evenIntegralEnergy_probability_eq_iff
#print axioms evenIntegralEnergy_finite_coercivity
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
