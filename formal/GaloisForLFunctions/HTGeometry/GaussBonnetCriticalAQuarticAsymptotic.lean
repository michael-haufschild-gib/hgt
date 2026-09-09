import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalASharpRanges
import Mathlib.Analysis.Calculus.Taylor

/-!
# Actual quartic critical asymptotics in logarithmic and physical radius

Apply Taylor's little-o theorem to the genuine critical Gibbs function
from arXiv:2609.00025. Its proven derivative family supplies all required
smoothness. The free-energy gap divided by the fourth power of displacement
converges to an explicit positive coefficient. Transport through log gives
the corresponding theorem for the original physical-radius free energy.
-/
noncomputable section
open Real Filter Asymptotics
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbCriticalALogQuarticCoefficient (x θ : ℝ) : ℝ :=
  exp x * (1 - 2 * egbCriticalAShape θ) / (12 * (1 + 2 * egbCriticalAShape θ))
def egbCriticalARadialQuarticCoefficient (x θ : ℝ) : ℝ :=
  (1 - 2 * egbCriticalAShape θ) / (12 * exp x ^ 3 * (1 + 2 * egbCriticalAShape θ))

theorem egbCriticalALogQuarticCoefficient_pos (x θ : ℝ) : 0 < egbCriticalALogQuarticCoefficient x θ := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hp : 0 < 1 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  unfold egbCriticalALogQuarticCoefficient
  positivity

theorem egbCriticalARadialQuarticCoefficient_pos (x θ : ℝ) : 0 < egbCriticalARadialQuarticCoefficient x θ := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hp : 0 < 1 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  unfold egbCriticalARadialQuarticCoefficient
  positivity

/-- The actual derivative formulas discharge every smoothness requirement. -/
theorem egbCriticalALogGibbs_contDiff (x θ l : ℝ) (n : ℕ) : ContDiff ℝ n (egbCriticalALogGibbs x θ l) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := (n : ℕ∞))
  intro m _
  cases m with
  | zero =>
    rw [iteratedDeriv_zero]
    exact fun u => (egbCriticalALogGibbs_hasDerivAt x θ l u).differentiableAt
  | succ m =>
    cases m with
    | zero =>
      rw [iteratedDeriv_one]
      exact fun u => (egbCriticalALogGibbs_second_hasDerivAt x θ l u).differentiableAt
    | succ m =>
      change Differentiable ℝ (iteratedDeriv (m + 2) (egbCriticalALogGibbs x θ l))
      rw [egbCriticalALogGibbs_iteratedDeriv]
      exact fun u => (egbCriticalAGibbsJet_hasDerivAt x θ u (m + 2)).differentiableAt

/-- The actual Taylor polynomial has only a constant term and a quartic term. -/
theorem egbCriticalALogGibbs_taylor_four (x θ l u : ℝ) :
    taylorWithinEval (egbCriticalALogGibbs x θ l) 4 Set.univ x u =
      egbCriticalALogGibbs x θ l x + egbCriticalALogQuarticCoefficient x θ * (u - x) ^ 4 := by
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDeriv_one,
    egbCriticalALogGibbs_first_derivative_zero, egbCriticalALogGibbs_second_derivative_zero,
    egbCriticalALogGibbs_third_derivative_zero, egbCriticalALogGibbs_fourth_derivative, smul_eq_mul]
  unfold egbCriticalALogQuarticCoefficient
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalALogGibbs_quartic_littleO (x θ l : ℝ) :
    (fun u => egbCriticalALogGibbs x θ l u -
      (egbCriticalALogGibbs x θ l x + egbCriticalALogQuarticCoefficient x θ * (u - x) ^ 4)) =o[nhds x]
        (fun u => (u - x) ^ 4) := by
  have h := taylor_isLittleO_univ (x₀ := x) (egbCriticalALogGibbs_contDiff x θ l 4)
  simpa only [egbCriticalALogGibbs_taylor_four] using h

/-- A genuine punctured-neighborhood limit, rather than a formal truncated series. -/
theorem egbCriticalALogGibbs_quartic_limit (x θ l : ℝ) :
    Tendsto (fun u => (egbCriticalALogGibbs x θ l u - egbCriticalALogGibbs x θ l x) / (u - x) ^ 4)
      (𝓝[≠] x) (nhds (egbCriticalALogQuarticCoefficient x θ)) := by
  have h := ((egbCriticalALogGibbs_quartic_littleO x θ l).tendsto_div_nhds_zero.mono_left (show (𝓝[≠] x) ≤ nhds x from nhdsWithin_le_nhds)).add
    (tendsto_const_nhds (x := egbCriticalALogQuarticCoefficient x θ))
  have he : (fun u => (egbCriticalALogGibbs x θ l u - egbCriticalALogGibbs x θ l x) / (u - x) ^ 4) =ᶠ[𝓝[≠] x]
      (fun u => (egbCriticalALogGibbs x θ l u -
        (egbCriticalALogGibbs x θ l x + egbCriticalALogQuarticCoefficient x θ * (u - x) ^ 4)) / (u - x) ^ 4 +
          egbCriticalALogQuarticCoefficient x θ) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hn : u - x ≠ 0 := sub_ne_zero.mpr hu
    field_simp
    ring
  exact (tendsto_congr' he).2 (by simpa only [zero_add] using h)

/-- The logarithmic coefficient is the previously computed actual stiffness divided by 24. -/
theorem egbCriticalALogQuarticCoefficient_stiffness (x θ : ℝ) :
    egbCriticalALogQuarticCoefficient x θ / exp x = egbCriticalAStiffness θ / 24 := by
  unfold egbCriticalALogQuarticCoefficient egbCriticalAStiffness
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

/-- The original physical-radius Gibbs function also has a strictly positive quartic leading term. -/
theorem egbCriticalA_radial_quartic_limit (x θ l : ℝ) :
    Tendsto (fun r =>
      (egbOffShellGibbsA (egbCriticalAPressure x θ) (egbCriticalATemperature x θ)
        (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) l r -
       egbOffShellGibbsA (egbCriticalAPressure x θ) (egbCriticalATemperature x θ)
        (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) l (exp x)) / (r - exp x) ^ 4)
      (𝓝[≠] (exp x)) (nhds (egbCriticalARadialQuarticCoefficient x θ)) := by
  have hpN : ∀ᶠ r : ℝ in nhds (exp x), 0 < r := isOpen_Ioi.mem_nhds (exp_pos x)
  have hp : ∀ᶠ r : ℝ in 𝓝[≠] (exp x), 0 < r := hpN.filter_mono nhdsWithin_le_nhds
  have hlog : Tendsto log (𝓝[≠] (exp x)) (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [log_exp] using (continuousAt_log (exp_ne_zero x)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, hp] with r hr hrp
      change log r ≠ x
      intro he
      have hxe : r = exp x := by rw [← exp_log hrp, he]
      exact hr hxe
  have hs : Tendsto (fun r => (log r - x) / (r - exp x)) (𝓝[≠] (exp x)) (nhds (1 / exp x)) := by
    have he : slope log (exp x) = (fun r => (log r - x) / (r - exp x)) := by
      funext r
      rw [slope_def_field, log_exp]
    have h := (hasDerivAt_log (exp_ne_zero x)).tendsto_slope
    rw [he] at h
    simpa only [one_div] using h
  have h := ((egbCriticalALogGibbs_quartic_limit x θ l).comp hlog).mul (hs.pow 4)
  have hc : egbCriticalALogQuarticCoefficient x θ * (1 / exp x) ^ 4 = egbCriticalARadialQuarticCoefficient x θ := by
    unfold egbCriticalALogQuarticCoefficient egbCriticalARadialQuarticCoefficient
    have hb := (egbCriticalAShape_bounds θ).1
    field_simp
  rw [hc] at h
  have he : (fun r =>
      (egbOffShellGibbsA (egbCriticalAPressure x θ) (egbCriticalATemperature x θ)
        (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) l r -
       egbOffShellGibbsA (egbCriticalAPressure x θ) (egbCriticalATemperature x θ)
        (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) l (exp x)) / (r - exp x) ^ 4) =ᶠ[𝓝[≠] (exp x)]
      (fun r => ((egbCriticalALogGibbs x θ l (log r) - egbCriticalALogGibbs x θ l x) / (log r - x) ^ 4) *
        ((log r - x) / (r - exp x)) ^ 4) := by
    filter_upwards [self_mem_nhdsWithin, hp] with r hr hrp
    have hl : log r - x ≠ 0 := by
      intro he
      have hxe : r = exp x := by rw [← exp_log hrp, sub_eq_zero.mp he]
      exact hr hxe
    unfold egbCriticalALogGibbs
    rw [exp_log hrp]
    field_simp
  exact (tendsto_congr' he).2 (by simpa only [Function.comp_def] using h)

end GaloisForLFunctions.HTGeometry
