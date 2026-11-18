import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Gamma averages from a regular Laplace transform

Cauchy's estimate gives geometric decay for a signed ray integral against
the probability densities tⁿ exp(−t)/n! when its transform extends across
the closed unit disk centred at −1. Weighted square integrability suffices
to identify every derivative with its physical moment.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

private def momentKernel (n : ℕ) (z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^n * cexp (z*(t:ℂ))

private theorem norm_momentKernel (n : ℕ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖momentKernel n z t‖ = t^n * Real.exp (z.re*t) := by
  rw [momentKernel,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,
    Complex.norm_exp]
  simp

private theorem memLp_momentKernel (n : ℕ) {z : ℂ} (hz : z.re < 0) :
    MemLp (momentKernel n z) 2 (volume.restrict (Ioi (0:ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold momentKernel; fun_prop)).mpr
  have h := (integrableOn_natPow_mul_cexp (c := ((-2*z.re:ℝ):ℂ)) (by simp; linarith) (2*n)).norm
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_natPow_mul_cexp (le_of_lt ht),norm_momentKernel _ _ (le_of_lt ht),mul_pow,
    sq (Real.exp _),← Real.exp_add,← pow_mul]
  simp only [Complex.ofReal_re]
  rw [Nat.mul_comm n 2]
  congr 2
  ring

private def rayMoment (D : ℝ → ℂ) (n : ℕ) (p : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ), momentKernel n (p+3/4) t * D t

private theorem hasDerivAt_rayMoment {D : ℝ → ℂ}
    (hD : MemLp D 2 (volume.restrict (Ioi (0:ℝ)))) (n : ℕ) {p : ℂ} (hp : p.re < -(3/4)) :
    HasDerivAt (rayMoment D n) (rayMoment D (n+1) p) p := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  have hi (m : ℕ) (z : ℂ) (hz : z.re < -(3/4)) :
      IntegrableOn (fun t : ℝ => momentKernel m (z+3/4) t * D t) (Ioi 0) :=
    (memLp_momentKernel m (by simp; linarith)).integrable_mul hD
  have hm (m : ℕ) (z : ℂ) : AEStronglyMeasurable (fun t : ℝ => momentKernel m (z+3/4) t * D t)
      (volume.restrict (Ioi 0)) :=
    (by unfold momentKernel; fun_prop : AEStronglyMeasurable (momentKernel m (z+3/4)) _).mul
      hD.aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun z t => momentKernel n (z+3/4) t * D t)
    (F' := fun z t => momentKernel (n+1) (z+3/4) t * D t)
    (bound := fun t => ‖momentKernel (n+1) ((b:ℂ)+3/4) t * D t‖)
    ((isOpen_lt continuous_re continuous_const).mem_nhds hpb)
    (Eventually.of_forall (hm n)) (hi n p hp) (hm (n+1) p) ?_
    (hi (n+1) (b:ℂ) hb).norm ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have ht0 := le_of_lt (show 0 < t from ht)
    simp only [norm_mul,norm_momentKernel _ _ ht0,Complex.add_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (add_le_add_left (le_of_lt hz) _) ht0)) (pow_nonneg ht0 _)) (norm_nonneg _)
  · refine Eventually.of_forall fun t z _ => ?_
    have h := (((((hasDerivAt_id z).add_const (3/4)).mul_const (t:ℂ)).cexp).const_mul
      ((t:ℂ)^n)).mul_const (D t)
    apply h.congr_deriv
    unfold momentKernel
    simp only [pow_succ,id_eq]
    ring

private theorem iteratedDeriv_rayMoment {D : ℝ → ℂ} (hD : MemLp D 2 (volume.restrict (Ioi (0:ℝ))))
    (n : ℕ) {p : ℂ} (hp : p.re < -(3/4)) :
    iteratedDeriv n (rayMoment D 0) p = rayMoment D n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (rayMoment D 0) =ᶠ[𝓝 p] rayMoment D n := by
      filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hp] with z hz
      exact ih hz
    rw [iteratedDeriv_succ,he.deriv_eq,(hasDerivAt_rayMoment hD n hp).deriv]

/-- The gamma test of a square-integrable, exponentially damped ray datum is integrable. -/
theorem integrableOn_damped_gammaMoment {D : ℝ → ℂ} (hD : MemLp D 2 (volume.restrict (Ioi (0:ℝ))))
    (n : ℕ) : IntegrableOn (fun t : ℝ => (t:ℂ)^n * cexp (-(t:ℂ)/4) * D t) (Ioi 0) := by
  have h := (memLp_momentKernel n (z := -(1/4)) (by norm_num)).integrable_mul hD
  apply h.congr (Eventually.of_forall fun t => ?_)
  change momentKernel n (-(1/4)) t * D t = _
  rw [momentKernel,show -(1/4:ℂ)*(t:ℂ) = -(t:ℂ)/4 by ring]

/-- A common disk of continuation bounds every modulated gamma average on a
whole frequency interval, with the same geometric constants throughout. -/
theorem gammaMoment_decay_on_band_of_regular_laplace {D : ℝ → ℂ}
    (hD : MemLp D 2 (volume.restrict (Ioi (0:ℝ)))) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall (-1) 1))
    (hag : G =ᶠ[𝓝 (-1:ℂ)] fun p => ∫ t in Ioi (0:ℝ), cexp ((p+3/4)*(t:ℂ)) * D t) :
    ∃ η R C : ℝ, 0 < η ∧ 1 < R ∧ ∀ ξ : ℝ, |ξ| ≤ η → ∀ n : ℕ,
      ‖(∫ t in Ioi (0:ℝ), (t:ℂ)^n * cexp (-(t:ℂ)/4) * D t * cexp ((ξ:ℂ)*I*(t:ℂ))) /
        (n.factorial:ℂ)‖ ≤ C/R^n := by
  obtain ⟨δ,hδ,hU⟩ := (isCompact_closedBall (-1:ℂ) 1).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ G) hG
  rw [cthickening_closedBall hδ.le (by norm_num)] at hU
  have han : AnalyticOnNhd ℂ G (Metric.closedBall (-1) (δ+1)) := fun z hz => hU hz
  obtain ⟨C,hC⟩ := (isCompact_closedBall (-1:ℂ) (δ+1)).exists_bound_of_continuousOn han.continuousOn
  have hbase : G =ᶠ[𝓝 (-1:ℂ)] rayMoment D 0 :=
    hag.trans (Eventually.of_forall fun p => by simp [rayMoment,momentKernel])
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hbase
  let η := min (ε/2) (δ/2)
  let R := 1+δ/2
  have hη : 0 < η := lt_min (half_pos hε) (half_pos hδ)
  have hR : 1 < R := by dsimp [R]; linarith
  refine ⟨η,R,C,hη,hR,fun ξ hξ n => ?_⟩
  let c : ℂ := -1+(ξ:ℂ)*I
  have hc : dist c (-1:ℂ) = |ξ| := by
    rw [dist_eq_norm,show c-(-1:ℂ) = (ξ:ℂ)*I by dsimp [c]; ring,norm_mul]
    simp
  have hsub : Metric.closedBall c R ⊆ Metric.closedBall (-1) (δ+1) := by
    intro z hz
    have hh := dist_triangle z c (-1:ℂ)
    rw [hc] at hh
    change dist z c ≤ R at hz
    change dist z (-1:ℂ) ≤ δ+1
    dsimp only [R] at hz
    linarith only [hh,hz,hξ.trans (min_le_right _ _)]
  have hnb : c ∈ Metric.ball (-1:ℂ) ε := by
    rw [Metric.mem_ball,hc]
    exact (hξ.trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  have he : G =ᶠ[𝓝 c] rayMoment D 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hnb] with z hz
    exact hball hz
  have hdiff : DiffContOnCl ℂ G (Metric.ball c R) :=
    ⟨(han.mono hsub).differentiableOn.mono Metric.ball_subset_closedBall,
      (han.mono hsub).continuousOn.mono Metric.closure_ball_subset_closedBall⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (zero_lt_one.trans hR) hdiff
    (fun z hz => hC z (hsub (Metric.sphere_subset_closedBall hz)))
  rw [he.iteratedDeriv_eq,iteratedDeriv_rayMoment hD n (by norm_num [c])] at h
  have hint : rayMoment D n c =
      ∫ t in Ioi (0:ℝ), (t:ℂ)^n * cexp (-(t:ℂ)/4) * D t * cexp ((ξ:ℂ)*I*(t:ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change (t:ℂ)^n * cexp ((c+3/4)*(t:ℂ)) * D t = _
    rw [show (c+3/4)*(t:ℂ) = -(t:ℂ)/4 + (ξ:ℂ)*I*(t:ℂ) by dsimp only [c]; ring,Complex.exp_add]
    ring
  rw [hint] at h
  rw [norm_div,Complex.norm_natCast,div_le_iff₀ (by positivity : (0:ℝ) < n.factorial)]
  exact h.trans_eq (by ring)

/-- A Laplace continuation across the closed unit disk controls every signed
physical gamma average exponentially in its order. The input is damped by exp(−3t/4). -/
theorem gammaMoment_decay_of_regular_laplace {D : ℝ → ℂ}
    (hD : MemLp D 2 (volume.restrict (Ioi (0:ℝ)))) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall (-1) 1))
    (hag : G =ᶠ[𝓝 (-1:ℂ)] fun p => ∫ t in Ioi (0:ℝ), cexp ((p+3/4)*(t:ℂ)) * D t) :
    ∃ R C : ℝ, 1 < R ∧ ∀ n : ℕ,
      ‖(∫ t in Ioi (0:ℝ), (t:ℂ)^n * cexp (-(t:ℂ)/4) * D t)/(n.factorial:ℂ)‖ ≤ C/R^n := by
  obtain ⟨η,R,C,hη,hR,h⟩ := gammaMoment_decay_on_band_of_regular_laplace hD hG hag
  refine ⟨R,C,hR,fun n => ?_⟩
  simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] using h 0 (by simpa using hη.le) n

#print axioms gammaMoment_decay_on_band_of_regular_laplace
#print axioms gammaMoment_decay_of_regular_laplace

end GaloisForLFunctions.ExclusionOfTheCriticalState
