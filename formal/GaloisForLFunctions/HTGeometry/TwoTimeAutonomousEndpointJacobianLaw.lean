import GaloisForLFunctions.HTGeometry.TwoTimeDuhamelObserverCoercivityLaw
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Conjugation by one autonomous endpoint, as a real continuous linear map. -/
def autonomousConjugationCLM (x : A) (s : ℝ) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A (exp (s • (-x)))).comp
    ((ContinuousLinearMap.mul ℝ A).flip (exp (s • x)))

theorem autonomousConjugationCLM_apply (x p : A) (s : ℝ) :
    autonomousConjugationCLM x s p =
      exp (s • (-x)) * p * exp (s • x) := by
  simp [autonomousConjugationCLM, mul_assoc]

theorem continuous_autonomousConjugationCLM (x : A) :
    Continuous (autonomousConjugationCLM x) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  unfold autonomousConjugationCLM
  fun_prop

/-- Duhamel response as a genuine continuous linear map in the generator direction. -/
def duhamelConjugationCLM (x : A) (t : ℝ) : A →L[ℝ] A :=
  ∫ s : ℝ in 0..t, autonomousConjugationCLM x s

theorem duhamelConjugationCLM_apply (x p : A) (t : ℝ) :
    duhamelConjugationCLM x t p = duhamelConjugationPrimitive x p t := by
  have hcont := continuous_autonomousConjugationCLM x
  rw [duhamelConjugationCLM,
    ContinuousLinearMap.intervalIntegral_apply (hcont.intervalIntegrable _ _) p]
  unfold duhamelConjugationPrimitive
  apply intervalIntegral.integral_congr
  intro s _
  exact autonomousConjugationCLM_apply x p s

/-- Left-translated Jacobian of one autonomous endpoint. -/
def autonomousEndpointJacobian (x : A) (t : ℝ) : A →L[ℝ] A :=
  (ContinuousLinearMap.mul ℝ A (exp (t • x))).comp
    (duhamelConjugationCLM x t)

theorem autonomousEndpointJacobian_apply (x p : A) (t : ℝ) :
    autonomousEndpointJacobian x t p =
      exp (t • x) * duhamelConjugationPrimitive x p t := by
  simp [autonomousEndpointJacobian, duhamelConjugationCLM_apply]

section ParameterSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Endpoint of a generator depending linearly on a real parameter vector. -/
def autonomousLinearGeneratorEndpoint
    (x : A) (G : E →L[ℝ] A) (t : ℝ) (v : E) : A :=
  exp (t • (x + G v))

/-- Fréchet Jacobian of a linearly parameterized autonomous endpoint. -/
def autonomousLinearGeneratorEndpointJacobian
    (x : A) (G : E →L[ℝ] A) (t : ℝ) : E →L[ℝ] A :=
  (autonomousEndpointJacobian x t).comp G

theorem autonomousLinearGeneratorEndpointJacobian_apply
    (x : A) (G : E →L[ℝ] A) (t : ℝ) (v : E) :
    autonomousLinearGeneratorEndpointJacobian x G t v =
      exp (t • x) * duhamelConjugationPrimitive x (G v) t := by
  simp [autonomousLinearGeneratorEndpointJacobian,
    autonomousEndpointJacobian_apply]

/-- Exact Fréchet differentiability with quadratic operator-norm remainder
for every bounded linear family of skew-adjoint generator directions. -/
theorem hasFDerivAt_autonomousLinearGeneratorEndpoint_zero
    (x : A) (G : E →L[ℝ] A) (hx : x ∈ skewAdjoint A)
    (hG : ∀ v, G v ∈ skewAdjoint A) {t : ℝ} (ht : 0 ≤ t) :
    HasFDerivAt (𝕜 := ℝ) (autonomousLinearGeneratorEndpoint x G t)
      (autonomousLinearGeneratorEndpointJacobian x G t) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound (t ^ (2 : ℕ) * ‖G‖ ^ (2 : ℕ)) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (n := 2) one_lt_two)
  filter_upwards
  intro v
  have h := norm_autonomousPerturbedEndpoint_linearizationError_le
    x (G v) hx (hG v) ht 1
  have hrewrite :
      autonomousLinearGeneratorEndpoint x G t (0 + v) -
          autonomousLinearGeneratorEndpoint x G t 0 -
          autonomousLinearGeneratorEndpointJacobian x G t v =
        autonomousPerturbedEndpoint x (G v) t 1 -
          autonomousPerturbedEndpoint x (G v) t 0 -
          (1 : ℝ) •
            (exp (t • x) * duhamelConjugationPrimitive x (G v) t) := by
    simp [autonomousLinearGeneratorEndpoint,
      autonomousLinearGeneratorEndpointJacobian_apply,
      autonomousPerturbedEndpoint]
  rw [hrewrite]
  calc
    ‖autonomousPerturbedEndpoint x (G v) t 1 -
        autonomousPerturbedEndpoint x (G v) t 0 -
        (1 : ℝ) • (exp (t • x) *
          duhamelConjugationPrimitive x (G v) t)‖ ≤
        t ^ (2 : ℕ) * ‖G v‖ ^ (2 : ℕ) := by simpa using h
    _ ≤ t ^ (2 : ℕ) * (‖G‖ * ‖v‖) ^ (2 : ℕ) := by
      gcongr
      exact G.le_opNorm v
    _ = (t ^ (2 : ℕ) * ‖G‖ ^ (2 : ℕ)) * ‖‖v‖ ^ (2 : ℕ)‖ := by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      ring

/-- Two nearby endpoints of one linearly parameterized generator. -/
def twoTimeAutonomousLinearGeneratorEndpoint
    (x : A) (G : E →L[ℝ] A) (t δ : ℝ) (v : E) : A × A :=
  (autonomousLinearGeneratorEndpoint x G t v,
    autonomousLinearGeneratorEndpoint x G (t + δ) v)

/-- Stacked two-time endpoint Jacobian on parameter space. -/
def twoTimeAutonomousLinearGeneratorEndpointJacobian
    (x : A) (G : E →L[ℝ] A) (t δ : ℝ) : E →L[ℝ] A × A :=
  (autonomousLinearGeneratorEndpointJacobian x G t).prod
    (autonomousLinearGeneratorEndpointJacobian x G (t + δ))

theorem hasFDerivAt_twoTimeAutonomousLinearGeneratorEndpoint_zero
    (x : A) (G : E →L[ℝ] A) (hx : x ∈ skewAdjoint A)
    (hG : ∀ v, G v ∈ skewAdjoint A)
    {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    HasFDerivAt (𝕜 := ℝ) (twoTimeAutonomousLinearGeneratorEndpoint x G t δ)
      (twoTimeAutonomousLinearGeneratorEndpointJacobian x G t δ) 0 := by
  have hfirst := hasFDerivAt_autonomousLinearGeneratorEndpoint_zero x G hx hG ht
  have hsecond := hasFDerivAt_autonomousLinearGeneratorEndpoint_zero x G hx hG
    (show 0 ≤ t + δ by linarith)
  change HasFDerivAt (𝕜 := ℝ)
    (fun v => (autonomousLinearGeneratorEndpoint x G t v,
      autonomousLinearGeneratorEndpoint x G (t + δ) v))
    ((autonomousLinearGeneratorEndpointJacobian x G t).prod
      (autonomousLinearGeneratorEndpointJacobian x G (t + δ))) 0
  exact hfirst.prodMk hsecond

/-- **Uniform parameter-space conorm floor.** If the generator map has conorm
`c`, two short-separated endpoints retain conorm `δ c / 4` at every base time,
independently of spectrum and spectral gaps. -/
theorem twoTimeAutonomousLinearGeneratorEndpointJacobian_lower
    (x : A) (G : E →L[ℝ] A) (hx : x ∈ skewAdjoint A)
    {c : ℝ} (hG : ∀ v, c * ‖v‖ ≤ ‖G v‖)
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * ‖x‖ ≤ 1) (v : E) :
    δ / 4 * c * ‖v‖ ≤
      ‖twoTimeAutonomousLinearGeneratorEndpointJacobian x G t δ v‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have henergy := duhamelConjugationPrimitive_twoTime_energy_lower
    x (G v) hx t hδ hsmall
  have hnorm (u : ℝ) :
      ‖autonomousLinearGeneratorEndpointJacobian x G u v‖ =
        ‖duhamelConjugationPrimitive x (G v) u‖ := by
    rw [autonomousLinearGeneratorEndpointJacobian_apply]
    have hu : exp (u • x) ∈ unitary A :=
      exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem u hx)
    exact CStarRing.norm_mem_unitary_mul _ hu
  have hfirst :
      ‖duhamelConjugationPrimitive x (G v) t‖ ≤
        ‖twoTimeAutonomousLinearGeneratorEndpointJacobian x G t δ v‖ := by
    rw [← hnorm t]
    simpa [twoTimeAutonomousLinearGeneratorEndpointJacobian] using
      norm_fst_le (autonomousLinearGeneratorEndpointJacobian x G t v,
        autonomousLinearGeneratorEndpointJacobian x G (t + δ) v)
  have hsecond :
      ‖duhamelConjugationPrimitive x (G v) (t + δ)‖ ≤
        ‖twoTimeAutonomousLinearGeneratorEndpointJacobian x G t δ v‖ := by
    rw [← hnorm (t + δ)]
    simpa [twoTimeAutonomousLinearGeneratorEndpointJacobian] using
      norm_snd_le (autonomousLinearGeneratorEndpointJacobian x G t v,
        autonomousLinearGeneratorEndpointJacobian x G (t + δ) v)
  have hfirstSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hfirst
  have hsecondSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hsecond
  have hpair :
      δ / 4 * ‖G v‖ ≤
        ‖twoTimeAutonomousLinearGeneratorEndpointJacobian x G t δ v‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith
  calc
    δ / 4 * c * ‖v‖ = δ / 4 * (c * ‖v‖) := by ring
    _ ≤ δ / 4 * ‖G v‖ := mul_le_mul_of_nonneg_left (hG v) (by positivity)
    _ ≤ _ := hpair

end ParameterSpace

end

end GaloisForLFunctions.HTGeometry
