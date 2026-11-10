import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PoleResidueCurvature

/-!
# The prime Gram form of the residue Hessian

A jointly holomorphic regularization of an actual gauge family has
negative logarithmic residue Hessian equal to the convergent prime Gram
form with weights `p/(p-1)^2`.

Restricting to real lines gives each diagonal value from the scalar
curvature theorem. Polarization proves convergence and equality for the
mixed entries. The resulting positive semidefinite form has kernel
exactly the common kernel of the first prime-phase differentials.
-/

open Complex Filter Topology Metric
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open GaloisForLFunctions.ArithmeticWeightTheory
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Real parameter vectors embedded in their complexification. -/
def complexParameter {d : ℕ} : (Fin d → ℝ) →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem complexParameter_smul {d : ℕ} (t : ℝ) (v : Fin d → ℝ) :
    complexParameter (t • v) = (t : ℂ) • complexParameter v := by
  ext i
  change ((t * v i : ℝ) : ℂ) = (t : ℂ) * (v i : ℂ)
  exact Complex.ofReal_mul _ _

/-- A line's second derivative is the Hessian evaluated twice on its direction. -/
theorem second_line_deriv_of_analyticAt {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → 𝕜} (hf : AnalyticAt 𝕜 f 0) (v : E) :
    deriv (deriv (fun t : 𝕜 => f (t • v))) 0 = fderiv 𝕜 (fderiv 𝕜 f) 0 v v := by
  have hv (t : 𝕜) : HasDerivAt (fun t : 𝕜 => t • v) v t := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const v
  have hnear : ∀ᶠ t : 𝕜 in 𝓝 0, AnalyticAt 𝕜 f (t • v) := by
    have hc : ContinuousAt (fun t : 𝕜 => t • v) 0 := continuousAt_id.smul continuousAt_const
    exact hc.tendsto.eventually (by simpa only [zero_smul] using hf.eventually_analyticAt)
  have he : deriv (fun t : 𝕜 => f (t • v)) =ᶠ[𝓝 0]
      fun t => fderiv 𝕜 f (t • v) v := by
    filter_upwards [hnear] with t ht
    exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hv t)).deriv
  rw [he.deriv_eq]
  have hdf : HasDerivAt (fun t : 𝕜 => fderiv 𝕜 f (t • v))
      (fderiv 𝕜 (fderiv 𝕜 f) 0 v) 0 := by
    have h : HasFDerivAt (fderiv 𝕜 f) (fderiv 𝕜 (fderiv 𝕜 f) 0) ((0 : 𝕜) • v) := by
      simpa only [zero_smul] using hf.fderiv.differentiableAt.hasFDerivAt
    simpa only [Function.comp_def] using h.comp_hasDerivAt 0 (hv 0)
  have h := ((ContinuousLinearMap.apply 𝕜 𝕜 v).hasFDerivAt.comp_hasDerivAt 0 hdf).deriv
  exact h

/-- Logarithmic modulus of the residue along real parameter vectors. -/
def residueLog {d : ℕ} (U : (Fin d → ℂ) × ℂ → ℂ) (v : Fin d → ℝ) : ℝ :=
  Real.log ‖U (complexParameter v, 1)‖

/-- The first imaginary phase differential, restricted to real parameter directions. -/
def primePhaseSpeed {d : ℕ} (u : Nat.Primes → (Fin d → ℂ) → ℂ)
    (p : Nat.Primes) (v : Fin d → ℝ) : ℝ :=
  (fderiv ℂ (u p) 0 (complexParameter v)).im

theorem primePhaseSpeed_add {d : ℕ} (u : Nat.Primes → (Fin d → ℂ) → ℂ)
    (p : Nat.Primes) (v w : Fin d → ℝ) :
    primePhaseSpeed u p (v + w) = primePhaseSpeed u p v + primePhaseSpeed u p w := by
  simp only [primePhaseSpeed, map_add, Complex.add_im]

theorem analyticAt_residueLog {d : ℕ} {U : (Fin d → ℂ) × ℂ → ℂ}
    (hU : AnalyticAt ℂ U (0, 1)) (hsl : U (0, 1) ∈ Complex.slitPlane) :
    AnalyticAt ℝ (residueLog U) 0 := by
  have hu : AnalyticAt ℝ (fun p => Complex.log (U p)) (0, 1) :=
    (hU.clog hsl).restrictScalars
  have hc : AnalyticAt ℝ (fun v : Fin d → ℝ => (complexParameter v, (1 : ℂ))) 0 :=
    ((complexParameter (d := d)).analyticAt (0 : Fin d → ℝ)).prod analyticAt_const
  have hh : AnalyticAt ℝ (fun v : Fin d → ℝ => Complex.log (U (complexParameter v, 1))) 0 := by
    have hu' : AnalyticAt ℝ (fun p => Complex.log (U p)) (complexParameter (0 : Fin d → ℝ), 1) := by
      simpa only [map_zero] using hu
    exact hu'.comp (f := fun v : Fin d → ℝ => (complexParameter v, (1 : ℂ))) hc
  have hr := (Complex.reCLM.analyticAt _).comp hh
  change AnalyticAt ℝ (fun v : Fin d → ℝ => Real.log ‖U (complexParameter v, 1)‖) 0
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using hr

/-- Negative Hessian of the logarithmic pole residue. -/
def residueMetric {d : ℕ} (U : (Fin d → ℂ) × ℂ → ℂ)
    (v w : Fin d → ℝ) : ℝ :=
  -fderiv ℝ (fderiv ℝ (residueLog U)) 0 v w

theorem residueMetric_symmetric {d : ℕ} {U : (Fin d → ℂ) × ℂ → ℂ}
    (hU : AnalyticAt ℂ U (0, 1)) (hsl : U (0, 1) ∈ Complex.slitPlane)
    (v w : Fin d → ℝ) : residueMetric U v w = residueMetric U w v := by
  have hc : ContDiffAt ℝ 2 (residueLog U) 0 := (analyticAt_residueLog hU hsl).contDiffAt
  exact congrArg Neg.neg ((hc.isSymmSndFDerivAt (by norm_num)) v w)

/-- The first line derivative is the Fréchet differential on its direction. -/
theorem line_deriv_of_differentiableAt {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f 0) (v : E) :
    deriv (fun t : 𝕜 => f (t • v)) 0 = fderiv 𝕜 f 0 v := by
  have hh : HasFDerivAt f (fderiv 𝕜 f 0) ((0 : 𝕜) • v) := by
    simpa only [zero_smul] using hf.hasFDerivAt
  have h := (hh.comp_hasDerivAt 0 ((hasDerivAt_id (0 : 𝕜)).smul_const v)).deriv
  simpa only [one_smul, Function.comp_def, id_eq] using h

/-- A unit prime phase has purely imaginary differential on every real direction. -/
theorem prime_phase_differential_re_zero {d : ℕ}
    {x : (Fin d → ℝ) → GaugeTorus} {u : Nat.Primes → (Fin d → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hphase : ∀ v : Fin d → ℝ, ‖v‖ < R → ∀ p, u p (complexParameter v) = twist (x v) p)
    (p : Nat.Primes) (v : Fin d → ℝ) :
    (fderiv ℂ (u p) 0 (complexParameter v)).re = 0 := by
  have hf : DifferentiableAt ℂ (u p) 0 :=
    (hu p).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  let V : Set ℂ := (fun z : ℂ => z • complexParameter v) ⁻¹' ball 0 R
  have hVo : IsOpen V := isOpen_ball.preimage (continuous_id.smul continuous_const)
  have hV0 : (0 : ℂ) ∈ V := by
    simpa only [V, Set.mem_preimage, zero_smul] using
      (mem_ball_self hR : (0 : Fin d → ℂ) ∈ ball 0 R)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => u p (z • complexParameter v)) V := by
    intro z hz
    exact (((hu p).differentiableAt (isOpen_ball.mem_nhds hz)).hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_id z).smul_const (complexParameter v))).differentiableAt.differentiableWithinAt
  have hcurve : AnalyticAt ℂ (fun z : ℂ => u p (z • complexParameter v)) 0 :=
    hdiff.analyticAt (hVo.mem_nhds hV0)
  have hu0 : u p ((0 : ℂ) • complexParameter v) = 1 := by
    simpa only [zero_smul, map_zero, hx0, twist_trivial] using
      hphase 0 (by simpa using hR) p
  have hc : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : Fin d → ℝ)) := by
    have h : ContinuousAt (fun t : ℝ => t • v) 0 := continuousAt_id.smul continuousAt_const
    simpa only [zero_smul] using h.tendsto
  have hunit : ∀ᶠ t : ℝ in 𝓝 0, ‖u p ((t : ℂ) • complexParameter v)‖ = 1 := by
    filter_upwards [hc.eventually (isOpen_ball.mem_nhds (mem_ball_self hR))] with t ht
    rw [← complexParameter_smul,
      hphase (t • v) (by simpa only [mem_ball, dist_zero_right] using ht) p, norm_twist]
  have h := (unit_phase_jets hcurve hu0 hunit).1
  rw [line_deriv_of_differentiableAt hf] at h
  exact h

theorem prime_phase_differential_zero_iff {d : ℕ}
    {x : (Fin d → ℝ) → GaugeTorus} {u : Nat.Primes → (Fin d → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hphase : ∀ v : Fin d → ℝ, ‖v‖ < R → ∀ p, u p (complexParameter v) = twist (x v) p)
    (p : Nat.Primes) (v : Fin d → ℝ) :
    primePhaseSpeed u p v = 0 ↔ fderiv ℂ (u p) 0 (complexParameter v) = 0 := by
  constructor
  · intro h
    exact Complex.ext (prime_phase_differential_re_zero hR hx0 hu hphase p v) h
  · intro h
    simp only [primePhaseSpeed, h, Complex.zero_im]

/-- Every real direction has the prime quadratic residue energy. -/
theorem gauge_residue_directional_hasSum {d : ℕ}
    {x : (Fin d → ℝ) → GaugeTorus} {u : Nat.Primes → (Fin d → ℂ) → ℂ}
    {U : (Fin d → ℂ) × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ v : Fin d → ℝ, ‖v‖ < R → ∀ p, u p (complexParameter v) = twist (x v) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ v : Fin d → ℝ, ‖v‖ < R →
      U (complexParameter v, (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x v) (σ : ℂ))
    (v : Fin d → ℝ) :
    HasSum (fun p : Nat.Primes =>
      primePhaseSpeed u p v ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) (residueMetric U v v) := by
  let vC := complexParameter v
  -- Keep both the real gauge curve and its complex extension inside the original ball.
  let D : ℝ := 1 + ‖v‖ + ‖vC‖
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg v, norm_nonneg vC]
  let r : ℝ := R / D
  have hr : 0 < r := div_pos hR hD
  have hrR : r ≤ R := div_le_self hR.le hD1
  have hm {a b : ℝ} (ha : 0 ≤ a) (har : a < r) (hb : b ≤ D) : a * b < R := by
    calc a * b ≤ a * D := mul_le_mul_of_nonneg_left hb ha
         _ < r * D := mul_lt_mul_of_pos_right har hD
         _ = R := div_mul_cancel₀ R hD.ne'
  have hcball {z : ℂ} (hz : z ∈ ball 0 r) : z • vC ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right, norm_smul]
    exact hm (norm_nonneg _) (by simpa only [mem_ball, dist_zero_right] using hz)
      (by dsimp [D]; linarith [norm_nonneg v])
  have hrball {t : ℝ} (ht : |t| < r) : ‖t • v‖ < R := by
    rw [norm_smul, Real.norm_eq_abs]
    exact hm (abs_nonneg _) ht (by dsimp [D]; linarith [norm_nonneg vC])
  have hdu : ∀ p, DifferentiableOn ℂ (fun z : ℂ => u p (z • vC)) (ball 0 r) := by
    intro p z hz
    exact (((hu p).differentiableAt (isOpen_ball.mem_nhds (hcball hz))).hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_id z).smul_const vC)).differentiableAt.differentiableWithinAt
  have hUc : AnalyticAt ℂ (fun w : ℂ × ℂ => U (w.1 • vC, w.2)) (0, 1) := by
    have hmap : AnalyticAt ℂ (fun w : ℂ × ℂ => (w.1 • vC, w.2)) (0, 1) :=
      (analyticAt_fst.smul analyticAt_const).prod analyticAt_snd
    have hh : AnalyticAt ℂ U ((0 : ℂ) • vC, 1) := by simpa only [zero_smul] using hU
    exact hh.comp (f := fun w : ℂ × ℂ => (w.1 • vC, w.2)) hmap
  have hs := gauge_residue_curvature_hasSum (x := fun t : ℝ => x (t • v))
    (u := fun p z => u p (z • vC)) (U := fun w : ℂ × ℂ => U (w.1 • vC, w.2))
    hr (by simpa only [zero_smul] using hx0) hdu
    (fun p z hz => hbd p (z • vC) (hcball hz))
    (fun t ht p => by
      have hh := hphase (t • v) (hrball ht) p
      rwa [complexParameter_smul] at hh)
    hUc (fun σ hσ hσr t ht => by
      change U ((t : ℂ) • complexParameter v, (σ : ℂ)) =
        ((σ : ℂ) - 1) * gaugeFibre (x (t • v)) (σ : ℂ)
      rw [← complexParameter_smul]
      exact hagree σ hσ (by linarith only [hσr, hrR]) (t • v) (hrball ht))
  have hfirst (p : Nat.Primes) : deriv (fun z : ℂ => u p (z • vC)) 0 =
      fderiv ℂ (u p) 0 vC :=
    line_deriv_of_differentiableAt ((hu p).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))) vC
  have hU0 : U (0, 1) = 1 := regularized_gauge_initial_residue (x := fun _ : ℝ => x 0)
    hR hx0 hU.continuousAt (fun σ hσ hσR => by
      simpa only [map_zero] using hagree σ hσ hσR 0 (by simpa using hR))
  have hsl : U (0, 1) ∈ Complex.slitPlane := by rw [hU0]; exact Or.inl (by norm_num)
  have he : (fun t : ℝ => Real.log ‖U ((t : ℂ) • vC, 1)‖) =
      (fun t : ℝ => residueLog U (t • v)) := by
    funext t
    simp only [residueLog, complexParameter_smul, vC]
  change HasSum (fun p : Nat.Primes =>
    (deriv (fun z : ℂ => u p (z • vC)) 0).im ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2)
    (-deriv (deriv (fun t : ℝ => Real.log ‖U ((t : ℂ) • vC, 1)‖)) 0) at hs
  rw [he, second_line_deriv_of_analyticAt (analyticAt_residueLog hU hsl) v] at hs
  simpa only [hfirst, primePhaseSpeed, residueMetric, vC] using hs

section Multivariate
variable {d : ℕ} {x : (Fin d → ℝ) → GaugeTorus}
  {u : Nat.Primes → (Fin d → ℂ) → ℂ} {U : (Fin d → ℂ) × ℂ → ℂ} {R M : ℝ}
  (hR : 0 < R) (hx0 : x 0 = 0)
  (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
  (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
  (hphase : ∀ v : Fin d → ℝ, ‖v‖ < R → ∀ p, u p (complexParameter v) = twist (x v) p)
  (hU : AnalyticAt ℂ U (0, 1))
  (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ v : Fin d → ℝ, ‖v‖ < R →
    U (complexParameter v, (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x v) (σ : ℂ))

include hR hx0 hu hbd hphase hU hagree

/-- The full negative residue Hessian is the convergent prime Gram form. -/
theorem gauge_residue_hessian_hasSum (v w : Fin d → ℝ) :
    HasSum (fun p : Nat.Primes => primePhaseSpeed u p v * primePhaseSpeed u p w *
      (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) (residueMetric U v w) := by
  have hU0 : U (0, 1) = 1 := regularized_gauge_initial_residue (x := fun _ : ℝ => x 0)
    hR hx0 hU.continuousAt (fun σ hσ hσR => by
      simpa only [map_zero] using hagree σ hσ hσR 0 (by simpa using hR))
  have hsl : U (0, 1) ∈ Complex.slitPlane := by rw [hU0]; exact Or.inl (by norm_num)
  have hadd : residueMetric U (v + w) (v + w) =
      residueMetric U v v + 2 * residueMetric U v w + residueMetric U w w := by
    have hsym := residueMetric_symmetric hU hsl v w
    unfold residueMetric at hsym ⊢
    simp only [map_add, add_apply]
    linarith only [hsym]
  -- Polarization also proves convergence of the signed mixed prime sum.
  have hs := (((gauge_residue_directional_hasSum hR hx0 hu hbd hphase hU hagree (v + w)).sub
    (gauge_residue_directional_hasSum hR hx0 hu hbd hphase hU hagree v)).sub
    (gauge_residue_directional_hasSum hR hx0 hu hbd hphase hU hagree w)).mul_left (1 / 2 : ℝ)
  have he (p : Nat.Primes) : (1 / 2 : ℝ) *
      ((primePhaseSpeed u p (v + w) ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2 -
        primePhaseSpeed u p v ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) -
        primePhaseSpeed u p w ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) =
      primePhaseSpeed u p v * primePhaseSpeed u p w * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2 := by
    rw [primePhaseSpeed_add]
    ring
  have hvw : (1 / 2 : ℝ) *
      ((residueMetric U (v + w) (v + w) - residueMetric U v v) - residueMetric U w w) =
      residueMetric U v w := by rw [hadd]; ring
  simpa only [he, hvw] using hs

/-- Positivity and the exact kernel of the residue Hessian. -/
theorem gauge_residue_metric_positive_and_kernel :
    (∀ v : Fin d → ℝ, 0 ≤ residueMetric U v v) ∧
      ∀ v : Fin d → ℝ, (∀ w : Fin d → ℝ, residueMetric U v w = 0) ↔
        ∀ p, primePhaseSpeed u p v = 0 := by
  constructor
  · intro v
    rw [← (gauge_residue_directional_hasSum hR hx0 hu hbd hphase hU hagree v).tsum_eq]
    exact tsum_nonneg fun p =>
      div_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _)
  · intro v
    have hdiag := gauge_residue_directional_hasSum hR hx0 hu hbd hphase hU hagree v
    have hqsum : HasSum (fun p => primePhaseSpeed u p v ^ 2 * primeDamping 1 p /
        (1 - primeDamping 1 p) ^ 2) (residueMetric U v v) := by
      simpa only [prime_boundary_weight] using hdiag
    have hz := phase_curvature_zero_iff (a := fun p => primePhaseSpeed u p v)
      (primeDamping_pos 1) (fun p => (primeDamping_le_half le_rfl p).trans_lt (by norm_num))
      hqsum.summable
    rw [hqsum.tsum_eq] at hz
    constructor
    · intro h
      exact hz.mp (h v)
    · intro h w
      have hs := gauge_residue_hessian_hasSum hR hx0 hu hbd hphase hU hagree v w
      simpa only [h, zero_mul, zero_div, tsum_zero] using hs.tsum_eq.symm
/-- The Hessian kernel is exactly the common kernel of the complex prime differentials. -/
theorem gauge_residue_hessian_kernel (v : Fin d → ℝ) :
    (∀ w : Fin d → ℝ, residueMetric U v w = 0) ↔
      ∀ p, fderiv ℂ (u p) 0 (complexParameter v) = 0 := by
  exact ((gauge_residue_metric_positive_and_kernel hR hx0 hu hbd hphase hU hagree).2 v).trans
    (forall_congr' fun p => prime_phase_differential_zero_iff hR hx0 hu hphase p v)
end Multivariate

#print axioms gauge_residue_directional_hasSum
#print axioms gauge_residue_hessian_hasSum
#print axioms gauge_residue_metric_positive_and_kernel
#print axioms gauge_residue_hessian_kernel
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
