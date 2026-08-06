import GaloisForLFunctions.HTGeometry.GaussianRadialCompletionLaw
import GaloisForLFunctions.HTGeometry.BohrBochnerFejerApprox

/-!
# The radial completion law for an arbitrary continuous reporter

A spectrally presented state curve is almost periodic with precompact range, so
composing it with any continuous reporter produces a continuous almost periodic
function, and the Bochner--Fejér approximation theorem supplies the trigonometric
approximants required by the radial completion law.  Consequently the Gaussian
radial observation of *every* continuous reporter converges to the completed-time
Haar average of that reporter along the state curve.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Bochner--Fejér approximants exist** for a continuous almost periodic
function. -/
theorem exists_trigPolyChar_approx_of_isBohrAlmostPeriodic {f : ℝ → ℂ}
    (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (S : Finset ℝ) (a : ℝ → ℂ),
      ∀ t, ‖f t - ∑ lam ∈ S, a lam * expChar lam t‖ ≤ δ := by
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic hfc hfa
  set F : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup f hfc C hC with hF
  have hfun : (fun x => F x) = f := rfl
  have huc : UniformContinuous fun x => F x := by
    rw [hfun]
    exact uniformContinuous_of_isBohrAlmostPeriodic hfc hfa
  have htb : HasTotallyBoundedOrbit fun x => F x := by
    rw [hfun]
    exact hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hfc hfa
  obtain ⟨S, a, -, happ⟩ := exists_trigPoly_spectrum_approx huc htb hδ
  exact ⟨S, a, happ⟩

/-- **Radial completion law, hypothesis-free form.**  Every continuous almost
periodic reporter has Gaussian radial averages converging to its Bohr mean. -/
theorem tendsto_integral_radial_bohrMean_of_almostPeriodic {m : ℕ} (hm : 0 < m)
    {f : ℝ → ℂ} (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f) :
    Tendsto
      (fun time : ℝ => ∫ x, f (time * ‖x‖)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (bohrMean f)) :=
  tendsto_integral_radial_bohrMean hm hfc hfa
    fun _ hδ => exists_trigPolyChar_approx_of_isBohrAlmostPeriodic hfc hfa hδ

/-- Finite sums of almost periodic vector-valued functions are almost
periodic. -/
theorem isBohrAlmostPeriodic_finsetSum {κ : Type*} {E : Type*}
    [NormedAddCommGroup E] (S : Finset κ) {F : κ → ℝ → E}
    (hc : ∀ i ∈ S, Continuous (F i))
    (ha : ∀ i ∈ S, HTGeometry.IsBohrAlmostPeriodic (F i)) :
    HTGeometry.IsBohrAlmostPeriodic fun t => ∑ i ∈ S, F i t := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isBohrAlmostPeriodic_const (0 : E)
  | insert j S hj ih =>
      have hcj := hc j (Finset.mem_insert_self j S)
      have haj := ha j (Finset.mem_insert_self j S)
      have hrest := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      have hcrest : Continuous fun t => ∑ i ∈ S, F i t :=
        continuous_finsetSum _ fun i hi => hc i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert hj] using
        isBohrAlmostPeriodic_add hcj haj hcrest hrest

section Composition

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

/-- Almost periodicity is preserved by composing with a function continuous on a
compact set containing the range. -/
theorem isBohrAlmostPeriodic_comp_of_range_subset {f : ℝ → E}
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) {K : Set E} (hK : IsCompact K)
    (hrange : ∀ t, f t ∈ K) {g : E → G} (hg : ContinuousOn g K) :
    HTGeometry.IsBohrAlmostPeriodic fun t => g (f t) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hg) ε hε
  obtain ⟨L, hL, hLprop⟩ := hfa (δ / 2) (by linarith)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hLprop a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hd : dist (f (x + τ)) (f x) < δ := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hτ x) (by linarith)
  have := hδg _ (hrange (x + τ)) _ (hrange x) hd
  rw [dist_eq_norm] at this
  exact le_of_lt this

/-- A fixed vector scaled by an almost periodic scalar is almost periodic. -/
theorem isBohrAlmostPeriodic_smul_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {z : ℝ → ℂ} (hz : HTGeometry.IsBohrAlmostPeriodic z) (w : E) :
    HTGeometry.IsBohrAlmostPeriodic fun t => z t • w := by
  intro ε hε
  obtain ⟨L, hL, hLprop⟩ := hz (ε / (‖w‖ + 1)) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hLprop a
  refine ⟨τ, hτmem, fun x => ?_⟩
  rw [← sub_smul, norm_smul]
  calc ‖z (x + τ) - z x‖ * ‖w‖ ≤ (ε / (‖w‖ + 1)) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (hτ x) (norm_nonneg w)
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, le_of_lt hε]

end Composition

section StateCurve

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The spectrally presented state curve of an observer. -/
def spectralStateCurve (Ev : ι → ℝ) (w : ι → E) (s : ℝ) : E :=
  ∑ i, Complex.exp (-((s * Ev i : ℝ) : ℂ) * Complex.I) • w i

omit [Fintype ι] in
theorem continuous_spectralPhase (Ev : ι → ℝ) (i : ι) :
    Continuous fun s : ℝ => -((s * Ev i : ℝ) : ℂ) * Complex.I :=
  ((Complex.continuous_ofReal.comp
    (continuous_id.mul continuous_const)).neg).mul continuous_const

theorem continuous_spectralStateCurve (Ev : ι → ℝ) (w : ι → E) :
    Continuous (spectralStateCurve Ev w) := by
  unfold spectralStateCurve
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_exp.comp (continuous_spectralPhase Ev i)).smul
    continuous_const

omit [Fintype ι] in
theorem spectralPhase_eq_expChar (Ev : ι → ℝ) (i : ι) :
    (fun s : ℝ => Complex.exp (-((s * Ev i : ℝ) : ℂ) * Complex.I))
      = expChar (-Ev i) := by
  funext s
  rw [expChar]
  congr 1
  push_cast
  ring

theorem isBohrAlmostPeriodic_spectralStateCurve (Ev : ι → ℝ) (w : ι → E) :
    HTGeometry.IsBohrAlmostPeriodic (spectralStateCurve Ev w) := by
  refine isBohrAlmostPeriodic_finsetSum (F := fun i s =>
      Complex.exp (-((s * Ev i : ℝ) : ℂ) * Complex.I) • w i) Finset.univ
    (fun i _ => (Complex.continuous_exp.comp
      (continuous_spectralPhase Ev i)).smul continuous_const) fun i _ => ?_
  refine isBohrAlmostPeriodic_smul_const ?_ (w i)
  rw [spectralPhase_eq_expChar Ev i]
  exact isBohrAlmostPeriodic_expChar _

theorem norm_spectralStateCurve_le (Ev : ι → ℝ) (w : ι → E) (s : ℝ) :
    ‖spectralStateCurve Ev w s‖ ≤ ∑ i, ‖w i‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

end StateCurve

/-- **Radial completion of an arbitrary continuous reporter.**  For a spectrally
presented state curve in a finite-dimensional state space, the Gaussian radial
observation of any continuous reporter converges to the completed-time Haar
average of that reporter along the curve. -/
theorem tendsto_integral_radial_bohrMean_continuous_reporter {m : ℕ} (hm : 0 < m)
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (Ev : ι → ℝ) (w : ι → E)
    {F : E → ℂ} (hF : Continuous F) :
    Tendsto
      (fun time : ℝ => ∫ x, F (spectralStateCurve Ev w (time * ‖x‖))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (bohrMean fun s : ℝ => F (spectralStateCurve Ev w s))) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hK : IsCompact (Metric.closedBall (0 : E) (∑ i, ‖w i‖)) :=
    isCompact_closedBall _ _
  have hrange : ∀ t : ℝ, spectralStateCurve Ev w t
      ∈ Metric.closedBall (0 : E) (∑ i, ‖w i‖) := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_spectralStateCurve_le Ev w t
  have hfa : HTGeometry.IsBohrAlmostPeriodic
      fun s : ℝ => F (spectralStateCurve Ev w s) :=
    isBohrAlmostPeriodic_comp_of_range_subset
      (isBohrAlmostPeriodic_spectralStateCurve Ev w) hK hrange hF.continuousOn
  exact tendsto_integral_radial_bohrMean_of_almostPeriodic hm
    (hF.comp (continuous_spectralStateCurve Ev w)) hfa

end

end GaloisForLFunctions.HTGeometry
