import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.TimeAverages.Action
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.GaussianActions

/-! # Time and field resolution of each circuit-specific replica pair -/

open Finset MeasureTheory ProbabilityTheory Real
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open Dephasing.PairedFields.SpectralEdge
noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The same denominator controls the attenuation from field variance and
from the frequency resolved by the observation window. -/
theorem norm_time_action (m u : ℝ) (c v : ℝ≥0) :
    let D := 1+(c:ℝ)*v
    ‖timeActionKernel m u c v‖ = (sqrt D)⁻¹ * exp (-(c*m^2+v*u^2)/(2*D)) := by
  intro D
  have hD : 0<D := by dsimp [D]; positivity
  change ‖(((sqrt D)⁻¹*exp (-(c*m^2)/(2*D)):ℝ):ℂ) *
    Complex.exp (((u*(m/D):ℝ):ℂ)*Complex.I - (((v:ℝ)/D*u^2/2:ℝ):ℂ))‖ = _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.norm_exp]
  simp only [Complex.sub_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Complex.ofReal_re,zero_sub]
  rw [mul_assoc,←Real.exp_add]
  congr 2
  field_simp
  ring

private def wave (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

private theorem prod_clock (E : I → ℝ) (z : I → ℂ) (p : I → ℕ) (t : ℝ) :
    (∏ i, (z i*wave (E i*t))^p i) =
      (∏ i, z i^p i)*wave (t*replicaMultiplicityEnergy E p) := by
  simp_rw [wave,mul_pow,prod_mul_distrib,←Complex.exp_nat_mul]
  congr 1
  rw [←Complex.exp_sum]
  congr 1
  unfold replicaMultiplicityEnergy
  push_cast
  rw [mul_sum,sum_mul]
  exact sum_congr rfl fun _ _ => by ring

private theorem twist_clock (E : I → ℝ) (z : I → ℂ) (p k : I → ℕ) (t : ℝ) :
    replicaMultiplicityTwist (fun i => z i*wave (E i*t)) p k =
      replicaMultiplicityTwist z p k * wave ((replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)*t) := by
  simp only [replicaMultiplicityTwist,←map_pow,←map_prod]
  rw [prod_clock,prod_clock,map_mul]
  have hc (x : ℝ) : (starRingEnd ℂ) (wave x) = wave (-x) := by
    simp [wave,←Complex.exp_conj]
  rw [hc]
  have hm (x y : ℝ) : wave x*wave y=wave (x+y) := by
    unfold wave
    rw [←Complex.exp_add]
    push_cast
    ring_nf
  calc
    _ = ((∏ i, z i^p i)*(starRingEnd ℂ) (∏ i, z i^k i)) *
        (wave (t*replicaMultiplicityEnergy E p)*wave (-(t*replicaMultiplicityEnergy E k))) := by ring
    _ = _ := by rw [hm]; congr 2; ring

/-- Field variance of the difference of the two replica energy sums. -/
def pairVariance (v : J → I → ℝ) (b : ℝ) (p k : I → ℕ) : ℝ≥0 :=
  ⟨∑ l, (b*slopeDifference v p k l)^2, sum_nonneg fun _ _ => sq_nonneg _⟩

private theorem integrable_action (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ≥0) (u : ℝ) :
    Integrable (fun t : ℝ => (exp (-(c*t^2)/2):ℂ)*wave (u*t)) μ := by
  apply (integrable_const (1:ℝ)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold wave
    fun_prop
  · filter_upwards with t
    simp only [wave,norm_mul,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le,Complex.norm_exp]
    have h : -((c:ℝ)*t^2)/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg c.coe_nonneg (sq_nonneg t))) (by norm_num)
    simpa using (Real.exp_le_one_iff.mpr h)

variable [DecidableEq I]

private theorem fixed_date_moment (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ)
    (q : ℕ) (b t : ℝ) :
    (∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g)
      (fun i => z i*Complex.exp (((E i*t:ℝ):ℂ)*Complex.I)) (t*b)^q
        ∂(Measure.pi fun _ : J => gaussianReal 0 1)) =
      ∑ p ∈ univ.piAntidiag q, ∑ k ∈ univ.piAntidiag q,
        ((fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k) *
        ((exp (-(pairVariance v b p k*t^2)/2):ℂ)*wave ((replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)*t)) := by
  have hterm (p k : I → ℕ) (t : ℝ) :
      (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist (fun i => z i*wave (E i*t)) p k *
        (exp (-(∑ l, (t*b*slopeDifference v p k l)^2)/2):ℂ) =
      ((fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k) *
        ((exp (-(pairVariance v b p k*t^2)/2):ℂ)*wave ((replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)*t)) := by
    have hsq : (∑ l, (t*b*slopeDifference v p k l)^2) = (pairVariance v b p k:ℝ)*t^2 := by
      change _ = (∑ l, (b*slopeDifference v p k l)^2)*t^2
      rw [sum_mul]
      exact sum_congr rfl fun _ _ => by ring
    rw [hsq,twist_clock]
    ring
  rw [field_fidelity_moment]
  exact sum_congr rfl fun p _ => sum_congr rfl fun k _ => hterm p k t

/-- Every circuit moment can be averaged over a finite measure on dates. -/
theorem integrable_time_field_moment (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ)
    (q : ℕ) (b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t => ∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g)
      (fun i => z i*Complex.exp (((E i*t:ℝ):ℂ)*Complex.I)) (t*b)^q
        ∂(Measure.pi fun _ : J => gaussianReal 0 1)) μ := by
  simp_rw [fixed_date_moment]
  exact integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun k _ =>
    (integrable_action μ (pairVariance v b p k)
      (replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)).const_mul _

/-- Averaging an actual circuit twist over independent local fields and
a Gaussian observation date preserves its complex phase. Each replica
pair has its own base detuning and variance in the local fields. -/
theorem time_field_replica_moment (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ)
    (q : ℕ) (b m : ℝ) (V : ℝ≥0) :
    (∫ t, ∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g)
      (fun i => z i*Complex.exp (((E i*t:ℝ):ℂ)*Complex.I)) (t*b)^q
        ∂(Measure.pi fun _ : J => gaussianReal 0 1) ∂gaussianReal m V) =
      ∑ p ∈ univ.piAntidiag q, ∑ k ∈ univ.piAntidiag q,
        (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k *
          timeActionKernel m (replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)
            (pairVariance v b p k) V := by
  let C (p k : I → ℕ) := (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k
  let u (p k : I → ℕ) := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
  have hi (p k : I → ℕ) := (integrable_action (gaussianReal m V) (pairVariance v b p k) (u p k)).const_mul (C p k)
  simp_rw [fixed_date_moment]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun k _ => hi p k))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun k _ => hi p k)]
  apply sum_congr rfl
  intro k _
  rw [integral_const_mul]
  exact congrArg (C p k * ·) (gaussian_time_action m (u p k) (pairVariance v b p k) V)

#print axioms time_field_replica_moment
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
