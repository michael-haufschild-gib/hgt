import GaloisForLFunctions.RHTower.PolynomialFockSharpPhaseTransition
import GaloisForLFunctions.RHTower.PolynomialMomentFockThetaTrace
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCompactOpen
import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex

/-!
# Pointed polynomial-Fock prime--theta carrier

The theta trace is bundled as a continuous linear map from the exact moment-Fock Hilbert carrier
to the compact-open Fréchet space of entire functions.  Pairing it with the normalized all-prime
sampler gives the literal joint incidence from the pointed-carrier theorem.  The distinguished
constant vector has the exact completed-zeta trace.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Theta trace as a compact-open continuous function. -/
def polynomialMomentFockThetaTraceContinuousMap
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) : C(ℂ, ℂ) :=
  ⟨polynomialMomentFockThetaTrace m hm f,
    (differentiable_polynomialMomentFockThetaTrace m hm f).continuous⟩

@[simp] theorem polynomialMomentFockThetaTraceContinuousMap_apply
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    polynomialMomentFockThetaTraceContinuousMap m hm f z =
      polynomialMomentFockThetaTrace m hm f z := rfl

/-- Algebraic theta-trace map into the compact-open ambient continuous-map space. -/
def polynomialMomentFockThetaTraceCompactOpenLinearMap
    (m : ℝ) (hm : 2 ≤ m) : MomentFock →ₗ[ℂ] C(ℂ, ℂ) where
  toFun := polynomialMomentFockThetaTraceContinuousMap m hm
  map_add' f g := by
    ext z
    exact polynomialMomentFockThetaTrace_add m hm f g z
  map_smul' c f := by
    ext z
    exact polynomialMomentFockThetaTrace_smul m hm c f z

/-- Vertical-strip estimates imply continuity into the compact-open topology. -/
theorem continuous_polynomialMomentFockThetaTraceCompactOpenLinearMap
    (m : ℝ) (hm : 2 ≤ m) :
    Continuous (polynomialMomentFockThetaTraceCompactOpenLinearMap m hm) := by
  apply continuous_of_continuousAt_zero
    (polynomialMomentFockThetaTraceCompactOpenLinearMap m hm)
  rw [ContinuousAt, map_zero]
  change Tendsto
    (polynomialMomentFockThetaTraceCompactOpenLinearMap m hm)
    (nhds 0) (nhds 0)
  rw [HTGeometry.hasBasis_nhds_zero_continuousMap.tendsto_right_iff]
  rintro ⟨K, ε⟩ ⟨hK, hε⟩
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (f := fun z : ℂ => z.im) Complex.continuous_im.continuousOn
  let A : ℝ := max 0 R
  let C : ℝ := polynomialMomentFockThetaTraceWeightBound m (2 * Real.pi * A)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact polynomialMomentFockThetaTraceWeightBound_nonneg _ _
  have hden : 0 < C + 1 := by linarith
  filter_upwards [Metric.ball_mem_nhds (0 : MomentFock) (div_pos hε hden)] with f hf
  intro z hzK
  have hfNorm : ‖f‖ < ε / (C + 1) := by
    simpa [Metric.mem_ball, dist_zero_right] using hf
  have hz : |z.im| ≤ A := by
    have hzR := hR z hzK
    rw [Real.norm_eq_abs] at hzR
    exact hzR.trans (le_max_right 0 R)
  have htrace := norm_polynomialMomentFockThetaTrace_le_verticalStrip
    m hm f (R := A) hz
  change ‖polynomialMomentFockThetaTrace m hm f z‖ < ε
  calc
    ‖polynomialMomentFockThetaTrace m hm f z‖ ≤ C * ‖f‖ := by
      simpa [C] using htrace
    _ ≤ (C + 1) * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f)
    _ < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left hfNorm hden
    _ = ε := by field_simp

/-- Entire theta trace as a continuous linear map into the compact-open Fréchet carrier. -/
def polynomialMomentFockThetaTraceCompactOpen
    (m : ℝ) (hm : 2 ≤ m) :
    MomentFock →L[ℂ] DeningerCompactOpenEntire where
  toFun f :=
    ⟨polynomialMomentFockThetaTraceContinuousMap m hm f,
      differentiable_polynomialMomentFockThetaTrace m hm f⟩
  map_add' f g := by
    ext z
    exact polynomialMomentFockThetaTrace_add m hm f g z
  map_smul' c f := by
    ext z
    exact polynomialMomentFockThetaTrace_smul m hm c f z
  cont := by
    exact Continuous.subtype_mk
      (continuous_polynomialMomentFockThetaTraceCompactOpenLinearMap m hm)
      (fun f => differentiable_polynomialMomentFockThetaTrace m hm f)

@[simp] theorem polynomialMomentFockThetaTraceCompactOpen_apply
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    polynomialMomentFockThetaTraceCompactOpen m hm f z =
      polynomialMomentFockThetaTrace m hm f z := rfl

/-- Joint normalized-prime and compact-open theta-trace incidence. -/
def polynomialPrimeThetaPointedCarrier (m : ℝ) (hm : 4 ≤ m) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo × DeningerCompactOpenEntire :=
  (polynomialCriticalPrimeSamplingOperator m hm).prod
    (polynomialMomentFockThetaTraceCompactOpen m (by linarith))

@[simp] theorem polynomialPrimeThetaPointedCarrier_apply
    (m : ℝ) (hm : 4 ≤ m) (f : MomentFock) :
    polynomialPrimeThetaPointedCarrier m hm f =
      (polynomialCriticalPrimeSamplingOperator m hm f,
        polynomialMomentFockThetaTraceCompactOpen m (by linarith) f) := rfl

theorem continuous_polynomialPrimeThetaPointedCarrier
    (m : ℝ) (hm : 4 ≤ m) :
    Continuous (polynomialPrimeThetaPointedCarrier m hm) :=
  (polynomialPrimeThetaPointedCarrier m hm).continuous

theorem polynomialPrimeThetaPointedCarrier_sampling_isCompactOperator_iff
    {m : ℝ} (hm : 4 ≤ m) :
    IsCompactOperator (polynomialCriticalPrimeSamplingOperator m hm) ↔ 4 < m :=
  polynomialCriticalPrimeSamplingOperator_isCompactOperator_iff hm

theorem polynomialPrimeThetaPointedCarrier_moment
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) (f : MomentFock) :
    polynomialMomentFockThetaMomentFunctional m (by linarith) n f =
      iteratedDeriv n ((polynomialPrimeThetaPointedCarrier m hm f).2 : ℂ → ℂ) 0 := by
  rw [polynomialMomentFockThetaMomentFunctional_apply]
  rfl

/-- Exact completed critical trace of the distinguished constant vector in the joint carrier. -/
theorem completedRiemannZeta₀_critical_eq_polynomialPrimeThetaPointedCarrier_one
    (m : ℝ) (hm : 4 ≤ m) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) =
      (polynomialPrimeThetaPointedCarrier m hm
        (polynomialMomentFockOne m (by linarith))).2
          ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  simpa using completedRiemannZeta₀_critical_eq_polynomialMomentFockThetaTrace_one
    m (by linarith) t

end

end RHTower
