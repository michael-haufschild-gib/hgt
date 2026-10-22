import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalCutoffTime
/-! All native and cutoff channels in one continuous causal spatial source and Bochner transform. -/
open MeasureTheory Set Filter GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave
noncomputable section

/-- A common nonempty Laplace chamber for all three actual principal evolutions. -/
def causalPrincipalThreshold (q : XiZeroCopy) : ℝ := 1+∑ i : Fin 3, principalResponseGrowth q i

theorem causalPrincipalThreshold_pos (q : XiZeroCopy) : 0 < causalPrincipalThreshold q := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => principalResponseGrowth_nonneg q i)
  unfold causalPrincipalThreshold
  linarith

theorem principalResponseGrowth_lt_threshold (q : XiZeroCopy) (i : Fin 3) :
    principalResponseGrowth q i < causalPrincipalThreshold q := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => principalResponseGrowth_nonneg q j)
    (Finset.mem_univ i)
  unfold causalPrincipalThreshold
  linarith

/-- The native square remainder and all three constructed cutoff-commutator channels. -/
def causalCuspSourceVector (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ : ℝ) : SpatialSpace :=
  timeCuspMainVector q branch a τ+∑ i : Fin 3, principalCutoffTimeVector q branch a i τ

theorem causalCuspSourceVector_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (causalCuspSourceVector q branch a) := by
  unfold causalCuspSourceVector
  exact (timeCuspMainVector_continuous q branch a).add
    (continuous_finsetSum _ (fun i _ => principalCutoffTimeVector_continuous q branch a i))

theorem causalCuspSourceVector_zero_of_nonpos (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ : ℝ) (hτ : τ ≤ 0) : causalCuspSourceVector q branch a τ = 0 := by
  simp only [causalCuspSourceVector,timeCuspMainVector_zero_before_zero q branch a τ hτ,
    principalCutoffTimeVector_zero_of_nonpos q branch a _ τ hτ,Finset.sum_const_zero,add_zero]

/-- Absolute convergence is proved in the original joint spatial norm for the entire assembled source. -/
theorem causalCuspSourceVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalPrincipalThreshold q < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) (Ioi 0) := by
  have hw₀ : -2 < w.re := by have := causalPrincipalThreshold_pos q; linarith
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    principalCutoffTimeVector_laplace_integrable q branch a i w
      ((principalResponseGrowth_lt_threshold q i).trans hw))
  apply ((timeCuspMainVector_laplace_integrable q branch a w hw₀).add hi).congr
  filter_upwards [] with τ
  change Complex.exp (-w*(τ:ℂ)) • timeCuspMainVector q branch a τ+
      (∑ i : Fin 3, Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) =
    Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ
  simp only [causalCuspSourceVector,smul_add,Finset.smul_sum]

/-- The joint transform is the native original transform plus every retained cutoff-response transform.
Identification of the latter with endpoint Green solutions is a separate equation. -/
theorem causalCuspSourceVector_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : causalPrincipalThreshold q < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) =
      cuspMainLaplaceVector q branch a w (by have := causalPrincipalThreshold_pos q; linarith)+
        ∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) := by
  have hw₀ : -2 < w.re := by have := causalPrincipalThreshold_pos q; linarith
  have hi (i : Fin 3) := principalCutoffTimeVector_laplace_integrable q branch a i w
    ((principalResponseGrowth_lt_threshold q i).trans hw)
  simp only [causalCuspSourceVector,smul_add,Finset.smul_sum]
  rw [integral_add (timeCuspMainVector_laplace_integrable q branch a w hw₀)
    (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i),timeCuspMainVector_laplace q branch a w hw₀]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact principalCutoffTimeVector_laplace q branch a i w
    ((principalResponseGrowth_lt_threshold q i).trans hw)

end
end RHTower.D4BMJointSource
