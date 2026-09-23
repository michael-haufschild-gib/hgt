import GaloisForLFunctions.HTGeometry.TracelessReplicaDyadicActionShellLaw

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric finite window in logarithmic observation scale. -/
def bilateralDyadicGaussianActionMass (action : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2 * N),
    dyadicGaussianActionKernel
      (((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) * action)

theorem bilateralDyadicGaussianActionMass_eq (action : ℝ) (N : ℕ) :
    bilateralDyadicGaussianActionMass action N =
      Real.exp (-((((1 / 2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2) -
        Real.exp (-((((2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2) := by
  let f : ℕ → ℝ := fun j =>
    Real.exp (-((((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2)
  have hterm : ∀ j,
      dyadicGaussianActionKernel
          (((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) * action) =
        f j - f (j + 1) := by
    intro j
    unfold dyadicGaussianActionKernel f
    congr 2
    rw [pow_succ]
    ring_nf
  rw [bilateralDyadicGaussianActionMass]
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  dsimp [f]
  congr 2
  · norm_num
  · congr 3
    have hpow :
        (2 : ℝ) ^ (2 * N) * (1 / 2 : ℝ) ^ N = (2 : ℝ) ^ N := by
      rw [show 2 * N = N * 2 by omega, pow_mul, div_pow]
      field_simp [pow_ne_zero]
      simp
    rw [hpow]

/-- Every nonzero action carries one unit of scale-complete dyadic mass;
exact zero action carries none. No minimum action gap is present. -/
theorem tendsto_bilateralDyadicGaussianActionMass (action : ℝ) :
    Tendsto (bilateralDyadicGaussianActionMass action)
      atTop (𝓝 (if action = 0 then 0 else 1)) := by
  by_cases ha : action = 0
  · subst action
    have hzero : bilateralDyadicGaussianActionMass 0 = fun _ => 0 := by
      funext N
      simp [bilateralDyadicGaussianActionMass,
        dyadicGaussianActionKernel]
    rw [hzero]
    simpa only [ite_true] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · rw [if_neg ha]
    have hloBase : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hloArg : Tendsto
        (fun N : ℕ => ((1 / 2 : ℝ) ^ N) * action)
        atTop (𝓝 0) := by
      simpa using hloBase.mul_const action
    have hloExponent : Tendsto
        (fun N : ℕ => -((((1 / 2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2)
        atTop (𝓝 0) := by
      convert ((hloArg.pow 2).neg.div_const 2) using 1
      all_goals norm_num
    have hlo : Tendsto
        (fun N : ℕ => Real.exp
          (-((((1 / 2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2))
        atTop (𝓝 1) := by
      convert Real.continuous_exp.continuousAt.tendsto.comp hloExponent using 1
      · rfl
      · rw [Real.exp_zero]
    have hhiBase : Tendsto (fun N : ℕ => (4 : ℝ) ^ N)
        atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have ha2 : 0 < action ^ (2 : ℕ) / 2 := by positivity
    have hhiPositive : Tendsto
        (fun N : ℕ => (4 : ℝ) ^ N * (action ^ (2 : ℕ) / 2))
        atTop atTop := hhiBase.atTop_mul_const ha2
    have hhiExponent : Tendsto
        (fun N : ℕ => -((((2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2)
        atTop atBot := by
      have hneg := tendsto_neg_atTop_atBot.comp hhiPositive
      convert hneg using 1
      funext N
      change -((((2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2 =
        -((4 : ℝ) ^ N * (action ^ (2 : ℕ) / 2))
      have hfour : (4 : ℝ) ^ N = ((2 : ℝ) ^ N) ^ (2 : ℕ) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul,
          mul_comm 2 N, pow_mul]
      rw [hfour]
      ring
    have hhi : Tendsto
        (fun N : ℕ => Real.exp
          (-((((2 : ℝ) ^ N) * action) ^ (2 : ℕ)) / 2))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hhiExponent
    have hsub := hlo.sub hhi
    norm_num at hsub
    exact hsub.congr' (Filter.Eventually.of_forall fun N =>
      (bilateralDyadicGaussianActionMass_eq action N).symm)

/-- Bilateral dyadic mass of a finite signed spectral packet. -/
def bilateralDyadicGaussianActionPacket
    {ι : Type*} (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (N : ℕ) : ℂ :=
  ∑ i ∈ support, coefficient i *
    (bilateralDyadicGaussianActionMass (detuning i) N : ℂ)

/-- One dyadic wavelet is exactly the packet-weighted sum of scalar
band-pass kernels. -/
theorem dyadicGaussianActionWavelet_eq_kernel_sum
    {ι : Type*} (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) :
    dyadicGaussianActionWavelet support coefficient detuning time =
      ∑ i ∈ support, coefficient i *
        (dyadicGaussianActionKernel (time * detuning i) : ℂ) := by
  unfold dyadicGaussianActionWavelet gaussianActionHeatPacket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (2 * time) * detuning i =
      2 * (time * detuning i) by ring,
    ← mul_sub, gaussianObserverActionKernel_sub_two_eq_dyadic]

/-- Exact packet identity: the symmetric logarithmic-scale window is the
sum of the actual dyadic Gaussian observer wavelets in that window. -/
theorem bilateralDyadicGaussianActionPacket_eq_wavelet_sum
    {ι : Type*} (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (N : ℕ) :
    bilateralDyadicGaussianActionPacket support coefficient detuning N =
      ∑ j ∈ Finset.range (2 * N),
        dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) := by
  simp_rw [dyadicGaussianActionWavelet_eq_kernel_sum]
  rw [bilateralDyadicGaussianActionPacket]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum]
  congr 1
  rw [bilateralDyadicGaussianActionMass]
  push_cast
  rfl

/-- **Gap-free scale-complete packet law.** Every nonzero spectral action
contributes its coefficient exactly once across all logarithmic observation
scales; exact collisions contribute zero. -/
theorem tendsto_bilateralDyadicGaussianActionPacket
    {ι : Type*} (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) :
    Tendsto (bilateralDyadicGaussianActionPacket support coefficient detuning)
      atTop (𝓝 (∑ i ∈ support,
        if detuning i = 0 then 0 else coefficient i)) := by
  unfold bilateralDyadicGaussianActionPacket
  apply tendsto_finsetSum
  intro i hi
  have hreal := tendsto_bilateralDyadicGaussianActionMass (detuning i)
  have hcomplex : Tendsto
      (fun N => (bilateralDyadicGaussianActionMass (detuning i) N : ℂ))
      atTop (𝓝 ((if detuning i = 0 then 0 else 1 : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hmul := hcomplex.const_mul (coefficient i)
  by_cases hzero : detuning i = 0 <;> simpa [hzero] using hmul

/-- Scale-complete dyadic reporter for the signed paired-replica packet. -/
def scaleCompleteComplexReplicaActionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (r N : ℕ) : ℂ :=
  bilateralDyadicGaussianActionPacket (complexReplicaPairSupport I r)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy) N

/-- Exact observer realization of the scale-complete replica reporter. -/
theorem scaleCompleteComplexReplicaActionMass_eq_wavelet_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ)
    (r N : ℕ) :
    scaleCompleteComplexReplicaActionMass coefficient energy r N =
      ∑ j ∈ Finset.range (2 * N),
        complexReplicaDyadicActionWavelet coefficient energy r
          ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ N) := by
  exact bilateralDyadicGaussianActionPacket_eq_wavelet_sum
    (complexReplicaPairSupport I r)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy) N

theorem complexReplicaNonzeroActionSum_eq_noncollisionSectorMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (r : ℕ) :
    (∑ pair ∈ complexReplicaPairSupport I r,
      if complexReplicaPairDetuning energy pair = 0 then 0
      else complexReplicaPairCoefficient coefficient pair) =
    complexReplicaSectorMass coefficient r
      (fun p q => replicaMultiplicityEnergy energy p ≠
        replicaMultiplicityEnergy energy q) := by
  classical
  unfold complexReplicaPairSupport complexReplicaPairDetuning
    complexReplicaPairCoefficient complexReplicaSectorMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : replicaMultiplicityEnergy energy p =
      replicaMultiplicityEnergy energy q
  · simp [h]
  · simp [h, sub_ne_zero.mpr h]

/-- **Scale-complete replica action law.** Across all dyadic observation
scales, every noncollision replica pair is recovered exactly once and every
exact recurrence pair is erased, with no spectral-gap premise or remainder. -/
theorem tendsto_scaleCompleteComplexReplicaActionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : I → ℂ) (energy : I → ℝ) (r : ℕ) :
    Tendsto (scaleCompleteComplexReplicaActionMass coefficient energy r)
      atTop (𝓝 (complexReplicaSectorMass coefficient r
        (fun p q => replicaMultiplicityEnergy energy p ≠
          replicaMultiplicityEnergy energy q))) := by
  rw [← complexReplicaNonzeroActionSum_eq_noncollisionSectorMass]
  exact tendsto_bilateralDyadicGaussianActionPacket
    (complexReplicaPairSupport I r)
    (complexReplicaPairCoefficient coefficient)
    (complexReplicaPairDetuning energy)

end

end GaloisForLFunctions.HTGeometry
