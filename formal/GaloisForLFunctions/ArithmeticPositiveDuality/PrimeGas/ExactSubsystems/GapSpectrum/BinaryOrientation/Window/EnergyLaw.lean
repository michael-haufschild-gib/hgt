import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.VacuumLimit
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleWallDickmanLaw
import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw

/-! # The measured binary energy in the critical window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

private theorem profile_zero : profile 0 = 0 := by simp [profile,criticalEulerProfile]

/-- Ratios of full binary partitions recover all exponential moments in the window. -/
theorem partition_ratio_window (u v : ℂ) :
    Tendsto (fun N => partition N (windowTemperature N v)/partition N (windowTemperature N u))
      atTop (𝓝 (Complex.exp (profile v-profile u))) := by
  have H := (inverse_partition_window u).div (inverse_partition_window v)
    (mul_ne_zero criticalConstant_ne (Complex.exp_ne_zero _))
  have he : (criticalConstant*Complex.exp (-profile u))/(criticalConstant*Complex.exp (-profile v)) =
      Complex.exp (profile v-profile u) := by
    rw [mul_div_mul_left _ _ criticalConstant_ne,← Complex.exp_sub]
    congr 1
    ring
  rw [he] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : (Real.log N:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N from hN))).ne'
  change ((Real.log N:ℂ)/partition N (windowTemperature N u))/
    ((Real.log N:ℂ)/partition N (windowTemperature N v)) = _
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  calc _ = ((Real.log N:ℂ)*(Real.log N:ℂ)⁻¹)*
      (partition N (windowTemperature N v)*(partition N (windowTemperature N u))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hL,one_mul]

/-- Exponential moment of the scaled energy in the actual finite Born ensemble.
The real drift u gives inverse temperature 1-u/log N. -/
def energyMoment (N : ℕ) (u : ℝ) (z : ℂ) : ℂ :=
  ∑ x : Config N, (finiteSquarefreeBornWeight (packet N) (1-u/Real.log N) x:ℂ)*
    Complex.exp (z*((finiteSquarefreeHamiltonian (packet N) x/Real.log N:ℝ):ℂ))

theorem energyMoment_eq (N : ℕ) (u : ℝ) (z : ℂ) : energyMoment N u z =
    partition N (windowTemperature N ((u:ℂ)+z))/partition N (windowTemperature N u) := by
  have hd : windowTemperature N (u:ℂ) = ((1-u/Real.log N:ℝ):ℂ) := by
    simp only [windowTemperature,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_div]
  rw [energyMoment,hd,partition_real,← partition_trace,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteSquarefreeBornWeight_eq,Complex.ofReal_div,Complex.ofReal_exp,div_mul_eq_mul_div,
    ← Complex.exp_add]
  apply congrArg (fun c : ℂ => Complex.exp c/(finiteSquarefreePartition (packet N) (1-u/Real.log N):ℂ))
  unfold windowTemperature
  push_cast
  ring

theorem energyMoment_limit (u : ℝ) (z : ℂ) :
    Tendsto (fun N => energyMoment N u z) atTop (𝓝 (Complex.exp (profile ((u:ℂ)+z)-profile u))) :=
  (partition_ratio_window (u:ℂ) ((u:ℂ)+z)).congr (fun N => (energyMoment_eq N u z).symm)

private theorem born_nonnegative (N : ℕ) (s : ℝ) (x : Config N) :
    0 ≤ finiteSquarefreeBornWeight (packet N) s x := by
  rw [← norm_finiteSquarefreeSourceCoefficient_sq]
  exact sq_nonneg _

/-- Energy divided by log N, with probabilities from the normalized finite orientation wave. -/
def energyLaw (N : ℕ) (u : ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteAtomicObserverSpectrum (finiteSquarefreeBornWeight (packet N) (1-u/Real.log N))
    (fun x => finiteSquarefreeHamiltonian (packet N) x/Real.log N),
    finiteAtomicObserverSpectrum_isProbabilityMeasure _ _ (born_nonnegative N _)
      (sum_squarefreeBitWeight (packet N) (squarefreePrimeOccupation (1-u/Real.log N)))⟩

theorem energyLaw_characteristic (N : ℕ) (u t : ℝ) :
    charFun (energyLaw N u : Measure ℝ) t = energyMoment N u ((t:ℂ)*Complex.I) := by
  change charFun (finiteAtomicObserverSpectrum (finiteSquarefreeBornWeight (packet N) (1-u/Real.log N))
    (fun x => finiteSquarefreeHamiltonian (packet N) x/Real.log N)) t = _
  rw [charFun_finiteAtomicObserverSpectrum _ _ (born_nonnegative N _),energyMoment]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun c : ℂ => (finiteSquarefreeBornWeight (packet N) (1-u/Real.log N) x:ℂ)*Complex.exp c)
  push_cast
  ring

/-- Every real drift gives a weak limit, characterized by the displaced exponential-integral profile. -/
theorem energy_window_limit (u : ℝ) :
    ∃ ν : ProbabilityMeasure ℝ, (∀ t : ℝ, charFun (ν : Measure ℝ) t =
      Complex.exp (profile ((u:ℂ)+(t:ℂ)*Complex.I)-profile u)) ∧
      Tendsto (fun N => energyLaw N u) atTop (𝓝 ν) := by
  apply GaloisForLFunctions.HTGeometry.exists_tendsto_of_tendsto_charFun
  · exact (Complex.continuous_exp.comp ((continuous_profile.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).sub continuous_const)).continuousAt
  · intro t
    exact (energyMoment_limit u ((t:ℂ)*Complex.I)).congr
      (fun N => (energyLaw_characteristic N u t).symm)

private theorem profile_imaginary (t : ℝ) :
    profile ((t:ℂ)*Complex.I) = GaloisForLFunctions.HTGeometry.dickmanExponent t := by
  unfold profile GaloisForLFunctions.HTGeometry.dickmanExponent
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hx.1.ne')).mpr
  rw [mul_comm,criticalEulerProfile_mul]
  push_cast
  ring_nf

/-- The squarefree orientation of two copies and the q-Euler wall have the same limiting energy law. -/
theorem critical_energy_dickman :
    Tendsto (fun N => energyLaw N 0) atTop (𝓝 GaloisForLFunctions.HTGeometry.dickmanLaw) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  have H := energyMoment_limit 0 ((t:ℂ)*Complex.I)
  rw [Complex.ofReal_zero,zero_add,profile_zero,sub_zero,profile_imaginary,
    ← GaloisForLFunctions.HTGeometry.charFun_dickmanLaw] at H
  exact H.congr (fun N => (energyLaw_characteristic N 0 t).symm)

#print axioms partition_ratio_window
#print axioms energyMoment_eq
#print axioms energyMoment_limit
#print axioms energyLaw_characteristic
#print axioms energy_window_limit
#print axioms critical_energy_dickman

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
