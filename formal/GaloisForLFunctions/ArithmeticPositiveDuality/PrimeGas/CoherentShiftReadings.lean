import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DilationGibbsState

/-!
# Coherent creation and annihilation readings

A square root of the Gibbs distribution with multiplicative phase is a unit
vector and a simultaneous eigenvector for all arithmetic co-shifts. Its
shifted residue readings retain the phase at the partition pole.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology ContinuousLinearMap
open _root_.RHTower.PrimeCoShift
open scoped ComplexConjugate

/-- Eigenvalue of the co-shift on a square root of the Gibbs distribution. -/
def coherentFactor (χ : ℕ+ → Circle) (β : ℝ) (a : ℕ+) : ℂ :=
  (χ a : ℂ) * (Real.exp (-β * energy a / 2) : ℝ)

theorem coherentFactor_mul (χ : ℕ+ →* Circle) (β : ℝ) (a b : ℕ+) :
    coherentFactor χ β (a*b) = coherentFactor χ β a * coherentFactor χ β b := by
  simp only [coherentFactor, energy_mul, map_mul, Circle.coe_mul, mul_add, add_div,
    Real.exp_add, Complex.ofReal_mul]
  ring

private theorem factor_sq (χ : ℕ+ → Circle) (β : TraceTemperature) (n : ℕ+) :
    ‖coherentFactor χ β.val n‖^2 = thermalWeight β n := by
  rw [coherentFactor, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add, thermalWeight, add_halves]

private def partitionMass (β : TraceTemperature) := ∑' n, thermalWeight β n

private theorem mass_pos (β : TraceTemperature) : 0 < partitionMass β :=
  (thermalWeight_pos β 1).trans_le ((thermalWeight_summable β).le_tsum 1
    (fun n _ => (thermalWeight_pos β n).le))

/-- Unit shell vector with Gibbs probabilities and phase χ(n). -/
def coherentVector (χ : ℕ+ → Circle) (β : TraceTemperature) : Gas :=
  ⟨fun n => coherentFactor χ β.val n / (Real.sqrt (partitionMass β) : ℂ), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_div, div_pow, factor_sq,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mass_pos β).le] using (thermalWeight_summable β).div_const (partitionMass β)⟩

theorem coherentVector_shell (χ : ℕ+ → Circle) (β : TraceTemperature) (n : ℕ+) :
    ‖coherentVector χ β n‖^2 = thermalWeight β n / (riemannZeta β.val).re := by
  change ‖coherentFactor χ β.val n / (Real.sqrt (partitionMass β) : ℂ)‖^2 = _
  rw [norm_div, div_pow, factor_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (mass_pos β).le, ← thermalWeight_partition]
  rfl

theorem coherentVector_unit (χ : ℕ+ → Circle) (β : TraceTemperature) :
    ‖coherentVector χ β‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [one_pow]
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ+ => ℂ) (by norm_num) (coherentVector χ β)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, coherentVector_shell, tsum_div_const,
    ← thermalWeight_partition, Complex.ofReal_re] at h
  exact h.trans (div_self (mass_pos β).ne')

theorem coShift_coherentVector (χ : ℕ+ →* Circle) (β : TraceTemperature) (a : ℕ+) :
    primeCoShift a (coherentVector χ β) = coherentFactor χ β.val a • coherentVector χ β := by
  apply lp.ext
  funext n
  change coherentFactor χ β.val (a*n) / _ = coherentFactor χ β.val a * (coherentFactor χ β.val n / _)
  rw [coherentFactor_mul, mul_div_assoc]

/-- Vector expectation in the normalized square-root Gibbs state. -/
def coherentReading (χ : ℕ+ → Circle) (β : TraceTemperature) (A : Gas →L[ℂ] Gas) : ℂ :=
  inner ℂ (coherentVector χ β) (A (coherentVector χ β))

theorem coherentReading_coShift (χ : ℕ+ →* Circle) (β : TraceTemperature) (a : ℕ+) :
    coherentReading χ β (primeCoShift a) = coherentFactor χ β.val a := by
  rw [coherentReading, coShift_coherentVector, inner_smul_right, inner_self_eq_norm_sq_to_K,
    coherentVector_unit]
  simp

/-- Every shifted observable factors through the two measured co-shift eigenvalues. -/
theorem coherentReading_shift (χ : ℕ+ →* Circle) (β : TraceTemperature) (a b : ℕ+)
    (A : Gas →L[ℂ] Gas) :
    coherentReading χ β (shiftObservable a b A) =
      conj (coherentFactor χ β.val a) * coherentFactor χ β.val b * coherentReading χ β A := by
  unfold coherentReading
  rw [shiftObservable, comp_apply, comp_apply, ← adjoint_inner_left (primeShift a).toContinuousLinearMap,
    ← primeCoShift_eq_adjoint, coShift_coherentVector, coShift_coherentVector, map_smul,
    inner_smul_left, inner_smul_right, mul_assoc]

/-- Every periodic diagonal has the same reading as in the Gibbs trace state. -/
theorem coherentReading_residue (χ : ℕ+ → Circle) (β : TraceTemperature) (m : ℕ+)
    (F : ZMod (m : ℕ) → ℂ) :
    coherentReading χ β (residueObservable m F) = periodicGibbsMean m F β := by
  rw [coherentReading, lp.inner_eq_tsum, periodicGibbsMean, periodicGibbs_trace_series,
    partition_eq_zeta, ← tsum_div_const]
  apply tsum_congr
  intro n
  change F (n : ℕ) * coherentVector χ β n * conj (coherentVector χ β n) = _
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, coherentVector_shell,
    Complex.ofReal_div, ← thermalWeight_partition]
  have hw : (thermalWeight β n : ℂ) = heat β.val n := by
    simp only [thermalWeight, heat, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [Complex.ofReal_re, hw, mul_div_assoc]

theorem coherentFactor_one_temperature (χ : ℕ+ →* Circle) (a : ℕ+) :
    coherentFactor χ 1 a = singletonAmplitude χ a := by
  have hp : (0 : ℝ) < (a : ℕ) := Nat.cast_pos.mpr a.pos
  change (χ a : ℂ) * (Real.exp (-(1:ℝ) * energy a / 2) : ℝ) = _ / (Real.sqrt (a : ℕ) : ℂ)
  rw [neg_one_mul, neg_div, Real.exp_neg, Real.exp_half, energy, Real.exp_log hp,
    Complex.ofReal_inv, div_eq_mul_inv]

private theorem factor_limit (χ : ℕ+ →* Circle) (a : ℕ+) :
    Tendsto (fun β : TraceTemperature => coherentFactor χ β.val a) atPartitionPole
      (𝓝 (singletonAmplitude χ a)) := by
  rw [← coherentFactor_one_temperature]
  have hc : Continuous (fun x : ℝ => coherentFactor χ x a) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_neg.mul continuous_const).div_const 2)))
  exact (hc.tendsto 1).comp (tendsto_comap.mono_right nhdsWithin_le_nhds)

/-- Mixed shift readings preserve the relative phase of creation blocks at the pole. -/
theorem coherent_shift_boundary (χ : ℕ+ →* Circle) (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (a b : ℕ+) :
    Tendsto (fun β => coherentReading χ β (shiftObservable a b (residueObservable m F)))
      atPartitionPole (𝓝 (conj (singletonAmplitude χ a) * singletonAmplitude χ b *
        ((∑ j, F j) / (m : ℕ)))) := by
  have ha := Complex.continuous_conj.continuousAt.tendsto.comp (factor_limit χ a)
  exact ((ha.mul (factor_limit χ b)).mul (periodicGibbsMean_limit m F)).congr'
    (Eventually.of_forall fun β => by
      exact ((coherentReading_shift χ β a b _).trans (congrArg
        (fun z => conj (coherentFactor χ β.val a) * coherentFactor χ β.val b * z)
        (coherentReading_residue χ β m F))).symm)

/-- The relative reading of two annihilators realizes the nested-refinement amplitude. -/
theorem coShift_ratio_boundary (χ : ℕ+ →* Circle) (m n : ℕ+) :
    Tendsto (fun β => coherentReading χ β (primeCoShift n) / coherentReading χ β (primeCoShift m))
      atPartitionPole (𝓝 (refinementAmplitude χ m n)) := by
  have hm : singletonAmplitude χ m ≠ 0 := by
    rw [← coherentFactor_one_temperature]
    exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  apply ((factor_limit χ n).div (factor_limit χ m) hm).congr'
  exact Eventually.of_forall fun β => congrArg₂ (· / ·)
    (coherentReading_coShift χ β n).symm (coherentReading_coShift χ β m).symm

#print axioms coherentVector_shell
#print axioms coherentVector_unit
#print axioms coShift_coherentVector
#print axioms coherentReading_coShift
#print axioms coherentReading_shift
#print axioms coherentReading_residue
#print axioms coherent_shift_boundary
#print axioms coShift_ratio_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
