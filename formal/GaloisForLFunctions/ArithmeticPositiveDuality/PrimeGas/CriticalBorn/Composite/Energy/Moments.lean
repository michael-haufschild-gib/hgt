import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy.Reading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Laws

/-! # Exact factorization of measured composite energy moments -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy

open Filter Finset Real MeasureTheory ProbabilityTheory
open Crossover
open GaloisForLFunctions.HTGeometry
open scoped Topology

private theorem index_re (a t : ℝ) : (indexParameter a t).re=(1-a)/2 := by
  simp [indexParameter]

private theorem total_mass (m : ℕ) (a t x : ℝ) :
    ‖wave m (indexParameter a t) x‖^2=(powerMass a x)^m := by
  rw [wave_mass,rawWave_sq,index_re,show 1-2*((1-a)/2)=a by ring]

private theorem shell_weight (m : ℕ) (a t x : ℝ) (n : ℕ+) :
    ‖wave m (indexParameter a t) x n‖^2=(multiplicity m x n:ℝ)*exp ((a-1)*energy n) := by
  rw [wave_apply,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    sq_sqrt (Nat.cast_nonneg _),norm_heat,sq,←exp_add,index_re]
  have e : -((1-a)/2)*energy n+ -((1-a)/2)*energy n=(a-1)*energy n := by ring
  rw [e]

/-- Reading the k-th energy moment shifts the heat index by k/log N.
The composite norm identity then gives an exact power of the elementary moment. -/
theorem moment_power (m : ℕ) (a t : ℝ) {N : ℕ} (hN : 2≤N) (k : ℕ) :
    (∫ y, (y:ℝ)^k ∂(codedLaw m a t N : Measure unitInterval)) =
      (∫ y, (y:ℝ)^k ∂(Dynamics.codeLaw a N : Measure unitInterval))^m := by
  have term (n : ℕ+) (hn : n∈shells m N) :
      ‖wave m (indexParameter a t) N n‖^2*(code m N n:ℝ)^k =
        exp (-(k:ℝ)*(m:ℝ))*‖wave m (indexParameter (a+k/log N) t) N n‖^2 := by
    have id : (a-1)*energy n+(k:ℝ)*(energy n/log N-m) =
        -(k:ℝ)*(m:ℝ)+(a+k/log N-1)*energy n := by ring
    rw [code_on_shell hN hn,←exp_nat_mul,shell_weight,shell_weight,mul_assoc,←exp_add,id,exp_add]
    ring
  rw [codedLaw,expectation,sum_congr rfl term,←Finset.mul_sum,←norm_shell_sum,total_mass,total_mass,
    Dynamics.code_moment a hN k,div_pow,mul_pow,←exp_nat_mul]
  rw [show -(k:ℝ)*(m:ℝ)=(m:ℝ)*(-(k:ℝ)) by ring]

private theorem elementary_moment (c : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => ∫ z,(z:ℝ)^k ∂(Dynamics.codeLaw (drift c N/log N) N : Measure unitInterval))
      atTop (𝓝 ((Bulk.bulkWeight c:ℝ)*exp (-(k:ℝ))+(1-(Bulk.bulkWeight c:ℝ)))) := by
  let f : C(unitInterval,ℝ) := ⟨fun y => (y:ℝ)^k,continuous_subtype_val.pow k⟩
  have h := (continuous_integral_real_continuousMap f).continuousAt.tendsto.comp (Dynamics.code_law_limit c)
  change Tendsto _ _ (𝓝 (∫ z,f z ∂bernoulliMeasure (Dynamics.code 0) (Dynamics.code 1) (Bulk.bulkWeight c))) at h
  rw [integral_bernoulliMeasure] at h
  have lo : f (Dynamics.code 0)=exp (-(k:ℝ)) := by
    change (exp ((0:ℝ)-1))^k=_
    rw [←exp_nat_mul]
    congr 1
    ring
  have hi : f (Dynamics.code 1)=1 := by change (exp ((1:ℝ)-1))^k=_; rw [sub_self,exp_zero,one_pow]
  rw [lo,hi] at h
  simpa only [Function.comp_def,smul_eq_mul,mul_one,f,ContinuousMap.coe_mk] using h

/-- The common clock may vary arbitrarily with the cutoff. -/
theorem moment_limit (m : ℕ) (c : ℝ) (t : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => ∫ z,(z:ℝ)^k ∂(codedLaw m (drift c N/log N) (t N) N : Measure unitInterval))
      atTop (𝓝 (((Bulk.bulkWeight c:ℝ)*exp (-(k:ℝ))+(1-(Bulk.bulkWeight c:ℝ)))^m)) := by
  apply ((elementary_moment c k).pow m).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (moment_power m _ _ hN k).symm

#print axioms moment_power
#print axioms moment_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Energy
