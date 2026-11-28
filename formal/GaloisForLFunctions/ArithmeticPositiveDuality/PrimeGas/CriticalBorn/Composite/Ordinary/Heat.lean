import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Multiplicity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Gram

/-! # One ordinary heat amplitude per distinct fixed-occupation shell -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Finset Real
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

/-- Ordinary restriction of the gas heat wave to labels with m excitations. -/
def wave (m : ℕ) (s : ℂ) (x : ℝ) : Gas :=
  ∑ n ∈ shells m x, lp.single 2 n (heat s n)

theorem wave_apply (m : ℕ) (s : ℂ) (x : ℝ) (n : ℕ+) :
    wave m s x n = if n∈shells m x then heat s n else 0 := by
  rw [wave,lp.coeFn_sum,Finset.sum_apply]
  simp only [lp.single_apply,Pi.single_apply,sum_ite_eq]

/-- The trace-class Gibbs operator produces this state from the uniform
sector vector in its trace half-plane. -/
theorem gibbs_preparation (m : ℕ) (s : {z : ℂ // 1<z.re}) (x : ℝ) :
    gibbsOperator s (wave m 0 x)=wave m s.val x := by
  apply Subtype.ext
  funext n
  rw [gibbsOperator_apply,wave_apply,wave_apply]
  by_cases h : n∈shells m x <;> simp [h,heat]

def mass (m : ℕ) (a x : ℝ) := ∑ n ∈ shells m x, exp ((a-1)*energy n)

/-- Squared amplitude at the power index of a complex heat parameter. -/
theorem heat_square (s : ℂ) (n : ℕ+) :
    ‖heat s n‖^2=exp (((1-2*s.re)-1)*energy n) := by
  rw [norm_heat,sq,←exp_add]
  congr 1
  ring

theorem wave_pair (m : ℕ) (s v : ℂ) (x : ℝ) :
    inner ℂ (wave m s x) (wave m v x)=∑ n ∈ shells m x, conj (heat s n)*heat v n := by
  calc
    _ = ∑ n ∈ shells m x, inner ℂ (lp.single 2 n (heat s n)) (wave m v x) := sum_inner _ _ _
    _ = _ := by
      refine sum_congr rfl fun n hn => ?_
      rw [lp.inner_single_left,RCLike.inner_apply,wave_apply,if_pos hn,mul_comm]

theorem wave_mass (m : ℕ) (s : ℂ) (x : ℝ) : ‖wave m s x‖^2=mass m (1-2*s.re) x := by
  have lhs : ((‖wave m s x‖^2:ℝ):ℂ) = inner ℂ (wave m s x) (wave m s x) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.ofReal_pow]
    rfl
  apply Complex.ofReal_injective
  rw [lhs,wave_pair,mass,Complex.ofReal_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.conj_mul',←heat_square,Complex.ofReal_pow]

/-- All complementary phases cancel before summing over distinct integer labels. -/
theorem reflected_pair (m : ℕ) (s : ℂ) (x : ℝ) :
    inner ℂ (wave m s x) (wave m (1-conj s) x)=(mass m 0 x:ℂ) := by
  rw [wave_pair,mass,Complex.ofReal_sum]
  refine sum_congr rfl fun n _ => ?_
  have hc : conj (heat s n)=heat (conj s) n := by simp [heat,←Complex.exp_conj]
  rw [hc,mul_comm,←heat_add,sub_add_cancel,heat,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The order-weighted mass is the known power of the elementary mass. -/
theorem weighted_total (m : ℕ) (a x : ℝ) :
    ∑ n ∈ shells m x, (multiplicity m x n:ℝ)*exp ((a-1)*energy n)=(powerMass a x)^m := by
  let s : ℂ := (((1-a)/2:ℝ):ℂ)
  have idx : 1-2*s.re=a := by change 1-2*((1-a)/2)=a; ring
  have term (n : ℕ+) : ‖Composite.wave m s x n‖^2=(multiplicity m x n:ℝ)*exp ((a-1)*energy n) := by
    rw [Composite.wave_apply,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      sq_sqrt (Nat.cast_nonneg _),heat_square,idx]
  rw [←sum_congr rfl (fun n _ => term n),←norm_shell_sum,Composite.wave_mass,rawWave_sq,idx]

/-- Removing the order degeneracy costs at most the number of permutations. -/
theorem mass_bounds (m : ℕ) (a x : ℝ) :
    mass m a x≤(powerMass a x)^m ∧ (powerMass a x)^m≤(m.factorial:ℝ)*mass m a x := by
  rw [←weighted_total,mass,mul_sum]
  constructor
  · refine sum_le_sum fun n hn => ?_
    exact le_mul_of_one_le_left (exp_pos _).le (by exact_mod_cast (multiplicity_bounds hn).1)
  · refine sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (multiplicity_bounds hn).2) (exp_pos _).le

theorem mass_pos (m : ℕ) (a x : ℝ) : 0 < mass m a x := by
  have h := (pow_pos (powerMass_pos a x) m).trans_le (mass_bounds m a x).2
  exact pos_of_mul_pos_right h (Nat.cast_nonneg _)

#print axioms gibbs_preparation
#print axioms reflected_pair
#print axioms wave_mass
#print axioms mass_bounds
#print axioms mass_pos

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
