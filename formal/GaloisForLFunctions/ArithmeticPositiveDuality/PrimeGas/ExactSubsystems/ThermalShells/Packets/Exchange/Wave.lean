import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Outgoing Born readings of finite superpositions in the full two-copy gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange

open Finset Real

/-- Equal unnormalized amplitudes on a finite set of energy eigenstates. -/
def wave (U : Finset ℕ+) : Gas := ∑ n ∈ U,lp.single 2 n (1:ℂ)

theorem wave_apply (U : Finset ℕ+) (n : ℕ+) : wave U n = if n ∈ U then 1 else 0 := by
  rw [wave,lp.coeFn_sum,Finset.sum_apply]
  simp only [lp.single_apply,Pi.single_apply,sum_ite_eq]

/-- A test of the conserved integer label after splitting, summed over the entire pair basis. -/
def outputTest (U : Finset ℕ+) (s : ℂ) (F : ℕ+ → ℝ) :=
  ∑' x : ℕ+ × ℕ+,‖split s (wave U) x‖^2 * F (x.1*x.2)

/-- The complete outgoing sum converges and equals a finite shell sum, even off the
isometry line. Multiplying each input amplitude by the square root of the test reduces
the weighted Born sum to the shell norm identity. -/
theorem hasSum_output (U : Finset ℕ+) (s : ℂ) (F : ℕ+ → ℝ) (hF : ∀ n ∈ U,0 ≤ F n) :
    HasSum (fun x : ℕ+ × ℕ+ => ‖split s (wave U) x‖^2 * F (x.1*x.2))
      (∑ n ∈ U,shellMass s n*F n) := by
  let g (n : ℕ+) : ℂ := if n ∈ U then (sqrt (F n):ℂ) else 0
  have mag (n : ℕ+) : ‖g n‖^2 = if n ∈ U then F n else 0 := by
    by_cases hn : n ∈ U
    · simp only [g,if_pos hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _),sq_sqrt (hF n hn)]
    · simp [g,hn]
  have hzero (n : ℕ+) (hn : n ∉ U) : shellMass s n*‖g n‖^2 = 0 := by rw [mag,if_neg hn,mul_zero]
  have H : HasSum (fun n => shellMass s n*‖g n‖^2) (∑ n ∈ U,shellMass s n*‖g n‖^2) :=
    hasSum_sum_of_ne_finset_zero hzero
  have sumEq : (∑ n ∈ U,shellMass s n*‖g n‖^2) = ∑ n ∈ U,shellMass s n*F n :=
    sum_congr rfl fun n hn => by rw [mag,if_pos hn]
  rw [sumEq] at H
  have actual := (split_hasSum_iff s g _).mpr H
  have one (x : ℕ+ × ℕ+) : ‖split s g x‖^2 = ‖split s (wave U) x‖^2*F (x.1*x.2) := by
    simp only [split,norm_mul,mul_pow,mag,wave_apply]
    by_cases hx : x.1*x.2 ∈ U <;> simp [hx]
  simpa only [one] using actual

#print axioms hasSum_output

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange
