import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography.Moments

/-! # Finite heat preparations containing every integer occupation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Finset Real InverseSpectrum.ShellMixing

/-- All energies log 1 through log(N+1), including the vacuum. -/
def prefixMass (b : ℝ) (N : ℕ) := ∑ k ∈ range (N+1), occupationWeight k^b

theorem prefix_pos (b : ℝ) (N : ℕ) : 0 < prefixMass b N := by
  apply sum_pos'
  · exact fun k _ => (rpow_pos_of_pos (occupationWeight_pos k) b).le
  · exact ⟨0,mem_range.mpr (Nat.succ_pos _),rpow_pos_of_pos (occupationWeight_pos _) b⟩

/-- The finite heat amplitude retains the input clock phase on every state. -/
def amplitude (s : ℂ) (N k : ℕ) := if k < N+1 then
  heat s (number k)/(sqrt (prefixMass (2*s.re) N):ℂ) else 0

def input (s : ℂ) (N : ℕ) : Gas :=
  gasOfCoords (amplitude s N) (summable_of_ne_finset_zero
    (s:=range (N+1)) (fun k hk => by
      simp only [amplitude,if_neg (fun h => hk (mem_range.mpr h)),norm_zero,zero_pow (two_ne_zero : (2:ℕ)≠0)]))

theorem heat_square (s : ℂ) (k : ℕ) : ‖heat s (number k)‖^2 = occupationWeight k^(2*s.re) := by
  rw [norm_heat,sq,←Real.exp_add,occupationWeight_eq,rpow_def_of_pos (inv_pos.mpr (by positivity)),
    Real.log_inv]
  change exp (-s.re*log ((k+1:ℕ):ℝ)+ -s.re*log ((k+1:ℕ):ℝ))=_
  rw [Nat.cast_add,Nat.cast_one]
  congr 1
  ring

theorem population_eq (s : ℂ) (N k : ℕ) : Tomography.population (input s N) k =
    if k<N+1 then occupationWeight k^(2*s.re)/prefixMass (2*s.re) N else 0 := by
  change ‖amplitude s N k‖^2=_
  unfold amplitude
  split_ifs
  · rw [norm_div,div_pow,heat_square,Complex.norm_real,Real.norm_of_nonneg (sqrt_nonneg _),
      sq_sqrt (prefix_pos _ _).le]
  · simp only [norm_zero,zero_pow (two_ne_zero : (2:ℕ)≠0)]

def reading (z : ℕ → SplitParameter) (s : ℂ) (N j : ℕ) := Tomography.survival z (input s N) j

theorem reading_eq (z : ℕ → SplitParameter) (s : ℂ) (N j : ℕ) :
    reading z s N j = prefixMass (2*s.re+(j:ℝ)) N / prefixMass (2*s.re) N := by
  rw [reading,Tomography.survival_moment,tsum_eq_sum (s := range (N+1)) (fun k hk => by
    rw [population_eq,if_neg (fun h => hk (mem_range.mpr h)),mul_zero])]
  change _ = (∑ k ∈ range (N+1), occupationWeight k^(2*s.re+(j:ℝ)))/_
  rw [Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [population_eq,if_pos (mem_range.mp hk),rpow_add (occupationWeight_pos k),rpow_natCast]
  ring

/-- At depth zero the physical preparation has unit norm. -/
theorem initial_mass (z : ℕ → SplitParameter) (s : ℂ) (N : ℕ) : reading z s N 0=1 := by
  rw [reading_eq,Nat.cast_zero,add_zero,div_self (prefix_pos _ _).ne']

#print axioms heat_square
#print axioms population_eq
#print axioms reading_eq
#print axioms initial_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
