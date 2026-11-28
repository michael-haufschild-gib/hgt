import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Branch
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Waves

/-! # Consecutive vacuum measurements on an arbitrary gas vector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography

open InverseSpectrum.ShellMixing GaloisForLFunctions.HTGeometry

/-- The surviving output is the vacuum row of the actual isometry. -/
def branch (z : SplitParameter) (f : Gas) : Gas := by
  let row (n : ℕ+) : ℕ+ × ℕ+ := (1,n)
  have inj : Function.Injective row := fun _ _ h => congrArg Prod.snd h
  exact ⟨fun n => splitIsometry z f (row n),HilbertSchmidt.memℓp_of_sq
    ((lp_summable_norm_sq (splitIsometry z f)).comp_injective inj)⟩

def survivor (z : ℕ → SplitParameter) (f : Gas) : ℕ → Gas
  | 0 => f
  | j+1 => branch (z j) (survivor z f j)

/-- Squared norm after j successive vacuum outcomes, for any initial vector. -/
def survival (z : ℕ → SplitParameter) (f : Gas) (j : ℕ) := ‖survivor z f j‖^2

/-- Here k indexes energy log(k+1). -/
def population (f : Gas) (k : ℕ) := ‖f (number k)‖^2

private theorem half_heat (z : SplitParameter) (k : ℕ) :
    ‖heat z.val (number k)‖^2 = occupationWeight k := by
  have h : ‖heat z.val (number k)‖ = ‖heat (1/2) (number k)‖ := by
    rw [norm_heat,norm_heat,z.property,Complex.div_ofNat_re,Complex.one_re]
  rw [h,←critical_heat,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le]
  rfl

/-- At every occupied integer, each branch multiplies the squared amplitude
by the reciprocal of that integer, independently of the chosen clock phase. -/
theorem survivor_mass (z : ℕ → SplitParameter) (f : Gas) (k j : ℕ) :
    population (survivor z f j) k = occupationWeight k^j * population f k := by
  induction j with
  | zero => simp only [survivor,pow_zero,one_mul]
  | succ j ih =>
    change ‖splitIsometry (z j) (survivor z f j) (1,number k)‖^2 = _
    rw [vacuum_apply,norm_mul,mul_pow,half_heat]
    change occupationWeight k * population (survivor z f j) k = _
    rw [ih,pow_succ]
    ring

theorem survival_hasSum (z : ℕ → SplitParameter) (f : Gas) (j : ℕ) :
    HasSum (fun k => occupationWeight k^j * population f k) (survival z f j) := by
  have eqn : (fun k => occupationWeight k^j * population f k) =
      fun k => ‖survivor z f j (number k)‖^2 := funext fun k => (survivor_mass z f k j).symm
  rw [eqn,survival,gas_norm_sq]
  exact (gas_coords_summable (survivor z f j)).hasSum

theorem survival_moment (z : ℕ → SplitParameter) (f : Gas) (j : ℕ) :
    survival z f j = ∑' k, occupationWeight k^j * population f k :=
  (survival_hasSum z f j).tsum_eq.symm

#print axioms survivor_mass
#print axioms survival_hasSum
#print axioms survival_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography
