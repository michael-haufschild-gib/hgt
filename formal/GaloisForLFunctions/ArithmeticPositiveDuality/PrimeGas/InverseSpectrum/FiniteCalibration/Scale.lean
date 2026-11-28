import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OneTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Isometry

/-! # The shell scale measured by an unknown cyclic-order Hamiltonian -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration

open CoassociativeSplitting

def twist (F : Kernel) (g : ℕ+ → ℂ) : Kernel := fun a b => F a b*g (a*b)

private theorem twisted_shell (F : Kernel) (g : ℕ+ → ℂ) (n : ℕ+) (x : ℕ+ × ℕ+) :
    shell (twist F g) n x = ‖g n‖^2 * shell F n x := by
  by_cases h : x.1*x.2=n
  · simp [shell,twist,h,mul_pow,mul_comm]
  · simp only [shell,if_neg h,mul_zero]

/-- A shell multiplier preserves an isometric composition precisely when it
changes only the phases of the integer basis states. -/
theorem multiplier_iff (F : Kernel) (g : ℕ+ → ℂ) :
    isometric F ∧ isometric (twist F g) ↔ normalized F ∧ ∀ n, ‖g n‖=1 := by
  rw [CoassociativeSplitting.isometric_iff,CoassociativeSplitting.isometric_iff]
  constructor
  · rintro ⟨hF,hg⟩
    refine ⟨hF,fun n => ?_⟩
    have h := (hF n).mul_left (‖g n‖^2)
    rw [mul_one] at h
    have eqn := ((hg n).congr_fun (fun x => (twisted_shell F g n x).symm)).unique h
    nlinarith only [eqn,norm_nonneg (g n)]
  · rintro ⟨hF,hg⟩
    refine ⟨hF,fun n => (hF n).congr_fun fun x => ?_⟩
    rw [twisted_shell,hg,one_pow,one_mul]

private def reference : Kernel := fun a b => channel (1/2) (a*b) a.val

private def relative (E : ℕ+ → ℝ) (s : ℂ) (n : ℕ+) :=
  Complex.exp (-s*(E n:ℂ))/heat (1/2) n

private theorem reference_isometric : isometric reference :=
  (split_isometric_iff _).mpr (by rw [Complex.div_ofNat_re,Complex.one_re])

private theorem relative_wave (E : ℕ+ → ℝ) (s : ℂ) (f : Gas) (x : ℕ+ × ℕ+) :
    InverseSpectrum.wave E s f x=CoassociativeSplitting.wave (twist reference (relative E s)) f x := by
  change _ = (((Real.sqrt x.1.val.totient:ℂ)*heat (1/2) (x.1*x.2)) *
    (Complex.exp (-s*(E (x.1*x.2):ℂ))/heat (1/2) (x.1*x.2))) * f (x.1*x.2)
  unfold InverseSpectrum.wave
  have nz : heat (1/2) (x.1*x.2)≠0 := Complex.exp_ne_zero _
  field_simp [nz]

private theorem unit_iff (E : ℕ+ → ℝ) (s : ℂ) (n : ℕ+) :
    ‖relative E s n‖=1 ↔ 2*s.re*E n=energy n := by
  have nz : ‖heat (1/2) n‖≠0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  rw [relative,norm_div,div_eq_iff nz,one_mul,Complex.norm_exp,norm_heat,Complex.mul_re,
    Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.div_ofNat_re,
    Complex.one_re,Real.exp_eq_exp]
  constructor <;> intro eqn <;> linarith only [eqn]

/-- No sign, additivity or regularity restriction on the energy assignment
is needed for the full Hilbert-space isometry criterion. -/
theorem isometric_iff_energy (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ↔ ∀ n, 2*s.re*E n=energy n := by
  have hr := (CoassociativeSplitting.isometric_iff reference).mp reference_isometric
  have iso : Isometric E s ↔ isometric (twist reference (relative E s)) := by
    unfold Isometric isometric
    simp only [relative_wave]
  have h := multiplier_iff reference (relative E s)
  rw [and_iff_right reference_isometric,and_iff_right hr] at h
  exact iso.trans (h.trans (forall_congr' (unit_iff E s)))

#print axioms multiplier_iff
#print axioms isometric_iff_energy

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration
