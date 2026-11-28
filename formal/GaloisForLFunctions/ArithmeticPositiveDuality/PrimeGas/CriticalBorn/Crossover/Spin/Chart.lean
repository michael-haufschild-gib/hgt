import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Dynamics.Phase
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinGibbs

/-! # Stereographic spin coordinate from temperature and clock displacements -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin

open Real Dynamics
open GaloisForLFunctions.HTGeometry.SchafferExl
open scoped ComplexConjugate

/-- Stereographic coordinate of the terminal amplitude relative to the bulk. -/
def coordinate (c h : ℝ) := spinLogSeed (c/2) (-h)

theorem coordinate_norm_sq (c h : ℝ) : ‖coordinate c h‖^2=exp c := by
  rw [coordinate,spinLogSeed_norm_sq,show 2*(c/2)=c by ring]

theorem coordinate_kernel (c d h k : ℝ) : conj (coordinate c h)*coordinate d k =
    (exp ((c+d)/2):ℂ)*clockPhase (h-k) 1 := by
  rw [coordinate,coordinate,spinLogSeed,spinLogSeed,←Complex.exp_conj,←Complex.exp_add,
    Complex.ofReal_exp,clockPhase,←Complex.exp_add]
  congr 1
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  simp only [mul_one,Complex.ofReal_neg,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

/-- Every nonzero complex chart coordinate is prepared by real physical offsets. -/
theorem coordinate_range : Set.range (fun v : ℝ × ℝ => coordinate v.1 v.2) = {z : ℂ | z≠0} := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact Complex.exp_ne_zero _
  · intro hz
    refine ⟨(2*(Complex.log z).re,-(Complex.log z).im),?_⟩
    change Complex.exp ((((2*(Complex.log z).re)/2:ℝ):ℂ)+
      ((-(-(Complex.log z).im):ℝ):ℂ)*Complex.I)=z
    rw [show 2*(Complex.log z).re/2=(Complex.log z).re by ring,neg_neg,
      Complex.re_add_im,Complex.exp_log hz]

/-- Half a turn is the unique destructive clock phase modulo complete turns. -/
theorem negative_phase_iff (θ : ℝ) :
    clockPhase θ 1 = -1 ↔ ∃ n : ℤ, θ=π+n*(2*π) := by
  rw [clockPhase,mul_one,←Complex.exp_pi_mul_I,Complex.exp_eq_exp_iff_exists_int]
  have fact (n : ℤ) : (π:ℂ)*Complex.I+(n:ℂ)*(2*(π:ℂ)*Complex.I) =
      ((π+n*(2*π):ℝ):ℂ)*Complex.I := by push_cast; ring
  simp only [fact,mul_left_inj' Complex.I_ne_zero,Complex.ofReal_inj]

#print axioms coordinate_kernel
#print axioms coordinate_range
#print axioms negative_phase_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin
