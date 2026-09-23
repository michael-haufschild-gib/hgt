import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# QNMTimeConvention

Morikawa, arXiv:2608.29806, equations (27)--(30), distinguishes amplitude
and probability decay. Ferrer-Sánchez et al., arXiv:2608.19774, equation (3.3),
parametrizes the closed lower frequency half-plane. These time, norm, and
width identities include the real-axis boundary. Division by zero is Lean
totalized division; the zero-hbar case has no physical interpretation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def qnmHarmonic (omega : ℂ) (t : ℝ) : ℂ := Complex.exp (-Complex.I * omega * t)

theorem norm_qnmHarmonic (omega : ℂ) (t : ℝ) :
    ‖qnmHarmonic omega t‖ = Real.exp (omega.im * t) := by
  rw [qnmHarmonic, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem normSq_qnmHarmonic (omega : ℂ) (t : ℝ) :
    ‖qnmHarmonic omega t‖ ^ (2 : ℕ) = Real.exp (2 * omega.im * t) := by
  rw [norm_qnmHarmonic, ← Real.exp_nat_mul]
  congr 1
  ring

theorem hasDerivAt_qnmHarmonic (omega : ℂ) (t : ℝ) :
    HasDerivAt (qnmHarmonic omega) ((-Complex.I * omega) * qnmHarmonic omega t) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-Complex.I * omega)).cexp
  convert! h using 1
  simp [qnmHarmonic, mul_comm]

theorem qnmHarmonic_semigroup (omega : ℂ) (t s : ℝ) :
    qnmHarmonic omega (t + s) = qnmHarmonic omega t * qnmHarmonic omega s := by
  simp [qnmHarmonic, mul_add, Complex.exp_add]

def qnmStableFrequency (a b : ℝ) : ℂ := a - Complex.I * |b|

theorem qnmStableFrequency_im (a b : ℝ) : (qnmStableFrequency a b).im = -|b| := by
  simp [qnmStableFrequency]

theorem qnmStableFrequency_nonpositive (a b : ℝ) : (qnmStableFrequency a b).im ≤ 0 := by
  rw [qnmStableFrequency_im]
  exact neg_nonpos.mpr (abs_nonneg b)

theorem norm_qnmStableHarmonic (a b t : ℝ) :
    ‖qnmHarmonic (qnmStableFrequency a b) t‖ = Real.exp (-|b| * t) := by
  rw [norm_qnmHarmonic, qnmStableFrequency_im]

theorem qnmStableHarmonic_contraction (a b t : ℝ) :
    ‖qnmHarmonic (qnmStableFrequency a b) (t ^ (2 : ℕ))‖ ≤ 1 := by
  rw [norm_qnmStableHarmonic, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg b)) (sq_nonneg t)

theorem qnm_width_decay_dictionary (energy width hbar t : ℝ) :
    ‖qnmHarmonic (((energy : ℂ) - Complex.I * width / 2) / hbar) t‖ ^ (2 : ℕ) =
      Real.exp (-(width / hbar) * t) := by
  rw [normSq_qnmHarmonic]
  congr 1
  simp [Complex.div_im, Complex.normSq_ofReal]
  by_cases hh : hbar = 0
  · simp [hh]
  · field_simp

end GaloisForLFunctions.HTGeometry
