import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorTail
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex Set Metric
noncomputable section
namespace RHTower

/-- The literal full Gaussian cofactor is holomorphic on every left half-plane. -/
theorem differentiableOn_steinhausFullGaussianCofactor_halfPlane
    (b : ℝ) {R : ℝ} (hR : 0 < R) (ω : SteinhausModel.Omega) :
    DifferentiableOn ℂ (fun s => steinhausFullGaussianCofactor s R ω) {s : ℂ | s.re < b} := by
  let u : ℕ → ℝ := fun n => ‖SteinhausModel.X (n + 1) ω *
    ((n + 1 : ℕ) : ℂ) ^ ((b : ℂ) - 1) *
      smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)‖
  have hu : Summable u := by
    exact (summable_steinhausFullGaussianCofactor
      (A := max b 0 + 1) (by have := le_max_right b 0; linarith)
      (s := (b : ℂ)) (by simp only [Complex.ofReal_re]; have := le_max_left b 0; linarith)
      hR ω).norm
  apply differentiableOn_tsum_of_summable_norm hu
  · intro n
    exact (((differentiable_id.sub_const (1 : ℂ)).const_cpow (c := ((n + 1 : ℕ) : ℂ))
      (by exact Or.inl (by exact_mod_cast Nat.succ_ne_zero n))).const_mul
        (SteinhausModel.X (n + 1) ω)).mul_const
          (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) |>.differentiableOn
  · exact isOpen_lt Complex.continuous_re continuous_const
  · intro n s hs
    dsimp only [u]
    simp only [norm_mul, SteinhausModel.norm_X, one_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (Nat.succ_pos n)
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    exact sub_le_sub_right hs.le 1

/-- Fixed-scale Gaussian smoothing makes the full cofactor entire for every phase. -/
theorem differentiable_steinhausFullGaussianCofactor
    {R : ℝ} (hR : 0 < R) (ω : SteinhausModel.Omega) :
    Differentiable ℂ (fun s => steinhausFullGaussianCofactor s R ω) := by
  intro s
  exact (differentiableOn_steinhausFullGaussianCofactor_halfPlane (s.re + 1) hR ω s
    (by dsimp; linarith)).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by dsimp; linarith))

/-- The actual coherent normalization preserves holomorphy. -/
theorem differentiable_normalizedFullGaussianCofactor
    {R : ℝ} (hR : 0 < R) (ω : SteinhausModel.Omega) (t : ℝ) :
    Differentiable ℂ (fun s => steinhausFullGaussianCofactor s R ω *
      (R : ℂ) ^ (-(s + (t : ℂ) * I))) := by
  exact (differentiable_steinhausFullGaussianCofactor hR ω).mul
    ((differentiable_id.add_const ((t : ℂ) * I)).neg.const_cpow (c := (R : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr hR.ne')))

end RHTower
