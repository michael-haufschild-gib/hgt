import GaloisForLFunctions.HTGeometry.DispersivePDE.NLSSolitons
import GaloisForLFunctions.HTGeometry.FokasLenellsUniformization

/-!
# Exact reverse-space-time Fokas–Lenells plane waves

Equation (1.7) of Yan–Zhang–Zhu, arXiv:2607.19649v1, is tested against
the corpus's FDNLS phases and NLS plane wave. Exponential wave numbers give
an unconditional family with frequency `k⁻¹ + a²`. Every derivative and the
simultaneous reflection in the residual is the actual Lean operation.

The waves are nondecaying when the amplitude is nonzero. They are exact
solutions of the PDE, not examples of the paper's weighted-Sobolev data.
-/

open Complex
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- A nonzero wave number, with no external positivity hypothesis. -/
def waveNumber (κ : ℝ) : ℝ := Real.exp κ

def waveFrequency (a κ : ℝ) : ℝ := (waveNumber κ)⁻¹ + a^2

/-- A global plane wave of the reverse-space-time nonlocal equation. -/
def planeWave (a κ t x : ℝ) : ℂ :=
  (a:ℂ) * FDNLS.staggerPhase (-waveNumber κ) x *
    FDNLS.staggerPhase (waveFrequency a κ) t

theorem phase_reverse_mul (r t : ℝ) :
    FDNLS.staggerPhase r t * FDNLS.staggerPhase r (-t) = 1 := by
  simp [FDNLS.staggerPhase, ← Complex.exp_add]

theorem planeWave_reverse_mul (a κ t x : ℝ) :
    planeWave a κ t x * planeWave a κ (-t) (-x) = (a:ℂ)^2 := by
  unfold planeWave
  calc
    _ = (a:ℂ)^2 *
      (FDNLS.staggerPhase (-waveNumber κ) x * FDNLS.staggerPhase (-waveNumber κ) (-x)) *
      (FDNLS.staggerPhase (waveFrequency a κ) t *
        FDNLS.staggerPhase (waveFrequency a κ) (-t)) := by ring
    _ = _ := by rw [phase_reverse_mul,phase_reverse_mul]; ring

theorem planeWave_norm (a κ t x : ℝ) : ‖planeWave a κ t x‖ = |a| := by
  simp [planeWave, FDNLS.norm_staggerPhase]

theorem planeWave_space_hasDerivAt (a κ t x : ℝ) :
    HasDerivAt (planeWave a κ t) (I*(waveNumber κ:ℂ)*planeWave a κ t x) x := by
  refine (((FDNLS.hasDerivAt_staggerPhase (-waveNumber κ) x).const_mul (a:ℂ)).mul_const
    (FDNLS.staggerPhase (waveFrequency a κ) t)).congr_deriv ?_
  simp only [planeWave, Complex.ofReal_neg]
  ring

theorem planeWave_time_hasDerivAt (a κ t x : ℝ) :
    HasDerivAt (fun s : ℝ => planeWave a κ s x)
      (-I*(waveFrequency a κ:ℂ)*planeWave a κ t x) t := by
  refine ((FDNLS.hasDerivAt_staggerPhase (waveFrequency a κ) t).const_mul
    ((a:ℂ)*FDNLS.staggerPhase (-waveNumber κ) x)).congr_deriv ?_
  simp only [planeWave]
  ring

theorem planeWave_mixed_hasDerivAt (a κ t x : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (planeWave a κ s) x)
      ((waveNumber κ:ℂ)*(waveFrequency a κ:ℂ)*planeWave a κ t x) t := by
  have heq : (fun s : ℝ => deriv (planeWave a κ s) x) =
      fun s : ℝ => I*(waveNumber κ:ℂ)*planeWave a κ s x := by
    funext s
    exact (planeWave_space_hasDerivAt a κ s x).deriv
  rw [heq]
  refine ((planeWave_time_hasDerivAt a κ t x).const_mul
    (I*(waveNumber κ:ℂ))).congr_deriv ?_
  ring_nf
  simp

/-- The residual uses actual Lean derivatives and actual simultaneous reflection. -/
def nonlocalResidual (q : ℝ → ℝ → ℂ) (t x : ℝ) : ℂ :=
  deriv (fun s : ℝ => deriv (q s) x) t - q t x +
    I*q t x*q (-t) (-x)*deriv (q t) x

/-- Every member of the exponential-wave-number family solves equation (1.7). -/
theorem planeWave_solves_nonlocal (a κ t x : ℝ) :
    nonlocalResidual (planeWave a κ) t x = 0 := by
  rw [nonlocalResidual, (planeWave_mixed_hasDerivAt a κ t x).deriv,
    (planeWave_space_hasDerivAt a κ t x).deriv]
  have hprod := planeWave_reverse_mul a κ t x
  have hk : (waveNumber κ:ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero κ
  have hfreq : (waveNumber κ:ℂ)*(waveFrequency a κ:ℂ) =
      1+(waveNumber κ:ℂ)*(a:ℂ)^2 := by
    simp [waveFrequency, mul_add, hk]
  rw [hfreq]
  calc
    _ = (1+(waveNumber κ:ℂ)*(a:ℂ)^2)*planeWave a κ t x - planeWave a κ t x +
      I^2*(waveNumber κ:ℂ)*(planeWave a κ t x*planeWave a κ (-t) (-x))*
        planeWave a κ t x := by ring
    _ = 0 := by rw [hprod, Complex.I_sq]; ring

/-- The corpus's NLS plane wave, retimed, also solves the nonlocal Fokas–Lenells equation. -/
theorem planeWave_eq_retimed_nls (t x : ℝ) :
    planeWave 1 0 t x = DispersivePDE.nlsPlaneWave (-2*t) x := by
  simp [planeWave, waveNumber, waveFrequency, DispersivePDE.nlsPlaneWave,
    DispersivePDE.brightPhase, FDNLS.staggerPhase, ← Complex.exp_add]
  congr 1
  ring

theorem retimed_nls_solves_nonlocal (t x : ℝ) :
    nonlocalResidual (fun t x => DispersivePDE.nlsPlaneWave (-2*t) x) t x = 0 := by
  have h : (fun t x => DispersivePDE.nlsPlaneWave (-2*t) x) = planeWave 1 0 := by
    funext t x
    exact (planeWave_eq_retimed_nls t x).symm
  rw [h]
  exact planeWave_solves_nonlocal 1 0 t x

end
end GaloisForLFunctions.HTGeometry.FokasLenells
