import GaloisForLFunctions.HTGeometry.DilatonOscillatorApplications

/-!
# Dilaton zero modes and the quartic ground state

The half-density factorization from arXiv:2608.21406v1 classifies zero modes
of every polynomial dilaton Hamiltonian by a constant undressed amplitude.
For a negative quartic log-weight, proper polynomial composition constructs
an actual complex Schwartz ground state. It is nonzero, has zero energy,
and spans the entire Schwartz kernel. No existence or boundary premise is used.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry

theorem dilatonSupercharge_kernel_iff (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM H ψ = 0 ↔
      ∀ x, dilatonUndressed H ψ x = dilatonUndressed H ψ 0 := by
  constructor
  · intro h x
    apply is_const_of_deriv_eq_zero (x := x) (y := 0)
    · exact fun x => (dilatonUndressed_derivative H ψ x).differentiableAt
    · intro x
      rw [(dilatonUndressed_derivative H ψ x).deriv, ← dilatonSuperchargeCLM_apply, h]
      simp
  · intro h
    have hf : dilatonUndressed H ψ = fun _ => dilatonUndressed H ψ 0 := funext h
    ext x
    have hd : deriv (dilatonUndressed H ψ) x = 0 := by rw [hf]; simp
    rw [(dilatonUndressed_derivative H ψ x).deriv, ← dilatonSuperchargeCLM_apply] at hd
    exact (mul_eq_zero.mp hd).resolve_left (dilatonGauge_ne_zero H x)

theorem dilatonHamiltonian_kernel_iff (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM H ψ = 0 ↔ dilatonSuperchargeCLM H ψ = 0 := by
  constructor
  · intro h
    have hp := dilatonHamiltonian_energy H ψ
    rw [h, schwartzPair_zero_right] at hp
    have hn : ‖(dilatonSuperchargeCLM H ψ).toLp 2 (volume : Measure ℝ)‖ ^ 2 = 0 := by
      exact_mod_cast hp.symm
    apply SchwartzMap.injective_toLp 2 (volume : Measure ℝ)
    have hzero := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_zero
    rw [SchwartzMap.toLpCLM_apply] at hzero
    exact (norm_eq_zero.mp (sq_eq_zero_iff.mp hn)).trans hzero.symm
  · intro h
    rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, h, map_zero]

theorem dilatonHamiltonian_kernel_classification (H : ℝ[X]) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM H ψ = 0 ↔
      ∀ x, dilatonUndressed H ψ x = dilatonUndressed H ψ 0 := by
  rw [dilatonHamiltonian_kernel_iff, dilatonSupercharge_kernel_iff]

def quarticDilatonSquareScale (k : ℝ) : ℝ := Real.sqrt (Real.exp k / (2 * Real.pi))

def quarticDilatonSquareMap (k x : ℝ) : ℝ := quarticDilatonSquareScale k * x ^ 2

theorem quarticDilatonSquareScale_pos (k : ℝ) : 0 < quarticDilatonSquareScale k := by
  unfold quarticDilatonSquareScale
  positivity

private theorem quarticDilatonSquareMap_temperate (k : ℝ) :
    Function.HasTemperateGrowth (quarticDilatonSquareMap k) := by
  exact (Function.HasTemperateGrowth.const (quarticDilatonSquareScale k)).mul
    ((Function.HasTemperateGrowth.id).pow 2)

private theorem quarticDilatonSquareMap_growth (k : ℝ) :
    ∃ (n : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖quarticDilatonSquareMap k x‖) ^ n := by
  let c := quarticDilatonSquareScale k
  have hc : 0 < c := quarticDilatonSquareScale_pos k
  refine ⟨1, 1 + c⁻¹, fun x => ?_⟩
  have habs : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hprod : c⁻¹ * (c * x ^ 2) = x ^ 2 := by field_simp
  have hineq := mul_le_mul_of_nonneg_right (by linarith : c⁻¹ ≤ 1 + c⁻¹)
    (by positivity : 0 ≤ c * x ^ 2)
  rw [hprod] at hineq
  change ‖x‖ ≤ (1 + c⁻¹) * (1 + ‖c * x ^ 2‖) ^ 1
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hc, abs_pow, sq_abs, pow_one]
  nlinarith [inv_pos.mpr hc]

/-- A genuine Schwartz ground state, constructed by proper polynomial composition. -/
def quarticDilatonGroundState (k : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (quarticDilatonSquareMap_temperate k) (quarticDilatonSquareMap_growth k)
    gaussianSchwartz

theorem quarticDilatonGroundState_apply (k x : ℝ) :
    quarticDilatonGroundState k x = ((Real.exp (-Real.exp k * x ^ 4 / 2) : ℝ) : ℂ) := by
  change gaussianSchwartz (quarticDilatonSquareMap k x) = _
  rw [gaussianSchwartz_apply]
  unfold gaussReal quarticDilatonSquareMap quarticDilatonSquareScale
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ Real.exp k / (2 * Real.pi))]
  congr 2
  field_simp

theorem quarticDilatonGroundState_zero (k : ℝ) : quarticDilatonGroundState k 0 = 1 := by
  simp [quarticDilatonGroundState_apply]

theorem quarticDilatonGroundState_ne_zero (k : ℝ) : quarticDilatonGroundState k ≠ 0 := by
  intro h
  have hx := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) h
  exact one_ne_zero (by simpa only [quarticDilatonGroundState_zero, _root_.zero_apply] using hx)

theorem quarticDilatonGroundState_undressed (k x : ℝ) :
    dilatonUndressed (quarticDilatonLogWeight k) (quarticDilatonGroundState k) x = 1 := by
  rw [dilatonUndressed, quarticDilatonGroundState_apply]
  simp only [dilatonGauge, quarticDilatonLogWeight, eval_mul, eval_C, eval_pow, eval_X]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -(-Real.exp k * x ^ 4) / 2 + -Real.exp k * x ^ 4 / 2 = 0 by ring,
    Real.exp_zero, Complex.ofReal_one]

theorem quarticDilatonGroundState_supercharge (k : ℝ) :
    dilatonSuperchargeCLM (quarticDilatonLogWeight k) (quarticDilatonGroundState k) = 0 := by
  rw [dilatonSupercharge_kernel_iff]
  intro x
  rw [quarticDilatonGroundState_undressed, quarticDilatonGroundState_undressed]

theorem quarticDilatonGroundState_eigenfunction (k : ℝ) :
    dilatonHamiltonianCLM (quarticDilatonLogWeight k) (quarticDilatonGroundState k) = 0 := by
  rw [dilatonHamiltonian_kernel_iff]
  exact quarticDilatonGroundState_supercharge k

/-- Every zero-energy Schwartz field is a scalar multiple of the constructed ground state. -/
theorem quarticDilaton_kernel_span (k : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (quarticDilatonLogWeight k) ψ = 0 ↔
      ψ = ψ 0 • quarticDilatonGroundState k := by
  constructor
  · intro h
    have hc := (dilatonHamiltonian_kernel_classification _ ψ).mp h
    ext x
    apply mul_left_cancel₀ (dilatonGauge_ne_zero (quarticDilatonLogWeight k) x)
    change dilatonUndressed (quarticDilatonLogWeight k) ψ x =
      dilatonGauge (quarticDilatonLogWeight k) x * (ψ 0 * quarticDilatonGroundState k x)
    rw [hc]
    have hz : dilatonUndressed (quarticDilatonLogWeight k) ψ 0 = ψ 0 := by
      simp [dilatonUndressed, dilatonGauge, quarticDilatonLogWeight]
    rw [hz, mul_left_comm, ← dilatonUndressed, quarticDilatonGroundState_undressed, mul_one]
  · intro h
    rw [h, map_smul, quarticDilatonGroundState_eigenfunction, smul_zero]

end GaloisForLFunctions.HTGeometry
