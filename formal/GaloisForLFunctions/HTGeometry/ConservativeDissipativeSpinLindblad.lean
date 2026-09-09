import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinAmplitudeDamping

/-!
# Actual Lindblad evolution and its nonlinear spin drift

Application of Schaffer–Exl, arXiv:2609.04530, through the newly constructed
amplitude-damping semigroup. An explicit Hamiltonian commutator plus lowering-jump
dissipator generates the exact linear matrix evolution. The real-time derivative
is proved, and its forward restriction equals the physical Kraus channel. On each
constructed pure spin density, this Lindblad generator decomposes exactly into the
paper's nonlinear spin field and a positive-rate reset-to-ground-state correction.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The fixed physical lowering operator. -/
def spinLowering : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- Lindblad generator with the same precession and damping coefficients as the spin mechanism. -/
def spinLindblad (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • (QuantumAlg.pauliZ * ρ - ρ * QuantumAlg.pauliZ) +
    ((2 * a ^ 2 : ℝ) : ℂ) • (spinLowering * ρ * spinLoweringᴴ -
      (1 / 2 : ℂ) • (spinLoweringᴴ * spinLowering * ρ + ρ * spinLoweringᴴ * spinLowering))

/-- Exact conservative and dissipative action of the constructed Lindblad operator. -/
theorem spinLindblad_entries (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinLindblad a ρ =
      !![((-2 * a ^ 2 : ℝ) : ℂ) * ρ 0 0, spinPlaneRate a * ρ 0 1;
        conj (spinPlaneRate a) * ρ 1 0, ((2 * a ^ 2 : ℝ) : ℂ) * ρ 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinLindblad, spinLowering, QuantumAlg.pauliZ, spinPlaneRate,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- Real-time linear evolution; its forward restriction is the constructed physical channel. -/
def spinAmplitudeEvolution (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (-2 * a ^ 2 * t) : ℂ) * ρ 0 0, spinPlaneFlow a 1 t * ρ 0 1;
    conj (spinPlaneFlow a 1 t) * ρ 1 0, ρ 1 1 + (1 - (Real.exp (-2 * a ^ 2 * t) : ℂ)) * ρ 0 0]

/-- The analytic linear flow is exactly the earlier normalized Kraus channel at every forward time. -/
theorem spinAmplitudeEvolution_channel (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    spinAmplitudeEvolution a ρ t = (spinAmplitudeChannel a t).map ρ := by
  rw [spinAmplitudeChannel_entries]
  simp only [spinAmplitudeEvolution, spinPlaneFlow, mul_one, spinDecayFactor, spinDecayMass]

/-- Actual differentiation closes the master equation with its explicit Lindblad generator. -/
theorem hasDerivAt_spinAmplitudeEvolution (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (spinAmplitudeEvolution a ρ) (spinLindblad a (spinAmplitudeEvolution a ρ t)) t := by
  have hm := (((hasDerivAt_id t).const_mul (-2 * a ^ 2)).exp).ofReal_comp
  have hz := hasDerivAt_spinPlaneFlow a 1 t
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change HasDerivAt (fun v => (Real.exp (-2 * a ^ 2 * v) : ℂ) * ρ 0 0) _ t
    apply (hm.mul_const (ρ 0 0)).congr_deriv
    simp [spinLindblad_entries, spinAmplitudeEvolution]
    ring
  · change HasDerivAt (fun v => spinPlaneFlow a 1 v * ρ 0 1) _ t
    apply (hz.mul_const (ρ 0 1)).congr_deriv
    simp [spinLindblad_entries, spinAmplitudeEvolution]
    ring
  · change HasDerivAt (fun v => conj (spinPlaneFlow a 1 v) * ρ 1 0) _ t
    apply (hz.star.mul_const (ρ 1 0)).congr_deriv
    simp [spinLindblad_entries, spinAmplitudeEvolution]
    ring
  · change HasDerivAt (fun v => ρ 1 1 + (1 - (Real.exp (-2 * a ^ 2 * v) : ℂ)) * ρ 0 0) _ t
    apply ((((hasDerivAt_const t (1 : ℂ)).sub hm).mul_const (ρ 0 0)).const_add (ρ 1 1)).congr_deriv
    simp [spinLindblad_entries, spinAmplitudeEvolution]
    ring

/-- The Lindblad completion conserves total trace on all raw matrices. -/
theorem spinLindblad_trace (a : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (spinLindblad a ρ) = 0 := by
  rw [spinLindblad_entries]
  simp [Matrix.trace, Fin.sum_univ_two]

/-- The linear master equation is the paper's nonlinear pure-spin drift plus its explicit jump-reset correction. -/
theorem spinLindblad_pure_spin_decomposition (a : ℝ) (z : ℂ) :
    spinLindblad a (spinChartDensity z) = spinDensityField a (spinChartDensity z) +
      ((2 * a ^ 2 * ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) •
        (spinChartDensity 0 - spinChartDensity z) := by
  have hn : (‖z‖ : ℂ) ^ 2 = conj z * z := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hd : 1 + (‖z‖ : ℂ) ^ 2 ≠ 0 := by
    have hh : (1 + ‖z‖ ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast hh
  rw [spinLindblad_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinChartDensity_entries, spinDensityField, QuantumAlg.pauliZ, spinPlaneRate,
      Matrix.smul_apply]
  all_goals rw [hn] at hd ⊢
  all_goals field_simp
  all_goals ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
