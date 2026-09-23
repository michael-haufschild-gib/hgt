import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalLindblad
import GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw

/-!
# Hilbert--Schmidt dissipation for the thermal Lindblad equation

This application of the energy mechanism in arXiv:2609.04530 uses the corpus's
existing trace-defined `finiteMatrixHilbertSchmidtEnergy`, centered at the
stationary thermal carrier. The exact population/coherence split yields two
relaxation exponents and an actual derivative equal to minus a positive damping
form. The same form is the real Hilbert--Schmidt pairing with the explicit
Lindblad generator. All input matrices are unrestricted.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Remove the stationary component selected by the conserved trace. -/
def spinThermalCentered (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ρ - Matrix.trace ρ • spinBathDensity u

/-- Explicit centered coordinates for all raw input matrices. -/
theorem spinThermalCentered_entries (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalCentered u ρ =
      !![ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ, ρ 0 1;
        ρ 1 0, ρ 1 1 - (spinBathLower u : ℂ) * Matrix.trace ρ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinThermalCentered, spinBathDensity_entries, mul_comm]

/-- Removing the stationary component leaves exactly zero trace. -/
theorem spinThermalCentered_trace (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace (spinThermalCentered u ρ) = 0 := by
  simp [spinThermalCentered, Matrix.trace_sub, Matrix.trace_smul, spinBathDensity_trace]

/-- Existing trace-defined Hilbert--Schmidt energy, centered at the actual stationary bath. -/
def spinThermalEnergy (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  finiteMatrixHilbertSchmidtEnergy (spinThermalCentered u ρ)

/-- Diagonal contribution to centered energy. -/
def spinThermalPopulationEnergy (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (spinThermalCentered u ρ 0 0) + Complex.normSq (spinThermalCentered u ρ 1 1)

/-- Coherence contribution to centered energy; the stationary bath has no off-diagonal entries. -/
def spinThermalCoherenceEnergy (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (ρ 0 1) + Complex.normSq (ρ 1 0)

/-- The pre-existing Hilbert--Schmidt energy is exactly the population/coherence decomposition. -/
theorem spinThermalEnergy_split (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ρ = spinThermalPopulationEnergy u ρ + spinThermalCoherenceEnergy ρ := by
  rw [spinThermalEnergy, finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  simp [spinThermalPopulationEnergy, spinThermalCoherenceEnergy, Fin.sum_univ_two, spinThermalCentered_entries]
  ring

/-- Both energy sectors are nonnegative on every raw complex matrix. -/
theorem spinThermalEnergy_sectors_nonneg (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ spinThermalPopulationEnergy u ρ ∧ 0 ≤ spinThermalCoherenceEnergy ρ := by
  exact ⟨add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)⟩

/-- Zero centered energy identifies the entire stationary trace ray, without normalized-state assumptions. -/
theorem spinThermalEnergy_eq_zero_iff (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u ρ = 0 ↔ ρ = Matrix.trace ρ • spinBathDensity u := by
  rw [spinThermalEnergy, finiteMatrixHilbertSchmidtEnergy_eq_zero_iff, spinThermalCentered, sub_eq_zero]

/-- Centering removes the affine thermal forcing and exposes the exact linear decay modes. -/
theorem spinThermalCentered_evolution (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalCentered u (spinThermalEvolution a u ρ t) =
      !![(Real.exp (-2 * a ^ (2 : ℕ) * t) : ℂ) * spinThermalCentered u ρ 0 0,
          spinPlaneFlow a 1 t * ρ 0 1;
        conj (spinPlaneFlow a 1 t) * ρ 1 0,
          (Real.exp (-2 * a ^ (2 : ℕ) * t) : ℂ) * spinThermalCentered u ρ 1 1] := by
  rw [spinThermalCentered_entries, spinThermalEvolution_trace]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinThermalEvolution, spinThermalCentered_entries] <;> ring

/-- The population part of energy decays at twice the coherence-energy exponent. -/
theorem spinThermalPopulationEnergy_evolution (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalPopulationEnergy u (spinThermalEvolution a u ρ t) =
      Real.exp (-4 * a ^ (2 : ℕ) * t) * spinThermalPopulationEnergy u ρ := by
  have he : Real.exp (-2 * a ^ (2 : ℕ) * t) * Real.exp (-2 * a ^ (2 : ℕ) * t) = Real.exp (-4 * a ^ (2 : ℕ) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [spinThermalPopulationEnergy, spinThermalCentered_evolution]
  change Complex.normSq ((Real.exp (-2 * a ^ (2 : ℕ) * t) : ℂ) * spinThermalCentered u ρ 0 0) +
      Complex.normSq ((Real.exp (-2 * a ^ (2 : ℕ) * t) : ℂ) * spinThermalCentered u ρ 1 1) = _
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, he]
  ring

/-- Precession drops out of the coherence-energy law. -/
theorem spinThermalCoherenceEnergy_evolution (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalCoherenceEnergy (spinThermalEvolution a u ρ t) =
      Real.exp (-2 * a ^ (2 : ℕ) * t) * spinThermalCoherenceEnergy ρ := by
  have he : Complex.normSq (spinPlaneFlow a 1 t) = Real.exp (-2 * a ^ (2 : ℕ) * t) := by
    rw [Complex.normSq_eq_norm_sq, spinPlaneFlow_norm_sq]
    simp
  change Complex.normSq (spinPlaneFlow a 1 t * ρ 0 1) +
      Complex.normSq (conj (spinPlaneFlow a 1 t) * ρ 1 0) = _
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj, he]
  unfold spinThermalCoherenceEnergy
  ring

/-- Exact two-exponent relaxation law for the corpus's trace-defined energy. -/
theorem spinThermalEnergy_evolution (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalEnergy u (spinThermalEvolution a u ρ t) =
      Real.exp (-4 * a ^ (2 : ℕ) * t) * spinThermalPopulationEnergy u ρ +
        Real.exp (-2 * a ^ (2 : ℕ) * t) * spinThermalCoherenceEnergy ρ := by
  rw [spinThermalEnergy_split, spinThermalPopulationEnergy_evolution, spinThermalCoherenceEnergy_evolution]

/-- The positive damping form revealed by the energy identity. -/
def spinThermalDissipation (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  4 * a ^ (2 : ℕ) * spinThermalPopulationEnergy u ρ + 2 * a ^ (2 : ℕ) * spinThermalCoherenceEnergy ρ

/-- Dissipation is nonnegative without imposing positivity or Hermiticity on the input. -/
theorem spinThermalDissipation_nonneg (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ spinThermalDissipation a u ρ := by
  obtain ⟨hp, hc⟩ := spinThermalEnergy_sectors_nonneg u ρ
  unfold spinThermalDissipation
  positivity

/-- The exact derivative is minus the constructed positive damping form. -/
theorem hasDerivAt_spinThermalEnergy_evolution (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun v : ℝ => spinThermalEnergy u (spinThermalEvolution a u ρ v))
      (-spinThermalDissipation a u (spinThermalEvolution a u ρ t)) t := by
  have hp := (((hasDerivAt_id t).const_mul (-4 * a ^ (2 : ℕ))).exp).mul_const (spinThermalPopulationEnergy u ρ)
  have hc := (((hasDerivAt_id t).const_mul (-2 * a ^ (2 : ℕ))).exp).mul_const (spinThermalCoherenceEnergy ρ)
  have hf : (fun v : ℝ => spinThermalEnergy u (spinThermalEvolution a u ρ v)) =
      (fun v => Real.exp (-4 * a ^ (2 : ℕ) * v) * spinThermalPopulationEnergy u ρ +
        Real.exp (-2 * a ^ (2 : ℕ) * v) * spinThermalCoherenceEnergy ρ) := by
    funext v
    exact spinThermalEnergy_evolution a u v ρ
  rw [hf]
  apply (hp.add hc).congr_deriv
  simp only [spinThermalDissipation, spinThermalPopulationEnergy_evolution,
    spinThermalCoherenceEnergy_evolution, id_eq, mul_one]
  ring

/-- Under constructed positive damping, loss vanishes exactly on the stationary trace ray. -/
theorem spinThermalDissipation_eq_zero_iff (s u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalDissipation (Real.exp s) u ρ = 0 ↔ ρ = Matrix.trace ρ • spinBathDensity u := by
  rw [← spinThermalEnergy_eq_zero_iff, spinThermalEnergy_split]
  obtain ⟨hp, hc⟩ := spinThermalEnergy_sectors_nonneg u ρ
  have ha : 0 < (Real.exp s) ^ (2 : ℕ) := by positivity
  unfold spinThermalDissipation
  constructor
  · intro h
    have h₁ := mul_nonneg ha.le hp
    have h₂ := mul_nonneg ha.le hc
    have hsum : (Real.exp s) ^ (2 : ℕ) * (spinThermalPopulationEnergy u ρ + spinThermalCoherenceEnergy ρ) = 0 := by nlinarith
    exact (mul_eq_zero.mp hsum).resolve_left (ne_of_gt ha)
  · intro h
    have hp0 : spinThermalPopulationEnergy u ρ = 0 := by linarith
    have hc0 : spinThermalCoherenceEnergy ρ = 0 := by linarith
    rw [hp0, hc0]
    ring

set_option maxHeartbeats 600000 in
/-- The damping form is exactly minus twice the real Hilbert--Schmidt pairing with the generator. -/
theorem spinThermalDissipation_trace (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalDissipation a u ρ =
      -2 * (Matrix.trace ((spinThermalCentered u ρ)ᴴ * spinThermalLindblad a u ρ)).re := by
  let δ := spinThermalCentered u ρ
  have hL : spinThermalLindblad a u ρ =
      !![((-2 * a ^ (2 : ℕ) : ℝ) : ℂ) * δ 0 0, spinPlaneRate a * δ 0 1;
        conj (spinPlaneRate a) * δ 1 0, ((-2 * a ^ (2 : ℕ) : ℝ) : ℂ) * δ 1 1] := by
    rw [spinThermalLindblad_entries]
    simp only [δ, spinThermalCentered_entries]
    rfl
  have hC : spinThermalCoherenceEnergy ρ = Complex.normSq (δ 0 1) + Complex.normSq (δ 1 0) := by
    simp [spinThermalCoherenceEnergy, δ, spinThermalCentered_entries]
  rw [spinThermalDissipation, hC, hL]
  change 4 * a ^ (2 : ℕ) * (Complex.normSq (δ 0 0) + Complex.normSq (δ 1 1)) +
      2 * a ^ (2 : ℕ) * (Complex.normSq (δ 0 1) + Complex.normSq (δ 1 0)) =
    -2 * (Matrix.trace (δᴴ *
      !![((-2 * a ^ (2 : ℕ) : ℝ) : ℂ) * δ 0 0, spinPlaneRate a * δ 0 1;
        conj (spinPlaneRate a) * δ 1 0, ((-2 * a ^ (2 : ℕ) : ℝ) : ℂ) * δ 1 1])).re
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    spinPlaneRate, Complex.normSq_apply, pow_two]
  ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
