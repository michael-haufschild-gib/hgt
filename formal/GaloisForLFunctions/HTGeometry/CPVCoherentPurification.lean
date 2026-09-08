import GaloisForLFunctions.HTGeometry.CPVConditionalClock
import GaloisForLFunctions.HTGeometry.CPVRadiationTemperature
import Mathlib

/-!
# Full complex coherent-state purification and partial trace

The two-mode series in arXiv:2601.07437, equations (23)--(24), is realized
inside the corpus Hilbert--Schmidt space for every nonvacuum disk radius
and every phase. The square-summable state is constructed before taking
its partial trace, so the thermal reduction is an actual infinite-state identity.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- The thermal half-density has the exact geometric coherent-state amplitudes. -/
theorem radiationVector_geometric (tau : ℝ) (n : ℕ) :
    radiationVector tau n = (Real.sqrt (1 - thermalRatio tau) : ℂ) *
      (coherentRadius tau : ℂ) ^ n := by
  have hp : Real.sqrt (thermalRatio tau ^ n) = coherentRadius tau ^ n := by
    rw [← coherentRadius_sq, ← pow_mul, Nat.mul_comm 2 n, pow_mul,
      Real.sqrt_sq (pow_nonneg (coherentRadius_pos tau).le n)]
  rw [radiationVector_apply, radiationMass, canonicalThermalMass,
    Real.sqrt_mul (sub_nonneg.mpr (thermalRatio_lt_one tau).le), hp,
    Complex.ofReal_mul, Complex.ofReal_pow]

/-- Polar disk phase agrees with the conditional-clock phase convention. -/
theorem coherentLabel_clockPhase (tau t : ℝ) :
    coherentLabel tau (-t) = (coherentRadius tau : ℂ) * clockPhase t := by
  unfold coherentLabel clockPhase
  rw [show -(t : ℂ) * Complex.I = ((-t : ℝ) : ℂ) * Complex.I by simp,
    Complex.exp_ofReal_mul_I]

/-- Exact geometric series coefficient of the two-mode squeezed state. -/
theorem conditionalClock_squeezed_coefficient (tau t : ℝ) (n : ℕ) :
    conditionalClock tau t n = (Real.sqrt (1 - thermalRatio tau) : ℂ) *
      coherentLabel tau (-t) ^ n := by
  rw [conditionalClock_apply, radiationVector_geometric, coherentLabel_clockPhase, mul_pow]
  ring

/-- Coherent-state purification at arbitrary disk phase. -/
def coherentPair (tau phi : ℝ) : ℕ × ℕ → ℂ :=
  thermofieldDiagonalKernel (conditionalClock tau (-phi))

/-- Equation (23), now as coefficients of a constructed square-summable vector. -/
theorem coherentPair_coefficient (tau phi : ℝ) (i j : ℕ) :
    coherentPair tau phi (i, j) = if i = j then
      (Real.sqrt (1 - thermalRatio tau) : ℂ) * coherentLabel tau phi ^ i else 0 := by
  simp only [coherentPair, thermofieldDiagonalKernel, conditionalClock_squeezed_coefficient, neg_neg]

/-- The entire infinite coherent pair is in the Hilbert--Schmidt domain. -/
theorem coherentPair_isHS (tau phi : ℝ) : HilbertSchmidt.IsHS (coherentPair tau phi) :=
  thermofieldDiagonalKernel_isHS _

/-- Normalization of the infinite two-mode coherent state for every phase. -/
theorem coherentPair_norm_sq (tau phi : ℝ) : HilbertSchmidt.hsNormSq (coherentPair tau phi) = 1 := by
  rw [coherentPair, hsNormSq_thermofieldDiagonalKernel, conditionalClock_norm_sq]

/-- Tracing out a bosonic partner removes all coherent phase information. -/
theorem coherentPair_partialTrace (tau phi : ℝ) (i j : ℕ) :
    (∑' k, coherentPair tau phi (i, k) * (starRingEnd ℂ) (coherentPair tau phi (j, k))) =
      if i = j then (radiationMass tau i : ℂ) else 0 := by
  rw [tsum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp only [coherentPair, thermofieldDiagonalKernel, ite_true]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, conditionalClock_probability]
    · simp [coherentPair, thermofieldDiagonalKernel, h, Ne.symm h]
  · intro k hk
    simp [coherentPair, thermofieldDiagonalKernel, Ne.symm hk]

/-- No finite-temperature disk label is the vacuum label. -/
theorem coherentLabel_ne_zero (tau phi : ℝ) : coherentLabel tau phi ≠ 0 := by
  intro h
  have hh := coherentLabel_normSq tau phi
  rw [h, Complex.normSq_zero] at hh
  exact (thermalRatio_pos tau).ne' hh.symm

/-- The phase-dependent infinite state is entangled for every allowed parameter. -/
theorem coherentPair_not_product (tau phi : ℝ) :
    ¬ ∃ f g : ℕ → ℂ, ∀ i j, coherentPair tau phi (i, j) = f i * g j := by
  rintro ⟨f, g, h⟩
  have hm : coherentPair tau phi (0, 0) * coherentPair tau phi (1, 1) -
      coherentPair tau phi (0, 1) * coherentPair tau phi (1, 0) = 0 := by
    rw [h, h, h, h]
    ring
  simp only [coherentPair_coefficient, ite_true, Nat.zero_ne_one, Nat.one_ne_zero,
    ite_false, pow_zero, pow_one, mul_one, mul_zero, sub_zero] at hm
  have hroot : (Real.sqrt (1 - thermalRatio tau) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sub_pos.mpr (thermalRatio_lt_one tau))).ne'
  exact (mul_ne_zero hroot (mul_ne_zero hroot (coherentLabel_ne_zero tau phi))) hm

end GaloisForLFunctions.HTGeometry.CPV
