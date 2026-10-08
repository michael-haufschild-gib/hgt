import GaloisForLFunctions.RHTower.WeilWorkQuantizationRationalTranslation
/-!
# Signed bilateral rational rigidity of the actual Weil phase

Periodicity of the actual reflected residues annihilates every nonzero
rational harmonic. No sign or negative-mass summability assumption is used.
The final alternative has only the original Weil-positive source as input;
it does not assert that such a phase representation always exists.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity HamburgerStability
  PhaseLockRigidity GaloisForLFunctions.HTGeometry


/-- Actual signed bilateral rational phases have no nonzero harmonic. -/
theorem quantization_bilateral_rational_harmonic_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v)
    (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I))
    {k : ℤ} (hk : k ≠ 0) : p k = 0 := by
  have he := quantization_phase_resonance_periodic hW hp hphase
    (Real.exp_pos ((k : ℝ) * Real.log ((u : ℝ) / v)))
  rw [quantization_rational_real_sum_power_add_one hu hv huv p hk,
    quantization_rational_real_sum_power hu hv huv p k] at he
  exact (mul_eq_zero.mp he.symm).resolve_left
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

/-- Signed bilateral rational phases force source rigidity without a sign premise. -/
theorem quantization_rigidity_of_bilateral_rational_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hv : 2 ≤ v) (hvu : v < u)
    (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hz (j : ℤ) (hj : j ≠ 0) : p j = 0 :=
    quantization_bilateral_rational_harmonic_zero hW (by omega) hv huv hp hphase hj
  have hsum (m : ℕ) (hm : 1 ≤ m) :
      (∑' j : ℤ, p j * quantizationFrequencyResidue lam
        (2 * (j : ℝ) * Real.log ((u : ℝ) / v)) m) =
      p 0 * dirichletExp (lamLog lam) m := by
    rw [tsum_eq_single 0]
    · simp [quantizationFrequencyResidue_zero hm]
    · intro j hj
      rw [hz j hj, zero_mul]
  obtain ⟨hne, hrows⟩ := quantization_phase_resonance_constant hW hp hphase
  rw [hsum 1 le_rfl, dirichletExp_one (lamLog_zero lam) (lamLog_one lam), mul_one] at hne hrows
  have hone (m : ℕ) (hm : m ≠ 0) : dirichletExp (lamLog lam) m = 1 := by
    have he := hrows m (Nat.one_le_iff_ne_zero.mpr hm)
    rw [hsum m (Nat.one_le_iff_ne_zero.mpr hm)] at he
    exact mul_left_cancel₀ hne (he.trans (mul_one (p 0)).symm)
  exact vonMangoldt_and_RH_of_coeff_eq_one
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
    (differentiableOn_weilContinuation hW) (fun _ hs => quantizationContinuation_eq_arch hW hs)
    (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW) hone

/-- Source-only alternative: every nonrigid source excludes signed bilateral rational phases. -/
theorem quantization_rigidity_or_no_bilateral_rational_phase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ u v : ℕ, 2 ≤ v → v < u → u.Coprime v → ∀ p : ℤ → ℂ,
        (Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2)) →
        ¬(∀ x : ℝ, 0 < x →
          cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
            ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) := by
  classical
  by_cases hR : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl hR
  · exact Or.inr fun u v hv hvu huv p hp hphase =>
      hR (quantization_rigidity_of_bilateral_rational_phase hW hv hvu huv hp hphase)

end RHTower.WeilSpectral
