import GaloisForLFunctions.RHTower.WeilWorkQuantizationResonance
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardVariance

/-!
# Exact critical resonance norm

The height-one resonance row is the actual forward coefficient divided by
sqrt n. Its finite squared norm has the existing source energy's exact
pole/variance decomposition. This rules out an unweighted bounded extension
of the normalized resonance functional, not approximation of the source phase.
-/

open Complex Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilSingularArithmetic

/-- The critical resonance row after subtracting a constant coefficient mode. -/
def quantizationCenteredResonance (lam : ℕ → ℝ) (c : ℂ) (n : ℕ) : ℂ :=
  quantizationFrequencyResidue lam (-2 * Real.log n) 1 -
    (Real.exp (-Real.log n / 2) : ℂ) * c

/-- Squared norm of the finite critical resonance row. -/
def quantizationResonanceEnergy (lam : ℕ → ℝ) (c : ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖quantizationCenteredResonance lam c n‖ ^ 2

theorem quantizationCenteredResonance_eq (lam : ℕ → ℝ) (c : ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    quantizationCenteredResonance lam c n =
      (Real.exp (-Real.log n / 2) : ℂ) * (forwardCoeff lam n - c) := by
  have hres : quantizationFrequencyResonates (-2 * Real.log n) 1 n := by
    refine ⟨hn, ?_⟩
    simp only [Nat.cast_one, Real.log_one]
    ring
  rw [quantizationCenteredResonance, quantizationFrequencyResidue_eq hres,
    forwardCoeff_eq_sourceCoeff]
  dsimp only [WeilWorkSettledPhase.sourceCoeff]
  rw [show -2 * Real.log (n : ℝ) / 4 = -Real.log n / 2 by ring]
  ring

theorem quantizationCenteredResonance_norm_sq (lam : ℕ → ℝ) (c : ℂ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖quantizationCenteredResonance lam c n‖ ^ 2 = ‖forwardCoeff lam n - c‖ ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : Real.exp (-Real.log (n : ℝ) / 2) ^ 2 = (n : ℝ)⁻¹ := by
    rw [pow_two, ← Real.exp_add,
      show -Real.log (n : ℝ) / 2 + -Real.log n / 2 = -Real.log n by ring,
      Real.exp_neg, Real.exp_log hn0]
  rw [quantizationCenteredResonance_eq lam c hn, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  ring

theorem quantizationResonanceEnergy_eq (lam : ℕ → ℝ) (c : ℂ) (N : ℕ) :
    quantizationResonanceEnergy lam c N =
      ∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n - c‖ ^ 2 / n := by
  exact Finset.sum_congr rfl fun n hn =>
    quantizationCenteredResonance_norm_sq lam c (Finset.mem_Icc.mp hn).1

/-- The exact finite squared norm is an upper bound for every coefficient vector. -/
theorem quantization_resonance_norm_bound (lam : ℕ → ℝ) (c : ℂ) (N : ℕ)
    (p : ℕ → ℂ) :
    ‖∑ n ∈ Finset.Icc 1 N, p n * quantizationCenteredResonance lam c n‖ ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖p n‖ ^ 2) * quantizationResonanceEnergy lam c N := by
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖p n * quantizationCenteredResonance lam c n‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
        (norm_sum_le _ _)
    _ = (∑ n ∈ Finset.Icc 1 N, ‖p n‖ * ‖quantizationCenteredResonance lam c n‖) ^ 2 := by
      simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- A conjugate row attains the exact bound, including the zero row. -/
theorem quantization_resonance_norm_attained (lam : ℕ → ℝ) (c : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, conj (quantizationCenteredResonance lam c n) *
      quantizationCenteredResonance lam c n) = (quantizationResonanceEnergy lam c N : ℂ) ∧
    (∑ n ∈ Finset.Icc 1 N, ‖conj (quantizationCenteredResonance lam c n)‖ ^ 2) =
      quantizationResonanceEnergy lam c N := by
  constructor
  · simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      quantizationResonanceEnergy, Complex.ofReal_sum]
  · simp only [Complex.norm_conj, quantizationResonanceEnergy]

/-- Every full-positive source has an exact critical norm coefficient, with
the pole contribution separated from the still-unresolved residual variance. -/
theorem exists_quantization_resonance_energy_variance {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ K V : ℝ, 0 < K ∧ 0 ≤ V ∧
      K = ‖WeilWorkSettledPhase.sourceCompletion hW 1‖ ^ 2 + V ∧
      Tendsto (fun N : ℕ => quantizationResonanceEnergy lam 0 N / Real.log N)
        atTop (𝓝 K) ∧
      Tendsto (fun N : ℕ => quantizationResonanceEnergy lam
        (WeilWorkSettledPhase.sourceCompletion hW 1) N / Real.log N) atTop (𝓝 V) := by
  simpa only [quantizationResonanceEnergy_eq, sub_zero] using
    exists_forwardCoeff_energy_variance hW

/-- The original source's critical resonance row has unbounded squared norm. -/
theorem tendsto_quantization_resonance_energy {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (quantizationResonanceEnergy lam 0) atTop atTop := by
  obtain ⟨K, V, hK, _, _, hlim, _⟩ := exists_quantization_resonance_energy_variance hW
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply (hlim.pos_mul_atTop hK hlog).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega))))

/-- No finite bound controls all finite critical resonance rows in coefficient
square norm. The only source premise is the original full Weil positivity. -/
theorem quantization_resonance_unbounded {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (C : ℝ) :
    ∃ (N : ℕ) (p : ℕ → ℂ),
      C * (∑ n ∈ Finset.Icc 1 N, ‖p n‖ ^ 2) <
        ‖∑ n ∈ Finset.Icc 1 N, p n * quantizationFrequencyResidue lam (-2 * Real.log n) 1‖ ^ 2 := by
  obtain ⟨N, hN⟩ := ((tendsto_quantization_resonance_energy hW).eventually_gt_atTop
    (max C 0)).exists
  have hpos : 0 < quantizationResonanceEnergy lam 0 N := lt_of_le_of_lt (le_max_right _ _) hN
  have hC : C < quantizationResonanceEnergy lam 0 N := lt_of_le_of_lt (le_max_left _ _) hN
  obtain ⟨hr, he⟩ := quantization_resonance_norm_attained lam 0 N
  refine ⟨N, fun n => conj (quantizationCenteredResonance lam 0 n), ?_⟩
  have hz : ∀ n : ℕ, quantizationFrequencyResidue lam (-2 * Real.log n) 1 =
      quantizationCenteredResonance lam 0 n := by simp [quantizationCenteredResonance]
  simp_rw [hz]
  rw [he, hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  nlinarith [mul_lt_mul_of_pos_right hC hpos]

end RHTower.WeilSpectral
