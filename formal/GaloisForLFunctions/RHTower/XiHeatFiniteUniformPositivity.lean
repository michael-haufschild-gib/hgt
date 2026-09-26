import GaloisForLFunctions.RHTower.XiHeatFiniteDecomposition
import GaloisForLFunctions.RHTower.XiHeatFiniteSamplingBands

/-!
# Uniform positivity at every finite Xi heat-Hankel order

At each finite order, separated actual Xi nodes provide an independent norm
energy floor, uniform over all coefficient vectors. The matching finite-degree
phase budget tends to zero, giving strict coercivity at sufficiently small
positive heat time. The cutoff depends on the order; no all-order common
cutoff or all-time positivity is assumed or concluded.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

/-- Every finite actual polynomial norm energy has a coefficient-uniform small-time floor. -/
theorem xiHeatFiniteNormEnergy_eventually_uniform_lower (N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a : Fin N → ℝ,
      η * (∑ j, a j ^ 2) ≤ xiHeatFiniteNormEnergy a τ := by
  classical
  cases N with
  | zero =>
    refine ⟨1, one_pos, Eventually.of_forall fun τ a => ?_⟩
    simpa using xiHeatFiniteNormEnergy_nonneg a τ
  | succ n =>
    let N := n + 1
    let M := xiHeatSamplingRadius N
    let B : ℝ := 1 + N * M
    let C : ℝ := N.factorial * (B ^ (N - 1)) ^ N
    have hN : (0 : ℝ) < N := by dsimp [N]; positivity
    have hM : 0 < M := xiHeatSamplingRadius_pos N
    have hB : 0 < B := by dsimp [B]; positivity
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨Real.exp (-M) / ((N : ℝ) ^ 3 * C ^ 2), by positivity, ?_⟩
    filter_upwards [eventually_exists_xiHeat_sampling_determinant N] with τ hτ
    obtain ⟨q, hq, hdet⟩ := hτ
    let z : Fin N → ℂ := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
    change (∀ i, ‖z i‖ ≤ M) at hq
    change 1 ≤ ‖(Matrix.vandermonde z).det‖ at hdet
    have hcap : polynomialSamplingCap z ≤ C := by
      have hs : ∑ i, ‖z i‖ ≤ (N : ℝ) * M := by
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
          Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hq i)
      have hscale : phaseFrequencyScale z ≤ B := by
        unfold phaseFrequencyScale
        dsimp [B]
        linarith
      have hz0 : 0 ≤ phaseFrequencyScale z := zero_le_one.trans (one_le_phaseFrequencyScale z)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (pow_nonneg hz0 (N - 1))
          (pow_le_pow_left₀ hz0 hscale (N - 1)) N) (Nat.cast_nonneg N.factorial)
    intro a
    let v : Fin N → ℂ := fun j => (a j : ℂ)
    have hv : (∑ j, ‖v j‖ ^ 2) = ∑ j, a j ^ 2 := by
      simp [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsample : (∑ j, a j ^ 2) ≤
        (N : ℝ) ^ 2 * C ^ 2 * ∑ i, ‖polynomialSample v (z i)‖ ^ 2 := by
      have h := polynomialSample_energy_bound z v
      rw [hv] at h
      have hd : 1 ≤ ‖(Matrix.vandermonde z).det‖ ^ 2 := by nlinarith
      have hleft := mul_le_mul_of_nonneg_right hd
        (show 0 ≤ ∑ j, a j ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have hcap0 : 0 ≤ polynomialSamplingCap z := by
        unfold polynomialSamplingCap
        positivity [one_le_phaseFrequencyScale z]
      have hright := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hcap0 hC.le).2 hcap) (sq_nonneg (N : ℝ)))
        (show 0 ≤ ∑ i, ‖polynomialSample v (z i)‖ ^ 2 from
          Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact (by simpa only [one_mul] using hleft).trans (h.trans hright)
    have hatom (i : Fin N) : Real.exp (-M) * ‖polynomialSample v (z i)‖ ^ 2 ≤
        xiHeatFiniteNormEnergy a τ := by
      have hre : (z i).re ≤ M := (Complex.re_le_norm _).trans (hq i)
      have hexp : Real.exp (-M) ≤ Real.exp (-(z i).re) :=
        Real.exp_le_exp.mpr (by linarith)
      have hterm := mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖polynomialSample v (z i)‖)
      have hn : ‖xiHeatFiniteAmplitude a τ (q i)‖ ^ 2 =
          Real.exp (-(z i).re) * ‖polynomialSample v (z i)‖ ^ 2 := by
        rw [xiHeatFiniteAmplitude_eq_sample, heatPhaseAmplitude_norm_sq]
        dsimp only [v, z]
        rw [one_mul, mul_comm]
      have hsum := (summable_xiHeatFiniteAmplitude_norm_sq a τ).sum_le_tsum {q i}
        (fun _ _ => sq_nonneg _)
      simp only [Finset.sum_singleton] at hsum
      rw [hn] at hsum
      exact hterm.trans hsum
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hatom i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hscaled := mul_le_mul_of_nonneg_left hsample (Real.exp_pos (-M)).le
    have hupper := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ (N : ℝ) ^ 2 * C ^ 2 by positivity)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < (N : ℝ) ^ 3 * C ^ 2 by positivity)).2
    calc
      _ ≤ Real.exp (-M) * ((N : ℝ) ^ 2 * C ^ 2 * ∑ i, ‖polynomialSample v (z i)‖ ^ 2) := hscaled
      _ = (N : ℝ) ^ 2 * C ^ 2 * (Real.exp (-M) * ∑ i, ‖polynomialSample v (z i)‖ ^ 2) := by ring
      _ ≤ (N : ℝ) ^ 2 * C ^ 2 * (N * xiHeatFiniteNormEnergy a τ) := hupper
      _ = _ := by ring

/-- Every finite Hankel order has one positive margin for all scaled coefficient directions. -/
theorem xiHeatHankelForm_eventually_scaled_coercive (N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a : Fin N → ℝ,
      η * (∑ j, a j ^ 2) ≤
        xiHeatHankelForm N (xiHeatScaledCoefficients a τ) (Real.exp τ) := by
  obtain ⟨η, hη, hK⟩ := xiHeatFiniteNormEnergy_eventually_uniform_lower N
  refine ⟨η / 2, by positivity, ?_⟩
  have hD := (xiHeatFinitePhaseBudget_tendsto_zero N).eventually_lt_const
    (show 0 < η / 2 by positivity)
  filter_upwards [hK, hD] with τ hK hD a
  have hbound := xiHeatHankelForm_scaled_lower_bound a τ
  have hA : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have herr := mul_le_mul_of_nonneg_left hD.le hA
  have henergy := hK a
  nlinarith only [hbound, herr, henergy]

/-- Literal full-Hankel coercivity; the same cutoff works for every coefficient vector. -/
theorem xiHeatHankelForm_eventually_weighted_coercive (N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ,
      η * (∑ j ∈ Finset.range N, (a j / (Real.exp τ) ^ j) ^ 2) ≤
        xiHeatHankelForm N a (Real.exp τ) := by
  obtain ⟨η, hη, h⟩ := xiHeatHankelForm_eventually_scaled_coercive N
  refine ⟨η, hη, ?_⟩
  filter_upwards [h] with τ hτ a
  let b : Fin N → ℝ := fun j => a j / (Real.exp τ) ^ (j : ℕ)
  have hb (j : ℕ) (hj : j < N) : xiHeatScaledCoefficients b τ j = a j := by
    simp only [xiHeatScaledCoefficients, dif_pos hj, b]
    exact div_mul_cancel₀ (a j) (pow_ne_zero j (Real.exp_pos τ).ne')
  have he : xiHeatHankelForm N (xiHeatScaledCoefficients b τ) (Real.exp τ) =
      xiHeatHankelForm N a (Real.exp τ) := by
    unfold xiHeatHankelForm
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hb j (Finset.mem_range.mp hj), hb k (Finset.mem_range.mp hk)]
  have h' := hτ b
  rw [he] at h'
  simpa only [b, Fin.sum_univ_eq_sum_range] using h'

/-- Unconditional simultaneous nonnegativity of every vector at each fixed finite order. -/
theorem xiHeatHankelForm_eventually_nonneg (N : ℕ) :
    ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ, 0 ≤ xiHeatHankelForm N a (Real.exp τ) := by
  obtain ⟨η, hη, h⟩ := xiHeatHankelForm_eventually_weighted_coercive N
  filter_upwards [h] with τ hτ a
  exact (mul_nonneg hη.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hτ a)

end
end RHTower
