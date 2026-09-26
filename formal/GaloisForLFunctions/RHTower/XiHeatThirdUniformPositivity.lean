import GaloisForLFunctions.RHTower.XiHeatThirdVanishingDebt
import GaloisForLFunctions.RHTower.XiHeatSamplingBands
import GaloisForLFunctions.HTGeometry.VandermondeSamplingEnergy

/-!
# Coefficient-uniform positivity of the third Xi heat form at small time

Three actual zero bands give separated bounded polynomial sampling nodes after
heat scaling. The full interpolation energy bounds every coefficient direction
below by one positive constant. The coefficient-uniform phase debt vanishes,
so the complete third Hankel form is eventually coercive, with every cross term
retained throughout the argument.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

/-- A positive energy floor independent of every real coefficient direction. -/
theorem xiHeatThirdNormEnergy_eventually_uniform_lower :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a b c : ℝ,
      η * (a ^ 2 + b ^ 2 + c ^ 2) ≤
        xiHeatThirdNormEnergy a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ := by
  classical
  let B : ℝ := 1 + 3 * 2305
  let C : ℝ := ((3 : ℕ).factorial : ℝ) * (B ^ 2) ^ 3
  have hC : 0 < C := by dsimp [C, B]; positivity
  refine ⟨Real.exp (-2305) / (27 * C ^ 2), by positivity, ?_⟩
  filter_upwards [eventually_exists_xiHeat_three_separated_nodes] with τ hτ
  obtain ⟨q, hq, h01, h12⟩ := hτ
  let z : Fin 3 → ℂ := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
  change (∀ i, ‖z i‖ ≤ 2305) at hq
  change 1 ≤ (z 1).re - (z 0).re at h01
  change 1 ≤ (z 2).re - (z 1).re at h12
  have hd01 : 1 ≤ ‖z 1 - z 0‖ := by
    have h := Complex.re_le_norm (z 1 - z 0)
    simp only [Complex.sub_re] at h
    linarith
  have hd12 : 1 ≤ ‖z 2 - z 1‖ := by
    have h := Complex.re_le_norm (z 2 - z 1)
    simp only [Complex.sub_re] at h
    linarith
  have hd02 : 1 ≤ ‖z 2 - z 0‖ := by
    have h := Complex.re_le_norm (z 2 - z 0)
    simp only [Complex.sub_re] at h
    linarith
  have hdet : 1 ≤ ‖(Matrix.vandermonde z).det‖ := by
    have he : (Matrix.vandermonde z).det =
        (z 1 - z 0) * (z 2 - z 0) * (z 2 - z 1) := by
      simp only [Matrix.det_fin_three, Matrix.vandermonde_apply]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
      ring
    rw [he, norm_mul, norm_mul]
    calc
      1 = 1 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hd01 hd02 (by positivity) (norm_nonneg _))
        hd12 (by positivity) (by positivity)
  have hcap : polynomialSamplingCap z ≤ C := by
    have hscale : phaseFrequencyScale z ≤ B := by
      unfold phaseFrequencyScale
      rw [Fin.sum_univ_three]
      dsimp [B]
      linarith [hq 0, hq 1, hq 2]
    unfold polynomialSamplingCap C
    have hnonneg : 0 ≤ phaseFrequencyScale z :=
      zero_le_one.trans (one_le_phaseFrequencyScale z)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ hnonneg hscale 2) 3)
      (Nat.cast_nonneg _)
  intro a b c
  let v : Fin 3 → ℂ := ![(a : ℂ), (b : ℂ), (c : ℂ)]
  have hval (i : Fin 3) : polynomialSample v (z i) =
      quadraticHeatValue a (b * Real.exp τ) (c * (Real.exp τ) ^ 2)
        (xiSpectralPoint (q i) ^ 2) := by
    simp [polynomialSample, Fin.sum_univ_three, v, z, quadraticHeatValue]
    ring
  have hv : (∑ j, ‖v j‖ ^ 2) = a ^ 2 + b ^ 2 + c ^ 2 := by
    simp [v, Fin.sum_univ_three, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsample : a ^ 2 + b ^ 2 + c ^ 2 ≤
      9 * C ^ 2 * ∑ i, ‖polynomialSample v (z i)‖ ^ 2 := by
    have h := polynomialSample_energy_bound z v
    rw [hv] at h
    have hd : 1 ≤ ‖(Matrix.vandermonde z).det‖ ^ 2 := by nlinarith
    have hleft := mul_le_mul_of_nonneg_right hd
      (show 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 by positivity)
    have hcap0 : 0 ≤ polynomialSamplingCap z := by
      unfold polynomialSamplingCap
      positivity [one_le_phaseFrequencyScale z]
    have hcap2 := (sq_le_sq₀ hcap0 hC.le).2 hcap
    have hright := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap2 (show (0 : ℝ) ≤ 3 ^ 2 by positivity))
      (show 0 ≤ ∑ i, ‖polynomialSample v (z i)‖ ^ 2 from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    calc
      _ = 1 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
      _ ≤ ‖(Matrix.vandermonde z).det‖ ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := hleft
      _ ≤ (3 : ℝ) ^ 2 * polynomialSamplingCap z ^ 2 *
          ∑ i, ‖polynomialSample v (z i)‖ ^ 2 := by
        simpa only [Nat.cast_ofNat] using h
      _ ≤ (3 : ℝ) ^ 2 * C ^ 2 * ∑ i, ‖polynomialSample v (z i)‖ ^ 2 := hright
      _ = _ := by ring
  have hatom (i : Fin 3) :
      Real.exp (-2305) * ‖polynomialSample v (z i)‖ ^ 2 ≤
        xiHeatThirdNormEnergy a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ := by
    have hre : (z i).re ≤ 2305 := (Complex.re_le_norm _).trans (hq i)
    have hexp : Real.exp (-2305) ≤ Real.exp (-(z i).re) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hterm := mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖polynomialSample v (z i)‖)
    have hn : ‖xiHeatThirdAmplitude a (b * Real.exp τ)
        (c * (Real.exp τ) ^ 2) τ (q i)‖ ^ 2 =
        Real.exp (-(z i).re) * ‖polynomialSample v (z i)‖ ^ 2 := by
      rw [xiHeatThirdAmplitude, heatPhaseAmplitude_norm_sq, hval]
      simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    have hsum := (summable_xiHeatThirdAmplitude_norm_sq a (b * Real.exp τ)
      (c * (Real.exp τ) ^ 2) τ).sum_le_tsum {q i} (fun _ _ => sq_nonneg _)
    simp only [Finset.sum_singleton] at hsum
    rw [hn] at hsum
    exact hterm.trans hsum
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hatom i)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsample (Real.exp_pos (-2305)).le
  have hupper := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 9 * C ^ 2 by positivity)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 27 * C ^ 2 by positivity)).2
  calc
    _ ≤ Real.exp (-2305) * (9 * C ^ 2 * ∑ i, ‖polynomialSample v (z i)‖ ^ 2) := hscaled
    _ = 9 * C ^ 2 * (Real.exp (-2305) * ∑ i, ‖polynomialSample v (z i)‖ ^ 2) := by ring
    _ ≤ 9 * C ^ 2 * (3 * xiHeatThirdNormEnergy a (b * Real.exp τ)
        (c * (Real.exp τ) ^ 2) τ) := hupper
    _ = _ := by ring

/-- The complete third form has a uniform positive coefficient margin at small heat time. -/
theorem xiHeatThirdQuadratic_eventually_uniform_coercive :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a b c : ℝ,
      η * (a ^ 2 + b ^ 2 + c ^ 2) ≤
        xiHeatThirdQuadratic a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) (Real.exp τ) := by
  obtain ⟨η, hη, hK⟩ := xiHeatThirdNormEnergy_eventually_uniform_lower
  refine ⟨η / 2, by positivity, ?_⟩
  have hD := xiHeatThirdUniformDebt_tendsto_zero.eventually_lt_const
    (show 0 < η / 2 by positivity)
  filter_upwards [hK, hD] with τ hK hD a b c
  have hbound := xiHeatThirdQuadratic_uniform_lower_bound a b c τ
  have hcoeff : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have herr := mul_le_mul_of_nonneg_left hD.le hcoeff
  have henergy := hK a b c
  nlinarith only [hbound, herr, henergy]

/-- Undoing the invertible coefficient scaling gives a bound for the literal third form. -/
theorem xiHeatThirdQuadratic_eventually_weighted_coercive :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a b c : ℝ,
      η * (a ^ 2 + (b / Real.exp τ) ^ 2 + (c / (Real.exp τ) ^ 2) ^ 2) ≤
        xiHeatThirdQuadratic a b c (Real.exp τ) := by
  obtain ⟨η, hη, h⟩ := xiHeatThirdQuadratic_eventually_uniform_coercive
  refine ⟨η, hη, ?_⟩
  filter_upwards [h] with τ hτ a b c
  have ht : Real.exp τ ≠ 0 := (Real.exp_pos τ).ne'
  have hb : b / Real.exp τ * Real.exp τ = b := div_mul_cancel₀ b ht
  have hc : c / (Real.exp τ) ^ 2 * (Real.exp τ) ^ 2 = c :=
    div_mul_cancel₀ c (pow_ne_zero 2 ht)
  have h' := hτ a (b / Real.exp τ) (c / (Real.exp τ) ^ 2)
  rw [hb, hc] at h'
  exact h'

/-- Every coefficient vector of the actual order-three Hankel form has a positive margin. -/
theorem xiHeatHankelForm_three_eventually_coercive :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ,
      η * (a 0 ^ 2 + (a 1 / Real.exp τ) ^ 2 + (a 2 / (Real.exp τ) ^ 2) ^ 2) ≤
        xiHeatHankelForm 3 a (Real.exp τ) := by
  obtain ⟨η, hη, h⟩ := xiHeatThirdQuadratic_eventually_weighted_coercive
  refine ⟨η, hη, ?_⟩
  filter_upwards [h] with τ hτ a
  have he : xiHeatHankelForm 3 a (Real.exp τ) =
      xiHeatThirdQuadratic (a 0) (a 1) (a 2) (Real.exp τ) := by
    simp [xiHeatHankelForm, xiHeatThirdQuadratic, Finset.sum_range_succ]
    ring
  rw [he]
  exact hτ (a 0) (a 1) (a 2)

end
end RHTower
