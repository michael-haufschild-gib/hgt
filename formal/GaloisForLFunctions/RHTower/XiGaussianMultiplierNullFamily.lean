import GaloisForLFunctions.RHTower.XiGaussianUniformHeatHalfLine

/-!
# Native null families inside every polynomial principal ideal

Multiplying the finite divisor annihilators by any fixed polynomial still
gives vanishing full native energy at a fixed positive heat time. The proof
uses a summable majorant for the entire product, including all cross terms.
One cutoff also controls the complete arithmetic source and its interaction
with every native unit vector throughout the later heat half-line.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- Fixed algebraic constraints imposed by a polynomial factor do not remove
the native null family. Neither the time nor the multiplier varies with degree. -/
theorem tendsto_xiGaussianNativeEnergy_mul_annihilator_zero
    (B : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiGaussianNativeEnergy (B * xiGaussianAnnihilator F) t) atTop (𝓝 0) := by
  classical
  obtain ⟨H, hH⟩ := exists_xiGaussianAnnihilator_dominating_head t
  have hpoint (q : XiZeroCopy) : Tendsto
      (fun F : Finset XiZeroCopy =>
        ‖xiPolynomialGaussianHeatTerm (B * xiGaussianAnnihilator F) t q‖)
      atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({q} : Finset XiZeroCopy)] with F hF
    have hq : q ∈ F := hF (Finset.mem_singleton_self q)
    simp only [xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
      xiGaussianAnnihilator_vanishes F ⟨q, hq⟩, mul_zero,
      zero_pow two_ne_zero, zero_mul, norm_zero]
  have hmul (P : Polynomial ℝ) (s : ℝ) (q : XiZeroCopy) :
      ‖xiPolynomialGaussianHeatTerm (B * P) s q‖ =
        ‖evalRealPolynomial B (xiSpectralPoint q ^ 2)‖ ^ 2 *
          ‖xiPolynomialGaussianHeatTerm P s q‖ := by
    simp only [norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
      norm_mul, mul_pow, mul_assoc]
  have hb : ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ q : XiZeroCopy,
      ‖‖xiPolynomialGaussianHeatTerm (B * xiGaussianAnnihilator F) t q‖‖ ≤
        ‖xiPolynomialGaussianHeatTerm (B * xiGaussianAnnihilator H)
          ((t : ℝ) / 2) q‖ := by
    filter_upwards [eventually_ge_atTop H] with F hF q
    rw [norm_norm, hmul, hmul]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Finset.union_eq_left.mpr hF] using hH F q
  simpa only [xiGaussianNativeEnergy, tsum_zero] using
    tendsto_tsum_of_dominated_convergence
      (summable_norm_xiPolynomialGaussianHeatTerm (div_pos t.property (by positivity))
        (B * xiGaussianAnnihilator H)) hpoint hb

/-- The same polynomial has small full native energy and complete prime--Gamma
residual at every time above the fixed positive anchor. -/
theorem eventually_xiGaussian_mul_annihilator_heatHalfLine_small
    (B : Polynomial ℝ) (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      xiGaussianNativeEnergy (B * xiGaussianAnnihilator F)
        (xiGaussianHeatAfter t₀ s) < (ε : ℝ) ∧
      |xiGaussianCompletedSourceResidual (B * xiGaussianAnnihilator F)
        (xiGaussianHeatAfter t₀ s)| < π * (ε : ℝ) := by
  filter_upwards [(tendsto_xiGaussianNativeEnergy_mul_annihilator_zero B t₀).eventually
    (Iio_mem_nhds ε.property)] with F hF s
  have hK : xiGaussianNativeEnergy (B * xiGaussianAnnihilator F)
      (xiGaussianHeatAfter t₀ s) < (ε : ℝ) := (xiGaussianNativeEnergy_antitone
    (B * xiGaussianAnnihilator F) s.property).trans_lt hF
  exact ⟨hK, (abs_xiGaussianCompletedSourceResidual_le_energy _ _).trans_lt
    (mul_lt_mul_of_pos_left hK Real.pi_pos)⟩

/-- All mixed arithmetic terms with the entire native unit ball vanish
uniformly in degree and in every later heat time. -/
theorem eventually_xiGaussian_mul_annihilator_mixed_source_small
    (B : Polynomial ℝ) (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t₀ ≤ 1},
        let Q := B * xiGaussianAnnihilator F
        let t := xiGaussianHeatAfter t₀ s
        |xiGaussianCompletedSourceResidual (P.1 + Q) t -
          xiGaussianCompletedSourceResidual P.1 t -
          xiGaussianCompletedSourceResidual Q t| < (ε : ℝ) := by
  let η : {η : ℝ // 0 < η} :=
    ⟨(ε : ℝ) / (2 * π), div_pos ε.property (by positivity)⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      π * ((η : ℝ) + (2 + 1 / (η : ℝ)) *
        xiGaussianNativeEnergy (B * xiGaussianAnnihilator F) t₀))
      atTop (𝓝 (π * (η : ℝ))) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add ((tendsto_xiGaussianNativeEnergy_mul_annihilator_zero
        B t₀).const_mul (2 + 1 / (η : ℝ)))).const_mul π
  have hη : π * (η : ℝ) < (ε : ℝ) := by
    dsimp only [η]
    field_simp
    linarith [ε.property]
  filter_upwards [hlim.eventually (Iio_mem_nhds hη)] with F hF s P
  dsimp only
  let Q := B * xiGaussianAnnihilator F
  let t := xiGaussianHeatAfter t₀ s
  have hP : xiGaussianNativeEnergy P.1 t ≤ 1 :=
    (xiGaussianNativeEnergy_antitone P.1 s.property).trans P.property
  have hQ : xiGaussianNativeEnergy Q t ≤ xiGaussianNativeEnergy Q t₀ :=
    xiGaussianNativeEnergy_antitone Q s.property
  have hηP : (η : ℝ) * xiGaussianNativeEnergy P.1 t ≤ (η : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hP η.property.le
  have hQ' := mul_le_mul_of_nonneg_left hQ
    (show 0 ≤ 2 + 1 / (η : ℝ) by have hp := η.property; positivity)
  calc
    _ ≤ |xiGaussianCompletedSourceResidual (P.1 + Q) t -
          xiGaussianCompletedSourceResidual P.1 t| +
        |xiGaussianCompletedSourceResidual Q t| := abs_sub _ _
    _ ≤ π * ((η : ℝ) * xiGaussianNativeEnergy P.1 t +
          (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t) +
        π * xiGaussianNativeEnergy Q t :=
      add_le_add (abs_xiGaussianCompletedSourceResidual_add_sub_le P.1 Q t η)
        (abs_xiGaussianCompletedSourceResidual_le_energy Q t)
    _ = π * ((η : ℝ) * xiGaussianNativeEnergy P.1 t +
        (2 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t) := by ring
    _ ≤ π * ((η : ℝ) + (2 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t₀) :=
      mul_le_mul_of_nonneg_left (add_le_add hηP hQ') Real.pi_pos.le
    _ < (ε : ℝ) := hF

end RHTower
