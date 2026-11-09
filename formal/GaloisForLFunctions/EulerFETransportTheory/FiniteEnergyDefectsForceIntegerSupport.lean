import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsVanishInTheUnitGap
import GaloisForLFunctions.EulerFETransportTheory.IntegrableDefectsForceIntegerSupport

/-!
# Finite-energy defects force integer support

Conjugation symmetry of the actual interior transform passes to its strong Hardy
boundary. The unit-gap theorem therefore annihilates the origin tent. Its Fejér
identity then forces every generalized-integer norm onto the ordinary lattice.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open RHTower.HamburgerStability GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Reality of the theta law makes the real canonical Hardy boundary even almost everywhere. -/
theorem finiteEnergyBoundary_re_even_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ᵐ y : ℝ, (defectBoundaryL2 (hg.toLp g) (-y)).re =
      (defectBoundaryL2 (hg.toLp g) y).re := by
  let σ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hσpos : ∀ n, 0 < σ n := fun n => by dsimp only [σ]; positivity
  have hσ : Tendsto σ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hσgt : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL := (tendsto_defectVerticalL2 (hg.toLp g)).comp hσgt
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hneg := ((volume : Measure ℝ).measurePreserving_neg).quasiMeasurePreserving
  have hsym : ∀ᵐ y : ℝ, ∀ i : ℕ,
      (defectVerticalL2 (hg.toLp g) (σ (ns i)) (-y)).re =
        (defectVerticalL2 (hg.toLp g) (σ (ns i)) y).re := by
    apply ae_all_iff.mpr
    intro i
    have htrace := defectVerticalL2_ae (hg.toLp g) (hσpos (ns i))
    filter_upwards [htrace, hneg.ae htrace] with y hy hn
    rw [hy, hn]
    change (defectLaplace (hg.toLp g : ℝ → ℂ)
      ((σ (ns i) : ℂ) + ((-y : ℝ) : ℂ) * I)).re =
      (defectLaplace (hg.toLp g : ℝ → ℂ) ((σ (ns i) : ℂ) + (y : ℂ) * I)).re
    rw [defectLaplace_congr_ae hg.coeFn_toLp, defectLaplace_congr_ae hg.coeFn_toLp]
    exact defectLaplace_re_neg_of_theta_defect hsupp hmom hgm hgb hθ (hσpos (ns i)) y
  filter_upwards [hae, hneg.ae hae, hsym] with y hy hn hs
  have hp := (Complex.continuous_re.tendsto _).comp hy
  have hm := (Complex.continuous_re.tendsto _).comp hn
  exact tendsto_nhds_unique hm (hp.congr' (Eventually.of_forall fun i => (hs i).symm))

private theorem beurling_finiteEnergy_origin_error_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    finiteEnergyTentError (hg.toLp g) 1 0 = 0 := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hgap := beurling_finiteEnergyBoundary_re_eq_zero_on_unit_gap B hBsum hgm hgb hg hθ
  have heven := finiteEnergyBoundary_re_even_of_theta_defect hsupp hmom hgm hgb hg hθ
  have hneg := ((volume : Measure ℝ).measurePreserving_neg).quasiMeasurePreserving.ae hgap
  have hI : Integrable (fun y : ℝ => defectTentTest 1 0 y *
      defectBoundaryL2 (hg.toLp g) y) :=
    (memLp_defectTentTest zero_lt_one 0).integrable_mul (Lp.memLp (defectBoundaryL2 (hg.toLp g)))
  have hRe : finiteEnergyTentError (hg.toLp g) 1 0 =
      ∫ y : ℝ, (defectTentTest 1 0 y * defectBoundaryL2 (hg.toLp g) y).re :=
    (integral_re hI).symm
  rw [hRe]
  apply integral_eq_zero_of_ae
  filter_upwards [hgap, hneg, heven, volume.ae_ne (0 : ℝ)] with y hp hn he hy0
  simp only [defectTentTest, div_one, Complex.re_ofReal_mul, Pi.zero_apply]
  by_cases hout : 1 ≤ |y|
  · rw [unitTent_eq_zero (by simpa only [sub_zero] using hout), zero_mul]
  · have hin : |y| < 1 := lt_of_not_ge hout
    have hz : (defectBoundaryL2 (hg.toLp g) y).re = 0 := by
      rcases lt_or_gt_of_ne hy0 with hy | hy
      · exact he.symm.trans (hn ⟨neg_pos.mpr hy, by linarith only [(abs_lt.mp hin).1]⟩)
      · exact hp ⟨hy, (abs_lt.mp hin).2⟩
    rw [hz, mul_zero]

/-- Strong boundary convergence removes the full origin Fejér defect. -/
theorem beurling_tendsto_finiteEnergy_fejerDefectKernel
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, fejerDefectKernel g ε s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := (tendsto_tentDefectKernel_finiteEnergy hg zero_lt_one 0).const_mul 2
  rw [beurling_finiteEnergy_origin_error_eq_zero B hBsum hgm hgb hg hθ, mul_zero] at ht
  refine ht.congr' (Eventually.of_forall fun ε => ?_)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [fejerDefectKernel, tentDefectKernel, Complex.ofReal_one, one_mul, zero_add]
  ring

/-- The positive sinc-squared weight has zero mass for every finite-energy Beurling defect. -/
theorem beurling_integral_sinc_sq_eq_zero_of_finiteEnergy_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂beurlingSystemIntegerMeasure B = 0 := by
  let ν := beurlingSystemIntegerMeasure B
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hD (ε : ℝ) :
      (∫ u : ℝ, (∫ s in (-1 : ℝ)..1, tentDualKernel 1 0 ε s u) ∂ν) =
        ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
          (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    rw [intervalIntegral_tentDualKernel zero_lt_one (zero_lt_one.trans_le hu)]
    simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight]
  have hdual := (tendsto_integral_tentDualKernel hsupp hmom (h := 1) zero_lt_one 0).const_mul 2
  simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight] at hdual
  have hdual' := hdual.congr' (Eventually.of_forall fun ε => congrArg (fun r : ℝ => 2 * r) (hD ε))
  have hright := ((tendsto_integral_fejerSeriesKernel_zero hsupp hmom).sub
    (tendsto_integral_fejerPolarKernel_neg (β : ℂ))).sub
      (beurling_tendsto_finiteEnergy_fejerDefectKernel B hBsum hgm hgb hg hθ)
  simp only [sub_zero] at hright
  have hzero : Tendsto (fun ε : ℝ => 2 * ∫ u : ℝ,
      Real.exp (-2 * Real.pi * u * ε) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν)
      (𝓝[>] 0) (𝓝 0) := by
    apply hright.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact (fejer_pairing_identity_of_theta_defect hsupp hmom hgm hgb hθ hε.1 hε.2.le).symm
  have he := tendsto_nhds_unique hdual' hzero
  linarith only [he]

/-- Finite energy and the actual FE force every generalized-integer norm onto the natural numbers. -/
theorem beurling_intNorm_nat_of_finiteEnergy_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ x : B.Integer, ∃ k : ℕ, B.intNorm x = k := by
  have hsum : Summable fun i : B.Integer =>
      (Real.sin (Real.pi * B.intNorm i) / (Real.pi * B.intNorm i)) ^ 2 := by
    refine (summable_norm_tentFourierCoefficient B.intNorm_pos (summable_beurling_inv_sq B hBsum)
      (h := 1) zero_lt_one).congr fun i => ?_
    simp only [tentFourierWeight, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (sq_nonneg _)
  have hz := beurling_integral_sinc_sq_eq_zero_of_finiteEnergy_defect B hBsum hgm hgb hg hθ
  rw [integral_beurlingSystemIntegerMeasure_eq_tsum] at hz
  intro x
  have ht := hsum.le_tsum x (fun _ _ => sq_nonneg _)
  rw [hz] at ht
  have hr := abs_sub_round_le_of_sinc_sq_le (B.one_le_intNorm x) ht
  simp only [mul_zero, Real.sqrt_zero, zero_mul] at hr
  have he : B.intNorm x = (round (B.intNorm x) : ℝ) :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hr (abs_nonneg _)))
  have hnonneg : (0 : ℤ) ≤ round (B.intNorm x) := by
    have hreal : (0 : ℝ) ≤ (round (B.intNorm x) : ℝ) := he ▸ (B.intNorm_pos x).le
    exact_mod_cast hreal
  refine ⟨(round (B.intNorm x)).toNat, ?_⟩
  have hm := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hnonneg)
  push_cast at hm
  exact he.trans hm.symm

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.finiteEnergyBoundary_re_even_of_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_tendsto_finiteEnergy_fejerDefectKernel
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_integral_sinc_sq_eq_zero_of_finiteEnergy_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_intNorm_nat_of_finiteEnergy_theta_defect
