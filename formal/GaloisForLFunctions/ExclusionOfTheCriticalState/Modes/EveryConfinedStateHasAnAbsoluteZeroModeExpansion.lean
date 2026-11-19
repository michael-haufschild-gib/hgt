import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheNullVectorsOfTheConfinedForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheAveragedStateIsTheSumOfItsZeroModes

/-!
# The averaged zero modes of every confined state

Four exponential averages make the coefficients absolutely summable even
after multiplication by the square of the zero ordinate. Partial fractions
cancel the base point of the subtracted Cauchy formula. Laplace inversion
therefore recovers every averaged null state for an arbitrary zero divisor.
-/

noncomputable section
open MeasureTheory Set Filter Complex Metric Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Each factor of the averaging denominator at a zero dominates its centered modulus. -/
private theorem norm_le_norm_add_real_of_strip {z : ℂ} (hz : -(1/2) ≤ z.re)
    {n : ℝ} (hn : 1 ≤ n) : ‖z‖ ≤ ‖z + (n : ℂ)‖ := by
  have h : 0 ≤ n*(2*z.re+n) := mul_nonneg (by linarith only [hn]) (by linarith only [hz,hn])
  have hs : ‖z‖^2 ≤ ‖z+(n : ℂ)‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero]
    linarith only [h]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

private theorem norm_averageSymbol_zero_le_fourth (q : XiZeroCopy) :
    ‖averageSymbol (centredZero q - 8)‖ ≤ (‖centredZero q‖^4)⁻¹ := by
  let z := centredZero q
  have hz := (abs_lt.mp (abs_re_centredZero_lt q)).1.le
  have h (n : ℕ) (hn : 1 ≤ n) : ‖z‖ ≤ ‖z + n‖ := by
    exact_mod_cast norm_le_norm_add_real_of_strip hz (n := (n : ℝ)) (by exact_mod_cast hn)
  have he : averageSymbol (z-8) = ((z+1)*(z+2)*(z+3)*(z+4))⁻¹ := by
    unfold averageSymbol
    congr 1
    ring
  change ‖averageSymbol (z-8)‖ ≤ _
  rw [he, norm_inv, norm_mul, norm_mul, norm_mul]
  apply inv_anti₀ (pow_pos (norm_pos_iff.mpr (centredZero_ne_zero q)) _)
  change ‖z‖^4 ≤ _
  calc ‖z‖^4 = ‖z‖*‖z‖*‖z‖*‖z‖ := by ring
       _ ≤ _ := by
         gcongr
         · exact_mod_cast h 1 (by decide)
         · exact_mod_cast h 2 (by decide)
         · exact_mod_cast h 3 (by decide)
         · exact_mod_cast h 4 (by decide)

/-- Absolute summability holds with two powers of the centered zero still in the numerator. -/
theorem domain_summable_zeroModeCoeff_sq_weight (R : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Summable fun q => ‖zeroModeCoeff R F q‖ * ‖centredZero q‖^2 := by
  let C := ‖(criticalAliasCoefficient R : ℂ)⁻¹‖ * transformMass F (-1)
  refine (summable_inv_sq_centredZero.mul_left C).of_nonneg_of_le
    (fun q => mul_nonneg (norm_nonneg _) (sq_nonneg _)) fun q => ?_
  have hf := norm_laplace_le_transformMass hF (σ := -1) (by norm_num)
    (p := centredZero q) (by linarith only [(abs_lt.mp (abs_re_centredZero_lt q)).1])
  have hm := mul_le_mul_of_nonneg_left hf (norm_nonneg (criticalAliasCoefficient R : ℂ)⁻¹)
  have hb := mul_le_mul hm (norm_averageSymbol_zero_le_fourth q) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (transformMass_nonneg _ _))
  have hv := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖centredZero q‖)
  have hn := (norm_pos_iff.mpr (centredZero_ne_zero q)).ne'
  unfold zeroModeCoeff
  simp only [norm_mul, norm_neg]
  refine hv.trans_eq ?_
  dsimp only [C]
  field_simp [hn]

theorem domain_summable_norm_zeroModeCoeff (R : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : Summable fun q => ‖zeroModeCoeff R F q‖ := by
  refine (domain_summable_zeroModeCoeff_sq_weight R hF).of_nonneg_of_le
    (fun q => norm_nonneg _) fun q => ?_
  apply le_mul_of_one_le_right (norm_nonneg _)
  simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (one_lt_norm_centredZero q).le 2

private theorem hasSum_subtracted_state (R : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {w : ℂ} (hw : xi (1/2+(w+8)) ≠ 0) :
    HasSum (fun q => -(criticalAliasCoefficient R : ℂ)⁻¹ *
      (negativeHalfLineLaplace (cx F) (centredZero q) *
        ((w+8-centredZero q)⁻¹ - (1-centredZero q)⁻¹)))
      (stateMeromorphic R F w - stateMeromorphic R F (-7)) := by
  obtain ⟨δ,hδ,hball⟩ := exists_zeroFree_ball hw
  have hs := ((summable_zeroSum_term hF hδ (hball (w+8) (mem_ball_self hδ))).hasSum).mul_left
    (-(criticalAliasCoefficient R : ℂ)⁻¹)
  change HasSum _ (-(criticalAliasCoefficient R : ℂ)⁻¹ * zeroSum F (w+8)) at hs
  convert hs using 1
  unfold stateMeromorphic
  rw [show (-7 : ℂ)+8 = 1 by norm_num, ← globalRemainder_sub_eq_zeroSum hF hw]
  ring

/-- The four residues of the averaging symbol cancel the common Cauchy subtraction
at every zero. The resulting transform identity holds for every confined null state. -/
theorem IsConfinedNullVector.hasSum_zeroModeTransform {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun q => zeroModeCoeff R F q * (w+8-centredZero q)⁻¹)
      (averageSymbol w * negativeHalfLineLaplace (cx F) w - archimedeanTransform R F w) := by
  have ha : (criticalAliasCoefficient R : ℂ) ≠ 0 := by exact_mod_cast (criticalAliasCoefficient_positive hR).ne'
  have hA := (hasSum_subtracted_state R hF.1 (xi_half_add_ne_zero_of_re hw)).mul_left (averageSymbol w)
  have h9 := (hasSum_subtracted_state R hF.1 (w := -9)
    (by convert xi_half_add_ofReal_ne_zero (-9) using 3; norm_num)).mul_left (1/6*(w+9)⁻¹)
  have h10 := (hasSum_subtracted_state R hF.1 (w := -10)
    (by convert xi_half_add_ofReal_ne_zero (-10) using 3; norm_num)).mul_left (1/2*(w+10)⁻¹)
  have h11 := (hasSum_subtracted_state R hF.1 (w := -11)
    (by convert xi_half_add_ofReal_ne_zero (-11) using 3; norm_num)).mul_left (1/2*(w+11)⁻¹)
  have h12 := (hasSum_subtracted_state R hF.1 (w := -12)
    (by convert xi_half_add_ofReal_ne_zero (-12) using 3; norm_num)).mul_left (1/6*(w+12)⁻¹)
  have hs := hA.sub (((h9.sub h10).add h11).sub h12)
  have hpart := averageSymbol_partialFraction (z := w) (by linarith only [hw])
  have hsum := hs.congr_fun (g := fun q => zeroModeCoeff R F q * (w+8-centredZero q)⁻¹)
    (fun q => by
      unfold zeroModeCoeff
      have hres := averageSymbol_mul_zeroResolvent (c := negativeHalfLineLaplace (cx F) (centredZero q))
        ha hw (abs_re_centredZero_lt q)
      rw [hpart] at hres ⊢
      linear_combination -hres)
  have he : averageSymbol w * negativeHalfLineLaplace (cx F) w - archimedeanTransform R F w =
      averageSymbol w * (stateMeromorphic R F w - stateMeromorphic R F (-7)) -
        (1/6*(w+9)⁻¹ * (stateMeromorphic R F (-9) - stateMeromorphic R F (-7)) -
         1/2*(w+10)⁻¹ * (stateMeromorphic R F (-10) - stateMeromorphic R F (-7)) +
         1/2*(w+11)⁻¹ * (stateMeromorphic R F (-11) - stateMeromorphic R F (-7)) -
         1/6*(w+12)⁻¹ * (stateMeromorphic R F (-12) - stateMeromorphic R F (-7))) := by
    rw [← nullVector_stateMeromorphic_eq_laplace hR hF (show -4 < w.re by linarith only [hw]), hpart]
    unfold archimedeanTransform
    ring
  rw [he]
  exact hsum

private theorem domain_averagedState_exp_three_le {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → |averagedState F t| ≤ B * Real.exp (-(3 * t)) := by
  set g : ℝ → ℝ := fun u => (F u ^ 2 * Real.exp (-(8 * u)) + probe 2 u) / 2
  have hg : Integrable g := (hF.exponential.add (integrable_probe (by norm_num : (0 : ℝ) < 2))).div_const 2
  have hg_neg : Integrable fun h : ℝ => g (-h) := hg.comp_neg
  have hg_nn : ∀ h : ℝ, 0 ≤ g (-h) := fun h =>
    div_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (probe_nonneg 2 (-h)))
      (by norm_num)
  set I : ℝ := ∫ h : ℝ, g (-h)
  have hI_nn : 0 ≤ I := integral_nonneg hg_nn
  have hexp_b : ∀ {b : ℝ}, 3 ≤ b → ∀ {t : ℝ}, 0 < t →
      |expAverage b F t| ≤ I * Real.exp (-(3 * t)) := by
    intro b hb t ht
    rw [expAverage_eq_setIntegral b F ht]
    have hmaj : Integrable (fun h : ℝ => Real.exp (-(3 * t)) * g (-h))
        (volume.restrict (Ioc (0 : ℝ) t)) := (hg_neg.const_mul (Real.exp (-(3 * t)))).restrict
    refine (Real.norm_eq_abs _).ge.trans ((norm_integral_le_of_norm_le hmaj ?_).trans ?_)
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun h hh => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp1 : Real.exp (-(b * (t - h))) ≤ Real.exp (-(3 * t)) * Real.exp (3 * h) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hdiff : 0 ≤ (b - 3) * (t - h) := mul_nonneg (by linarith) (sub_nonneg.mpr hh.2)
        linarith
      have hneg_h : -h < 0 := neg_lt_zero.mpr hh.1
      have hsq_F : (|F (-h)| * Real.exp (-(4 * (-h)))) ^ 2 = F (-h) ^ 2 * Real.exp (-(8 * (-h))) := by
        rw [mul_pow, sq_abs, sq (Real.exp (-(4 * (-h)))), ← Real.exp_add]; congr 2; ring
      have hsq_e : Real.exp (-h) ^ 2 = probe 2 (-h) := by
        rw [probe_of_neg hneg_h, sq, ← Real.exp_add]; congr 1; ring
      have hprod : (|F (-h)| * Real.exp (-(4 * (-h)))) * Real.exp (-h) =
          Real.exp (3 * h) * |F (-h)| := by
        rw [mul_assoc, ← Real.exp_add, mul_comm |F (-h)|]; congr 2; ring
      have hle_g : Real.exp (3 * h) * |F (-h)| ≤ g (-h) := by
        dsimp [g]
        nlinarith [sq_nonneg (|F (-h)| * Real.exp (-(4 * (-h))) - Real.exp (-h)),
          hsq_F, hsq_e, hprod]
      calc Real.exp (-(b * (t - h))) * |F (-h)|
          ≤ (Real.exp (-(3 * t)) * Real.exp (3 * h)) * |F (-h)| :=
            mul_le_mul_of_nonneg_right hexp1 (abs_nonneg _)
        _ = Real.exp (-(3 * t)) * (Real.exp (3 * h) * |F (-h)|) := by ring
        _ ≤ Real.exp (-(3 * t)) * g (-h) :=
            mul_le_mul_of_nonneg_left hle_g (Real.exp_pos _).le
    · calc ∫ h in Ioc (0 : ℝ) t, Real.exp (-(3 * t)) * g (-h)
          ≤ ∫ h : ℝ, Real.exp (-(3 * t)) * g (-h) :=
            setIntegral_le_integral (hg_neg.const_mul _)
              (Eventually.of_forall fun h => mul_nonneg (Real.exp_pos _).le (hg_nn h))
        _ = I * Real.exp (-(3 * t)) := by rw [integral_const_mul, mul_comm]
  refine ⟨2 * I, by positivity, fun t ht => ?_⟩
  obtain ⟨l9, u9⟩ := abs_le.mp (hexp_b (by norm_num : (3 : ℝ) ≤ 9) ht)
  obtain ⟨l10, u10⟩ := abs_le.mp (hexp_b (by norm_num : (3 : ℝ) ≤ 10) ht)
  obtain ⟨l11, u11⟩ := abs_le.mp (hexp_b (by norm_num : (3 : ℝ) ≤ 11) ht)
  obtain ⟨l12, u12⟩ := abs_le.mp (hexp_b (by norm_num : (3 : ℝ) ≤ 12) ht)
  unfold averagedState
  rw [abs_le]
  constructor <;> linarith

/-- Every averaged confined null state is the sum of its zeta modes and its
four exponential averaging terms on the full open half-line. -/
theorem IsConfinedNullVector.averagedState_eq_modes {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    {t : ℝ} (ht : 0 < t) :
    (averagedState F t : ℂ) = zeroModeSeries R F t + archimedeanModes R F t := by
  have hS_sum : Summable fun q => ‖zeroModeCoeff R F q‖ :=
    domain_summable_norm_zeroModeCoeff R hF.1
  obtain ⟨B, hB0, hB⟩ := domain_averagedState_exp_three_le hF.1
  set S : ℝ := ∑' q, ‖zeroModeCoeff R F q‖
  set K : ℝ := ‖stateMeromorphic R F (-9)‖ + ‖stateMeromorphic R F (-10)‖ +
    ‖stateMeromorphic R F (-11)‖ + ‖stateMeromorphic R F (-12)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun q => norm_nonneg _
  have hK0 : 0 ≤ K := by positivity
  have hcA : Continuous fun s : ℝ => ((averagedState F s : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_averagedState hF.1.integrable)
  have hcZ_Ici : ContinuousOn (zeroModeSeries R F) (Ici 0) := by
    refine continuousOn_tsum (fun q => (by fun_prop : Continuous fun s : ℝ =>
        zeroModeCoeff R F q * Complex.exp ((centredZero q - 8) * s)).continuousOn)
      hS_sum fun q s hs => ?_
    rw [norm_mul]
    calc ‖zeroModeCoeff R F q‖ * ‖Complex.exp ((centredZero q - 8) * s)‖
        ≤ ‖zeroModeCoeff R F q‖ * 1 :=
          mul_le_mul_of_nonneg_left ((norm_cexp_zeroMode_le q hs).trans
            (Real.exp_le_one_iff.mpr (by nlinarith [mem_Ici.mp hs]))) (norm_nonneg _)
      _ = ‖zeroModeCoeff R F q‖ := mul_one _
  have hcZ : ContinuousOn (zeroModeSeries R F) (Ioi 0) := hcZ_Ici.mono Ioi_subset_Ici_self
  have hcR : Continuous (archimedeanModes R F) := by unfold archimedeanModes; fun_prop
  have hφc : ContinuousOn (fun s : ℝ => ((averagedState F s : ℝ) : ℂ) - zeroModeSeries R F s -
      archimedeanModes R F s) (Ioi 0) :=
    (hcA.continuousOn.sub hcZ).sub hcR.continuousOn
  have bA : ∀ s : ℝ, 0 < s → ‖((averagedState F s : ℝ) : ℂ)‖ ≤ B * Real.exp (-(3 * s)) :=
    fun s hs => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB s hs
  have bZ : ∀ s : ℝ, 0 < s → ‖zeroModeSeries R F s‖ ≤ S * Real.exp (-(3 * s)) := by
    intro s hs
    have hb : ∀ q, ‖zeroModeCoeff R F q * Complex.exp ((centredZero q - 8) * s)‖ ≤
        ‖zeroModeCoeff R F q‖ * Real.exp (-(15 / 2 * s)) := fun q => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_cexp_zeroMode_le q hs.le) (norm_nonneg _)
    have h15 : ‖zeroModeSeries R F s‖ ≤ S * Real.exp (-(15 / 2 * s)) := by
      unfold zeroModeSeries; dsimp [S]; rw [← tsum_mul_right]
      exact (norm_tsum_le_tsum_norm
        ((hS_sum.mul_right _).of_nonneg_of_le (fun q => norm_nonneg _) hb)).trans
        (Summable.tsum_le_tsum hb
          ((hS_sum.mul_right _).of_nonneg_of_le (fun q => norm_nonneg _) hb)
          (hS_sum.mul_right _))
    exact h15.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hS0)
  have bR : ∀ s : ℝ, 0 < s → ‖archimedeanModes R F s‖ ≤ K * Real.exp (-(3 * s)) := fun s hs =>
    (norm_archimedeanModes_le R F hs.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK0)
  -- The exponential bounds place the difference in the space for Laplace inversion.
  have hmem : MemLp (fun s : ℝ => ((averagedState F s : ℝ) : ℂ) - zeroModeSeries R F s -
      archimedeanModes R F s) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    refine ((memLp_two_expRay_restrict (w := 3) (by norm_num) 0).const_mul
      (((B + S + K : ℝ)) : ℂ)).of_le (hφc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_expRay,
      show -((3 : ℂ).re * s) = -(3 * s) by simp]
    calc ‖((averagedState F s : ℝ) : ℂ) - zeroModeSeries R F s - archimedeanModes R F s‖
        ≤ ‖((averagedState F s : ℝ) : ℂ)‖ + ‖zeroModeSeries R F s‖ + ‖archimedeanModes R F s‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (B + S + K) * Real.exp (-(3 * s)) := by nlinarith [bA s hs, bZ s hs, bR s hs]
  have hlap : ∀ w : ℂ, 0 < w.re → laplaceRay (fun s : ℝ => ((averagedState F s : ℝ) : ℂ) -
      zeroModeSeries R F s - archimedeanModes R F s) w = 0 := by
    intro w hw
    have hexp : ∀ s : ℝ, 0 < s → ‖expRay w s‖ ≤ 1 := fun s hs => by
      rw [norm_expRay]; exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hint : ∀ f : ℝ → ℂ, ContinuousOn f (Ioi 0) → ∀ M : ℝ,
        (∀ s : ℝ, 0 < s → ‖f s‖ ≤ M * Real.exp (-(3 * s))) →
          IntegrableOn (fun s => f s * expRay w s) (Ioi 0) := by
      intro f hf M hM
      refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 3)).const_mul M).mono'
        ((hf.mul (continuous_expRay w).continuousOn).aestronglyMeasurable measurableSet_Ioi)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
      rw [norm_mul, show -3 * s = -(3 * s) by ring]
      calc ‖f s‖ * ‖expRay w s‖ ≤ M * Real.exp (-(3 * s)) * 1 :=
            mul_le_mul (hM s hs) (hexp s hs) (norm_nonneg _) ((norm_nonneg _).trans (hM s hs))
        _ = M * Real.exp (-(3 * s)) := mul_one _
    have iA := hint _ hcA.continuousOn _ bA
    have iZ := hint _ hcZ _ bZ
    have iR := (integral_archimedeanModes_mul_expRay R F hw).1
    have vA : ∫ s in Ioi (0 : ℝ), ((averagedState F s : ℝ) : ℂ) * expRay w s =
        averageSymbol w * negativeHalfLineLaplace (cx F) w := by
      rw [← integral_averagedState_laplace hF.1 hw]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      simp only [expRay]; ring
    have hsum_trans := hF.hasSum_zeroModeTransform hR hw
    -- Integrate the absolutely convergent mode series on the positive ray.
    have hsum_int : HasSum (fun q => zeroModeCoeff R F q * (w + 8 - centredZero q)⁻¹)
        (∫ s in Ioi (0 : ℝ), zeroModeSeries R F s * expRay w s) := by
      have hlt : ∀ q : XiZeroCopy, (centredZero q - 8).re < w.re := fun q => by
        have := (abs_lt.mp (abs_re_centredZero_lt q)).2
        have hre : (centredZero q - 8).re = (centredZero q).re - 8 := by simp
        linarith
      have hI : ∀ q : XiZeroCopy, Integrable (fun s : ℝ => zeroModeCoeff R F q *
          (Complex.exp ((centredZero q - 8) * s) * expRay w s)) (volume.restrict (Ioi 0)) :=
        fun q => (integrableOn_cexp_mul_expRay (hlt q)).const_mul _
      have hN : ∀ q : XiZeroCopy, ∫ s in Ioi (0 : ℝ), ‖zeroModeCoeff R F q *
          (Complex.exp ((centredZero q - 8) * s) * expRay w s)‖ =
            ‖zeroModeCoeff R F q‖ * (w.re - (centredZero q - 8).re)⁻¹ := fun q => by
        simp_rw [norm_mul (zeroModeCoeff R F q)]
        rw [integral_const_mul, integral_norm_cexp_mul_expRay (hlt q)]
      have hS_int : Summable fun q : XiZeroCopy => ∫ s in Ioi (0 : ℝ), ‖zeroModeCoeff R F q *
          (Complex.exp ((centredZero q - 8) * s) * expRay w s)‖ := by
        simp_rw [hN]
        refine (hS_sum.mul_right (2 / 15)).of_nonneg_of_le
          (fun q => mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (by linarith [hlt q])))
          fun q => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have := (abs_lt.mp (abs_re_centredZero_lt q)).2
        have hre : (centredZero q - 8).re = (centredZero q).re - 8 := by simp
        rw [hre]
        calc (w.re - ((centredZero q).re - 8))⁻¹ ≤ (15 / 2 : ℝ)⁻¹ :=
              inv_anti₀ (by norm_num) (by linarith)
          _ = 2 / 15 := by norm_num
      have h := hasSum_integral_of_summable_integral_norm hI hS_int
      have hval : ∫ s in Ioi (0 : ℝ), zeroModeSeries R F s * expRay w s =
          ∫ s in Ioi (0 : ℝ), ∑' q, zeroModeCoeff R F q *
            (Complex.exp ((centredZero q - 8) * s) * expRay w s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        simp only [zeroModeSeries]; rw [← tsum_mul_right]; exact tsum_congr fun q => by ring
      rw [hval]
      refine h.congr_fun fun q => ?_
      rw [integral_const_mul, integral_cexp_mul_expRay (hlt q)]
      congr 2; ring
    have vZ := hsum_int.unique hsum_trans
    have iAZ : IntegrableOn (fun x : ℝ => ((averagedState F x : ℝ) : ℂ) * expRay w x -
        zeroModeSeries R F x * expRay w x) (Ioi 0) := iA.sub iZ
    have hpt : ∀ x : ℝ, (((averagedState F x : ℝ) : ℂ) - zeroModeSeries R F x -
        archimedeanModes R F x) * expRay w x = ((averagedState F x : ℝ) : ℂ) * expRay w x -
          zeroModeSeries R F x * expRay w x - archimedeanModes R F x * expRay w x := fun x => by ring
    unfold laplaceRay
    simp_rw [hpt]
    rw [integral_sub iAZ iR, integral_sub iA iZ, vA, vZ,
      (integral_archimedeanModes_mul_expRay R F hw).2]
    ring
  have hae := ae_eq_zero_of_laplaceRay_eq_zero hmem hlap
  have heq := Measure.eqOn_open_of_ae_eq (f := fun s : ℝ => ((averagedState F s : ℝ) : ℂ) -
      zeroModeSeries R F s - archimedeanModes R F s) (g := fun _ => (0 : ℂ))
    hae isOpen_Ioi hφc continuousOn_const
  have h0 := heq ht
  simp only at h0
  linear_combination h0

/-- The ungrouped series over all zero copies converges absolutely to the
averaged state after subtraction of the known four exponential terms. -/
theorem IsConfinedNullVector.hasSum_averagedState {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun q => zeroModeCoeff R F q * cexp ((centredZero q-8)*t))
      ((averagedState F t : ℂ) - archimedeanModes R F t) := by
  rw [hF.averagedState_eq_modes hR ht, add_sub_cancel_right]
  apply Summable.hasSum
  apply Summable.of_norm_bounded (domain_summable_norm_zeroModeCoeff R hF.1)
  intro q
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact (norm_cexp_zeroMode_le q ht.le).trans (Real.exp_le_one_iff.mpr (by nlinarith only [ht]))

/-- At every positive critical ratio, the right-zero modes alone recover the
averaged state up to the decay rate of the critical line. -/
theorem IsConfinedNullVector.averagedState_sub_rightModes_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) :
    ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ‖(averagedState F t : ℂ) - ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
        zeroModeCoeff R F q * cexp ((centredZero q-8)*t) else 0)‖ ≤ K * Real.exp (-(8*t)) := by
  classical
  let C := ‖stateMeromorphic R F (-9)‖ + ‖stateMeromorphic R F (-10)‖ +
    ‖stateMeromorphic R F (-11)‖ + ‖stateMeromorphic R F (-12)‖
  refine ⟨(∑' q, ‖zeroModeCoeff R F q‖) + C, fun t ht => ?_⟩
  let f := fun q => zeroModeCoeff R F q * cexp ((centredZero q-8)*t)
  let S := {q : XiZeroCopy | 0 < (centredZero q).re}
  have hs := hF.hasSum_averagedState hR ht
  have hind (A : Set XiZeroCopy) : Summable (A.indicator f) := by
    apply Summable.of_norm_bounded hs.summable.norm
    intro q
    by_cases hq : q ∈ A <;> simp [hq, f]
  have hsplit := (hind Sᶜ).hasSum.add (hind S).hasSum
  have he : ∀ q, Sᶜ.indicator f q + S.indicator f q = f q := by
    intro q
    by_cases hq : q ∈ S <;> simp [hq]
  have htotal : (∑' q, Sᶜ.indicator f q) + (∑' q, S.indicator f q) =
      (averagedState F t : ℂ) - archimedeanModes R F t := (hsplit.congr_fun (fun q => (he q).symm)).unique hs
  have hb (q : XiZeroCopy) :
      ‖Sᶜ.indicator f q‖ ≤ ‖zeroModeCoeff R F q‖ * Real.exp (-(8*t)) := by
    by_cases hq : 0 < (centredZero q).re
    · simp only [Set.indicator_of_notMem (show q ∉ Sᶜ from not_not_intro hq), norm_zero]
      positivity
    · rw [Set.indicator_of_mem (show q ∈ Sᶜ from hq)]
      dsimp only [f]
      rw [norm_mul, norm_cexp_zeroMode]
      have hp := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) ht.le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hp])) (norm_nonneg _)
  have hsM := (domain_summable_norm_zeroModeCoeff R hF.1).mul_right (Real.exp (-(8*t)))
  have hnorm := hsM.of_nonneg_of_le (fun q => norm_nonneg (Sᶜ.indicator f q)) hb
  have hleft := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hb hnorm hsM)
  rw [tsum_mul_right] at hleft
  have htail : ‖archimedeanModes R F t‖ ≤ C*Real.exp (-(8*t)) :=
    (norm_archimedeanModes_le R F ht.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  have hi : (∑' q : XiZeroCopy, if 0 < (centredZero q).re then
      zeroModeCoeff R F q * cexp ((centredZero q-8)*t) else 0) = ∑' q, S.indicator f q := by
    apply tsum_congr
    intro q
    by_cases hq : 0 < (centredZero q).re <;> simp [S, f, hq, Set.indicator]
  rw [hi]
  rw [show (averagedState F t : ℂ) - ∑' q, S.indicator f q =
    (∑' q, Sᶜ.indicator f q) + archimedeanModes R F t by linear_combination -htotal]
  exact (norm_add_le _ _).trans ((add_le_add hleft htail).trans_eq (add_mul _ _ _).symm)

#print axioms domain_summable_zeroModeCoeff_sq_weight
#print axioms IsConfinedNullVector.hasSum_zeroModeTransform
#print axioms IsConfinedNullVector.averagedState_eq_modes
#print axioms IsConfinedNullVector.hasSum_averagedState
#print axioms IsConfinedNullVector.averagedState_sub_rightModes_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
