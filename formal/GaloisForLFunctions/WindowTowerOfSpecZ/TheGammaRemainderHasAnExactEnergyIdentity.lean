import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderPaysAUniformReserve

/-!
# The exact remainder of the retained Gamma comparison

Splitting the Gamma jump integral at the unit window retains its exact exterior
tail. The two odd lag identities identify the polynomial terms, leaving an
integrable nonnegative kernel remainder and the positive exterior reserve.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty LatticeSectionTheory SpacingScaleHarmonicAnalysis

/-- The part of the Gamma density beyond its retained polynomial lag terms. -/
def retainedGammaRemainderWeight (t : ℝ) : ℝ :=
  archLevySinhWeight t - 1 / t - 1 / 2 + t / 24 + t ^ 2 / 16

/-- The exact exterior Gamma reserve beyond the retained comparison. -/
def retainedGammaTailReserve : ℝ :=
  archLevyAntideriv 1 - Real.log 2 - Real.pi / 4 + 1 / 4 - 1 / 96

private theorem gamma_weight_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 ≤ archLevySinhWeight t := by
  refine le_of_mul_le_mul_left (a := t) ?_ ht
  have h := mul_archLevyDensity_ge_sharp ht ht1
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht]
  have he : t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) =
      2 * (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) := by
    field_simp [ht.ne']
    ring
  rw [he]
  linarith only [h]

theorem retainedGammaRemainderWeight_nonneg {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ retainedGammaRemainderWeight t := by
  unfold retainedGammaRemainderWeight
  linarith only [gamma_weight_lower ht.1 ht.2]

private theorem local_gamma_terms_integrable {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    IntegrableOn (fun t => (autocorr F 0 - autocorr F t) / t) (Ioc (0 : ℝ) 1) ∧
    IntegrableOn (fun t => retainedGammaRemainderWeight t *
      (autocorr F 0 - autocorr F t)) (Ioc (0 : ℝ) 1) := by
  let D := fun t => autocorr F 0 - autocorr F t
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi : IntegrableOn (fun t => D t * archLevySinhWeight t) (Ioi (0 : ℝ)) :=
    integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) 1) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hw := gamma_weight_lower ht.1 ht.2
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hwinv : 1 / t ≤ archLevySinhWeight t := by linarith only [hw, ht.2, ht2]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 1) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨hilog, ?_⟩
  apply (((((hi.mono_set hsub).sub hilog).sub (hiD.div_const 2)).add
    (hitD.div_const 24)).add (hit2D.div_const 16)).congr
  exact Eventually.of_forall fun t => by dsimp [retainedGammaRemainderWeight, D]; ring

/-- The discarded local Gamma term is integrable and nonnegative. -/
theorem retainedGammaRemainder_integrable_nonneg {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    IntegrableOn (fun t => retainedGammaRemainderWeight t *
      (autocorr F 0 - autocorr F t)) (Ioc (0 : ℝ) 1) ∧
    0 ≤ ∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t *
      (autocorr F 0 - autocorr F t) := by
  refine ⟨(local_gamma_terms_integrable hF hcs).2, ?_⟩
  apply setIntegral_nonneg measurableSet_Ioc
  intro t ht
  exact mul_nonneg (retainedGammaRemainderWeight_nonneg ht)
    (sub_nonneg.mpr ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t)))

private theorem gamma_position_remainder_identity {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F =
      (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * (∫ x, F x ^ 2) -
      (∫ t in Ioc (0 : ℝ) 1, t * (autocorr F 0 - autocorr F t)) / 24 -
      (∫ x, x * F x) ^ 2 / 16 +
      (∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) + 2 * retainedGammaTailReserve * (∫ x, F x ^ 2) := by
  let M := autocorr F 0
  let D := fun t => M - autocorr F t
  let W := fun t => D t * archLevySinhWeight t
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hi : IntegrableOn W (Ioi (0 : ℝ)) := integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hsubtail : Ioi (1 : ℝ) ⊆ Ioi 0 := fun t ht => lt_trans zero_lt_one ht
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) 1) :=
    (local_gamma_terms_integrable hF hcs).1
  have hiR : IntegrableOn (fun t => retainedGammaRemainderWeight t * D t) (Ioc (0 : ℝ) 1) :=
    (local_gamma_terms_integrable hF hcs).2
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 1) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hzero := odd_autocorr_integral_zero ⟨hF, hcs⟩ hs ho
  norm_num at hzero
  have hD : (∫ t in Ioc (0 : ℝ) 1, D t) = M := by
    change (∫ t in Ioc (0 : ℝ) 1, M - autocorr F t) = M
    rw [integral_sub (f := fun _ : ℝ => M) (g := autocorr F)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self), hzero, sub_zero, setIntegral_const]
    norm_num
  have hlocal : (∫ t in Ioc (0 : ℝ) 1, W t) =
      (∫ t in Ioc (0 : ℝ) 1, D t / t) + M / 2 -
      (∫ t in Ioc (0 : ℝ) 1, t * D t) / 24 -
      (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * D t) / 16 +
      ∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t * D t := by
    have he : W = fun t => D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16 +
        retainedGammaRemainderWeight t * D t := by
      funext t
      dsimp [W, retainedGammaRemainderWeight]
      ring
    rw [he, integral_add
      (f := fun t => D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16)
      (g := fun t => retainedGammaRemainderWeight t * D t)
      (((hilog.add (hiD.div_const 2)).sub (hitD.div_const 24)).sub (hit2D.div_const 16)) hiR,
      integral_sub (f := fun t => D t / t + D t / 2 - t * D t / 24)
        (g := fun t => t ^ 2 * D t / 16)
        ((hilog.add (hiD.div_const 2)).sub (hitD.div_const 24)) (hit2D.div_const 16),
      integral_sub (f := fun t => D t / t + D t / 2) (g := fun t => t * D t / 24)
        (hilog.add (hiD.div_const 2)) (hitD.div_const 24),
      integral_add (f := fun t => D t / t) (g := fun t => D t / 2) hilog (hiD.div_const 2),
      integral_div, integral_div, integral_div, hD]
  have htail : (∫ t in Ioi (1 : ℝ), W t) = 2 * archLevyAntideriv 1 * M := by
    have he : ∀ t ∈ Ioi (1 : ℝ), W t = 2 * archLevyDensity t * M := by
      intro t ht
      dsimp [W, D, M]
      rw [autocorr_eq_zero_of_support (x := t) hs (by norm_num; exact ht), sub_zero,
        archLevySinhWeight, exp_half_div_sinh_eq (lt_trans zero_lt_one ht)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)]
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, W t) +
      (∫ t in Ioi (1 : ℝ), W t) = biScaleLevyEnergy F := by
    rw [← setIntegral_union (s := Ioc (0 : ℝ) 1) (t := Ioi (1 : ℝ))
      (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi (hi.mono_set hsub) (hi.mono_set hsubtail),
      Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  rw [hlocal, htail] at hsplit
  have hGamma := congrArg (fun z : ℝ => z * M) neg_gammaBracket_zero_eq
  have hM2 := unit_odd_jump_second_moment hF hcs hs ho
  simp only [autocorr_zero_eq] at hM2
  dsimp [D, M] at hsplit hGamma
  simp only [autocorr_zero_eq] at hsplit hGamma ⊢
  unfold retainedGammaTailReserve
  nlinarith only [hsplit, hGamma, hM2]

/-- The full odd unit-window form equals the retained form plus its exact Gamma remainder. -/
theorem weilQuad_eq_retainedOddGamma_add_remainder {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    weilQuad F = retainedOddGammaLowerForm F +
      (∫ t in Ioc (0 : ℝ) 1, retainedGammaRemainderWeight t *
        ((∫ x, F x ^ 2) - autocorr F t)) +
      2 * retainedGammaTailReserve * (∫ x, F x ^ 2) := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht))
  have hN : ∀ n : ℕ, 2 < n → ∀ u, F u * F (u + Real.log n) = 0 := by
    intro n hn u
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hlog : 1 < Real.log n :=
      lt_of_lt_of_le (by linarith only [Real.log_three_gt_d9])
        (Real.log_le_log (by norm_num) hn3)
    by_cases hu : F u = 0
    · rw [hu, zero_mul]
    · have huI : u ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        by_contra hnot
        exact hu (image_eq_zero_of_notMem_tsupport fun h => hnot (hs h))
      have hz : F (u + Real.log n) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
        have hbound := (hs h).2
        linarith only [huI.1, hlog, hbound]
      rw [hz, mul_zero]
  have hfull := weil_eq_markovForm_add_pole hF hcs hN
  have hstep := markovForm_succ hF.continuous hcs (N := 1) le_rfl
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hstep
  have hbase : markovForm 1 F = EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
    norm_num [markovForm, creationPotential, primeJump]
    rw [levyJump_eq_biScale hF hcs]
  have hw : primeJumpWeight 2 = Real.log 2 / Real.sqrt 2 := by
    unfold primeJumpWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hgamma := gamma_position_remainder_identity hF hcs hs ho
  simp only [autocorr_zero_eq] at hgamma
  change markovForm 2 F = markovForm 1 F - 2 * primeJumpWeight 2 * autocorr F (Real.log 2) at hstep
  rw [hbase, hw] at hstep
  change weilQuad F = markovForm 2 F + coshPairing F ^ 2 / 2 - sinhPairing F ^ 2 / 2 at hfull
  rw [coshPairing_eq_zero_of_odd ho] at hfull
  unfold retainedOddGammaLowerForm
  nlinarith only [hgamma, hstep, hfull]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainder_integrable_nonneg
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_eq_retainedOddGamma_add_remainder
