import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.TheLeftTraceUpToTheRateOfTheZeros
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Signed fractional-part averages of the actual critical state

The right-hand tail of the test is controlled by the damped prime wave.
Consequently the natural cutoff limit is the absolutely convergent
two-sided integral. Its factorial remainder decays at every late center.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

private abbrev mangoldtRow (Φ : ℝ → ℝ) :=
  logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ

private abbrev densityCharge (Φ : ℝ → ℝ) :=
  ∫ u in Iic (0:ℝ), Φ u*Real.exp (-u/2)

private theorem measurable_mangoldtRow {Φ : ℝ → ℝ} (hm : Measurable Φ) :
    Measurable (mangoldtRow Φ) := Measurable.tsum fun _ => measurable_const.mul (hm.comp (by fun_prop))

private theorem measurable_fractional_test : Measurable fractionalPrimeTest :=
  (by fun_prop : Measurable fun v : ℝ => Real.exp (-v/2)).mul (measurable_fract.comp Real.measurable_exp)

private theorem fractional_test_bounds (v : ℝ) :
    |fractionalPrimeTest v| ≤ 1 ∧ |fractionalPrimeTest v| ≤ Real.exp (v/2) := by
  have heq : fractionalPrimeTest v = -weightedFloorDiscrepancy (1/2) v := by
    rw [fractionalPrimeTest,weightedFloorDiscrepancy,neg_mul,neg_neg,show -(1/2:ℝ)*v = -v/2 by ring]
  rw [heq,abs_neg]
  exact ⟨abs_weightedFloorDiscrepancy_le_one (by norm_num) (by norm_num) v,
    (abs_weightedFloorDiscrepancy_le (1/2) v).2.trans_eq (by congr 1; ring)⟩

private theorem integrable_polar_test (M T : ℝ) :
    IntegrableOn (fun t => Real.exp (t/2)*fractionalPrimeTest (T-t)) (Iic M) := by
  have h := integrableOn_exp_mul_Iic (by norm_num : (0:ℝ) < 1/2) M
  apply h.mono' (((by fun_prop : Measurable fun t : ℝ => Real.exp (t/2)).mul
    (measurable_fractional_test.comp (by fun_prop))).aestronglyMeasurable.restrict)
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),show (1/2:ℝ)*t=t/2 by ring]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (fractional_test_bounds _).1

private theorem weighted_mangoldt_error_integrable {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hm : Measurable Φ) (he : F =ᵐ[volume] Φ) (hs : ∀ u, 0 ≤ u → Φ u=0) :
    IntegrableOn (fun t => Real.exp (-t/2)*|mangoldtRow Φ t-Real.exp (t/2)*densityCharge Φ|)
      (Ioi 0) := by
  let d := (7/16:ℝ)
  have hd : zetaZeroAbscissa-1/2 < d := by
    dsimp only [d]; linarith only [ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths]
  have hZ := memLp_damped_prime_sum_sub_pole_of_abscissa hW ht hF hd
  let c := (1/2:ℝ)-d
  have hc : 0 < ((c:ℝ):ℂ).re := by norm_num [c,d]
  have hp := (memLp_two_expRay_restrict hc 0).mul' (r := 1) hZ
  have hh := (memLp_one_iff_integrable.mp hp).norm
  have hhalf : ((-(1/2):ℝ):ℂ)= -(1/2) := by norm_num
  have hA : negativeHalfLineLaplace (cx F) (-(1/2)) = (densityCharge Φ:ℂ) := by
    rw [← hhalf,negativeHalfLineLaplace_ofReal]
    apply congrArg Complex.ofReal
    rw [densityCharge,setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic (0:ℝ))
      (f := fun u : ℝ => Φ u*Real.exp (-u/2)) (fun u hu => by
      rw [hs u (lt_of_not_ge hu).le,zero_mul])]
    apply integral_congr_ae
    filter_upwards [he] with u hu
    rw [hu,show -(1/2:ℝ)*u = -u/2 by ring]
  have hshift : ∀ᵐ t ∂volume, ∀ n : ℕ, F (t-Real.log n)=Φ (t-Real.log n) :=
    ae_all_iff.2 fun n => (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae_eq_comp he
  apply hh.congr
  filter_upwards [ae_restrict_of_ae hshift] with t ht'
  have hrow : (∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)) = (mangoldtRow Φ t:ℂ) := by
    rw [mangoldtRow,logShiftWave,Complex.ofReal_tsum]
    apply tsum_congr fun n => ?_
    have hcoef : primeAtom n = vonMangoldt n/Real.sqrt n := by
      by_cases hn : 2 ≤ n
      · exact if_pos hn
      · rcases (show n=0 ∨ n=1 by omega) with rfl | rfl <;> simp [primeAtom]
    rw [hcoef,ht' n,Complex.ofReal_mul]
  change ‖(expRay (d:ℂ) t*((∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ))-
    negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ)))*expRay (c:ℂ) t‖=_
  rw [hrow,hA,← Complex.ofReal_mul,← Complex.ofReal_sub,norm_mul,norm_mul,
    norm_expRay,norm_expRay,Complex.ofReal_re,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs]
  rw [mul_comm (densityCharge Φ),mul_right_comm,← Real.exp_add]
  dsimp only [c,d]; congr 2 <;> ring

/-- The ordinary integral of the centered Mangoldt wave against the
positive fractional-part kernel is the Stirling response at every late center. -/
theorem criticalState_fractional_mangoldt_response {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hΦ : Continuous Φ) (he : F =ᵐ[volume] Φ) (hs : ∀ u, 0 ≤ u → Φ u=0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {T : ℝ} (hT : 0 ≤ T) :
    let A := ∫ u in Iic (0:ℝ), Φ u*Real.exp (-u/2)
    let W := logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ
    let g := fun t : ℝ => (W t-Real.exp (t/2)*A)*fractionalPrimeTest (T-t)
    Integrable g ∧ (∫ t, g t) = stirlingTestResponse Φ T ∧
      |∫ t, g t| ≤ C*(1+T)*Real.exp (-T/2) := by
  let W := mangoldtRow Φ
  let A := densityCharge Φ
  let g := fun t : ℝ => (W t-Real.exp (t/2)*A)*fractionalPrimeTest (T-t)
  let p := fun t : ℝ => W t*fractionalPrimeTest (T-t)
  let q := fun t : ℝ => Real.exp (t/2)*fractionalPrimeTest (T-t)
  have hg : g = fun t => p t-A*q t := by funext t; dsimp [g,p,q]; ring
  have hip (M : ℝ) : IntegrableOn p (Iic M) := (integral_mangoldt_fractional_cut hΦ.measurable hC hb M T).1
  have hiq (M : ℝ) : IntegrableOn q (Iic M) := integrable_polar_test M T
  have hneg : IntegrableOn g (Iic 0) := by rw [hg]; exact (hip 0).sub ((hiq 0).const_mul A)
  have hi := weighted_mangoldt_error_integrable hW ht hF hΦ.measurable he hs
  have hmW := measurable_mangoldtRow hΦ.measurable
  have hpos : IntegrableOn g (Ioi 0) := by
    apply (hi.const_mul (Real.exp (T/2))).mono' (((hmW.sub ((by fun_prop : Measurable fun t : ℝ => Real.exp (t/2)).mul measurable_const)).mul
      (measurable_fractional_test.comp (by fun_prop))).aestronglyMeasurable.restrict)
    refine Eventually.of_forall fun t => ?_
    rw [g,Real.norm_eq_abs,abs_mul]
    calc _ ≤ |W t-Real.exp (t/2)*A|*Real.exp ((T-t)/2) :=
           mul_le_mul_of_nonneg_left (fractional_test_bounds _).2 (abs_nonneg _)
      _ = _ := by rw [show (T-t)/2=T/2+(-t/2) by ring,Real.exp_add]; ring
  have hint : Integrable g := by simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hpos
  have hlim := (aecover_Iic (μ := volume) (tendsto_id (α := ℝ) (x := atTop))).integral_tendsto_of_countably_generated hint
  have hR := tendsto_mangoldt_fractional_response hΦ.measurable hs hC hb hT
  have hval : (∫ t, g t)=stirlingTestResponse Φ T := tendsto_nhds_unique hlim
    (hR.congr' (Eventually.of_forall fun M => by
      change (∫ t in Iic M, p t) - A*(∫ t in Iic M, q t) = ∫ t in Iic M, g t
      rw [hg,integral_sub (hip M) ((hiq M).const_mul A),integral_const_mul]))
  refine ⟨hint,hval,?_⟩
  change |∫ t, g t| ≤ _
  rw [hval]; exact abs_stirlingTestResponse_le hC hb hT

/-- An off-line zero forces a single state for which the absolutely
convergent signed average decays at every nonnegative observation time. -/
theorem riemannHypothesis_or_fractional_mangoldt_bound : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (C : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ C ∧
      ∀ T : ℝ, 0 ≤ T →
        let A := ∫ u in Iic (0:ℝ), Φ u*Real.exp (-u/2)
        let W := logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ
        let g := fun t : ℝ => (W t-Real.exp (t/2)*A)*fractionalPrimeTest (T-t)
        Integrable g ∧ (∫ t, g t)=stirlingTestResponse Φ T ∧
          |∫ t, g t| ≤ C*(1+T)*Real.exp (-T/2) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,C,hW,ht,hF,hΦ,he,hC,fun _ hT =>
    criticalState_fractional_mangoldt_response hW ht hF hΦ he hs hC hb hT⟩

#print axioms riemannHypothesis_or_fractional_mangoldt_bound
#print axioms criticalState_fractional_mangoldt_response
end GaloisForLFunctions.ExclusionOfTheCriticalState
