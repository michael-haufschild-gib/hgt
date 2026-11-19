import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedFractionalPartAverageOnTheCriticalState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeNumberTheoremOnTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ExponentiallyIntegrableChangeOfPrimeVariance
import GaloisForLFunctions.RHTower.ZetaGateProductAFEMainTermInputs
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero

/-!
# The signed ordinary-prime response at every late time

The positive fractional-part test suppresses the centered Mangoldt wave.
Its fixed mass measures the surviving square contribution when only ordinary
primes are retained. The limiting sign is opposite to that of the state integral.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The positive fractional-part kernel has total mass given by the central zeta value. -/
theorem fractionalPrimeTest_mass : Integrable fractionalPrimeTest ∧
    (∫ v, fractionalPrimeTest v)= -2*(riemannZeta (1/2)).re := by
  let f := weightedFloorDiscrepancy (1/2)
  have he : fractionalPrimeTest=fun v => -f v := by
    funext v
    change Real.exp (-v/2)*Int.fract (Real.exp v) =
      -(-Real.exp (-(1/2)*v)*Int.fract (Real.exp v))
    rw [show -(1/2:ℝ)*v= -v/2 by ring,neg_mul,neg_neg]
  rw [he,integral_neg]
  refine ⟨(integrable_weightedFloorDiscrepancy (by norm_num : (0:ℝ)<1/2) (by norm_num)).neg,?_⟩
  have hF := fourier_weightedFloorDiscrepancy (σ := 1/2) (by norm_num) (by norm_num) 0
  have hfreq : (∫ v, (f v:ℂ))=2*riemannZeta (1/2) := by
    simpa [f,Real.fourier_real_eq_integral_exp_smul,div_eq_mul_inv,mul_comm] using hF
  rw [integral_complex_ofReal] at hfreq
  have hr : (∫ v, f v)=2*(riemannZeta (1/2)).re := by simpa using congrArg Complex.re hfreq
  rw [hr]; ring

private abbrev properRow (Φ : ℝ → ℝ) (t : ℝ) :=
  ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j))

private theorem bounded_proper_row {Φ : ℝ → ℝ} {C L : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (hL : Tendsto (properRow Φ) atTop (𝓝 L)) : ∃ B : ℝ, ∀ t, |properRow Φ t| ≤ B := by
  obtain ⟨M,hM,habs⟩ := properPowerWave_absolute_envelope (by norm_num : (0:ℝ)<2) hC hb
  obtain ⟨U,hU⟩ := eventually_atTop.1 (hL.abs.eventually_lt_const (lt_add_one |L|))
  refine ⟨max (|L|+1) (M*Real.exp (2*U)),fun t => ?_⟩
  rcases le_or_gt U t with ht | ht
  · exact (hU t ht).le.trans (le_max_left ..)
  have hn (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    split_ifs <;> first | exact le_rfl | exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hp : |properRow Φ t| ≤ ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*|Φ (t-Real.log (properPrimePowerIndex j))| := by
    have hi : Summable (fun j => ‖vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j))‖) := by
      simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn _)] using (habs t).1
    simpa only [properRow,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn _)] using norm_tsum_le_tsum_norm hi
  exact hp.trans ((habs t).2.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by linarith only [ht])) hM).trans (le_max_right ..)))

private theorem fractional_convolution_limit {Q : ℝ → ℝ} (hm : Measurable Q) {B L : ℝ}
    (hb : ∀ t, |Q t| ≤ B) (hL : Tendsto Q atTop (𝓝 L)) :
    (∀ T : ℝ, Integrable (fun t => Q t*fractionalPrimeTest (T-t))) ∧
      Tendsto (fun T : ℝ => ∫ t, Q t*fractionalPrimeTest (T-t)) atTop (𝓝 (L*∫ v, fractionalPrimeTest v)) := by
  let K := fractionalPrimeTest
  have hiK : Integrable K := fractionalPrimeTest_mass.1
  have hmK : Measurable K := measurable_fractionalPrimeTest
  have hiB := hiK.abs.const_mul B
  have hmQ (T : ℝ) : Measurable (fun v : ℝ => Q (T-v)*K v) := (hm.comp (by fun_prop)).mul hmK
  have hbound (T v : ℝ) : ‖Q (T-v)*K v‖ ≤ B*|K v| := by
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
  have hi (T : ℝ) : Integrable (fun v : ℝ => Q (T-v)*K v) :=
    hiB.mono' (hmQ T).aestronglyMeasurable (Eventually.of_forall (hbound T))
  constructor
  · intro T
    simpa only [sub_sub_cancel,K] using (hi T).comp_sub_left T
  · have hpt (v : ℝ) : Tendsto (fun T : ℝ => Q (T-v)*K v) atTop (𝓝 (L*K v)) := by
      simpa only [Function.comp_apply,id_eq,sub_eq_add_neg] using
        (hL.comp (tendsto_atTop_add_const_right _ (-v) tendsto_id)).mul_const (K v)
    have h := tendsto_integral_filter_of_dominated_convergence (fun v : ℝ => B*|K v|)
      (Eventually.of_forall fun T => (hmQ T).aestronglyMeasurable)
      (Eventually.of_forall fun T => Eventually.of_forall (hbound T)) hiB
      (Eventually.of_forall hpt)
    rw [integral_const_mul] at h
    refine h.congr fun T => ?_
    change (∫ v : ℝ, Q (T-v)*K v) = _
    simpa only [sub_sub_cancel,K] using
      (integral_sub_left_eq_self (fun t : ℝ => Q t*K (T-t)) volume T)

private theorem tendsto_stirling_response {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) : Tendsto (stirlingTestResponse Φ) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => Real.exp ((-1/4)*T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
  have h0 := h.const_mul (5*C)
  rw [mul_zero] at h0
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  have hbase : 1+T ≤ 5*Real.exp (T/4) := by
    linarith only [Real.add_one_le_exp (T/4),Real.one_le_exp (div_nonneg hT (by norm_num : (0:ℝ) ≤ 4))]
  apply (abs_stirlingTestResponse_le hC hb hT).trans
  calc C*(1+T)*Real.exp (-T/2) ≤ C*(5*Real.exp (T/4))*Real.exp (-T/2) :=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hC) (Real.exp_pos _).le
    _ = (5*C)*(Real.exp (T/4)*Real.exp (-T/2)) := by ring
    _ = _ := by rw [← Real.exp_add,show T/4 + -T/2 = (-1/4)*T by ring]

/-- On the state forced by failure of RH the positive fractional-part test of
the ordinary-prime polar error tends to zeta at one half times the integral
of the state. The product with that integral is eventually strictly negative. -/
theorem riemannHypothesis_or_ordinary_fractional_response : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      let m := ∫ u, Φ u
      let f := fun T t : ℝ => ordinaryPrimePolarError Φ t*fractionalPrimeTest (T-t)
      (∀ T : ℝ, 0 ≤ T → Integrable (f T)) ∧
      Tendsto (fun T : ℝ => ∫ t, f T t) atTop (𝓝 ((riemannZeta (1/2)).re*m)) ∧
      ∀ᶠ T : ℝ in atTop, (∫ t, f T t)*m < 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨Φ,hΦ,he,h⟩ := criticalState_tendsto_dominated_properPowerWave hW ht hF
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ u, Φ u
  let K := fractionalPrimeTest
  let W := logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ
  let A := ∫ u in Iic (0:ℝ), Φ u*Real.exp (-u/2)
  let f := fun T t : ℝ => ordinaryPrimePolarError Φ t*K (T-t)
  have hQ : Tendsto (properRow Φ) atTop (𝓝 (m/2)) := h Φ hΦ (fun _ => le_rfl)
  obtain ⟨B,hB⟩ := bounded_proper_row hC hb hQ
  have hmQ : Measurable (properRow Φ) := Measurable.tsum fun _ => measurable_const.mul (hΦ.measurable.comp (by fun_prop))
  have hconv := fractional_convolution_limit hmQ hB hQ
  have hA : A=∫ u, Real.exp (-u/2)*Φ u := by
    rw [show A=∫ u, Φ u*Real.exp (-u/2) from setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Iic (0:ℝ)) (fun u hu => by rw [hs u (lt_of_not_ge hu).le,zero_mul])]
    exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
  have hsplit (t : ℝ) : W t=(ordinaryPrimeWave Φ t).re+properRow Φ t := by
    calc W t = ∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t := by
                 apply tsum_congr fun n => ?_
                 simp only [continuousIntegerAtom,div_eq_mul_inv,mul_assoc]
      _ = _ := mangoldt_atom_sum_split hb t
  have hpair (T : ℝ) (hT : 0 ≤ T) : Integrable (f T) ∧
      (∫ t, f T t)=stirlingTestResponse Φ T-∫ t, properRow Φ t*K (T-t) := by
    have hfull := criticalState_fractional_mangoldt_response hW ht hF hΦ he hs hC hb hT
    let g := fun t : ℝ => (W t-Real.exp (t/2)*A)*K (T-t)
    have hI : Integrable g := hfull.1
    have heq (t : ℝ) : f T t=g t-properRow Φ t*K (T-t) := by
      dsimp only [f,ordinaryPrimePolarError,g]
      rw [hA,hsplit]; ring
    have hefun := funext heq
    rw [hefun,integral_sub hI (hconv.1 T)]
    exact ⟨hI.sub (hconv.1 T),congrArg (· - ∫ t, properRow Φ t*K (T-t)) hfull.2.1⟩
  have hc : 0-(m/2)*(∫ v, K v)=(riemannZeta (1/2)).re*m := by
    rw [show (∫ v, K v)=_ from fractionalPrimeTest_mass.2]; ring
  have hlim := (tendsto_stirling_response hC hb).sub hconv.2
  rw [hc] at hlim
  have hread : Tendsto (fun T : ℝ => ∫ t, f T t) atTop (𝓝 ((riemannZeta (1/2)).re*m)) :=
    hlim.congr' ((eventually_ge_atTop (0:ℝ)).mono fun T hT => (hpair T hT).2.symm)
  have hm : m≠0 := by
    intro hm
    apply criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
      (by norm_num : 0 ≤ (0:ℂ).re)
    have he0 := negativeHalfLineLaplace_ofReal 0 F
    simpa only [Complex.ofReal_zero,zero_mul,Real.exp_zero,mul_one,integral_congr_ae he,
      show (∫ u, Φ u)=0 from hm] using he0
  have hzeta : (riemannZeta (1/2)).re < 0 := by
    simpa using _root_.RHTower.re_riemannZeta_ofReal_neg (σ := 1/2) (by norm_num) (by norm_num)
  have hneg : (riemannZeta (1/2)).re*m*m<0 := by
    rw [mul_assoc]
    exact mul_neg_of_neg_of_pos hzeta (mul_self_pos.mpr hm)
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun _ hT => (hpair _ hT).1,hread,
    (hread.mul_const m).eventually_lt_const hneg⟩

#print axioms riemannHypothesis_or_ordinary_fractional_response
end GaloisForLFunctions.ExclusionOfTheCriticalState
