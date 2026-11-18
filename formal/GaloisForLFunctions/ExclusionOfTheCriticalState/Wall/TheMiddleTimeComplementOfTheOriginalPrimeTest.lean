import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateIsUniqueUpToSign
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheAbsoluteFirstWindowInTheOriginalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheEarlyMassOfTheSignedFractionalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegratedErrorInThePrimeSquareLayer

/-!
# The signed middle complement of the original fractional test

The two exterior time intervals have small absolute mass. On the middle
interval, the proper-power transfer restores the literal square charge.
The first-window estimate then removes the signed near row in absolute
integral, uniformly on all measurable selections of the same times.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The original ordinary-prime test can be replaced, on every measurable
mask, by the literal centered row on (T/6,6T]. The absolute error retains
the constant square charge and is uniform in the mask. -/
theorem riemannHypothesis_or_middle_time_signed_test : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧
      ∀ᶠ T : ℝ in atTop, ∀ D : Set ℝ, MeasurableSet D →
        let m := ∫ u, Φ u
        let S := fun t : ℝ => (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
        let f := fun t : ℝ => |m*ordinaryPrimePolarError Φ t-
          (Ioc (T/6) (6*T)).indicator (fun t => m*S t) t| *fractionalPrimeTest (T-t)
        IntegrableOn f D ∧ (∫ t in D, f t) ≤ B*Real.exp (-T/240) := by
  rcases riemannHypothesis_or_integer_mangoldt_sign_transfer with hr | ⟨W₀,F,Φ,D₀,hW,ht,hF,hΦ,he,hD₀,htail⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨B₀,hB₀,hearly⟩ := early_signed_fractional_mass_of_confinement hΦ hC hb
  obtain ⟨B₁,hB₁,hlate⟩ := criticalState_late_absolute_ordinary_test hW ht hF hΦ he
  let m := ∫ u, Φ u
  let S := fun t : ℝ => (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
  let P := ordinaryPrimePolarError Φ
  let E := fun t => |P t-S t|
  have hS : Measurable S := (Measurable.tsum (fun n : ℕ => measurable_const.mul
    (measurable_const.mul (hΦ.measurable.comp (by fun_prop))))).sub measurable_const
  have hWm : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hΦ.measurable.comp (by fun_prop)))
  have hP : Measurable P := (Complex.continuous_re.measurable.comp hWm).sub (by fun_prop)
  have htransfer : ∀ᶠ V : ℝ in atTop, IntegrableOn E (Ioi (V+1)) ∧
      (∫ t in Ioi (V+1), E t) ≤ D₀*Real.exp ((-1/40)*V) := by
    filter_upwards [htail] with V hV
    simpa only [m,S,P,E,sign_part_distances_eq_abs_sub] using hV
  have hcut : Tendsto (fun T : ℝ => T/6-1) atTop atTop := tendsto_atTop.2 fun a =>
    eventually_atTop.2 ⟨6*(a+1),fun _ h => by linarith only [h]⟩
  let B := |m| *B₀ + |m| *D₀*Real.exp (1/40) + B₁
  refine Or.inr ⟨W₀,F,Φ,B,hW,ht,hF,hΦ,he,by dsimp only [B]; positivity,?_⟩
  filter_upwards [hcut.eventually htransfer,eventually_ge_atTop (0:ℝ)] with T hx hT
  rw [sub_add_cancel] at hx
  let U := T/6
  let V := 6*T
  let I := Ioc U V
  let K := fun t => fractionalPrimeTest (T-t)
  let f := fun t => |m*P t-I.indicator (fun z => m*S z) t| *K t
  have hUV : U ≤ V := by dsimp only [U,V]; linarith only [hT]
  have hK : Measurable K := measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id)
  have hf : Measurable f := ((measurable_const.mul hP).sub
    ((measurable_const.mul hS).indicator measurableSet_Ioc)).abs.mul hK
  have hK0 (t : ℝ) : 0 ≤ K t := mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
  have hf0 (t : ℝ) : 0 ≤ f t := mul_nonneg (abs_nonneg _) (hK0 t)
  have restrict_le {J : Set ℝ} (hJ : MeasurableSet J) {g : ℝ → ℝ}
      (hg : IntegrableOn g J) (hle : ∀ t ∈ J, f t ≤ g t) :
      IntegrableOn f J ∧ (∫ t in J, f t) ≤ ∫ t in J, g t := by
    have hi : IntegrableOn f J := hg.mono' hf.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem (μ := volume) hJ] with t htj
      simpa only [Real.norm_of_nonneg (hf0 t)] using hle t htj)
    exact ⟨hi,setIntegral_mono_on hi hg hJ hle⟩
  have hE0 := hearly U (by dsimp only [U]; positivity) T
  have hfront := restrict_le measurableSet_Iic (hE0.1.const_mul |m|) (fun t htj => by
    have hnot : t ∉ I := fun h => (not_lt_of_ge htj) h.1
    change |m*P t-I.indicator (fun z => m*S z) t| *K t ≤ |m| *((|S t|+|P t|)*K t)
    rw [indicator_of_notMem hnot,sub_zero,abs_mul,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg m)) (hK0 t))
  have hEweighted : IntegrableOn (fun t => |m| *E t) (Ioi U) := hx.1.const_mul |m|
  have hinter := restrict_le measurableSet_Ioc (hEweighted.mono_set
    (show I ⊆ Ioi U from fun _ h => h.1)) (fun t htj => by
    change |m*P t-I.indicator (fun z => m*S z) t| *K t ≤ |m| *E t
    rw [indicator_of_mem htj,← mul_sub,abs_mul]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg m) (abs_nonneg _))
      ((le_abs_self (K t)).trans (fractionalPrimeTest_bounds _).1))
  have hend := hlate T univ hT MeasurableSet.univ
  simp only [univ_inter] at hend
  have hrowEnd := restrict_le measurableSet_Ioi hend.1 (fun t htj => by
    have hnot : t ∉ I := fun h => (not_le_of_gt htj) h.2
    change |m*P t-I.indicator (fun z => m*S z) t| *K t ≤ |m*P t| *K t
    rw [indicator_of_notMem hnot,sub_zero])
  have hfrontCost : (∫ t in Iic U, f t) ≤ |m| *B₀*Real.exp (-T/12) := by
    apply hfront.2.trans
    rw [integral_const_mul,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [U,show (5*(T/6)-T)/2 = -T/12 by ring] using hE0.2
  have hmidE : (∫ t in I, E t) ≤ ∫ t in Ioi U, E t := setIntegral_mono_set hx.1
    (Eventually.of_forall fun _ => abs_nonneg _) (ae_of_all _ fun _ h => h.1)
  have hmidCost : (∫ t in I, f t) ≤ (|m| *D₀*Real.exp (1/40))*Real.exp (-T/240) := by
    apply hinter.2.trans
    rw [integral_const_mul,show (-T/240:ℝ) = -(T/240) by ring]
    apply (mul_le_mul_of_nonneg_left (hmidE.trans hx.2) (abs_nonneg _)).trans_eq
    rw [show (-1/40:ℝ)*(T/6-1) = 1/40 + -(T/240) by ring,Real.exp_add]; ring
  have hleft : IntegrableOn f (Iic V) := by
    rw [← Iic_union_Ioc_eq_Iic hUV]; exact hfront.1.union hinter.1
  have hall : Integrable f := by
    rw [← integrableOn_univ,← union_compl_self (Iic V),compl_Iic]
    exact hleft.union hrowEnd.1
  have htotal : (∫ t, f t) ≤ B*Real.exp (-T/240) := by
    rw [← integral_add_compl (measurableSet_Iic (a := V)) hall,compl_Iic,
      ← Iic_union_Ioc_eq_Iic hUV,setIntegral_union (Iic_disjoint_Ioc le_rfl)
        measurableSet_Ioc hfront.1 hinter.1]
    have hlo := Real.exp_le_exp.mpr (by linarith only [hT] : -T/12 ≤ -T/240)
    have hhi := Real.exp_le_exp.mpr (by linarith only [hT] : -T/10 ≤ -T/240)
    have low := hfrontCost.trans (mul_le_mul_of_nonneg_left hlo (mul_nonneg (abs_nonneg _) hB₀))
    have high := (hrowEnd.2.trans hend.2).trans (mul_le_mul_of_nonneg_left hhi hB₁)
    change (∫ t in Iic U, f t)+(∫ t in I, f t)+(∫ t in Ioi V, f t) ≤ _
    dsimp only [B]
    linarith only [low,hmidCost,high]
  intro D _
  exact ⟨hall.integrableOn,(setIntegral_le_integral hall (Eventually.of_forall hf0)).trans htotal⟩

#print axioms riemannHypothesis_or_middle_time_signed_test

/-- The two critical representatives give the same oriented first reading.
Normalization fixes the state up to sign, and both the charge and the atom
change sign together. -/
private theorem same_critical_state_window {W V : ℝ} {F G Φ Ψ : ℝ → ℝ}
    (hW : 0 < W) (hTW : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W : EReal))
    (hTV : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (V : EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hG : IsCriticalHalfLineGroundState V G)
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ) (he : F =ᵐ[volume] Φ) (he' : G =ᵐ[volume] Ψ) :
    criticalWidthSignedReading Φ = criticalWidthSignedReading Ψ := by
  have hWV : W = V := EReal.coe_injective (hTW.symm.trans hTV)
  subst V
  rcases criticalHalfLineGroundState_unique_up_to_sign hW hTW hF hG with h | h
  · exact congrArg criticalWidthSignedReading ((Continuous.ae_eq_iff_eq volume hΦ hΨ).mp
      (he.symm.trans (h.trans he')))
  have heq : Φ = fun u => -Ψ u := (Continuous.ae_eq_iff_eq volume hΦ hΨ.neg).mp (by
    filter_upwards [he,he',h] with u h₁ h₂ h₃
    change F u = -G u at h₃
    rwa [h₁,h₂] at h₃)
  rw [heq]
  funext t
  simp only [criticalWidthSignedReading,continuousIntegerAtom,integral_neg,mul_neg,neg_mul,neg_neg]

/-- The part outside the first window consists exactly of integers past its
far edge. Every index below the near endpoint gives a zero state atom. -/
private theorem outside_window_eq_far_integer_tail {Φ : ℝ → ℝ}
    (hs : ∀ v, 0 ≤ v → Φ v = 0) (t : ℝ) :
    let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
    (∑' n : {j : ℕ // j ∉ wallIntegerWindow t (criticalWallWidth t)}, v n) =
      ∑' n : {j : ℕ // Real.exp t+criticalWallWidth t < j}, v n := by
  classical
  let x := Real.exp t
  let H := criticalWallWidth t
  let J := wallIntegerWindow t H
  let A : Set ℕ := {n | n ∉ J}
  let B : Set ℕ := {n | x+H < n}
  let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
  have hx : 0 < x := Real.exp_pos _
  have hxH : 0 ≤ x+H := add_nonneg hx.le (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  change (∑' n : A, v n) = ∑' n : B, v n
  rw [tsum_subtype A v,tsum_subtype B v]
  apply tsum_congr
  intro n
  by_cases hB : n ∈ B
  · have hA : n ∈ A := fun hn => (not_lt_of_ge
        ((Nat.le_floor_iff hxH).mp (Finset.mem_Ioc.mp hn).2)) hB
    rw [indicator_of_mem hA,indicator_of_mem hB]
  rw [indicator_of_notMem hB]
  by_cases hA : n ∈ A
  · rw [indicator_of_mem hA]
    have hnx : (n:ℝ) ≤ x := le_of_not_gt fun h => hA (Finset.mem_Ioc.mpr
      ⟨(Nat.floor_lt hx.le).mpr h,(Nat.le_floor_iff hxH).mpr (le_of_not_gt hB)⟩)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [v,continuousIntegerAtom]
    have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp (by exact_mod_cast hn : 0 < (n:ℝ))).mpr hnx
    simp only [v,continuousIntegerAtom,hs _ (sub_nonneg.mpr hlog),mul_zero]
  · rw [indicator_of_notMem hA]

/-- On every measurable time set the original ordinary-prime test differs
in absolute integral by o(1) from the signed integer complement confined to
(T/6,6T]. The square charge belongs to that same complement. -/
theorem riemannHypothesis_or_original_test_on_middle_complement : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ D : Set ℝ, MeasurableSet D →
        let m := ∫ u, Φ u
        let C := fun t : ℝ => m*((∑' n : {j : ℕ // Real.exp t+criticalWallWidth t < j},
          (ArithmeticFunction.vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t)-m/2)
        let f := fun t => |m*ordinaryPrimePolarError Φ t-(Ioc (T/6) (6*T)).indicator C t| *
          fractionalPrimeTest (T-t)
        IntegrableOn f D ∧ (∫ t in D, f t) < ε := by
  rcases riemannHypothesis_or_middle_time_signed_test with hr | ⟨W₀,F,Φ,B,hW,hTW,hF,hΦ,he,hB,hcore⟩
  · exact Or.inl hr
  rcases riemannHypothesis_or_first_window_absolute_test_vanishes with hr | ⟨V,G,Ψ,_,hTV,hG,hΨ,he',hwin⟩
  · exact Or.inl hr
  have hsame := same_critical_state_window hW hTW hTV hF hG hΦ hΨ he he'
  rw [← hsame] at hwin
  obtain ⟨_,_,Φ',hc',he'',hs,⟨C₀,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW hTW hF
  have hΦ' : Φ'=Φ := (Continuous.ae_eq_iff_eq volume hc' hΦ).mp (he''.symm.trans he)
  subst Φ'
  let m := ∫ u, Φ u
  let P := fun t => m*ordinaryPrimePolarError Φ t
  let S := fun t : ℝ => m*((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2)
  let W := criticalWidthSignedReading Φ
  let C := fun t => S t-W t
  have hS : Measurable S := measurable_const.mul ((Measurable.tsum (fun n : ℕ => measurable_const.mul
    (measurable_const.mul (hΦ.measurable.comp (by fun_prop))))).sub measurable_const)
  have hWm : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hΦ.measurable.comp (by fun_prop)))
  have hP : Measurable P := measurable_const.mul ((Complex.continuous_re.measurable.comp hWm).sub (by fun_prop))
  have hC : Measurable C := hS.sub (measurable_criticalWidthSignedReading hΦ)
  have hid (t : ℝ) : C t = m*((∑' n : {j : ℕ // Real.exp t+criticalWallWidth t < j},
      (ArithmeticFunction.vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t)-m/2) := by
    have h := centered_mangoldt_eq_criticalWidthReading_add_complement hb t
    change S t = W t + m*((∑' n : {j : ℕ // j ∉ wallIntegerWindow t (criticalWallWidth t)},
      (ArithmeticFunction.vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t)-m/2) at h
    rw [outside_window_eq_far_integer_tail hs t] at h
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm ..))
  have hrate : Tendsto (fun T : ℝ => B*Real.exp (-T/240)) atTop (𝓝 0) := by
    have hneg : Tendsto (fun T : ℝ => -T/240) atTop atBot :=
      tendsto_atBot.2 fun a => eventually_atTop.2 ⟨-240*a,fun _ h => by linarith only [h]⟩
    simpa only [Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul B
  refine Or.inr ⟨W₀,F,Φ,hW,hTW,hF,hΦ,he,fun ε hε => ?_⟩
  filter_upwards [hcore,hwin (ε/2) (half_pos hε),hrate.eventually_lt_const (half_pos hε)] with T hT hW0 hsmall
  intro D hD
  let I := Ioc (T/6) (6*T)
  let K := fun t => fractionalPrimeTest (T-t)
  let f := fun t => |P t-I.indicator C t| *K t
  let p := fun t => |P t-I.indicator S t| *K t
  let w := fun t => |W t| *K t
  have hcD : IntegrableOn p D ∧ (∫ t in D, p t) ≤ B*Real.exp (-T/240) := hT D hD
  have hwD : IntegrableOn w D ∧ (∫ t in D, w t) < ε/2 := hW0 D hD
  have hm : Measurable f := (hP.sub (hC.indicator measurableSet_Ioc)).abs.mul
    (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))
  have hK (t : ℝ) : 0 ≤ K t := mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
  have hle (t : ℝ) : f t ≤ p t+w t := by
    dsimp only [f,p,w]
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (hK _)
    by_cases h : t ∈ I
    · rw [indicator_of_mem h,indicator_of_mem h,show P t-C t=(P t-S t)+W t by dsimp only [C]; ring]
      exact abs_add_le ..
    · rw [indicator_of_notMem h,indicator_of_notMem h]
      exact le_add_of_nonneg_right (abs_nonneg _)
  have hsum : IntegrableOn (fun t => p t+w t) D := hcD.1.add hwD.1
  have hfi : IntegrableOn f D := hsum.mono' hm.aestronglyMeasurable (Eventually.of_forall fun t =>
    (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hK t))).le.trans (hle t))
  have hsumBound := (integral_mono hfi hsum hle).trans_eq (integral_add hcD.1 hwD.1)
  have hfinal := hsumBound.trans_lt (add_lt_add (hcD.2.trans_lt hsmall) hwD.2)
  rw [add_halves] at hfinal
  simpa only [f,P,I,K,funext hid,m] using And.intro hfi hfinal

#print axioms riemannHypothesis_or_original_test_on_middle_complement
end GaloisForLFunctions.ExclusionOfTheCriticalState
