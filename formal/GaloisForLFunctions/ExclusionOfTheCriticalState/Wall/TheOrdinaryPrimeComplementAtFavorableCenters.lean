import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheEarlyMassOfTheSignedFractionalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.AllFuturePrimeIncrementsAtTheSameCenters
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegratedErrorInThePrimeSquareLayer

/-!
# The ordinary-prime error on favorable integer centers

In each late octave, select centers by their actual Mangoldt increments. The
absolute prime-power transfer pays for removing large errors from this set.
The remaining fractional mass is bounded below uniformly in the test time.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- On a measurable positive set, logarithmic mass is precisely elapsed time
under the exponential change of variables. -/
private theorem log_mass_eq_preimage_volume {A : Set ℝ} (hm : MeasurableSet A) (hpos : A ⊆ Ioi 0) :
    (∫ u in A, u⁻¹) = volume.real (Real.exp ⁻¹' A) := by
  let B := Real.exp ⁻¹' A
  have hB : MeasurableSet B := hm.preimage Real.measurable_exp
  have him : Real.exp '' B = A := by
    ext u
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ht
    · intro hu
      have hx := Real.exp_log (hpos hu)
      exact ⟨Real.log u,by change Real.exp (Real.log u) ∈ A; rwa [hx],hx⟩
  have h := integral_image_eq_integral_abs_deriv_smul hB
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn (fun u : ℝ => u⁻¹)
  rw [him] at h
  rw [h]
  calc _ = ∫ _t in B, (1:ℝ) := by
             apply setIntegral_congr_fun hB
             intro t _
             rw [abs_of_pos (Real.exp_pos _),smul_eq_mul,mul_inv_cancel₀ (Real.exp_pos _).ne']
       _ = _ := by rw [setIntegral_const,smul_eq_mul,mul_one]

private theorem discard_large_transfer_errors {B : Set ℝ} {T : ℝ} (hmB : MeasurableSet B)
    (hfin : volume B ≠ ⊤) (hB : B ⊆ Ioi T) {q η : ℝ} (hη : 0 < η)
    (hvol : q ≤ volume.real B) {E : ℝ → ℝ} (hm : Measurable E) (hn : ∀ t, 0 ≤ E t)
    (hi : IntegrableOn E (Ioi T)) (hcost : ∫ t in Ioi T, E t ≤ η*q/2) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ B ∧ q/2 ≤ volume.real A ∧ ∀ t ∈ A, E t < η := by
  let D := B ∩ {t | η ≤ E t}
  have hD : MeasurableSet D := hmB.inter (measurableSet_le measurable_const hm)
  have hDB : D ⊆ B := inter_subset_left
  have hDT := hDB.trans hB
  have hDfin : volume D ≠ ⊤ := ((measure_mono hDB).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  have hlow := setIntegral_ge_of_const_le_real (c := η) hD hDfin (fun _ h => h.2) (hi.mono_set hDT)
  have hupper : (∫ t in D, E t) ≤ ∫ t in Ioi T, E t := setIntegral_mono_set hi
    (Eventually.of_forall hn) (ae_of_all _ fun _ h => hDT h)
  have hdrop : volume.real D ≤ q/2 := by
    apply (le_of_mul_le_mul_left _ hη)
    exact (hlow.trans (hupper.trans hcost)).trans_eq (by ring)
  refine ⟨B \ D,hmB.diff hD,sdiff_subset,?_,?_⟩
  · rw [measureReal_sdiff hDB hD hfin]; linarith only [hvol,hdrop]
  · rintro t ⟨ht,hnot⟩; exact lt_of_not_ge fun h => hnot ⟨ht,h⟩

/-- The fractional test stays above a half on the octave immediately to the
right of the test time. The left endpoint is excluded because its value is zero. -/
private theorem fractionalPrimeTest_octave_lower {T t : ℝ} (ht : t ∈ Ioc T (T+Real.log 2)) :
    (1/2:ℝ) ≤ fractionalPrimeTest (T-t) := by
  have hv := sub_neg.mpr ht.1
  rw [fractionalPrimeTest,Int.fract_eq_self.mpr ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.2 hv⟩,← Real.exp_add]
  calc (1/2:ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),one_div]
       _ ≤ Real.exp (T-t) := Real.exp_le_exp.2 (by linarith only [ht.2])
       _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hv])

/-- On a set of fixed positive fractional-test mass in every late octave, the
oriented ordinary-prime error exceeds the complete complementary integer row
minus the prescribed loss. The same centers control every future divisor prefix. -/
theorem riemannHypothesis_or_ordinary_prime_complement_on_every_late_octave : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∃ c k : ℝ, 0 < c ∧ c < 1 ∧ 0 < k ∧ ∀ᶠ T : ℝ in atTop,
        ∃ B : Set ℝ, MeasurableSet B ∧ B ⊆ Ioc T (T+Real.log 2) ∧
          k ≤ (∫ t in B, fractionalPrimeTest (T-t)) ∧ ∀ t ∈ B,
            let x := Real.exp t
            let J := wallIntegerWindow t (criticalWallWidth t)
            let m := ∫ u, Φ u
            let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
            m*((∑' n : {j : ℕ // j ∉ J}, v n)-m/2)-ε < m*ordinaryPrimePolarError Φ t ∧
              ∀ y ≥ x, let D := ⌊Real.exp (Real.log x/4)⌋₊
                -(1-c)*(y-x)-c*Real.exp (Real.log (2*Real.exp T)/4)-1-D*Real.log D ≤
                  lateDivisorCenteredCount D x y := by
  rcases riemannHypothesis_or_integer_mangoldt_sign_transfer with hr | ⟨W₀,F,Φ,D₀,hW,ht,hF,hΦ,he,hD₀,htail⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ u, Φ u
  let P := ordinaryPrimePolarError Φ
  let S := fun t : ℝ => (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
  let E := fun t => |P t-S t|
  have hmeS : Measurable S := (Measurable.tsum fun n : ℕ => measurable_const.mul
    (measurable_const.mul (hΦ.measurable.comp (by fun_prop)))).sub measurable_const
  have hmW : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hΦ.measurable.comp (by fun_prop)))
  have hmeP : Measurable P := (Complex.continuous_re.measurable.comp hmW).sub (by fun_prop)
  have hmE : Measurable E := (hmeP.sub hmeS).abs
  have htail' : ∀ᶠ V : ℝ in atTop, IntegrableOn E (Ioi (V+1)) ∧
      (∫ t in Ioi (V+1), E t) ≤ D₀*Real.exp ((-1/40)*V) := by
    filter_upwards [htail] with V hV
    simpa only [E,P,S,m,sign_part_distances_eq_abs_sub] using hV
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun ε hε => ?_⟩
  have heps := half_pos hε
  obtain ⟨c,κ,hc0,hc1,hκ,hall⟩ := criticalState_all_future_prefixes_at_favorable_state_centers hW ht hF hΦ he
    2 (ε/2) (by norm_num) heps
  let η := (ε/2)/(|m|+1)
  have hm1 : 0 < |m|+1 := by positivity
  have hη : 0 < η := div_pos heps hm1
  have hηm : |m|*η ≤ ε/2 := by
    calc _ ≤ (|m|+1)*η := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hη.le
         _ = _ := by dsimp only [η]; field_simp [hm1.ne']
  have hdec : Tendsto (fun v : ℝ => D₀*Real.exp ((-1/40)*v)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply,id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/40:ℝ)<0))).const_mul D₀
  have hcost := hdec.eventually_lt_const (by positivity : 0 < η*(κ/2)/2)
  have hshift : Tendsto (fun T : ℝ => T-1) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using (tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_id)
  refine ⟨c,κ/8,hc0,hc1,by positivity,?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually hall,hshift.eventually htail',hshift.eventually hcost] with T hA hE hsmall
  obtain ⟨A,hmA,hAI,hvol,_,hread⟩ := hA
  let x := Real.exp T
  have hx : 0 < x := Real.exp_pos _
  let U := Real.exp ⁻¹' A
  have hmU : MeasurableSet U := hmA.preimage Real.measurable_exp
  have hUI : U ⊆ Ioc T (T+Real.log 2) := by
    intro t htu
    have h := hAI htu
    have hhi : 2*x=Real.exp (T+Real.log 2) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]; ring
    exact ⟨Real.exp_lt_exp.mp h.1,Real.exp_le_exp.mp (h.2.trans_eq hhi)⟩
  have hUfin : volume U ≠ ⊤ := measure_ne_top_of_subset hUI (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hUvol : κ/2 ≤ volume.real U := by
    have h := (fractionalPrimeTest_mass_of_log_window_subset hmA hx (by norm_num : (0:ℝ)<2) hAI hvol).1
    rwa [log_mass_eq_preimage_volume hmA (fun u hu => hx.trans (hAI hu).1)] at h
  have hE0 : IntegrableOn E (Ioi T) := by simpa only [sub_add_cancel] using hE.1
  have hE1 : ∫ t in Ioi T, E t ≤ η*(κ/2)/2 := by
    apply le_trans _ hsmall.le; simpa only [sub_add_cancel] using hE.2
  obtain ⟨B,hmB,hBU,hBvol,hgood⟩ := discard_large_transfer_errors hmU hUfin
    (fun t hu => (hUI hu).1) hη hUvol hmE (fun t => abs_nonneg _) hE0 hE1
  have hBI := hBU.trans hUI
  have hBfin : volume B ≠ ⊤ := ((measure_mono hBU).trans_lt (lt_top_iff_ne_top.mpr hUfin)).ne
  have hKi : IntegrableOn (fun t => fractionalPrimeTest (T-t)) B :=
    (integrableOn_const (C := (1:ℝ)) hBfin).mono' (measurable_fractionalPrimeTest.comp
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using (fractionalPrimeTest_bounds (T-t)).1)
  have hKm := setIntegral_ge_of_const_le_real hmB hBfin (fun t htB => fractionalPrimeTest_octave_lower (hBI htB)) hKi
  refine ⟨B,hmB,hBI,(by linarith only [hBvol,hKm]),fun t htB => ?_⟩
  have htr := hread (Real.exp t) (hBU htB)
  rw [Real.log_exp] at htr
  refine ⟨?_,fun y hy => by simpa only [Real.log_exp] using (htr.2 y hy).2⟩
  have hdist := (mul_le_mul_of_nonneg_left (hgood t htB).le (abs_nonneg m)).trans hηm
  have hcmp : -(ε/2) ≤ m*(P t-S t) := by
    change |m| * |P t-S t| ≤ ε/2 at hdist
    rw [← abs_mul] at hdist
    exact (neg_le_neg hdist).trans (neg_abs_le _)
  have hsplit := centered_mangoldt_eq_criticalWidthReading_add_complement hb t
  change m*S t=criticalWidthSignedReading Φ t + _ at hsplit
  dsimp only
  change _ < m*P t
  linarith only [hsplit,htr.1,hcmp]

#print axioms riemannHypothesis_or_ordinary_prime_complement_on_every_late_octave

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
          (Ioc (T/6) (6*T)).indicator (fun t => m*S t) t|*fractionalPrimeTest (T-t)
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
  let B := |m|*B₀ + |m|*D₀*Real.exp (1/40) + B₁
  refine Or.inr ⟨W₀,F,Φ,B,hW,ht,hF,hΦ,he,by dsimp only [B]; positivity,?_⟩
  filter_upwards [hcut.eventually htransfer,eventually_ge_atTop (0:ℝ)] with T hx hT
  rw [sub_add_cancel] at hx
  let U := T/6
  let V := 6*T
  let I := Ioc U V
  let K := fun t => fractionalPrimeTest (T-t)
  let f := fun t => |m*P t-I.indicator (fun z => m*S z) t|*K t
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
    change |m*P t-I.indicator (fun z => m*S z) t|*K t ≤ |m|*((|S t|+|P t|)*K t)
    rw [indicator_of_notMem hnot,sub_zero,abs_mul,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (abs_nonneg _)) (abs_nonneg m)) (hK0 t))
  have hinter := restrict_le measurableSet_Ioc ((hx.1.const_mul |m|).mono_set
    (show I ⊆ Ioi U from fun _ h => h.1)) (fun t htj => by
    change |m*P t-I.indicator (fun z => m*S z) t|*K t ≤ |m|*E t
    rw [indicator_of_mem htj,← mul_sub,abs_mul]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg m) (abs_nonneg _))
      ((le_abs_self (K t)).trans (fractionalPrimeTest_bounds _).1))
  have hend := hlate T univ hT MeasurableSet.univ
  simp only [univ_inter] at hend
  have hrowEnd := restrict_le measurableSet_Ioi hend.1 (fun t htj => by
    have hnot : t ∉ I := fun h => (not_le_of_gt htj) h.2
    change |m*P t-I.indicator (fun z => m*S z) t|*K t ≤ |m*P t|*K t
    rw [indicator_of_notMem hnot,sub_zero])
  have hfrontCost : (∫ t in Iic U, f t) ≤ |m|*B₀*Real.exp (-T/12) := by
    apply hfront.2.trans
    rw [integral_const_mul,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [U,show (5*(T/6)-T)/2 = -T/12 by ring] using hE0.2
  have hmidE : (∫ t in I, E t) ≤ ∫ t in Ioi U, E t := setIntegral_mono_set hx.1
    (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ h => h.1)
  have hmidCost : (∫ t in I, f t) ≤ (|m|*D₀*Real.exp (1/40))*Real.exp (-T/240) := by
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
end GaloisForLFunctions.ExclusionOfTheCriticalState
