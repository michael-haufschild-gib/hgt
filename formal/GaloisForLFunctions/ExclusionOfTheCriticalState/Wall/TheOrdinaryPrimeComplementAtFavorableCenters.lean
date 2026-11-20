import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.AllFuturePrimeIncrementsAtTheSameCenters
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheMiddleTimeComplementOfTheOriginalPrimeTest

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
             dsimp only
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
              ∀ y ≥ x, let D := ⌊Real.exp (Real.log x/4)⌋₊;
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
  have hηm : |m| *η ≤ ε/2 := by
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


/-- Below its center the state row has no integer weight: the wall support
kills every integer `n ≤ e^t`. Hence the complement of the first critical
window is exactly the tail strictly beyond `e^t + √(e^t · t)`. -/
private theorem tsum_compl_wallWindow_eq {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0) (t : ℝ) :
    (∑' n : {j : ℕ // j ∉ wallIntegerWindow t (criticalWallWidth t)},
        (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t) =
      ∑' n : {j : ℕ // Real.exp t+Real.sqrt (Real.exp t*Real.log (Real.exp t)) < j},
        (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t := by
  let v := fun n : ℕ => (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let w := criticalWallWidth t
  have hwidth : Real.sqrt (Real.exp t*Real.log (Real.exp t)) = w := by
    rw [Real.log_exp,Real.sqrt_mul (Real.exp_pos t).le,← Real.exp_half]; rfl
  have hv (n : ℕ) (hn : (n:ℝ) ≤ Real.exp t) : v n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [v,continuousIntegerAtom]
    · have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp (by exact_mod_cast hpos)).2 hn
      simp [v,continuousIntegerAtom,hs _ (sub_nonneg.2 hlog)]
  have hw0 : 0 ≤ Real.exp t+w := add_nonneg (Real.exp_pos t).le
    (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  have e1 : (∑' n : {j : ℕ // j ∉ wallIntegerWindow t w}, v n) =
      ∑' n, ({j | j ∉ wallIntegerWindow t w} : Set ℕ).indicator v n := tsum_subtype _ v
  have e2 : (∑' n : {j : ℕ // Real.exp t+w < j}, v n) =
      ∑' n, ({j : ℕ | Real.exp t+w < j} : Set ℕ).indicator v n := tsum_subtype _ v
  rw [hwidth]
  refine e1.trans (Eq.trans (tsum_congr fun n => ?_) e2.symm)
  by_cases hn : Real.exp t+w < n
  · have hJ : n ∉ wallIntegerWindow t w := by
      intro hm
      have hle : n ≤ ⌊Real.exp t+w⌋₊ := (Finset.mem_Ioc.1 hm).2
      exact absurd ((Nat.cast_le.2 hle).trans (Nat.floor_le hw0)) (not_le.2 hn)
    rw [Set.indicator_of_mem (show n ∈ {j | j ∉ wallIntegerWindow t w} from hJ),
      Set.indicator_of_mem (show n ∈ {j : ℕ | Real.exp t+w < j} from hn)]
  · rw [Set.indicator_of_notMem (show n ∉ {j : ℕ | Real.exp t+w < j} from hn)]
    by_cases hJ : n ∈ wallIntegerWindow t w
    · exact Set.indicator_of_notMem (show n ∉ {j | j ∉ wallIntegerWindow t w} from fun h => h hJ) _
    · rw [Set.indicator_of_mem (show n ∈ {j | j ∉ wallIntegerWindow t w} from hJ)]
      apply hv
      have hle : n ≤ ⌊Real.exp t+w⌋₊ := Nat.le_floor (le_of_not_gt hn)
      have hlow : n ≤ ⌊Real.exp t⌋₊ := by
        by_contra hc
        exact hJ (Finset.mem_Ioc.2 ⟨lt_of_not_ge hc,hle⟩)
      exact (Nat.cast_le.2 hlow).trans (Nat.floor_le (Real.exp_pos t).le)

/-- The comparison on favorable centers with the complementary row written as
the centered Mangoldt tail strictly beyond the critical width
`x + √(x log x)`, `x = e^t`. -/
theorem riemannHypothesis_or_ordinary_prime_tail_beyond_the_critical_width : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∃ c k : ℝ, 0 < c ∧ c < 1 ∧ 0 < k ∧ ∀ᶠ T : ℝ in atTop,
        ∃ B : Set ℝ, MeasurableSet B ∧ B ⊆ Ioc T (T+Real.log 2) ∧
          k ≤ (∫ t in B, fractionalPrimeTest (T-t)) ∧ ∀ t ∈ B,
            let x := Real.exp t
            let m := ∫ u, Φ u
            m*((∑' n : {j : ℕ // x+Real.sqrt (x*Real.log x) < j},
                (ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2)-ε <
                  m*ordinaryPrimePolarError Φ t ∧
              ∀ y ≥ x, let D := ⌊Real.exp (Real.log x/4)⌋₊;
                -(1-c)*(y-x)-c*Real.exp (Real.log (2*Real.exp T)/4)-1-D*Real.log D ≤
                  lateDivisorCenteredCount D x y := by
  rcases riemannHypothesis_or_ordinary_prime_complement_on_every_late_octave with hr |
    ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,h⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΨ,he,fun ε hε => ?_⟩
  obtain ⟨c,k,hc0,hc1,hk,hev⟩ := h ε hε
  refine ⟨c,k,hc0,hc1,hk,?_⟩
  filter_upwards [hev] with T hT
  obtain ⟨B,hmB,hBI,hkB,hB⟩ := hT
  refine ⟨B,hmB,hBI,hkB,fun t htB => ?_⟩
  have hBt := hB t htB
  dsimp only at hBt ⊢
  rw [← tsum_compl_wallWindow_eq hs t]
  exact hBt

#print axioms riemannHypothesis_or_ordinary_prime_tail_beyond_the_critical_width

end GaloisForLFunctions.ExclusionOfTheCriticalState
