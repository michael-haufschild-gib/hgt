import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLateTimeEndpointOfTheTestedIntegerRows

/-!
# Upper integer tail of the original signed test

Before the test center, exponential confinement controls the absolute sum.
After the center, translation leaves ordered reciprocal prime intervals.
Together the two estimates bound the contribution of all integers above a
fixed cutoff throughout the middle time interval.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

private theorem confined_upper_band {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (k L : ℕ), 1 ≤ k → ∀ t : ℝ,
      |finiteCriticalComplementBand Φ k L t| ≤ A*(Real.sqrt k)⁻¹*Real.exp (2*t) := by
  let a := fun n : ℕ => Real.log n/(n:ℝ)^2+1/(n:ℝ)^2
  have ha : Summable a := GaloisForLFunctions.summable_log_nat_div_sq.add
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hpos (n : ℕ) : 0 ≤ a n := add_nonneg
    (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)) (by positivity)
  refine ⟨C*(∑' n, a n),mul_nonneg hC (tsum_nonneg hpos),fun k L hk t => ?_⟩
  let b := C*(Real.sqrt k)⁻¹*Real.exp (2*t)
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ n ∈ Finset.Ioc k L, b*a n := by
          apply Finset.sum_le_sum
          intro n hn
          have hkn := (Finset.mem_Ioc.mp hn).1
          have hn0 := hk0.trans (show (k:ℝ)<n by exact_mod_cast hkn)
          split_ifs
          · have hcoeff : |vonMangoldt n-1| ≤ Real.log n+1 := by
              apply (abs_sub _ _).trans
              rw [abs_of_nonneg vonMangoldt_nonneg,abs_one]
              exact add_le_add vonMangoldt_le_log le_rfl
            have hroot := (inv_le_inv₀ (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hk0)).mpr
              (Real.sqrt_le_sqrt (show (k:ℝ)≤n by exact_mod_cast hkn.le))
            have hΦ : |continuousIntegerAtom Φ n t| ≤ b/(n:ℝ)^2 := by
              rw [continuousIntegerAtom,abs_mul,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
              apply (mul_le_mul hroot (hb _) (abs_nonneg _) (by positivity)).trans_eq
              rw [mul_sub,Real.exp_sub,two_mul (Real.log n),Real.exp_add,Real.exp_log hn0]
              dsimp only [b]; ring
            rw [abs_mul]
            exact (mul_le_mul hcoeff hΦ (abs_nonneg _) (add_nonneg (Real.log_natCast_nonneg _) zero_le_one)).trans_eq
              (by dsimp only [a]; ring)
          · exact (abs_zero.le).trans (mul_nonneg hb0 (hpos _))
       _ ≤ ∑' n, b*a n := (ha.mul_left b).sum_le_tsum _ (fun n _ => mul_nonneg hb0 (hpos n))
       _ = _ := by rw [tsum_mul_left]; dsimp only [b]; ring

private theorem upper_band_before_center {Φ : ℝ → ℝ} (hc : Continuous Φ)
    {A : ℝ} (hA : 0 ≤ A) (hab : ∀ (k L : ℕ), 1 ≤ k → ∀ t : ℝ,
      |finiteCriticalComplementBand Φ k L t| ≤ A*(Real.sqrt k)⁻¹*Real.exp (2*t))
    (U T : ℝ) (k L : ℕ) (hk : 1 ≤ k) :
    let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
    IntegrableOn f (Ioc U T) ∧ |∫ t in Ioc U T, f t| ≤ A*(Real.sqrt k)⁻¹*Real.exp (2*T)/2 := by
  let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
  let H := fun t : ℝ => (A*(Real.sqrt k)⁻¹)*Real.exp (2*t)
  have hHm : IntegrableOn H (Iic T) := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) T).const_mul _
  have hsub : Ioc U T ⊆ Iic T := fun _ ht => ht.2
  have hH := hHm.mono_set hsub
  have hm : Measurable (finiteCriticalComplementBand Φ k L) := by
    unfold finiteCriticalComplementBand
    refine Finset.measurable_sum (Finset.Ioc k L) ?_
    intro n _
    exact Measurable.ite (measurableSet_lt (by fun_prop : Measurable fun t : ℝ =>
      Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const)
      (measurable_const.mul (measurable_const.mul (hc.measurable.comp (measurable_id.sub_const _)))) measurable_const
  have hf (t : ℝ) : ‖f t‖ ≤ H t := by
    change ‖finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)‖ ≤ H t
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1).trans (hab k L hk t)
  refine ⟨hH.mono' ((hm.mul (measurable_fractionalPrimeTest.comp
    (measurable_const.sub measurable_id))).aestronglyMeasurable) (Eventually.of_forall hf),?_⟩
  change |∫ t in Ioc U T, f t| ≤ _
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le (μ := volume.restrict (Ioc U T))
    (f := f) (g := H) hH (Eventually.of_forall hf)).trans
  have hnon : 0 ≤ᵐ[volume.restrict (Iic T)] H :=
    Eventually.of_forall fun t => by dsimp only [H,Pi.zero_apply]; positivity
  apply (setIntegral_mono_set hHm hnon (Eventually.of_forall fun _ hx => hsub hx)).trans_eq
  dsimp only [H]
  rw [integral_const_mul,integral_exp_mul_Iic (by norm_num : (0:ℝ)<2)]
  ring

/-- Uniform signed high-index estimate for every continuous representative
of the forced state, on any bounded time interval containing the test center. -/
theorem criticalState_upper_integer_tail {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U T M s : ℝ) (k : ℕ), U ≤ T → T ≤ M → 1 ≤ T →
      0 ≤ s → Real.exp (4*T+s) ≤ k →
      |(∫ v, Φ v)*(∫ t in Ioc U M, criticalComplementBand Φ k t*fractionalPrimeTest (T-t))|
        ≤ D*Real.exp (-s/8) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨A,hA,habs⟩ := confined_upper_band hC hb
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hd (by norm_num : (-4:ℝ)< -1/2)).congr
    filter_upwards [he] with v hv
    rw [hv,show (-1/2:ℝ)*v = -v/2 by ring,mul_comm]
  obtain ⟨B,hB,hlate⟩ := criticalComplement_late_band_interval hs hp (by norm_num : (0:ℝ)<1/8) (by norm_num)
  let m := ∫ v, Φ v
  refine ⟨|m| *(A/2+B),by positivity,
    fun U T M s k hU hM hT hS hcut => ?_⟩
  have hk0 := (Real.exp_pos _).trans_le hcut
  have hk : 1 ≤ k := by exact_mod_cast (Real.one_le_exp (by linarith only [hT,hS])).trans hcut
  have hsqrt : (Real.sqrt k)⁻¹*Real.exp (2*T) ≤ Real.exp (-s/8) := by
    have hr := Real.sqrt_le_sqrt hcut
    rw [← Real.exp_half] at hr
    have h := (inv_le_inv₀ (Real.sqrt_pos.mpr hk0) (Real.exp_pos _)).mpr hr
    apply (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans
    rw [← Real.exp_neg,← Real.exp_add,Real.exp_le_exp]
    linarith only [hS]
  have hpow : Real.exp (T/2)*(k:ℝ)^(-(1/8:ℝ)) ≤ Real.exp (-s/8) := by
    have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hcut (by norm_num : -(1/8:ℝ) ≤ 0)
    apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_mul,← Real.exp_add]; congr 1; ring
  have hL (L : ℕ) : |m*(∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t))|
      ≤ |m| *(A/2+B)*Real.exp (-s/8) := by
    let f := fun t => finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t)
    obtain ⟨hi,hei⟩ := upper_band_before_center hc hA habs U T k L hk
    obtain ⟨hj,hej⟩ := hlate T M k L hk hT hM
    change IntegrableOn f (Ioc U T) at hi
    change IntegrableOn f (Ioc T M) at hj
    have hsplit : (∫ t in Ioc U M, f t)=(∫ t in Ioc U T, f t)+(∫ t in Ioc T M, f t) := by
      rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi hj,Ioc_union_Ioc_eq_Ioc hU hM]
    change |m*(∫ t in Ioc U M, f t)| ≤ _
    rw [abs_mul,hsplit,mul_assoc |m|]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
    apply (abs_add_le _ _).trans ((add_le_add hei hej).trans ?_)
    calc _ = (A/2)*((Real.sqrt k)⁻¹*Real.exp (2*T))+
              B*(Real.exp (T/2)*(k:ℝ)^(-(1/8:ℝ))) := by ring
         _ ≤ (A/2)*Real.exp (-s/8)+B*Real.exp (-s/8) := add_le_add
            (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (mul_le_mul_of_nonneg_left hpow hB)
         _ = _ := by ring
  have hl := (finiteCriticalComplementBand_on_bounded_cut hc hC hb k U M T).const_mul m
  exact le_of_tendsto hl.abs (Eventually.of_forall hL)

/-- Removing the part through k from the original far-edge sum leaves the
doubly truncated series, with its original signs and both endpoint conventions. -/
theorem far_integer_sum_sub_prefix {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) (k : ℕ) (t : ℝ) :
    (∑' n : {j : ℕ // pastCriticalEdge j t}, (vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t) -
      finiteCriticalComplementRow Φ k t = criticalComplementBand Φ k t := by
  let a := fun n : ℕ => (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let A : Set ℕ := {n | pastCriticalEdge n t}
  let J := Finset.Ioc 0 k
  have ha : Summable a := ((summable_mangoldt_integerAtom hb t).sub
    (summable_continuousIntegerAtom hb t)).congr fun n => by simp only [a,sub_mul,one_mul]
  have hsplit : (∑ n ∈ J, A.indicator a n) +
      (∑' n : {j : ℕ // j ∉ J}, A.indicator a n.val) = ∑' n, A.indicator a n :=
    (ha.indicator A).sum_add_tsum_compl (s := J)
  have hf : finiteCriticalComplementRow Φ k t = ∑ n ∈ J, A.indicator a n := rfl
  let B : Set ℕ := {j | j ∉ J}
  have hrest : (∑' n : {j : ℕ // j ∉ J}, A.indicator a n.val) = criticalComplementBand Φ k t := by
    change (∑' n : B, A.indicator a n.val) = _
    refine (tsum_subtype B (A.indicator a)).trans ?_
    unfold criticalComplementBand
    apply tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hB : 0 ∈ B := by simp [B,J]
      have ha0 : A.indicator a 0 = 0 := by
        by_cases h : 0 ∈ A <;> simp [h,a,continuousIntegerAtom]
      rw [indicator_of_mem hB,ha0,if_neg (fun h => (Nat.not_lt_zero k) h.1)]
    · have hJ : n ∈ J ↔ n ≤ k := by simp [J,hn]
      by_cases hkn : k < n
      · have hB : n ∈ B := fun h => (not_le.mpr hkn) (hJ.mp h)
        rw [indicator_of_mem hB]
        by_cases hA : n ∈ A
        · rw [indicator_of_mem hA,if_pos ⟨hkn,hA⟩]
        · rw [indicator_of_notMem hA,if_neg (fun h => hA h.2)]
      · have hB : n ∉ B := fun h => h (hJ.mpr (le_of_not_gt hkn))
        rw [indicator_of_notMem hB,if_neg (fun h => hkn h.1)]
  change (∑' n : A, a n.val) - _ = _
  rw [tsum_subtype A a,hf,← hsplit,hrest,add_sub_cancel_left]

/-- On the original middle time interval, all integers past exp(4T+s) have
total oriented signed cost O(exp(-s/8)), uniformly in T and in the cutoff.
The moving first window has already been excluded inside the infinite series. -/
theorem riemannHypothesis_or_upper_integer_tail_of_original_test : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ (U T M s : ℝ) (k : ℕ), U ≤ T → T ≤ M → 1 ≤ T →
        0 ≤ s → Real.exp (4*T+s) ≤ k →
        |(∫ v, Φ v)*(∫ t in Ioc U M, ((∑' n : {j : ℕ // pastCriticalEdge j t},
          (vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t)-finiteCriticalComplementRow Φ k t)*
          fractionalPrimeTest (T-t))|
          ≤ D*Real.exp (-s/8) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨_,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,?_⟩
  simpa only [far_integer_sum_sub_prefix hb] using criticalState_upper_integer_tail hW ht hF hc he

#print axioms criticalState_upper_integer_tail
#print axioms riemannHypothesis_or_upper_integer_tail_of_original_test
end GaloisForLFunctions.ExclusionOfTheCriticalState
