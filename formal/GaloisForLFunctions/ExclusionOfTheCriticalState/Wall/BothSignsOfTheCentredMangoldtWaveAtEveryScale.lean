import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheEarlyMassOfThePositivePrimeDetector
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw

/-!
# Both signs on every late logarithmic interval

Testing the centred Mangoldt wave against a visible zero supplies a growing
complex response. The positive comparison bounds its signed response.
Both sign masses survive after excising the whole initial interval.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- Every right zero seen by the reflected transform forces both signs of
the centred Mangoldt wave on every sufficiently late observation interval. -/
theorem seen_zero_forces_both_signs_of_centred_wave {F Φ : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ u, |Φ u| ≤ K*Real.exp (2*u))
    {ρ : ℂ} (hhalf : 1/2 < ρ.re) (hone : ρ.re < 1) (hz : riemannZeta ρ=0)
    (hseen : negativeHalfLineLaplace (cx F) (1/2-ρ)≠0) {η : ℝ} (hη : 0 < η) (hη' : η < ρ.re) :
    let V := logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, s=1 ∨ s= -1 →
      m*Real.exp ((ρ.re-1/2)*T) ≤ ∫ t in Ioc (η*T) T, max (s*V t) 0 := by
  let V := logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ
  obtain ⟨H,d,B,D,hd0,hB,hD,_,hdom,hmain⟩ := visible_zero_detector_for_centred_wave hd hc he hs hK hb hhalf hone hz hseen
  have hiΦ : Integrable Φ := hd.integrable.congr he
  let D' := D+1
  have hD' : 0 < D' := by dsimp only [D']; linarith only [hD]
  let δ := ρ.re-1/2
  have hδ : 0 < δ := sub_pos.2 hhalf
  let κ := (ρ.re-η)/2
  have hκ : 0 < κ := half_pos (sub_pos.2 hη')
  have hκ' : 1/2+κ ≤ 2 := by dsimp only [κ]; linarith only [hone,hη]
  obtain ⟨A,hA,hV⟩ := centredMangoldtWave_exponential_bound hK hb hs (by linarith only [hκ] : 1/2<1/2+κ) hκ'
  let C := 2*(75+2*|Real.eulerMascheroniConstant|)*(∫ u, |Φ u|)
  have hDmax (v : ℝ) : ‖H v‖ ≤ D'*positivePrimeDetector v :=
    (hdom v).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (positivePrimeDetector_nonneg v))
  have hdpos := norm_pos_iff.2 hd0
  let m := ‖d‖/(8*D')
  have hm : 0 < m := div_pos hdpos (by positivity)
  refine ⟨m,hm,?_⟩
  have habsorb := eventually_absorb_detector_remainders (a := η-1/2+κ) hδ
    (by dsimp only [δ,κ]; linarith only [hη']) (half_pos hdpos) (B+D'*C) (2*D'*(A*κ⁻¹))
  filter_upwards [eventually_ge_atTop (0:ℝ),habsorb] with T hT ht
  intro s hs'
  obtain ⟨hH,herr⟩ := hmain T hT
  obtain ⟨hJ,hC⟩ := bounded_positive_detector_response hc hiΦ hs hK hb T hT
  let R := ∫ t : ℝ, (V t:ℂ)*H (T-t)
  let M := cexp ((ρ-1/2)*T)*d
  have hn : ‖M‖=Real.exp (δ*T)*‖d‖ := by
    rw [norm_mul,Complex.norm_exp]; dsimp only [δ]; congr 2; simp [Complex.mul_re]
  have htriangle : ‖M‖ ≤ B+‖R‖ := by
    have h := norm_add_le (M-R) R
    rw [sub_add_cancel,norm_sub_rev M R] at h
    exact h.trans (add_le_add_right herr _)
  have hsign := dominated_integral_le_signed_mass hD'.le (fun t => positivePrimeDetector_nonneg (T-t))
    hJ hH (fun t => hDmax (T-t)) hs'
  have hmV : Measurable V := Measurable.tsum fun n : ℕ => by fun_prop
  have hi : IntegrableOn (fun t : ℝ => max (s*V t) 0) (Ioc (η*T) T) := by
    have hσ : 0 < 1/2+κ := by linarith only [hκ]
    apply (((integrableOn_exp_mul_Iic hσ T).const_mul A).mono_set Ioc_subset_Iic_self).mono' (by fun_prop)
    filter_upwards with t
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    apply max_le _ (mul_nonneg hA (Real.exp_pos _).le)
    rcases hs' with rfl | rfl
    · exact (one_mul _).le.trans ((le_abs_self _).trans (hV t))
    · rw [neg_one_mul]; exact (neg_le_abs _).trans (hV t)
  have hloc := positivePrimeDetector_sign_split hs' hJ hi
  have hearly := early_positivePrimeDetector_mass_le hκ hA hV η T
  let mass := ∫ t in Ioc (η*T) T, max (s*V t) 0
  have hL : ‖R‖ ≤ D'*(2*((A*κ⁻¹)*Real.exp ((η-1/2+κ)*T)+2*mass)+C) :=
    hsign.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hloc.trans (add_le_add_right hearly _)) (by norm_num)) hC) hD'.le)
  rw [hn] at htriangle
  have hfinal : ‖d‖*Real.exp (δ*T) ≤ 8*D'*mass := by
    linarith only [htriangle,hL,ht]
  change (‖d‖/(8*D'))*Real.exp (δ*T) ≤ mass
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  exact hfinal.trans_eq (mul_comm ..)

/-- Failure of RH provides a reflected pole whose logarithmic sign mass
persists for every horizon and every admissible starting fraction. -/
theorem riemannHypothesis_or_both_signs_of_centred_wave : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (ρ : ℂ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      1/2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ=0 ∧
      ∀ η : ℝ, 0 < η → η < ρ.re → ∃ m : ℝ, 0 < m ∧
        ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, s=1 ∨ s= -1 →
          m*Real.exp ((ρ.re-1/2)*T) ≤ ∫ t in Ioc (η*T) T, max (s*
            logShiftWave (fun n : ℕ => centredMangoldtCoefficients n/Real.sqrt n) Φ t) 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨K,hK,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨z,hz,hz0,hz' ,hseen⟩ := criticalState_exists_seen_left_zetaZero hW ht hF
  let ρ := 1-z
  have hre : ρ.re=1-z.re := by simp [ρ]
  have hh : 1/2<ρ.re := by linarith only [hre,hz']
  have h1 : ρ.re<1 := by linarith only [hre,hz0]
  have hzero := riemannZeta_one_sub_eq_zero_of_mem_openStrip hz hz0 (by linarith only [hz'])
  have harg : 1/2-ρ=z-1/2 := by dsimp only [ρ]; ring
  exact Or.inr ⟨W₀,F,Φ,ρ,hW,ht,hF,hc,he,hh,h1,hzero,fun _ hη hη' =>
    seen_zero_forces_both_signs_of_centred_wave (criticalHalfLineEnergyDomain_of_groundState hF)
      hc he hs hK hb hh h1 hzero (harg.symm ▸ hseen) hη hη'⟩

#print axioms riemannHypothesis_or_both_signs_of_centred_wave
end GaloisForLFunctions.ExclusionOfTheCriticalState
