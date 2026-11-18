import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedFractionalPartAverageOnTheCriticalState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeVarianceAfterACommonSieve

/-!
# Fractional-part test with literal integer centering

Tilting the fractional-part kernel moves the Mellin parameter inside the
critical strip. Its square integral bounds the test of the integer
quadrature discrepancy uniformly in the observation time.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

private def tiltedFloorTest (r v : ℝ) := Real.exp (r*v)*fractionalPrimeTest v

/-- Exponential tilting moves the fractional-part Mellin parameter. -/
theorem fractionalPrimeTest_tilt_eq (r v : ℝ) :
    Real.exp (r*v)*fractionalPrimeTest v= -weightedFloorDiscrepancy (1/2-r) v := by
  rw [fractionalPrimeTest,weightedFloorDiscrepancy,← mul_assoc,← Real.exp_add,neg_mul,neg_neg,
    show r*v+ -v/2= -(1/2-r)*v by ring]

private theorem integrable_tiltedFloorTest_square {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1/2) :
    Integrable (fun v => (tiltedFloorTest r v)^2) := by
  let σ := 1/2-r
  have hs : 0 < σ := sub_pos.mpr hr'
  have hs' : σ < 1 := by dsimp only [σ]; linarith only [hr]
  have he (v : ℝ) : tiltedFloorTest r v = -weightedFloorDiscrepancy σ v := fractionalPrimeTest_tilt_eq r v
  have hm := measurable_weightedFloorDiscrepancy σ
  apply (integrable_weightedFloorDiscrepancy hs hs').abs.mono'
  · simpa only [he,neg_sq] using (hm.pow_const 2).aestronglyMeasurable
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _),he,neg_sq,← sq_abs, sq]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_weightedFloorDiscrepancy_le_one hs.le hs'.le v)

/-- Translating the tilted kernel preserves its square norm. Thus every
critical-strip square-integrable discrepancy has an exponentially small
absolute response, uniformly over all real translations. -/
theorem tilted_discrepancy_fractional_test_bound {D : ℝ → ℝ} (hm : Measurable D)
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1/2)
    (hD : MemLp (fun t : ℝ => Real.exp (r*t)*D t) 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ,
      let f := fun t => D t*fractionalPrimeTest (T-t)
      Integrable f ∧ (∫ t, |f t|) ≤ B*Real.exp (-r*T) := by
  let g := fun t : ℝ => Real.exp (r*t)*D t
  let J := tiltedFloorTest r
  have hg : Integrable (fun t => (g t)^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hD.1).1 hD
  have hJ : Integrable (fun v => (J v)^2) := integrable_tiltedFloorTest_square hr hr'
  let B := (∫ t, (g t)^2)+(∫ v, (J v)^2)
  have hB : 0 ≤ B := add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  refine ⟨B,hB,fun T => ?_⟩
  let f := fun t : ℝ => D t*fractionalPrimeTest (T-t)
  let C := Real.exp (-r*T)
  let H := fun t : ℝ => C*((g t)^2+(J (T-t))^2)
  have hI : Integrable H := (hg.add (hJ.comp_sub_left T)).const_mul C
  have hf (t : ℝ) : ‖f t‖ ≤ H t := by
    have he : f t=C*(g t*J (T-t)) := by
      have hex : Real.exp (-r*T)*Real.exp (r*t)*Real.exp (r*(T-t))=1 := by
        rw [← Real.exp_add,← Real.exp_add,show -r*T+r*t+r*(T-t)=0 by ring,Real.exp_zero]
      calc f t = (Real.exp (-r*T)*Real.exp (r*t)*Real.exp (r*(T-t)))*f t := by rw [hex,one_mul]
        _ = _ := by dsimp only [f,C,g,J,tiltedFloorTest]; ring
    rw [he,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _ : 0<C),abs_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    nlinarith only [sq_nonneg (|g t|-|J (T-t)|),sq_abs (g t),sq_abs (J (T-t)),
      sq_nonneg (g t),sq_nonneg (J (T-t))]
  have hIf : Integrable f := hI.mono' (hm.mul (measurable_fractionalPrimeTest.comp
    (measurable_const.sub measurable_id))).aestronglyMeasurable (Eventually.of_forall hf)
  refine ⟨hIf,(integral_mono hIf.abs hI hf).trans_eq ?_⟩
  dsimp only [H,B]
  rw [integral_const_mul,integral_add (f := fun t => (g t)^2) (g := fun t => (J (T-t))^2)
    hg (hJ.comp_sub_left T),integral_sub_left_eq_self (fun v => (J v)^2) volume T,mul_comm]

/-- The signed test of the literal row with coefficients Λ(n) − 1 decays
at every rate below one half. Both the time integral and the integer row
are taken on the original critical representative. -/
theorem criticalState_integerCentred_fractional_response {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1/2) :
    let V := fun t : ℝ => ∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      let f := fun t => V t*fractionalPrimeTest (T-t)
      Integrable f ∧ |∫ t, f t| ≤ B*Real.exp (-r*T) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*A
  let W := logShiftWave (fun n : ℕ => vonMangoldt n/Real.sqrt n) Φ
  let V := fun t : ℝ => ∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  have hD : Continuous D := (continuous_integerReferenceWave hc hC hb).sub (by fun_prop)
  obtain ⟨M,hM,hbound⟩ := tilted_discrepancy_fractional_test_bound hD.measurable hr hr'
    (criticalState_subcritical_integer_error hW ht hF hc he hC hb hr hr')
  have hA : (∫ u in Iic (0:ℝ), Φ u*Real.exp (-u/2))=A := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic (0:ℝ))
      (f := fun u : ℝ => Φ u*Real.exp (-u/2)) (fun u hu => by rw [hs u (lt_of_not_ge hu).le,zero_mul])]
    exact integral_congr_ae (Eventually.of_forall fun u => mul_comm ..)
  have hrow (t : ℝ) : V t = (W t-Real.exp (t/2)*A)-D t := by
    have hW' : W t=∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t := by
      apply tsum_congr fun n => ?_
      simp only [continuousIntegerAtom,div_eq_mul_inv,mul_assoc]
    dsimp only [V,D]
    rw [hW',centred_mangoldt_atom_sum_split hb t,mangoldt_atom_sum_split hb t]; ring
  let q := 1/2-r
  have hq : 0 < q := sub_pos.mpr hr'
  refine ⟨C*(1+q⁻¹)+M,by positivity,fun T hT => ?_⟩
  let K := fun t : ℝ => fractionalPrimeTest (T-t)
  have h := criticalState_fractional_mangoldt_response hW ht hF hc he hs hC hb hT
  change Integrable (fun t => (W t-Real.exp (t/2)*_)*K t) ∧ _ at h
  simp only [hA] at h
  have hI := (hbound T).1
  have hp : (fun t => V t*K t) = fun t => (W t-Real.exp (t/2)*A)*K t-D t*K t :=
    funext fun t => by rw [hrow,sub_mul]
  change Integrable (fun t => V t*K t) ∧ |∫ t, V t*K t| ≤ _
  rw [hp,integral_sub h.1 hI]
  refine ⟨h.1.sub hI,(abs_sub _ _).trans ?_⟩
  have htime : 1+T ≤ (1+q⁻¹)*Real.exp (q*T) := by
    have hx := Real.add_one_le_exp (q*T)
    have he1 : 1 ≤ Real.exp (q*T) := Real.one_le_exp (mul_nonneg hq.le hT)
    have hT' : T ≤ q⁻¹*Real.exp (q*T) := by
      rw [← div_eq_inv_mul,le_div_iff₀ hq]; linarith only [hx]
    rw [add_mul,one_mul]
    exact add_le_add he1 hT'
  have hfirst := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime hC)
    (Real.exp_pos (-T/2)).le)
  have he' : C*((1+q⁻¹)*Real.exp (q*T))*Real.exp (-T/2)= C*(1+q⁻¹)*Real.exp (-r*T) := by
    calc _ = (C*(1+q⁻¹))*(Real.exp (q*T)*Real.exp (-T/2)) := by ring
      _ = _ := by rw [← Real.exp_add,show q*T + -T/2= -r*T by dsimp only [q]; ring]
  rw [add_mul]
  exact add_le_add (h.2.2.trans (hfirst.trans_eq he')) (abs_integral_le_integral_abs.trans (hbound T).2)

/-- A signed observation decaying faster than the damping of an unaveraged
wave controls their mixed product in absolute integral on the full ray. -/
theorem integrable_mixed_response {E Y : ℝ → ℝ} {d r ε B : ℝ}
    (hE : MemLp (fun t : ℝ => Real.exp (-(d*t))*E t) 2 halfLineLaplaceMeasure)
    (hm : Measurable Y) (hB : 0 ≤ B) (hY : ∀ t, 0 ≤ t → |Y t| ≤ B*Real.exp (-r*t))
    (hgap : ε+d < r) :
    IntegrableOn (fun t : ℝ => Real.exp (ε*t)*|E t*Y t|) (Ioi 0) := by
  let q := r-(ε+d)
  have hq : 0 < ((q:ℝ):ℂ).re := sub_pos.mpr hgap
  let g := fun t : ℝ => Real.exp ((ε+d)*t)*Y t
  have hg : MemLp g 2 halfLineLaplaceMeasure := by
    apply ((memLp_two_expRay_restrict hq 0).norm.const_mul B).mono
      ((by fun_prop : Measurable fun t : ℝ => Real.exp ((ε+d)*t)).mul hm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with t ht
    change ‖Real.exp ((ε+d)*t)*Y t‖ ≤ ‖B*‖expRay ((q:ℝ):ℂ) t‖‖
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),
      Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _)),norm_expRay,Complex.ofReal_re]
    calc _ ≤ Real.exp ((ε+d)*t)*(B*Real.exp (-r*t)) :=
           mul_le_mul_of_nonneg_left (hY t ht.le) (Real.exp_pos _).le
      _ = B*Real.exp (-(q*t)) := by
           rw [mul_left_comm,← Real.exp_add]
           congr 2; dsimp only [q]; ring
  have h := (memLp_one_iff_integrable.mp (hE.mul' (r := 1) hg)).norm
  refine h.congr (Eventually.of_forall fun t => ?_)
  change ‖(Real.exp ((ε+d)*t)*Y t)*(Real.exp (-(d*t))*E t)‖=_
  rw [show (Real.exp ((ε+d)*t)*Y t)*(Real.exp (-(d*t))*E t)=
    (Real.exp (-(d*t))*Real.exp ((ε+d)*t))*(E t*Y t) by ring,
    ← Real.exp_add,show -(d*t)+(ε+d)*t=ε*t by ring,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]

/-- Only the integer-centered endpoint is averaged. The ordinary-prime
polar error in the other factor is evaluated at the original time. -/
theorem riemannHypothesis_or_mixed_integerCentred_prime_covariance : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < 1-zetaZeroAbscissa →
        let V := fun t : ℝ => ∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t
        let Y := fun T : ℝ => ∫ t, V t*fractionalPrimeTest (T-t)
        IntegrableOn (fun T : ℝ => Real.exp (ε*T)*|ordinaryPrimePolarError Φ T*Y T|) (Ioi 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun ε hε hε' => ?_⟩
  obtain ⟨d,hd,hd'⟩ := exists_between (by linarith only [hε'] : zetaZeroAbscissa-1/2 < 1/2-ε)
  obtain ⟨r,hr,hr'⟩ := exists_between (by linarith only [hd'] : ε+d < 1/2)
  have hd0 := (sub_nonneg.mpr half_le_zetaZeroAbscissa).trans_lt hd
  have hr0 := (add_nonneg hε hd0.le).trans hr.le
  obtain ⟨B,hB,h⟩ := criticalState_integerCentred_fractional_response hW ht hF hc he hs hC hb hr0 hr'
  let V := fun t : ℝ => ∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  have hmV : Measurable V := Measurable.tsum fun n : ℕ =>
    measurable_const.mul (measurable_const.mul (hc.measurable.comp (measurable_id.sub measurable_const)))
  let f := fun z : ℝ × ℝ => V z.2*fractionalPrimeTest (z.1-z.2)
  have hmf : Measurable f := (hmV.comp measurable_snd).mul
    (measurable_fractionalPrimeTest.comp (measurable_fst.sub measurable_snd))
  apply integrable_mixed_response (memLp_damped_ordinaryPrimePolarError hW ht hF he hd)
    hmf.stronglyMeasurable.integral_prod_right'.measurable hB (fun t ht => (h t ht).2) hr

/-- Failure of RH forces this decay for one actual state simultaneously at
every subcritical rate. -/
theorem riemannHypothesis_or_integerCentred_fractional_response : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ r : ℝ, 0 ≤ r → r < 1/2 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
        let f := fun t => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)*fractionalPrimeTest (T-t)
        Integrable f ∧ |∫ t, f t| ≤ B*Real.exp (-r*T) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun _ hr hr' =>
    criticalState_integerCentred_fractional_response hW ht hF hc he hs hC hb hr hr'⟩

#print axioms riemannHypothesis_or_integerCentred_fractional_response
#print axioms riemannHypothesis_or_mixed_integerCentred_prime_covariance
end GaloisForLFunctions.ExclusionOfTheCriticalState
