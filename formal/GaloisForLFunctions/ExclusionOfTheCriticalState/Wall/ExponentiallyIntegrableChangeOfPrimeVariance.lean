import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SubcriticalMeanSquareOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.TheLeftTraceUpToTheRateOfTheZeros

/-!
# Integer centering preserves the late ordinary-prime variance

Above the centered zero abscissa the damped ordinary-prime error lies in L².
The opposite exponential tilt is available for the integer discrepancy.
Their product controls the difference of the two squared prime waves.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- The polar-subtracted ordinary-prime wave of a real representative. -/
def ordinaryPrimePolarError (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (ordinaryPrimeWave Φ t).re-Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u)

private theorem polar_charge_eq {F Φ : ℝ → ℝ} (he : F =ᵐ[volume] Φ) :
    negativeHalfLineLaplace (cx F) (-(1/2))=((∫ u, Real.exp (-u/2)*Φ u:ℝ):ℂ) := by
  rw [negativeHalfLineLaplace,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [he] with u hu
  simp only [cx,hu,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat]
  congr 2; ring

/-- Removing the proper powers from the damped Mangoldt estimate preserves
square integrability above the centered zero abscissa. -/
theorem memLp_damped_ordinaryPrimePolarError {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ)
    {d : ℝ} (hd : zetaZeroAbscissa-1/2 < d) :
    MemLp (fun t : ℝ => Real.exp (-(d*t))*ordinaryPrimePolarError Φ t) 2 halfLineLaplaceMeasure := by
  have h0 : 0 < d := (sub_nonneg.2 half_le_zetaZeroAbscissa).trans_lt hd
  have hall := memLp_damped_prime_sum_sub_pole_of_abscissa hW ht hF hd
  have hpow := criticalState_memLp_damped_properPowerWave hW ht hF h0
  let g := fun t : ℝ => expRay (d:ℂ) t*(ordinaryPrimeWave Φ t-
    negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ))
  have htranslate : ∀ᵐ t ∂volume, ∀ p : Nat.Primes, F (t-Real.log (p:ℕ))=Φ (t-Real.log (p:ℕ)) :=
    ae_all_iff.2 fun p => (measurePreserving_sub_right volume (Real.log (p:ℕ))).quasiMeasurePreserving.ae_eq_comp he
  have hg : MemLp g 2 halfLineLaplaceMeasure := by
    apply MemLp.ae_eq _ (hall.sub hpow)
    filter_upwards [beyondWallProfile_primeForm hW (criticalHalfLineEnergyDomain_of_groundState hF),
      ae_restrict_of_ae htranslate] with t ht' hφ
    let f := fun n : ℕ => (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)
    have hsupp : Function.support f ⊆ {n : ℕ | IsPrimePow n} := by
      intro n hn
      by_contra hh
      have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (show ¬ IsPrimePow n from hh)
      exact hn (by simp [f,primeAtom,hz])
    have hsplit := tsum_eq_ordinary_primes_add_proper_powers (f := f) ht'.1 hsupp
    have hprime : (∑' p : Nat.Primes, f (p:ℕ))=ordinaryPrimeWave Φ t := by
      apply tsum_congr fun p => ?_
      dsimp only [f]; rw [hφ]; rfl
    change expRay (d:ℂ) t*((∑' n, f n)-_) - expRay (d:ℂ) t*(∑' j, f (properPrimePowerIndex j))=_
    rw [hsplit,hprime]; dsimp only [g]; ring
  have hre : MemLp (fun t => (g t).re) 2 halfLineLaplaceMeasure :=
    hg.mono (Complex.continuous_re.comp_aestronglyMeasurable hg.1) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  apply MemLp.ae_eq (Eventually.of_forall fun t => ?_) hre
  have hdamp : expRay (d:ℂ) t=((Real.exp (-(d*t)):ℝ):ℂ) := by simp [expRay]
  simp only [g,hdamp,polar_charge_eq he,Complex.re_ofReal_mul,Complex.sub_re,
    Complex.ofReal_re,ordinaryPrimePolarError,mul_comm (Real.exp (t/2))]

/-- Opposite exponential L² weights control the absolute difference of squares
after a perturbation. The majorant retains both the cross term and its square. -/
theorem weighted_variance_change_bound {E G : ℝ → ℝ}
    {d β r : ℝ} (hcross : r+d ≤ β) (hsq : r ≤ 2*β)
    (h1 : MemLp (fun t : ℝ => Real.exp (-(d*t))*E t) 2 halfLineLaplaceMeasure)
    (h2 : MemLp (fun t : ℝ => Real.exp (β*t)*G t) 2 halfLineLaplaceMeasure) :
    let V := fun t : ℝ => Real.exp (r*t)*|(E t-G t)^2-(E t)^2|
    IntegrableOn V (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), V t) ≤
      (∫ t in Ioi (0:ℝ), (Real.exp (-(d*t))*E t)^2) +
      2*(∫ t in Ioi (0:ℝ), (Real.exp (β*t)*G t)^2) := by
  let V := fun t : ℝ => Real.exp (r*t)*|(E t-G t)^2-E t^2|
  let f := fun t : ℝ => Real.exp (-(d*t))*E t
  let g := fun t : ℝ => Real.exp (β*t)*G t
  have undo (k : ℝ) (u : ℝ → ℝ) (hm : AEStronglyMeasurable (fun t : ℝ => Real.exp (k*t)*u t) halfLineLaplaceMeasure) :
      AEStronglyMeasurable u halfLineLaplaceMeasure := by
    have hw : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(k*t))) halfLineLaplaceMeasure := by fun_prop
    apply (hw.mul hm).congr (Eventually.of_forall fun t => ?_)
    change Real.exp (-(k*t))*(Real.exp (k*t)*u t)=u t
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  have hE := undo (-d) E (by simpa only [neg_mul] using h1.1)
  have hG := undo β G h2.1
  have hf2 : Integrable (fun t => f t^2) halfLineLaplaceMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm h1.1).1 h1
  have hg2 : Integrable (fun t => g t^2) halfLineLaplaceMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm h2.1).1 h2
  have hmajor := hf2.add (hg2.const_mul 2)
  have hnon (t : ℝ) : 0 ≤ V t := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hpoint : ∀ᵐ t ∂halfLineLaplaceMeasure, V t ≤ f t^2+2*g t^2 := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hcmp (a b : ℝ) (h : a ≤ b) : Real.exp (a*t) ≤ Real.exp (b*t) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h ht0)
    have hprod : Real.exp (r*t)*|E t*G t| ≤ |f t*g t| := by
      calc _ ≤ Real.exp ((β-d)*t)*|E t*G t| :=
            mul_le_mul_of_nonneg_right (hcmp _ _ (by linarith only [hcross])) (abs_nonneg _)
        _ = _ := by
            dsimp only [f,g]; rw [show (β-d)*t= -(d*t)+β*t by ring,Real.exp_add]
            simp only [abs_mul,abs_of_pos (Real.exp_pos _)]; ring
    have hsq' : Real.exp (r*t)*G t^2 ≤ g t^2 := by
      calc _ ≤ Real.exp ((2*β)*t)*G t^2 := mul_le_mul_of_nonneg_right (hcmp _ _ hsq) (sq_nonneg _)
        _ = _ := by dsimp only [g]; rw [show (2*β)*t=β*t+β*t by ring,Real.exp_add]; ring
    have hab : |(E t-G t)^2-E t^2| ≤ 2*|E t*G t|+G t^2 := by
      rw [show (E t-G t)^2-E t^2=G t^2-2*(E t*G t) by ring]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),add_comm])
    calc V t ≤ Real.exp (r*t)*(2*|E t*G t|+G t^2) := mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le
      _ ≤ 2*|f t*g t|+g t^2 := by rw [mul_add,mul_left_comm (Real.exp _) 2]; linarith only [hprod,hsq']
      _ ≤ _ := by rw [abs_mul]; nlinarith only [sq_nonneg (|f t|-|g t|),sq_abs (f t),sq_abs (g t)]
  have hi : Integrable V halfLineLaplaceMeasure := hmajor.mono' (by dsimp only [V]; fun_prop)
    (hpoint.mono fun t ht => (Real.norm_of_nonneg (hnon t)).le.trans ht)
  refine ⟨hi,(integral_mono_ae hi hmajor hpoint).trans_eq ?_⟩
  change (∫ t, f t^2+2*g t^2 ∂halfLineLaplaceMeasure) = _
  rw [integral_add hf2 (hg2.const_mul 2),integral_const_mul]

/-- The actual ordinary-prime and integer-centered squared waves differ by
an exponentially integrable function at every rate below 1 − Θ. -/
theorem criticalState_integrable_change_of_prime_variance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1-zetaZeroAbscissa) :
    IntegrableOn (fun t : ℝ => Real.exp (r*t)*|(integerCentredPrimeWave Φ t)^2-
      (ordinaryPrimePolarError Φ t)^2|) (Ioi 0) := by
  obtain ⟨d,hd,hd'⟩ := exists_between (by linarith only [hr'] : zetaZeroAbscissa-1/2 < 1/2-r)
  have hd0 : 0 < d := (sub_nonneg.2 half_le_zetaZeroAbscissa).trans_lt hd
  let β := r+d
  have hβ : 0 ≤ β := add_nonneg hr hd0.le
  have hβ' : β < 1/2 := by dsimp only [β]; linarith only [hd']
  let G := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u)
  have h := weighted_variance_change_bound (E := ordinaryPrimePolarError Φ) (G := G)
    (d := d) (β := β) (r := r)
    (le_refl _) (by dsimp only [β]; linarith only [hr,hd0])
    (memLp_damped_ordinaryPrimePolarError hW ht hF he hd)
    ((criticalState_subcritical_integer_error hW ht hF hc he hC hb hβ hβ').mono_measure Measure.restrict_le_self)
  apply h.1.congr_fun _ measurableSet_Ioi
  intro t _
  dsimp only
  rw [integerCentredPrimeWave_eq hb]
  have hshift : ordinaryPrimePolarError Φ t-G t=(ordinaryPrimeWave Φ t).re-integerReferenceWave Φ t := by
    dsimp only [ordinaryPrimePolarError,G]; ring
  rw [hshift]

/-- Failure of RH produces one state for which integer centering preserves
the whole late variance to exponential accuracy. -/
theorem riemannHypothesis_or_integrable_change_of_prime_variance : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ r : ℝ, 0 ≤ r → r < 1-zetaZeroAbscissa →
        IntegrableOn (fun t : ℝ => Real.exp (r*t)*|(integerCentredPrimeWave Φ t)^2-
          (ordinaryPrimePolarError Φ t)^2|) (Ioi 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun _ => criticalState_integrable_change_of_prime_variance hW ht hF hΦ he hC hb⟩

#print axioms riemannHypothesis_or_integrable_change_of_prime_variance
end GaloisForLFunctions.ExclusionOfTheCriticalState
