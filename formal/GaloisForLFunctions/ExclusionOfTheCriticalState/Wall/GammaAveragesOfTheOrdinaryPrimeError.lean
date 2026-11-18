import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOneEquiv
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePolarTermsOfTheOrdinaryPrimeHead
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.GammaAveragesOfLaplaceData
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeHeadsAreHardyTransforms

/-!
# The signed ordinary-prime error on growing gamma windows

On the logarithmic prime axis the gamma density tⁿ exp(−t)/n! is centred at
n+1 and has standard deviation √(n+1). For every energy-domain profile its
signed ordinary-prime error on these windows tends geometrically to minus
half its zero-frequency charge.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The signed ordinary-prime profile on the logarithmic axis. -/
def ordinaryPrimeWave (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑' q : Nat.Primes, (vonMangoldtAtom (q:ℕ):ℂ) * (F (t-Real.log (q:ℕ)):ℂ)

private theorem prime_damping (F : ℝ → ℝ) (c : ℝ) (n : ℕ) (t : ℝ) :
    primeHeadDatumTerm F c n t = cexp (-(c:ℂ)*(t:ℂ)) *
      ((vonMangoldtAtom n:ℂ)*(F (t-Real.log n):ℂ)) := by
  unfold primeHeadDatumTerm dampedNegativeProfile
  simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_sub]
  rw [show -(c:ℂ)*(t:ℂ) = -(c:ℂ)*Real.log n + -(c:ℂ)*((t:ℂ)-Real.log n) by ring,Complex.exp_add]
  ring

private theorem ordinaryPrimeWave_hilbert {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ P : HalfLineLaplaceL2,
      ((P : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure] fun t => cexp (-(3/4)*(t:ℂ))*ordinaryPrimeWave F t) ∧
      ∀ z : ℂ, ∀ hz : 0 < z.re, inner ℂ (halfLineLaplaceFeature z hz) P =
        ordinaryPrimeHead F (-(z+3/4)) := by
  let c : ℝ := 3/4
  have hc : c ≤ 4 := by norm_num [c]
  have hc0 : 1/2 < c := by norm_num [c]
  let V := fun q : Nat.Primes => primeHeadDatumLp hF hc (q:ℕ)
  have hnorm : Summable (fun q => ‖V q‖) :=
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_primeHeadDatumLp_le hF hc)
      ((summable_primeHead_damping hc0).mul_right _)).comp_injective Subtype.coe_injective
  have hsum := hnorm.of_norm
  let P : HalfLineLaplaceL2 := ∑' q, V q
  refine ⟨P,?_,?_⟩
  · let e := HTGeometry.natEquivPrimes
    have hN : Summable (fun n : ℕ =>
        (eLpNorm (primeHeadDatumTerm F c (e n:ℕ)) 2 (volume.restrict (Ioi (0:ℝ)))).toReal) := by
      refine (hnorm.comp_injective e.injective).congr fun n => ?_
      change ‖primeHeadDatumLp hF hc (e n:ℕ)‖ = _
      rw [primeHeadDatumLp,Lp.norm_toLp]
    have hAE := ae_summable_of_summable_eLpNorm
      (fun n : ℕ => memLp_primeHeadDatumTerm hF hc (e n:ℕ)) hN
    have heNat := coeFn_tsum_ae_eq (f := fun n : ℕ => V (e n)) (hsum.comp_injective e.injective)
      (fun n => (memLp_primeHeadDatumTerm hF hc (e n:ℕ)).coeFn_toLp) hAE
    rw [e.tsum_eq V] at heNat
    have he : (P : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure] fun t => ∑' q : Nat.Primes,
        primeHeadDatumTerm F c (q:ℕ) t :=
      heNat.trans (Eventually.of_forall fun t => e.tsum_eq (fun q : Nat.Primes => primeHeadDatumTerm F c (q:ℕ) t))
    apply he.trans (Eventually.of_forall fun t => ?_)
    simp only [prime_damping,tsum_mul_left,c,Complex.ofReal_div,Complex.ofReal_ofNat,ordinaryPrimeWave]
  · intro z hz
    have h := hsum.hasSum.mapL (innerSL ℂ (halfLineLaplaceFeature z hz))
    have hterm (q : Nat.Primes) : inner ℂ (halfLineLaplaceFeature z hz) (V q) =
        (vonMangoldtAtom (q:ℕ):ℂ) * (cexp ((-(z+c))*Real.log (q:ℕ)) *
          levyHead F (-(z+c)) (Real.log (q:ℕ))) := by
      rw [← halfLineLaplaceTransform, halfLineLaplaceTransform_eq_laplaceRay,
        ← laplaceRay_primeHeadDatumTerm F c (q:ℕ) z]
      unfold laplaceRay
      apply integral_congr_ae
      filter_upwards [(memLp_primeHeadDatumTerm hF hc (q:ℕ)).coeFn_toLp] with t ht
      change (V q) t * expRay z t = _
      rw [show (V q) t = primeHeadDatumTerm F c (q:ℕ) t from ht]
    have he := (h.congr_fun fun q => (hterm q).symm).tsum_eq.symm
    change inner ℂ (halfLineLaplaceFeature z hz) P = _ at he
    simpa only [c,Complex.ofReal_div,Complex.ofReal_ofNat,ordinaryPrimeHead] using he

/-- Ordinary-prime error integrated against the gamma probability density of order n. -/
def ordinaryPrimeErrorGammaMean (F : ℝ → ℝ) (n : ℕ) : ℂ :=
  (∫ t in Ioi (0:ℝ), (t:ℂ)^n * cexp (-(t:ℂ)) *
    (ordinaryPrimeWave F t - negativeHalfLineLaplace (cx F) (-(1/2)) * cexp ((t:ℂ)/2))) / (n.factorial:ℂ)

/-- The twice-centred ordinary-prime wave is a damped Hilbert datum whose actual
Laplace transform continues across the closed unit disk about minus one. -/
theorem exists_regular_ordinaryPrimeError_datum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ (D : HalfLineLaplaceL2) (G : ℂ → ℂ),
      ((D : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure] fun t => cexp (-(3/4)*(t:ℂ)) *
        (ordinaryPrimeWave F t - negativeHalfLineLaplace (cx F) (-(1/2)) * cexp ((t:ℂ)/2) +
          negativeHalfLineLaplace (cx F) 0 / 2)) ∧
      AnalyticOnNhd ℂ G (Metric.closedBall (-1) 1) ∧
      G =ᶠ[𝓝 (-1:ℂ)] fun p => ∫ t in Ioi (0:ℝ), cexp ((p+3/4)*(t:ℂ)) * D t := by
  let A := negativeHalfLineLaplace (cx F) (-(1/2))
  let B := negativeHalfLineLaplace (cx F) 0 / 2
  obtain ⟨P,hP,hread⟩ := ordinaryPrimeWave_hilbert hF
  have h₁ : 0 < ((1/4:ℝ):ℂ).re := by norm_num
  have h₃ : 0 < ((3/4:ℝ):ℂ).re := by norm_num
  let X := halfLineLaplaceFeature _ h₁
  let Y := halfLineLaplaceFeature _ h₃
  let D := P - A • X + B • Y
  obtain ⟨G,hG,hagree⟩ := exists_analyticOnNhd_regular_ordinaryPrimeHead hF
  have hlocal : {p : ℂ | -4 < p.re ∧ p.re < -(3/4)} ∈ 𝓝 (-1:ℂ) :=
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).mem_nhds
      (by constructor <;> norm_num)
  have htrans : G =ᶠ[𝓝 (-1:ℂ)] fun p => ∫ t in Ioi (0:ℝ), cexp ((p+3/4)*(t:ℂ)) * D t := by
    filter_upwards [hlocal] with p hp
    obtain ⟨hp4,hp3⟩ := hp
    let z := -(p+3/4)
    have hz : 0 < z.re := by dsimp [z]; simp; linarith
    have hparam : -(z+3/4) = p := by dsimp [z]; ring
    have h1 : z+star (((1/4:ℝ):ℂ)) = -(p+1/2) := by simp [z]; ring
    have h3 : z+star (((3/4:ℝ):ℂ)) = -p := by simp [z]
    have he : inner ℂ (halfLineLaplaceFeature z hz) D = G p := by
      rw [hagree p hp4 (by linarith)]
      simp only [D,inner_add_right,inner_sub_right,inner_smul_right,X,Y,inner_halfLineLaplaceFeature,
        hread z hz]
      rw [hparam,h1,h3]
      simp only [A,B,div_eq_mul_inv,inv_neg,mul_inv_rev]
      ring
    rw [← he,← halfLineLaplaceTransform,halfLineLaplaceTransform_eq_laplaceRay,laplaceRay]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change D t * cexp (-(z*(t:ℂ))) = _
    rw [show -(z*(t:ℂ)) = (p+3/4)*(t:ℂ) by dsimp only [z]; ring,mul_comm]
  refine ⟨D,G,?_,hG,htrans⟩
  filter_upwards [Lp.coeFn_add (P - A • X) (B • Y),Lp.coeFn_sub P (A • X),Lp.coeFn_smul A X,
    Lp.coeFn_smul B Y,(halfLineLaplaceFeatureRaw_memLp h₁).coeFn_toLp,
    (halfLineLaplaceFeatureRaw_memLp h₃).coeFn_toLp,hP] with t ha hs hax hby hx hy hp
  change ((P - A • X + B • Y) t) = cexp (-(3/4)*(t:ℂ)) * (ordinaryPrimeWave F t - A*cexp ((t:ℂ)/2) + B)
  rw [ha,Pi.add_apply,hs,Pi.sub_apply,hax,hby,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,hp,
    show X t = halfLineLaplaceFeatureRaw _ t from hx,show Y t = halfLineLaplaceFeatureRaw _ t from hy]
  have hxstar : star (((1/4:ℝ):ℂ)) = (1/4:ℂ) := by norm_num
  have hystar : star (((3/4:ℝ):ℂ)) = (3/4:ℂ) := by norm_num
  simp only [halfLineLaplaceFeatureRaw,hxstar,hystar]
  have hphase : cexp (-(3/4)*(t:ℂ)) * cexp ((t:ℂ)/2) = cexp (-(1/4)*(t:ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination A * hphase

/-- After polar subtraction, the ordinary-prime error has limiting gamma mean
minus half the zero-frequency charge, with a geometric bound uniform in the order. -/
theorem ordinaryPrimeWave_gamma_averages {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ R C : ℝ, 1 < R ∧ ∀ n : ℕ,
      ‖ordinaryPrimeErrorGammaMean F n + negativeHalfLineLaplace (cx F) 0 / 2‖ ≤ C/R^n := by
  let A := negativeHalfLineLaplace (cx F) (-(1/2))
  let B := negativeHalfLineLaplace (cx F) 0 / 2
  obtain ⟨D,G,hd,hG,htrans⟩ := exists_regular_ordinaryPrimeError_datum hF
  obtain ⟨R,C,hR,hbound⟩ := gammaMoment_decay_of_regular_laplace (Lp.memLp D) hG htrans
  refine ⟨R,C,hR,fun n => ?_⟩
  let k := fun t : ℝ => (t:ℂ)^n * cexp (-(t:ℂ))
  let E := fun t : ℝ => ordinaryPrimeWave F t - A*cexp ((t:ℂ)/2)
  have he : (fun t : ℝ => (t:ℂ)^n * cexp (-(t:ℂ)/4) * D t) =ᵐ[halfLineLaplaceMeasure]
      fun t => k t * E t + k t * B := by
    filter_upwards [hd] with t ht
    change D t = cexp (-(3/4)*(t:ℂ)) * (E t + B) at ht
    rw [ht]
    have hphase : cexp (-(t:ℂ)/4) * cexp (-(3/4)*(t:ℂ)) = cexp (-(t:ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    dsimp only [k]
    linear_combination (t:ℂ)^n * (E t+B) * hphase
  change _ =ᵐ[volume.restrict (Ioi (0:ℝ))] _ at he
  have hk : IntegrableOn k (Ioi 0) := by
    simpa only [k,one_mul] using integrableOn_natPow_mul_cexp (c := 1) (by norm_num) n
  have hkB := hk.mul_const B
  have hD := (integrableOn_damped_gammaMoment (Lp.memLp D) n).congr he
  have hE : IntegrableOn (fun t => k t * E t) (Ioi 0) := by
    apply (hD.sub hkB).congr (Eventually.of_forall fun t => ?_)
    exact add_sub_cancel_right (k t * E t) (k t * B)
  have hmass : (∫ t in Ioi (0:ℝ), k t) = (n.factorial:ℂ) := by
    simpa only [k,one_mul,one_pow,div_one] using integral_Ioi_pow_mul_cexp (c := 1) (by norm_num) n
  have hb := hbound n
  rw [integral_congr_ae he,integral_add hE hkB,integral_mul_const,hmass,add_div,
    mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)] at hb
  exact hb

/-- Off RH the actual confined state has a nonzero ordinary-prime bias on the growing windows. -/
theorem riemannHypothesis_or_criticalState_prime_gamma_bias :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ negativeHalfLineLaplace (cx F) 0 ≠ 0 ∧
      Tendsto (ordinaryPrimeErrorGammaMean F) atTop (𝓝 (-(negativeHalfLineLaplace (cx F) 0 / 2))) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  refine Or.inr ⟨W₀,F,hW,ht,hF,criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
    (by simp),?_⟩
  obtain ⟨R,C,hR,hb⟩ := ordinaryPrimeWave_gamma_averages (criticalHalfLineEnergyDomain_of_groundState hF)
  have hlim : Tendsto (fun n : ℕ => C/R^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hR)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
  simpa only [dist_eq_norm,sub_neg_eq_add] using hb n

#print axioms ordinaryPrimeWave_gamma_averages
#print axioms riemannHypothesis_or_criticalState_prime_gamma_bias

end GaloisForLFunctions.ExclusionOfTheCriticalState
