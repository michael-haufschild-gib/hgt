import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOrdinaryPrimeWaveOnTheThirdConfinedSpan
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.OneSidedLaplaceMassFromSignedGammaMoments
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.RHTower.WeilLagExponentialExceptionRigidity

/-!
# Opposite excursions in the uncentred ordinary-prime wave

Three confined rungs give a profile whose two elementary prime charges vanish.
The singularity of its ordinary-prime head forces exponential absolute mass.
The signed gamma means are summable, so both signs carry that mass separately.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

open private ordinaryPrimeWave_hilbert from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.GammaAveragesOfTheOrdinaryPrimeError

private theorem ordinaryPrimeWave_real (F : ℝ → ℝ) (t : ℝ) :
    ((ordinaryPrimeWave F t).re : ℂ) = ordinaryPrimeWave F t := by
  let v := ∑' q : Nat.Primes, vonMangoldtAtom (q:ℕ) * F (t-Real.log (q:ℕ))
  have he : (v:ℂ) = ordinaryPrimeWave F t := by
    simp only [v,ordinaryPrimeWave,Complex.ofReal_tsum,Complex.ofReal_mul]
  rw [← he, Complex.ofReal_re]

/-- Absolute integrability at every positive damping gives a physical Laplace
continuation on the open left half-plane. -/
private theorem ordinary_continuation_of_all_dampings {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hall : ∀ b : ℝ, 0 < b → b ≤ 1 → IntegrableOn
      (fun t => Real.exp (-b*t) * |(ordinaryPrimeWave F t).re|) (Ioi 0)) :
    ∃ J : ℂ → ℂ, DifferentiableOn ℂ J {p : ℂ | p.re < 0} ∧
      EqOn J (ordinaryPrimeHead F) {p : ℂ | p.re < -(1/2)} := by
  let V := ordinaryPrimeWave F
  have hm : Measurable V := by
    unfold V ordinaryPrimeWave
    apply Measurable.tsum
    intro q
    exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (hF.meas.comp (measurable_id.sub_const _)))
  have habs (t : ℝ) : ‖V t‖ = |(V t).re| := by
    calc ‖V t‖ = ‖((V t).re : ℂ)‖ := congrArg norm (ordinaryPrimeWave_real F t).symm
         _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hint (b : ℝ) (hb : 0 < b) :
      IntegrableOn (fun t => ‖V t‖ * Real.exp (-b*t)) (Ioi 0) := by
    let d := min b 1
    have hd := hall d (lt_min hb zero_lt_one) (min_le_right _ _)
    apply hd.mono' ((hm.norm.mul (by fun_prop)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖‖V t‖ * Real.exp (-b*t)‖ ≤ Real.exp (-d*t) * |(V t).re|
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),habs,mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right (min_le_left b 1) (le_of_lt ht)
      dsimp only [d]; linarith only [this])) (abs_nonneg _)
  let J := fun p : ℂ => ∫ t in Ioi (0:ℝ), V t * cexp (p*(t:ℂ))
  have hJ : DifferentiableOn ℂ J {p : ℂ | p.re < 0} := by
    intro p hp
    have h := OneSidedConfiguration.analyticAt_laplace_of_integrable hm.aestronglyMeasurable hint
      (z := -p) (by rw [neg_re]; exact neg_pos.mpr hp)
    have hcomp := h.differentiableAt.comp p (differentiable_neg p)
    simpa only [J,Function.comp_def,neg_neg] using hcomp.differentiableWithinAt
  let U := {p : ℂ | p.re < -(1/2)}
  have hu : IsOpen U := isOpen_lt continuous_re continuous_const
  have hsub : U ⊆ {p : ℂ | p.re < 0} := fun p h =>
    (show p.re < -(1/2:ℝ) from h).trans (by norm_num : -(1/2:ℝ) < 0)
  let K := J + properPowerHead F
  have hK := ((hJ.add (differentiableOn_properPowerHead hF)).mono hsub).analyticOnNhd hu
  obtain ⟨P,hP,hread⟩ := ordinaryPrimeWave_hilbert hF
  have hloc : K =ᶠ[𝓝 (-1:ℂ)] primeHead F := by
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds
      (show (-1:ℂ).re < -(3/4:ℝ) by norm_num)] with p (hp : p.re < -(3/4))
    let z := -(p+3/4)
    have hz : 0 < z.re := by dsimp [z]; simp; linarith
    have he := hread z hz
    rw [show -(z+3/4) = p by dsimp [z]; ring, ← halfLineLaplaceTransform,
      halfLineLaplaceTransform_eq_laplaceRay, laplaceRay] at he
    have ej : J p = ordinaryPrimeHead F p := by
      rw [← he]
      apply integral_congr_ae
      filter_upwards [hP] with t ht
      change V t * cexp (p*(t:ℂ)) = P t * cexp (-(z*(t:ℂ)))
      rw [ht, mul_comm (cexp _) (ordinaryPrimeWave F t), mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp only [z]; ring
    change J p + properPowerHead F p = primeHead F p
    rw [ej]; exact (primeHead_eq_prime_add_properPowerHead hF (by linarith)).symm
  have heq : EqOn K (primeHead F) U :=
    hK.eqOn_of_preconnected_of_eventuallyEq ((differentiableOn_primeHead hF).analyticOnNhd hu)
      (convex_halfSpace_re_lt _).isPreconnected (by change (-1:ℂ).re < -(1/2:ℝ); norm_num) hloc
  refine ⟨J,hJ,fun p hp => ?_⟩
  have he := heq hp
  change J p + properPowerHead F p = primeHead F p at he
  exact add_right_cancel (he.trans (primeHead_eq_prime_add_properPowerHead hF hp))

private theorem neutral_ordinary_gamma_moments {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (ha : negativeHalfLineLaplace (cx F) (-(1/2)) = 0)
    (hb : negativeHalfLineLaplace (cx F) 0 = 0) :
    let v := fun t => (ordinaryPrimeWave F t).re
    (∀ n, IntegrableOn (fun t => primeGammaWeight n t * v t) (Ioi 0)) ∧
      Summable fun n => |∫ t in Ioi (0:ℝ), primeGammaWeight n t * v t| := by
  intro v
  obtain ⟨P,hP,-⟩ := ordinaryPrimeWave_hilbert hF
  let W := fun (n : ℕ) (t : ℝ) => primeGammaWeight n t * v t
  have ec (n : ℕ) (t : ℝ) : ((W n t : ℝ):ℂ) =
      ((t:ℂ)^n * cexp (-(t:ℂ)) * ordinaryPrimeWave F t) / n.factorial := by
    simp only [W,v,primeGammaWeight,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_natCast,Complex.ofReal_exp,Complex.ofReal_neg,ordinaryPrimeWave_real]
    ring
  have hi (n : ℕ) : IntegrableOn (fun t => (W n t:ℂ)) (Ioi 0) := by
    apply ((integrableOn_damped_gammaMoment (Lp.memLp P) n).div_const (n.factorial:ℂ)).congr
    filter_upwards [hP] with t ht
    change (t:ℂ)^n * cexp (-(t:ℂ)/4) * P t / n.factorial = (W n t : ℂ)
    rw [ht,ec,← mul_assoc, mul_assoc ((t:ℂ)^n), ← Complex.exp_add]
    rw [show -(t:ℂ)/4 + -(3/4)*(t:ℂ) = -(t:ℂ) by ring]
  have hir (n : ℕ) : IntegrableOn (W n) (Ioi 0) := (hi n).re
  refine ⟨hir,?_⟩
  obtain ⟨R,C,hR,hbnd⟩ := ordinaryPrimeWave_gamma_averages hF
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (f := fun n : ℕ => C * (R⁻¹)^n) ?_
    ((summable_geometric_of_lt_one (inv_nonneg.mpr (zero_lt_one.trans hR).le)
      (inv_lt_one_of_one_lt₀ hR)).mul_left C)
  intro n
  have e : ordinaryPrimeErrorGammaMean F n = ((∫ t in Ioi (0:ℝ), W n t : ℝ):ℂ) := by
    simp only [ordinaryPrimeErrorGammaMean,ha,zero_mul,sub_zero]
    rw [← integral_div,← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => (ec n t).symm
  simpa only [hb,zero_div,zero_mul,add_zero,e,Complex.norm_real,Real.norm_eq_abs,div_eq_mul_inv,
    inv_pow] using hbnd n

/-- The uncentred wave over ordinary primes has infinite positive and negative
mass even after exponential damping. Both elementary prime charges vanish on
the same nonzero combination of three rungs. -/
theorem IsCriticalLadder.exists_double_neutral_opposite_prime_mass {R : Fin 3 → ℝ}
    {Φ : Fin 3 → ℝ → ℝ} (hL : IsCriticalLadder 2 R Φ) :
    ∃ (c : Fin 3 → ℝ) (b : ℝ), c ≠ 0 ∧ 0 < b ∧
      let H := fun u => ∑ i, c i * Φ i u
      let v := fun t => (ordinaryPrimeWave H t).re
      negativeHalfLineLaplace (cx H) (-(1/2)) = 0 ∧ negativeHalfLineLaplace (cx H) 0 = 0 ∧
      (¬ IntegrableOn (fun t => Real.exp (-b*t) * max (v t) 0) (Ioi 0)) ∧
      (¬ IntegrableOn (fun t => Real.exp (-b*t) * max (-v t) 0) (Ioi 0)) := by
  obtain ⟨c,hc,ha,hb,-,-,-,hobs⟩ := hL.exists_double_neutral_ordinary_prime_head
  let H := fun u => ∑ i, c i * Φ i u
  let v := fun t => (ordinaryPrimeWave H t).re
  have hd : CriticalHalfLineEnergyDomain H := (hL.bare_neg_of_nonzero hc).1
  obtain ⟨b,hbp,hb1,habs⟩ : ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
      ¬ IntegrableOn (fun t => Real.exp (-b*t)*|v t|) (Ioi 0) := by
    by_contra! hall
    exact hobs (ordinary_continuation_of_all_dampings hd hall)
  obtain ⟨hi,hs⟩ := neutral_ordinary_gamma_moments hd ha hb
  refine ⟨c,b,hc,hbp,ha,hb,fun hp => habs (integrable_abs_of_posPart_of_summable_gamma_moments
    hbp.le hb1 hi hs hp),fun hm => ?_⟩
  have hi' (n : ℕ) : IntegrableOn (fun t => primeGammaWeight n t * (-v t)) (Ioi 0) := by
    exact (hi n).neg.congr (Eventually.of_forall fun t => (mul_neg (primeGammaWeight n t) (v t)).symm)
  have hs' : Summable fun n => |∫ t in Ioi (0:ℝ), primeGammaWeight n t * (-v t)| := by
    simpa only [mul_neg,integral_neg,abs_neg] using hs
  have h := integrable_abs_of_posPart_of_summable_gamma_moments hbp.le hb1 hi' hs' hm
  exact habs (by simpa only [abs_neg] using h)

/-- Infinite damped positive mass forces excursions above every smaller exponential
on every tail. The order-zero gamma moment controls the bounded initial interval. -/
private theorem late_prime_excursions {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hi : IntegrableOn (fun t => primeGammaWeight 0 t * f t) (Ioi 0))
    (hm : Measurable f)
    (hn : ¬ IntegrableOn (fun t => Real.exp (-b*t) * max (f t) 0) (Ioi 0))
    (M T : ℝ) (hM : 0 < M) :
    ∃ t : ℝ, T < t ∧ M*Real.exp ((b/2)*t) < f t := by
  by_contra! h
  apply hn
  have hsmall : IntegrableOn (fun t => Real.exp (-t)*|f t|) (Ioi 0) := by
    apply hi.abs.congr
    exact Eventually.of_forall fun t => by simp [primeGammaWeight,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hlarge := (integrableOn_exp_mul_Ioi (show -(b/2) < 0 by linarith) 0).const_mul M
  apply ((hsmall.const_mul (Real.exp T)).add hlarge).mono'
    (((by fun_prop : Measurable fun t : ℝ => Real.exp (-b*t)).mul
      (hm.max measurable_const)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have hm0 : 0 ≤ max (f t) 0 := le_max_right _ _
  change ‖Real.exp (-b*t) * max (f t) 0‖ ≤
    Real.exp T * (Real.exp (-t) * |f t|) + M * Real.exp (-(b/2)*t)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hm0)]
  rcases le_or_gt t T with hT | hT
  · apply le_add_of_le_of_nonneg _ (mul_nonneg hM.le (Real.exp_pos _).le)
    rw [← mul_assoc,← Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr (by
      have he := mul_nonneg hb.le ht0
      linarith only [he,hT])) (max_le (le_abs_self _) (abs_nonneg _)) hm0 (Real.exp_pos _).le
  · apply le_add_of_nonneg_of_le (by positivity)
    have ht' : max (f t) 0 ≤ M * Real.exp (b/2*t) :=
      max_le (h t hT) (mul_nonneg hM.le (Real.exp_pos _).le)
    calc _ ≤ Real.exp (-b*t) * (M*Real.exp (b/2*t)) :=
           mul_le_mul_of_nonneg_left ht' (Real.exp_pos _).le
         _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring

/-- Without RH or a lone quartet, three actual states produce a double-neutral
ordinary-prime wave with opposite exponential excursions arbitrarily far out. -/
theorem riemannHypothesis_or_quartet_or_double_neutral_prime_excursions :
    RiemannHypothesis ∨ (∃ ρ, HasSingleOffLineQuartet ρ) ∨
      ∃ (R : Fin 3 → ℝ) (Φ : Fin 3 → ℝ → ℝ) (c : Fin 3 → ℝ) (δ : ℝ),
        IsCriticalLadder 2 R Φ ∧ c ≠ 0 ∧ 0 < δ ∧
        let H := fun u => ∑ i, c i * Φ i u
        negativeHalfLineLaplace (cx H) (-(1/2)) = 0 ∧ negativeHalfLineLaplace (cx H) 0 = 0 ∧
        ∀ M T : ℝ, 0 < M →
          (∃ t : ℝ, T < t ∧ M*Real.exp (δ*t) < (ordinaryPrimeWave H t).re) ∧
          (∃ t : ℝ, T < t ∧ (ordinaryPrimeWave H t).re < -(M*Real.exp (δ*t))) := by
  classical
  by_cases hq : ∃ ρ, HasSingleOffLineQuartet ρ
  · exact Or.inr (Or.inl hq)
  rcases no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp (not_exists.mp hq) with h | h4
  · exact Or.inl h
  rcases riemannHypothesis_or_criticalLadder with h | ⟨_,_,_,_,_,hL⟩
  · exact Or.inl h
  have h3 : (3 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := (by norm_num : (3:ℕ∞) ≤ 4).trans h4
  obtain ⟨R,Φ,hL,-,-⟩ := hL 2 h3
  obtain ⟨c,b,hc,hb,ha,hz,hpos,hneg⟩ := hL.exists_double_neutral_opposite_prime_mass
  let H := fun u => ∑ i, c i * Φ i u
  let v := fun t => (ordinaryPrimeWave H t).re
  have hd : CriticalHalfLineEnergyDomain H := (hL.bare_neg_of_nonzero hc).1
  have hi : IntegrableOn (fun t => primeGammaWeight 0 t * v t) (Ioi 0) :=
    (neutral_ordinary_gamma_moments hd ha hz).1 0
  have hm : Measurable v := by
    apply continuous_re.measurable.comp
    apply Measurable.tsum
    intro q
    exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (hd.meas.comp (measurable_id.sub_const _)))
  refine Or.inr (Or.inr ⟨R,Φ,c,b/2,hL,hc,half_pos hb,ha,hz,fun M T hM => ?_⟩)
  refine ⟨late_prime_excursions hb hi hm hpos M T hM,?_⟩
  have hi' : IntegrableOn (fun t => primeGammaWeight 0 t * (-v t)) (Ioi 0) := by
    exact hi.neg.congr (Eventually.of_forall fun t => (mul_neg (primeGammaWeight 0 t) (v t)).symm)
  obtain ⟨t,ht,he⟩ := late_prime_excursions hb hi' hm.neg hneg M T hM
  refine ⟨t,ht,?_⟩
  change v t < -(M*Real.exp (b/2*t))
  linarith only [he]

#print axioms riemannHypothesis_or_quartet_or_double_neutral_prime_excursions
#print axioms IsCriticalLadder.exists_double_neutral_opposite_prime_mass

end GaloisForLFunctions.ExclusionOfTheCriticalState
