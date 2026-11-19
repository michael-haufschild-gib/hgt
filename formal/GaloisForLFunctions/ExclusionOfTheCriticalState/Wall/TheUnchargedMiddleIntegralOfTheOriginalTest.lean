import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheMiddleTimeComplementOfTheOriginalPrimeTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedOrdinaryPrimeResponseAtEveryLateTime
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLateTimeEndpointOfTheTestedIntegerRows

/-!
# The uncharged middle integral of the original test

The ordinary-prime limit and the integrated square charge agree. Removing
that charge leaves a vanishing signed integral of the complete middle row.
The identity is independent of the sign chosen for the critical state.
-/

noncomputable section
open scoped Classical
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri

private theorem representatives_eq_or_neg {W V : ℝ} {F G Φ Ψ : ℝ → ℝ}
    (hW : 0<W) (hTW : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal))
    (hTV : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(V:EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hG : IsCriticalHalfLineGroundState V G)
    (hc : Continuous Φ) (hc' : Continuous Ψ) (he : F =ᵐ[volume] Φ) (he' : G =ᵐ[volume] Ψ) :
    Φ=Ψ ∨ Φ=fun t => -Ψ t := by
  have hWV : W=V := EReal.coe_injective (hTW.symm.trans hTV)
  subst V
  rcases criticalHalfLineGroundState_unique_up_to_sign hW hTW hF hG with h | h
  · exact Or.inl ((Continuous.ae_eq_iff_eq volume hc hc').mp (he.symm.trans (h.trans he')))
  apply Or.inr
  apply (Continuous.ae_eq_iff_eq volume hc hc'.neg).mp
  filter_upwards [he,he',h] with t h₁ h₂ h₃
  change F t= -G t at h₃
  rwa [h₁,h₂] at h₃

private theorem polar_neg (Ψ : ℝ → ℝ) (t : ℝ) :
    ordinaryPrimePolarError (fun u => -Ψ u) t = -ordinaryPrimePolarError Ψ t := by
  simp only [ordinaryPrimePolarError,ordinaryPrimeWave,Complex.ofReal_neg,mul_neg,tsum_neg,
    Complex.neg_re,integral_neg]
  ring

private theorem oriented_polar_limit (hr : ¬RiemannHypothesis) {W : ℝ} (hW : 0<W)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ) :
    let m := ∫ v, Φ v
    let p := fun T t => (m*ordinaryPrimePolarError Φ t)*fractionalPrimeTest (T-t)
    (∀ T : ℝ, 0≤T → Integrable (p T)) ∧ Tendsto (fun T => ∫ t, p T t) atTop
      (𝓝 ((riemannZeta (1/2)).re*m^2)) := by
  obtain ⟨V,G,Ψ,_,ht',hG,hc',he',hI,hlim,_⟩ := riemannHypothesis_or_ordinary_fractional_response.resolve_left hr
  let m := ∫ u, Ψ u
  have hi (T : ℝ) (hT : 0≤T) := (hI T hT).const_mul m
  have hl := hlim.const_mul m
  have hp : (∀ T : ℝ, 0≤T → Integrable (fun t => (m*ordinaryPrimePolarError Ψ t)*fractionalPrimeTest (T-t))) ∧
      Tendsto (fun T : ℝ => ∫ t, (m*ordinaryPrimePolarError Ψ t)*fractionalPrimeTest (T-t)) atTop
      (𝓝 ((riemannZeta (1/2)).re*m^2)) := by
    refine ⟨fun T hT => by simpa only [mul_assoc] using hi T hT,?_⟩
    have hv : m*((riemannZeta (1/2)).re*m)=(riemannZeta (1/2)).re*m^2 := by ring
    rw [← hv]
    apply hl.congr
    intro T
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => (mul_assoc m _ _).symm)
  rcases representatives_eq_or_neg hW ht ht' hF hG hc hc' he he' with e | e
  · rw [e]; exact hp
  · rw [e]; simpa only [polar_neg,integral_neg,neg_mul_neg,show ∀ x : ℝ, (-x)^2=x^2 by intro x; ring] using hp

private theorem complement_eq_far (Φ : ℝ → ℝ) (t : ℝ) :
    (∑' n : {j : ℕ // Real.exp t+criticalWallWidth t<j},
      (vonMangoldt n.val-1)*continuousIntegerAtom Φ n.val t)=criticalComplementBand Φ 0 t := by
  classical
  let S := {j : ℕ | Real.exp t+criticalWallWidth t<j}
  let f := fun j : ℕ => (vonMangoldt j-1)*continuousIntegerAtom Φ j t
  change (∑' n : S, f n)=_
  rw [tsum_subtype S]
  apply tsum_congr
  intro n
  by_cases h : n∈S
  · have hp : 0<n := by
      have hx : 0 < (n:ℝ) := lt_trans (add_pos_of_pos_of_nonneg (Real.exp_pos _) (mul_nonneg
        (Real.exp_pos _).le (Real.sqrt_nonneg t))) h
      exact Nat.cast_pos.mp hx
    rw [indicator_of_mem h,if_pos ⟨hp,h⟩]
  · rw [indicator_of_notMem h,if_neg (fun hc => h hc.2)]

private abbrev middle (T : ℝ) := Ioc (T/6) (6*T)

private theorem kernel_mass_in_middle :
    Tendsto (fun T : ℝ => ∫ t in middle T, fractionalPrimeTest (T-t)) atTop
      (𝓝 (∫ r, fractionalPrimeTest r)) := by
  let f := fun T r : ℝ => if T-r ∈ middle T then fractionalPrimeTest r else 0
  have hm (T : ℝ) : Measurable (f T) := by
    change Measurable (fun r => if T-r ∈ middle T then fractionalPrimeTest r else 0)
    exact measurable_fractionalPrimeTest.ite (measurableSet_Ioc.preimage (measurable_const.sub measurable_id)) measurable_const
  have hb (T r : ℝ) : ‖f T r‖ ≤ |fractionalPrimeTest r| := by
    rw [Real.norm_eq_abs]; dsimp only [f]
    by_cases h : T-r∈middle T <;> simp [h]
  have hp (r : ℝ) : Tendsto (fun T => f T r) atTop (𝓝 (fractionalPrimeTest r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2*|r|+1)] with T h
    have hm : T-r∈middle T := ⟨by linarith only [h,le_abs_self r,abs_nonneg r],
      by linarith only [h,neg_abs_le r,abs_nonneg r]⟩
    simp only [f,if_pos hm]
  have h := tendsto_integral_filter_of_dominated_convergence (fun r => |fractionalPrimeTest r|)
    (Eventually.of_forall fun T => (hm T).aestronglyMeasurable)
    (Eventually.of_forall fun T => Eventually.of_forall (hb T)) fractionalPrimeTest_mass.1.abs
    (Eventually.of_forall hp)
  apply h.congr
  intro T
  let v := (middle T).indicator (fun t => fractionalPrimeTest (T-t))
  calc (∫ r, f T r) = ∫ r, v (T-r) := by
          apply integral_congr_ae (Eventually.of_forall fun r => ?_)
          dsimp only [f,v]
          by_cases hr : T-r∈middle T <;> simp [hr]
       _ = ∫ t, v t := integral_sub_left_eq_self v volume T
       _ = _ := integral_indicator measurableSet_Ioc

private theorem orientation_neg (Ψ : ℝ → ℝ) (T : ℝ) :
    (∫ v, -Ψ v)*(∫ t in middle T, criticalComplementBand (fun v => -Ψ v) 0 t*fractionalPrimeTest (T-t)) =
    (∫ v, Ψ v)*(∫ t in middle T, criticalComplementBand Ψ 0 t*fractionalPrimeTest (T-t)) := by
  have hr (t : ℝ) : criticalComplementBand (fun u => -Ψ u) 0 t= -criticalComplementBand Ψ 0 t := by
    unfold criticalComplementBand
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    by_cases h : 0<n ∧ pastCriticalEdge n t <;> simp [h,continuousIntegerAtom]
  simp only [hr,neg_mul,integral_neg,mul_neg,neg_neg]

/-- Removing the square charge from the original middle complement leaves
a signed integral tending to zero at all late times on every forced state. -/
theorem riemannHypothesis_or_uncharged_middle_tends_to_zero : RiemannHypothesis ∨
    ∀ {W : ℝ}, 0<W → (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) →
    ∀ {F Φ : ℝ → ℝ}, IsCriticalHalfLineGroundState W F → Continuous Φ → F =ᵐ[volume] Φ →
    Tendsto (fun T : ℝ => (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
      criticalComplementBand Φ 0 t*fractionalPrimeTest (T-t))) atTop (𝓝 0) := by
  by_cases hr : RiemannHypothesis
  · exact Or.inl hr
  obtain ⟨V,G,Ψ,hV,ht',hG,hΨ,he',happrox⟩ := riemannHypothesis_or_original_test_on_middle_complement.resolve_left hr
  let m := ∫ v, Ψ v
  let P := fun t => m*ordinaryPrimePolarError Ψ t
  let C := fun t => m*(criticalComplementBand Ψ 0 t-m/2)
  let K := fun T t => fractionalPrimeTest (T-t)
  let Q := fun T t => (middle T).indicator C t*K T t
  let D := fun T t => P t*K T t-Q T t
  obtain ⟨hpi,hpl⟩ := oriented_polar_limit hr hV ht' hG hΨ he'
  have hmeas : Measurable C := by
    apply measurable_const.mul
    apply Measurable.sub _ measurable_const
    apply Measurable.tsum
    intro n
    have hedge : MeasurableSet {t : ℝ | pastCriticalEdge n t} := measurableSet_lt
      (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const
    exact Measurable.ite ((MeasurableSet.const _).inter hedge) (measurable_const.mul
      (measurable_const.mul (hΨ.measurable.comp (measurable_id.sub measurable_const)))) measurable_const
  have hmQ (T : ℝ) : Measurable (Q T) :=
    (hmeas.indicator measurableSet_Ioc).mul (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))
  have hdiff (ε : ℝ) (hε : 0<ε) : ∀ᶠ T in atTop, Integrable (D T) ∧ |∫ t, D T t|<ε := by
    filter_upwards [happrox ε hε,eventually_ge_atTop (0:ℝ)] with T h hT
    obtain ⟨hi,hb⟩ := h univ MeasurableSet.univ
    simp only [integrableOn_univ,setIntegral_univ,complement_eq_far] at hi hb
    have hn (t : ℝ) : |D T t| = |P t-(middle T).indicator C t| *K T t := by
      have hk : 0 ≤ K T t := mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
      dsimp only [D,Q]; rw [← sub_mul,abs_mul,abs_of_nonneg hk]
    have hI : Integrable (fun t => |D T t|) := by simpa only [hn,P,middle,C,m,K] using hi
    have hbound : (∫ t, |D T t|)<ε := by simpa only [hn,P,middle,C,m,K] using hb
    refine ⟨hI.mono' ((hpi T hT).aestronglyMeasurable.sub (hmQ T).aestronglyMeasurable)
      (Eventually.of_forall fun t => (Real.norm_eq_abs (D T t)).le),?_⟩
    exact (show |∫ t, D T t| ≤ ∫ t, |D T t| by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (D T)).trans_lt hbound
  have hdlim : Tendsto (fun T => ∫ t, D T t) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hdiff ε hε] with T h
    simpa only [Real.dist_eq,sub_zero] using h.2
  have hlim := (hpl.sub hdlim).add (kernel_mass_in_middle.const_mul (m^2/2))
  have hzero : (riemannZeta (1/2)).re*m^2-0+(m^2/2)*(∫ r, fractionalPrimeTest r)=0 := by
    rw [fractionalPrimeTest_mass.2]; ring
  rw [hzero] at hlim
  have hz : Tendsto (fun T => m*(∫ t in middle T, criticalComplementBand Ψ 0 t*K T t)) atTop (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [hdiff 1 zero_lt_one,eventually_ge_atTop (0:ℝ)] with T h hT
    let S := middle T
    have hqi : Integrable (Q T) := ((hpi T hT).sub h.1).congr (Eventually.of_forall fun t =>
      sub_sub_cancel (P t*K T t) (Q T t))
    have hpq : (∫ t, P t*K T t)-(∫ t, D T t)=∫ t, Q T t := by
      rw [← integral_sub (hpi T hT) h.1]
      exact integral_congr_ae (Eventually.of_forall fun t => sub_sub_cancel _ _)
    have heq (t : ℝ) : Q T t=S.indicator (fun t => C t*K T t) t := by
      by_cases ht : t∈S <;> simp [Q,show middle T=S from rfl,ht]
    have hci : IntegrableOn (fun t => C t*K T t) S := (integrable_indicator_iff measurableSet_Ioc).mp
      ((show Q T = _ from funext heq) ▸ hqi)
    have hki := (fractionalPrimeTest_mass.1.comp_sub_left T).integrableOn (s := S)
    change (∫ t, P t*K T t)-(∫ t, D T t)+(m^2/2)*(∫ t in S, K T t)=_
    rw [hpq,show Q T = _ from funext heq,integral_indicator measurableSet_Ioc,← integral_const_mul,
      ← integral_add hci (hki.const_mul (m^2/2)),← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only [C]; ring)
  apply Or.inr
  intro W hW ht F Φ hF hc he
  rcases representatives_eq_or_neg hW ht ht' hF hG hc hΨ he he' with e | e
  · rw [e]; exact hz
  · rw [e]; simpa only [orientation_neg] using hz

#print axioms riemannHypothesis_or_uncharged_middle_tends_to_zero
end GaloisForLFunctions.ExclusionOfTheCriticalState
