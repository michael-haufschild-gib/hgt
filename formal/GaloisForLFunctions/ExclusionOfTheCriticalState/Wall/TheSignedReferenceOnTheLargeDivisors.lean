import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLargeDivisorMomentsOfThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeVarianceAfterACommonSieve
import GaloisForLFunctions.HTGeometry.ExpRayL2

/-!
# The signed reference row above the fourth-root divisor cutoff

For the centered Mangoldt row, removing divisors through exp(t/4) and keeping
the entire ordered complement costs exponentially little absolute late mass.
The integer reference is subtracted at every integer, and the square charge
survives in both rows.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem double_tilt_absolute_tail {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : MemLp (fun t : ℝ => Real.exp ((2*r)*t)*g t) 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ U : ℝ, 0 ≤ U → IntegrableOn g (Ioi U) ∧
      (∫ t in Ioi U, |g t|) ≤ B*Real.exp (-(r*U)) := by
  have h₁ : MemLp (fun t : ℝ => Real.exp ((2*r)*t)*g t) 2 (volume.restrict (Ioi 0)) :=
    hg.mono_measure Measure.restrict_le_self
  have h₂ : MemLp (fun t : ℝ => Real.exp (-(r*t))) 2 (volume.restrict (Ioi 0)) := by
    simpa only [norm_expRay,Complex.ofReal_re] using (memLp_two_expRay_restrict
      (w := (r:ℂ)) hr 0).norm
  have h := (memLp_one_iff_integrable.mp (h₁.mul' (r := 1) h₂)).norm
  have hi : IntegrableOn (fun t : ℝ => Real.exp (r*t)*|g t|) (Ioi 0) := by
    apply h.congr
    refine Eventually.of_forall fun t => ?_
    change ‖Real.exp (-(r*t))*(Real.exp ((2*r)*t)*g t)‖=_
    rw [← mul_assoc,← Real.exp_add,show -(r*t)+(2*r)*t=r*t by ring,Real.norm_eq_abs,abs_mul,
      abs_of_pos (Real.exp_pos _)]
  have hm : AEStronglyMeasurable g volume := by
    apply ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-((2*r)*t)))).aestronglyMeasurable.mul hg.1).congr
    refine Eventually.of_forall fun t => ?_
    change Real.exp (-((2*r)*t))*(Real.exp ((2*r)*t)*g t)=g t
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  refine ⟨_,integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _),
    fun U hU => ⟨?_,(abs_tail_le_exp_neg_mul hr.le hU hi).trans_eq (mul_comm ..)⟩⟩
  apply (hi.mono_set (Ioi_subset_Ioi hU)).mono' (hm.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := U))] with t ht
  rw [Real.norm_eq_abs]
  exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg hr.le (hU.trans ht.le)))

/-- Removing the small divisors from the logarithmic Möbius sum keeps the
literal integer and square references with an exponentially small absolute
tail on every continuous critical representative. -/
theorem criticalState_large_divisor_signed_tail {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ (L : ℝ → ℝ) (B : ℝ), 0 ≤ B ∧
      let m := ∫ u, Φ u
      let M := ∫ u, Real.exp (-u/2)*Φ u
      let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
      (∀ t : ℝ, 0 ≤ t → Tendsto
        (lateDivisorPartial (fun d => -((moebius d:ℤ):ℝ)*Real.log d) Φ M (1/4) t) atTop (𝓝 (L t))) ∧
      ∀ U : ℝ, 0 ≤ U → IntegrableOn (fun t => S t-(L t-m/2)) (Ioi U) ∧
        (∫ t in Ioi U, |S t-(L t-m/2)|) ≤ B*Real.exp (-U/16) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hwall,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let M := ∫ u, Real.exp (-u/2)*Φ u
  let m := ∫ u, Φ u
  let E := fun t : ℝ => (∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-Real.exp (t/2)*M
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*M
  let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
  obtain ⟨_,L,_,hsmall,hL⟩ := criticalState_large_divisor_moments hW ht hF hc he hwall hC hb
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num)
  have hD := criticalState_subcritical_integer_error hW ht hF hc he hC hb
    (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num)
  change MemLp (fun t : ℝ => Real.exp ((1/8)*t)*(E t-L t)) 2 at hsmall
  change MemLp (fun t : ℝ => Real.exp ((1/8)*t)*D t) 2 at hD
  have hsplit (t : ℝ) : S t = E t - D t - m/2 := by
    dsimp only [S,E,D]
    rw [centred_mangoldt_atom_sum_split hb t,mangoldt_atom_sum_split hb t]
    ring
  let g := fun t => S t-(L t-m/2)
  have hg : MemLp (fun t : ℝ => Real.exp ((2*(1/16))*t)*g t) 2 := by
    refine MemLp.ae_eq ?_ (hsmall.sub hD)
    refine Eventually.of_forall fun t => ?_
    change Real.exp ((1/8)*t)*(E t-L t)-Real.exp ((1/8)*t)*D t=_
    dsimp only [g]; rw [hsplit,show (2*(1/16):ℝ)=1/8 by norm_num]; ring
  obtain ⟨B,hB,hcost⟩ := double_tilt_absolute_tail (by norm_num : (0:ℝ)<1/16) hg
  refine ⟨L,B,hB,fun t h => (hL t h).2,fun U hU => ?_⟩
  simpa only [show -((1/16)*U) = -U/16 by ring] using hcost U hU

/-- The complete fourth-root complement, including every boundary index in its
original increasing order. The estimate is in total absolute mass, hence
survives restriction to late time windows. -/
theorem riemannHypothesis_or_large_divisor_signed_tail : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (L : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧
      let m := ∫ u, Φ u
      let M := ∫ u, Real.exp (-u/2)*Φ u
      let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
      (∀ t : ℝ, 0 ≤ t → Tendsto
        (lateDivisorPartial (fun d => -((moebius d:ℤ):ℝ)*Real.log d) Φ M (1/4) t) atTop (𝓝 (L t))) ∧
      ∀ U : ℝ, 0 ≤ U → IntegrableOn (fun t => S t-(L t-m/2)) (Ioi U) ∧
        (∫ t in Ioi U, |S t-(L t-m/2)|) ≤ B*Real.exp (-U/16) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨L,B,hB,h⟩ := criticalState_large_divisor_signed_tail hW ht hF hc he
  exact Or.inr ⟨W₀,F,Φ,L,B,hW,ht,hF,hc,he,hB,h⟩

#print axioms riemannHypothesis_or_large_divisor_signed_tail
end GaloisForLFunctions.ExclusionOfTheCriticalState
