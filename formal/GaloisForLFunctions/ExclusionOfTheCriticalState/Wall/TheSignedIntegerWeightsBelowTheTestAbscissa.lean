import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheStateWeightsAfterTheOriginalFractionalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFirstAbsoluteMomentOfStateIncrements
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheCenteredFractionalTestBelowItsAbscissa
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.TheCriticalHalfLineStateHasNoBoundaryLaplaceZero
import GaloisForLFunctions.RHTower.WeilLagTwoSidedMeshSampling
import GaloisForLFunctions.RHTower.Sieve.CharacterWindowMass

/-!
# Signed integer weights below the test abscissa

Translation to the particle coordinate separates the half-charge from the
oscillatory part of the original fractional kernel.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

/-- The original oriented weight at exp(p), scaled by exp(T/2), reads the
fractional part at frequency exp(T-p) against the positive half tilt. -/
theorem scaled_testedIntegerWeight_eq_fractional_reading (Φ : ℝ → ℝ) (T p : ℝ) :
    Real.exp (T/2)*testedIntegerWeight Φ T p =
      (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v*Int.fract (Real.exp (T-p)*Real.exp (-v))) := by
  let g := fun v : ℝ => Real.exp (v/2)*Φ v*Int.fract (Real.exp (T-p)*Real.exp (-v))
  change _ = (∫ u, Φ u)*(∫ v, g v)
  rw [testedIntegerWeight,← integral_const_mul,← integral_sub_right_eq_self g p,← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hphase : Real.exp (T-p)*Real.exp (-(t-p)) = Real.exp (T-t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hscale : Real.exp (T/2)*Real.exp (-p/2)*Real.exp (-(T-t)/2)=Real.exp ((t-p)/2) := by
    rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have hroot : (Real.sqrt (Real.exp p))⁻¹ = Real.exp (-p/2) := by
    rw [← Real.exp_half,neg_div,Real.exp_neg]
  dsimp only [g]
  rw [continuousIntegerAtom,Real.log_exp,hroot,fractionalPrimeTest,hphase]
  linear_combination (∫ u, Φ u)*Φ (t-p)*Int.fract (Real.exp (T-t))*hscale

private theorem centered_reading {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hs : ∀ v, 0 ≤ v → Φ v = 0) (hi : Integrable fun v => Real.exp (v/2)*Φ v) (y : ℝ) :
    (∫ v, Real.exp (v/2)*Φ v*Int.fract (y*Real.exp (-v))) -
      (1/2)*(∫ v, Real.exp (v/2)*Φ v) = ∫ z, Φ (-z)*centeredLogFraction y z := by
  let g := fun v : ℝ => Real.exp (v/2)*Φ v
  have hm : Measurable g := (Real.measurable_exp.comp (measurable_id.div_const 2)).mul hc.measurable
  have hf : Integrable fun v : ℝ => g v*Int.fract (y*Real.exp (-v)) := by
    refine hi.abs.mono' ((hm.mul (measurable_fract.comp (measurable_const.mul
      (Real.measurable_exp.comp measurable_neg)))).aestronglyMeasurable) (Eventually.of_forall fun v => ?_)
    change |g v*Int.fract _| ≤ |g v|
    rw [abs_mul,abs_of_nonneg (Int.fract_nonneg (y*Real.exp (-v)))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  change (∫ v, g v*Int.fract (y*Real.exp (-v)))-(1/2)*(∫ v, g v) = _
  rw [← integral_const_mul,← integral_sub hf (hi.const_mul (1/2)),
    ← integral_neg_eq_self (fun v => g v*Int.fract (y*Real.exp (-v))-(1/2)*g v) volume]
  apply integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Ioi (0:ℝ)
  · simp only [g,neg_neg,centeredLogFraction,indicator_of_mem hz,_root_.RHTower.burnolCenteredSawtooth]
    ring
  · rw [centeredLogFraction,indicator_of_notMem hz]
    simp only [g,hs _ (neg_nonneg.mpr (le_of_not_gt hz)),mul_zero,zero_mul,sub_zero]

private theorem reflected_increment {F Φ : ℝ → ℝ} (he : F =ᵐ[volume] Φ) (s : ℝ) :
    (∫ x, |Φ (-(x-s))-Φ (-x)|) = ∫ u, |F u-F (u+s)| := by
  rw [← integral_neg_eq_self (fun x => |Φ (-(x-s))-Φ (-x)|) volume]
  have hshift := (measurePreserving_add_right volume s).quasiMeasurePreserving.ae he
  apply integral_congr_ae
  filter_upwards [he,hshift] with u hu hv
  change F (u+s) = Φ (u+s) at hv
  rw [show -(-u-s)=u+s by ring,neg_neg,hu,hv,abs_sub_comm]

/-- Every nonnegative real Laplace tilt has the orientation of the total charge. -/
theorem criticalState_positive_tilt_charge {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ)
    {s : ℝ} (hs : 0 ≤ s) : 0 < (∫ u, Φ u)*(∫ u, Real.exp (s*u)*Φ u) := by
  let L := fun x : ℝ => (negativeHalfLineLaplace (cx F) (x : ℂ)).re
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc : ContinuousOn L (Icc 0 s) := by
    intro x hx
    have h := differentiableAt_laplace_of_sq hd hd.exponential (w := (x : ℂ))
      (by simp only [Complex.ofReal_re]; linarith only [hx.1])
    exact (Complex.continuous_re.continuousAt.comp
      (h.continuousAt.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hn (x : ℝ) (hx : x ∈ Icc 0 s) : L x ≠ 0 := by
    intro hz
    apply criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF
      (show 0 ≤ (x : ℂ).re from hx.1)
    dsimp only [L] at hz
    rw [negativeHalfLineLaplace_ofReal,Complex.ofReal_re] at hz
    rw [negativeHalfLineLaplace_ofReal,hz,Complex.ofReal_zero]
  have hL (x : ℝ) : L x = ∫ v, Real.exp (x*v)*Φ v := by
    simp only [L,negativeHalfLineLaplace_ofReal,Complex.ofReal_re]
    exact integral_congr_ae (he.mono fun u hu =>
      (congrArg (fun a : ℝ => a * Real.exp (x*u)) hu).trans (mul_comm (Φ u) _))
  have h := _root_.HTGeometry.mul_pos_of_ne_zero_on_Icc hs hc hn
  simpa only [hL,zero_mul,Real.exp_zero,one_mul] using h

/-- Below the test abscissa, the scaled oriented integer weight approaches the
half tilt with error little-o of the square root of the frequency ratio n/X. -/
theorem criticalState_signed_weight_below_abscissa {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
    0 < a ∧ ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 0 < Y ∧ ∀ T p : ℝ, Y ≤ Real.exp (T-p) →
      |Real.exp (T/2)*testedIntegerWeight Φ T p-a| ≤ ε*Real.exp ((p-T)/2) := by
  let m := ∫ u, Φ u
  have hhalf (v : ℝ) : (1/2)*v=v/2 := by ring
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have htlt : Integrable fun v : ℝ => Real.exp (v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hd (by norm_num : (-4:ℝ)<1/2)).congr
    filter_upwards [he] with u hu
    rw [hu,hhalf,mul_comm]
  have hpos := criticalState_positive_tilt_charge hW ht hF he (by norm_num : (0:ℝ)≤1/2)
  simp only [hhalf] at hpos
  refine ⟨div_pos hpos (by norm_num),fun ε hε => ?_⟩
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let δ := ε/(2*(1+|m|))
  have hden : 0 < 2*(1+|m|) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hsmall := (criticalState_tendsto_L1_increment_div_sqrt hW ht hF).eventually_lt_const hδ
  obtain ⟨η,hη,hmod⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨2/η,div_pos (by norm_num) hη,fun T p hy => ?_⟩
  let y := Real.exp (T-p)
  have hy0 : 0 < y := Real.exp_pos _
  have hb : 1/y < η := by
    apply (div_lt_iff₀ hy0).mpr
    have hyη := (div_le_iff₀ hη).mp hy
    linarith only [hyη]
  have hinc (s : ℝ) (h : s ∈ Ioc 0 (1/y)) :
      (∫ x, |Φ (-(x-s))-Φ (-x)|) ≤ δ*Real.sqrt (1/y) := by
    rw [reflected_increment he]
    have hquot : (∫ u, |F u-F (u+s)|)/Real.sqrt s < δ := hmod ⟨h.1,h.2.trans_lt hb⟩
    exact ((div_lt_iff₀ (Real.sqrt_pos.2 h.1)).mp hquot).le.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h.2) hδ.le)
  have hk := centeredLogFraction_bound_of_increments (f := fun x => Φ (-x))
    (hc.measurable.comp measurable_neg) (hd.integrable.congr he).comp_neg hy0 hinc
  have hprice : Real.exp (T/2)*testedIntegerWeight Φ T p -
      m*(∫ v, Real.exp (v/2)*Φ v)/2 = m*(∫ z, Φ (-z)*centeredLogFraction y z) := by
    rw [scaled_testedIntegerWeight_eq_fractional_reading,← centered_reading hc hs htlt y]
    dsimp only [m,y]; ring
  have hroot : Real.sqrt (1/y)=Real.exp ((p-T)/2) := by
    dsimp only [y]; rw [one_div,← Real.exp_neg,← Real.exp_half,neg_sub]
  change |Real.exp (T/2)*testedIntegerWeight Φ T p-m*(∫ v, Real.exp (v/2)*Φ v)/2| ≤ _
  rw [hprice,abs_mul,← hroot]
  apply (mul_le_mul_of_nonneg_left hk (abs_nonneg m)).trans
  have hcst := (div_mul_cancel₀ ε hden.ne' : δ*(2*(1+|m|))=ε)
  calc |m| *(2*(δ*Real.sqrt (1/y))) = (2*|m| *δ)*Real.sqrt (1/y) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hcst,hδ] : 2*|m| *δ ≤ ε)
         (Real.sqrt_nonneg _)

/-- Failure of RH forces a single state with positive lower-range half tilt
and a uniform square-root error for the original oriented integer weights. -/
theorem riemannHypothesis_or_signed_weight_below_abscissa : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
      0 < a ∧ ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 0 < Y ∧ ∀ T p : ℝ, Y ≤ Real.exp (T-p) →
        |Real.exp (T/2)*testedIntegerWeight Φ T p-a| ≤ ε*Real.exp ((p-T)/2) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  obtain ⟨_,_,Φ,hc,he,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,criticalState_signed_weight_below_abscissa hW ht hF hc he⟩

#print axioms criticalState_positive_tilt_charge
#print axioms riemannHypothesis_or_signed_weight_below_abscissa

/-- The signed sum of all original tested weights through N reads the
ordinary Chebyshev discrepancy with the positive half-tilt coefficient.
The remainder is little-o of N√N/X uniformly as X/N tends to infinity. -/
theorem criticalState_lower_integer_sum {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 0 < Y ∧ ∀ (T : ℝ) (N : ℕ), 0 < N →
      Y ≤ Real.exp (T-Real.log N) →
      |(∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) -
        a*Real.exp (-T/2)*(Chebyshev.psi N-N)| ≤ ε*(N*Real.sqrt N)*Real.exp (-T) := by
  let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
  dsimp only
  intro ε hε
  obtain ⟨Y,hY,hy⟩ := (criticalState_signed_weight_below_abscissa hW ht hF hc he).2
    (ε/7) (div_pos hε (by norm_num))
  refine ⟨Y,hY,fun T N _ hratio => ?_⟩
  let A := Finset.Ioc 0 N
  let c := fun n : ℕ => vonMangoldt n-1
  let w := fun n : ℕ => testedIntegerWeight Φ T (Real.log n)
  have hψ := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (Nat.cast_nonneg (α := ℝ) N)
  simp only [Chebyshev.psi_zero,sub_zero,Nat.floor_zero,Nat.floor_natCast] at hψ
  have hsum : ∑ n ∈ A, c n = Chebyshev.psi N-N := by
    simp only [A,c,Finset.sum_sub_distrib,← hψ,Finset.sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
  have habs : ∑ n ∈ A, |c n| ≤ 7*N := by
    calc ∑ n ∈ A, |c n| ≤ ∑ n ∈ A, (vonMangoldt n+1) := Finset.sum_le_sum fun n _ => by
           simpa only [abs_of_nonneg vonMangoldt_nonneg,abs_one] using abs_sub (vonMangoldt n) (1:ℝ)
         _ = Chebyshev.psi N+N := by
           simp only [A,Finset.sum_add_distrib,← hψ,Finset.sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
         _ ≤ _ := by linarith only [_root_.RHTower.psi_nat_le_six_mul N]
  let d := ε/7*Real.sqrt N*Real.exp (-T)
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hw (n : ℕ) (hn : n ∈ A) : |w n-a*Real.exp (-T/2)| ≤ d := by
    obtain ⟨hn0,hnN⟩ := Finset.mem_Ioc.mp hn
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
    have hl := Real.log_le_log hn' (Nat.cast_le.mpr hnN)
    have h := hy T (Real.log n) (hratio.trans (Real.exp_le_exp.mpr (sub_le_sub_left hl T)))
    have hid : w n-a*Real.exp (-T/2) =
        Real.exp (-T/2)*(Real.exp (T/2)*w n-a) := by
      rw [mul_sub,← mul_assoc,← Real.exp_add,show -T/2+T/2=0 by ring,Real.exp_zero,one_mul,mul_comm a]
    have hx : Real.exp (-T/2)*Real.exp ((Real.log n-T)/2) = Real.sqrt n*Real.exp (-T) := by
      rw [← Real.exp_log hn',← Real.exp_half,Real.log_exp,← Real.exp_add,← Real.exp_add]
      congr 1; ring
    rw [hid,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (-T/2)*(ε/7*Real.exp ((Real.log n-T)/2)) :=
           mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
         _ = ε/7*Real.sqrt n*Real.exp (-T) := by
           linear_combination (ε/7)*hx
         _ ≤ d := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hnN)) (by positivity))
           (Real.exp_pos _).le
  change |(∑ n ∈ A, c n*w n)-a*Real.exp (-T/2)*(Chebyshev.psi N-N)| ≤ _
  rw [← hsum,mul_comm (a*Real.exp (-T/2)),Finset.sum_mul,← Finset.sum_sub_distrib]
  calc _ ≤ ∑ n ∈ A, |c n*w n-c n*(a*Real.exp (-T/2))| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ n ∈ A, |c n| *d := Finset.sum_le_sum fun n hn => by
         rw [← mul_sub,abs_mul]; exact mul_le_mul_of_nonneg_left (hw n hn) (abs_nonneg _)
       _ = (∑ n ∈ A, |c n|)*d := (Finset.sum_mul ..).symm
       _ ≤ (7*N)*d := mul_le_mul_of_nonneg_right habs hd
       _ = _ := by dsimp only [d]; ring

#print axioms criticalState_lower_integer_sum
end GaloisForLFunctions.ExclusionOfTheCriticalState
