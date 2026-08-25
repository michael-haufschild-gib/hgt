import GaloisForLFunctions.HTGeometry.RealAnalyticInnerPhase
import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiAEWeakPhase
import GaloisForLFunctions.HTGeometry.ContinuousPhaseLiftUniqueness
import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram

/-!
# Real-analytic inner factorizations produce weak-phase witnesses

This module is the phase receiver in the Makarov--Poltoratski basic criterion.  A real-analytic
inner factor contributes a monotone phase.  A continuous outer phase with little weak-`L¹`
Poisson tails contributes the outer coordinate.  An a.e. exponential factorization determines the
additive phase identity up to one constant multiple of `2π`; continuous phase-lift uniqueness
absorbs that constant without changing the endpoint class.
-/

open Complex Filter MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Continuous real phases whose exponentials agree a.e. have exponentials agreeing everywhere. -/
theorem exp_phase_eq_of_ae_eq_of_continuous
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : (fun x => Complex.exp ((f x : ℂ) * I)) =ᵐ[volume]
      fun x => Complex.exp ((g x : ℂ) * I)) :
    ∀ x, Complex.exp ((f x : ℂ) * I) = Complex.exp ((g x : ℂ) * I) := by
  let d : ℝ → ℂ := fun x =>
    Complex.exp ((f x : ℂ) * I) - Complex.exp ((g x : ℂ) * I)
  have hd : Continuous d :=
    (((Complex.continuous_ofReal.comp hf).mul continuous_const).cexp).sub
      (((Complex.continuous_ofReal.comp hg).mul continuous_const).cexp)
  have hdzero : d =ᵐ[volume] 0 := hfg.mono fun x hx => by simp [d, hx]
  intro x
  have hx : x ∈ (volume : Measure ℝ).support := by
    rw [Measure.support_eq_univ]
    exact mem_univ x
  exact sub_eq_zero.mp
    (continuous_eq_zero_on_support_of_ae_eq_zero volume d hd hdzero x hx)

/-- A real-analytic inner times a continuous weak outer phase supplies the exact a.e. phase
coordinate required by the Makarov--Poltoratski endpoint obstruction. -/
noncomputable def aeSmirnovToeplitzWeakPhaseWitness_of_realAnalyticInner_factorization
    {γ h : ℝ → ℝ} {theta : ℂ → ℂ}
    (hγ : Continuous γ)
    (hthetaAnalytic : ∀ x : ℝ, AnalyticAt ℂ theta (x : ℂ))
    (hthetaUnit : ∀ x : ℝ, ‖theta (x : ℂ)‖ = 1)
    (hthetaContract : ∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1)
    (hhContinuous : Continuous h)
    (hhWeak : PoissonWeakL1LittleO h)
    (hfactor : (fun x =>
      Complex.exp ((γ x : ℂ) * I) * theta (x : ℂ)) =ᵐ[volume]
        fun x => Complex.exp ((h x : ℂ) * I)) :
    AESmirnovToeplitzWeakPhaseWitness γ := by
  let alpha := realAnalyticInnerPhase theta
  let f : ℝ → ℝ := fun x => γ x + alpha x
  let c : ℝ := f 0 - h 0
  let hc : ℝ → ℝ := fun x => h x + c
  have halpha : Continuous alpha := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hasDerivAt_realAnalyticInnerPhase hthetaAnalytic x).continuousAt
  have hf : Continuous f := hγ.add halpha
  have hhc : Continuous hc := hhContinuous.add continuous_const
  have hfactor' : (fun x => Complex.exp ((f x : ℂ) * I)) =ᵐ[volume]
      fun x => Complex.exp ((h x : ℂ) * I) := by
    filter_upwards [hfactor] with x hx
    rw [show Complex.exp ((f x : ℂ) * I) =
        Complex.exp ((γ x : ℂ) * I) * Complex.exp ((alpha x : ℂ) * I) by
      rw [← Complex.exp_add]
      congr 1
      simp [f, add_mul]]
    rw [exp_realAnalyticInnerPhase hthetaAnalytic hthetaUnit x]
    exact hx
  have hexp := exp_phase_eq_of_ae_eq_of_continuous hf hhContinuous hfactor'
  have hcexp : Complex.exp ((c : ℂ) * I) = 1 := by
    have h0 := hexp 0
    calc
      Complex.exp ((c : ℂ) * I) =
          Complex.exp ((f 0 : ℂ) * I) / Complex.exp ((h 0 : ℂ) * I) := by
        rw [← Complex.exp_sub]
        congr 1
        simp [c, sub_mul]
      _ = 1 := by rw [h0]; exact div_self (Complex.exp_ne_zero _)
  have hexpCorrected : ∀ x,
      Complex.exp ((f x : ℂ) * I) = Complex.exp ((hc x : ℂ) * I) := by
    intro x
    rw [show Complex.exp ((hc x : ℂ) * I) =
        Complex.exp ((h x : ℂ) * I) * Complex.exp ((c : ℂ) * I) by
      rw [← Complex.exp_add]
      congr 1
      simp [hc, add_mul], hcexp, mul_one]
    exact hexp x
  have hbase : f 0 = hc 0 := by simp [hc, c]
  have hphase : f = hc := eq_of_exp_eq_of_eq_at hf hhc hexpCorrected hbase
  refine
    { innerPhase := alpha
      outerHilbertPhase := hc
      innerPhase_monotone :=
        monotone_realAnalyticInnerPhase hthetaAnalytic hthetaUnit hthetaContract
      phase_balance_ae := Filter.Eventually.of_forall fun x => congrFun hphase x
      outerHilbertPhase_weakL1LittleO := ?_ }
  exact hhWeak.add (poissonWeakL1LittleO_of_abs_le (f := fun _ => c)
    (C := |c|) fun _ => le_rfl)

end

end GaloisForLFunctions.HTGeometry
