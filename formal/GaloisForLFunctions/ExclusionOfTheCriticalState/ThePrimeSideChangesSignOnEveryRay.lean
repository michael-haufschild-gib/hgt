import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LandauTailSignObstruction
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLeftContinuationHasSquareIntegrableVerticalTraces
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.StateProductMultiplicity
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheContinuationIsPolynomiallyBoundedOffTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState
import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockTailSeparation

/-!
# The prime side changes sign on every ray

Both the full Hardy datum beyond the wall and its prime-minus-pole part
have both signs on every positive tail, in the almost-everywhere sense.

Reflecting and damping the datum gives an integrable real profile. Landau's
theorem and regularity of the state continuation along the real axis would
make a one-signed profile's transform entire. The entire state product would
then retain the full multiplicity of every Xi zero, contradicting the exact
one-order loss at a seen zero. For the prime-minus-pole wave, the same
argument forces continuation across the left half-strip, contradicting
the pole at a seen left zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem expRay_real_eq (a v : ℝ) :
    expRay (a : ℂ) v = (Real.exp (-a*v) : ℂ) := by
  rw [expRay,← Complex.ofReal_mul,← Complex.ofReal_neg,← Complex.ofReal_exp,neg_mul]

/-- Reflection and extra exponential damping turn a half-line Hardy datum into an integrable real profile. -/
private def reflectedRealDatum (D : Lp ℂ 2 halfLineLaplaceMeasure) (u : ℝ) : ℝ :=
  (Iio 0).indicator (fun v => Real.exp v*(D (-v)).re) u

private theorem measurable_reflectedRealDatum (D : Lp ℂ 2 halfLineLaplaceMeasure) :
    Measurable (reflectedRealDatum D) :=
  ((Real.measurable_exp.mul ((Lp.stronglyMeasurable D).measurable.comp measurable_neg).re).indicator
    measurableSet_Iio)

private theorem reflectedRealDatum_support (D : Lp ℂ 2 halfLineLaplaceMeasure)
    (u : ℝ) (hu : 0 ≤ u) : reflectedRealDatum D u = 0 :=
  indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt.mpr hu) _

private theorem integrable_reflectedRealDatum (D : Lp ℂ 2 halfLineLaplaceMeasure) :
    Integrable (reflectedRealDatum D) := by
  have hi := integrableOn_laplaceRay (Lp.memLp D) (w := (1 : ℂ)) (by norm_num)
  have hind := IntegrableOn.integrable_indicator hi.re measurableSet_Ioi
  have hneg := ((Measure.measurePreserving_neg volume).integrable_comp
    hind.aestronglyMeasurable).mpr hind
  refine hneg.congr (Eventually.of_forall fun u => ?_)
  change (Ioi (0 : ℝ)).indicator (fun v => (D v*expRay ((1 : ℝ) : ℂ) v).re) (-u) =
    reflectedRealDatum D u
  by_cases hu : u < 0
  · rw [indicator_of_mem (show -u ∈ Ioi (0:ℝ) from neg_pos.mpr hu),
      reflectedRealDatum,indicator_of_mem (show u ∈ Iio (0:ℝ) from hu),expRay_real_eq]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [show -(1 : ℝ)*(-u) = u by ring]
    ring
  · rw [indicator_of_notMem (show -u ∉ Ioi (0:ℝ) from fun hh => hu (neg_pos.mp hh)),
      reflectedRealDatum_support D u (not_lt.mp hu)]

private theorem laplace_reflectedRealDatum (D : Lp ℂ 2 halfLineLaplaceMeasure)
    {x : ℝ} (hx : 0 < x) :
    negativeHalfLineLaplace (cx (reflectedRealDatum D)) (x : ℂ) =
      ((laplaceRay D ((x+1 : ℝ) : ℂ)).re : ℂ) := by
  have hi := integrableOn_laplaceRay (Lp.memLp D) (w := ((x+1 : ℝ) : ℂ))
    (by simp only [Complex.ofReal_re]; linarith only [hx])
  have he : (fun u => reflectedRealDatum D u*Real.exp (x*u)) =
      fun u : ℝ => (Ioi (0:ℝ)).indicator
        (fun v => (D v*expRay ((x+1 : ℝ) : ℂ) v).re) (-u) := by
    funext u
    by_cases hu : u < 0
    · rw [reflectedRealDatum,indicator_of_mem (show u ∈ Iio (0:ℝ) from hu),
        indicator_of_mem (show -u ∈ Ioi (0:ℝ) from neg_pos.mpr hu),expRay_real_eq]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      calc
        _ = (D (-u)).re*Real.exp (u+x*u) := by rw [Real.exp_add]; ring
        _ = _ := by congr 2; ring
    · rw [reflectedRealDatum_support D u (not_lt.mp hu),zero_mul,
        indicator_of_notMem (show -u ∉ Ioi (0:ℝ) from fun hh => hu (neg_pos.mp hh))]
  rw [negativeHalfLineLaplace_ofReal,he,integral_neg_eq_self,integral_indicator measurableSet_Ioi]
  congr 1
  exact integral_re hi

private theorem signed_tail_reflectedRealDatum {D : Lp ℂ 2 halfLineLaplaceMeasure}
    {s T : ℝ} (h : ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ s*(D v).re) :
    ∀ᵐ u ∂volume.restrict (Iio (-(max T 0))), 0 ≤ s*reflectedRealDatum D u := by
  have hfull := (ae_restrict_iff' measurableSet_Ioi).mp h
  have hneg := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hfull
  filter_upwards [ae_restrict_of_ae hneg,ae_restrict_mem measurableSet_Iio] with u hu hmem
  have hu' : u < -(max T 0) := hmem
  have hu0 : u < 0 := by linarith only [hu',le_max_right T 0]
  have huT : T < -u := by linarith only [hu',le_max_left T 0]
  rw [reflectedRealDatum,indicator_of_mem (show u ∈ Iio (0:ℝ) from hu0)]
  calc
    0 ≤ Real.exp u*(s*(D (-u)).re) := mul_nonneg (Real.exp_pos _).le (hu huT)
    _ = s*(Real.exp u*(D (-u)).re) := by ring

/-- The state continuation is regular at every real point. -/
private theorem analyticAt_stateMeromorphic_real {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    AnalyticAt ℂ (stateMeromorphic W₀ F) (x : ℂ) := by
  let U := {w : ℂ | xi (w+17/2) ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun
    (xi_differentiable.continuous.comp (continuous_id.add continuous_const)) continuous_const
  have hd : DifferentiableOn ℂ (stateMeromorphic W₀ F) U := by
    intro w hw
    have hxi : xi (1/2+(w+8)) ≠ 0 := by rw [xi_half_add_shift]; exact hw
    have h := differentiableAt_globalRemainder_of_xi_ne_zero hF hxi
    exact ((h.comp w (differentiableAt_id.add_const (8:ℂ))).neg.div_const _).differentiableWithinAt
  apply hd.analyticAt (hU.mem_nhds ?_)
  change xi ((x:ℂ)+17/2) ≠ 0
  have he : (x:ℂ)+17/2 = ((x+17/2 : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  exact xi_ne_zero_of_real _

private theorem criticalState_stateMeromorphic_real {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (x : ℝ) :
    stateMeromorphic W₀ F (x : ℂ) = ((stateMeromorphic W₀ F (x : ℂ)).re : ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha : AnalyticOnNhd ℝ (fun t : ℝ => (stateMeromorphic W₀ F (t:ℂ)).im) univ := by
    intro t _
    exact (Complex.imCLM.analyticAt _).comp
      (analyticAt_ofReal_comp (analyticAt_stateMeromorphic_real hd t))
  have hev : (fun t : ℝ => (stateMeromorphic W₀ F (t:ℂ)).im) =ᶠ[𝓝 (0:ℝ)] 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (-4:ℝ)<0 by norm_num)] with t ht'
    change -4 < t at ht'
    change (stateMeromorphic W₀ F (t:ℂ)).im = 0
    rw [stateMeromorphic_eq_levyContinuation (by simp only [Complex.ofReal_re]; linarith only [ht']),
      levyContinuation_eq_laplace hW ht hF (by simpa only [Complex.ofReal_re] using ht'),
      negativeHalfLineLaplace_ofReal,Complex.ofReal_im]
  have him := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0:ℝ)) hev (mem_univ x)
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Pi.zero_apply,Complex.ofReal_im] using him


/-- An entire reflected transform cannot represent the critical state beyond the wall. -/
private theorem criticalState_no_entire_reflected_transform {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (heq : ∀ x : ℝ, x < -10 → H (x:ℂ) = stateMeromorphic W₀ F (x:ℂ)) : False := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let P : ℂ → ℂ := fun w => xi (w+17/2)*H w
  have hP : Differentiable ℂ P :=
    (xi_differentiable.comp (differentiable_id.add_const _)).mul hH
  have hprod : stateXiProduct W₀ F = P := by
    have hf : ∃ᶠ w : ℂ in 𝓝[≠] (-11:ℂ), stateXiProduct W₀ F w = P w := by
      have hev : ∀ᶠ x : ℝ in 𝓝[≠] (-11:ℝ), stateXiProduct W₀ F (x:ℂ) = P (x:ℂ) := by
        filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds
          (show (-11:ℝ) < -10 by norm_num))] with x hx
        have hxi : xi ((x:ℂ)+17/2) ≠ 0 := by
          have he : (x:ℂ)+17/2 = ((x+17/2:ℝ):ℂ) := by push_cast; ring
          rw [he]
          exact xi_ne_zero_of_real _
        rw [stateXiProduct_eq hd hxi]
        dsimp only [P]
        rw [heq x hx]
      simpa using (tendsto_ofReal_nhdsNE (-11)).frequently hev.frequently
    have hA : AnalyticOnNhd ℂ (stateXiProduct W₀ F) univ :=
      fun w _ => (differentiable_stateXiProduct hd).analyticAt w
    have hB : AnalyticOnNhd ℂ P univ := fun w _ => hP.analyticAt w
    have hEq := hA.eqOn_of_preconnected_of_frequently_eq
      hB isPreconnected_univ (mem_univ (-11:ℂ)) hf
    exact funext fun w => hEq (mem_univ w)
  obtain ⟨ρ,hζ,hρ,hρhalf⟩ :=
    exists_zetaZero_re_gt_half_of_not_riemannHypothesis (not_riemannHypothesis_of_threshold ht)
  let z : ℂ := ρ-1/2
  have hxi : xi (1/2+z) = 0 := by
    have he : (1:ℂ)/2+z = ρ := by dsimp only [z]; ring
    rw [he]
    exact (xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith only [hρ]) (by
      intro e; rw [e] at hρhalf; norm_num at hρhalf)).mpr hζ
  have hz0 : 0 ≤ z.re := by dsimp only [z]; simp only [Complex.sub_re,re_one_half]; linarith
  have hL := criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF hz0
  apply hL
  apply (le_analyticOrderAt_stateXiProduct_iff hW hd hxi).mp
  rw [hprod]
  have hξ : AnalyticAt ℂ (fun w : ℂ => xi (w+17/2)) (z-8) :=
    (xi_differentiable.comp (differentiable_id.add_const _)).analyticAt _
  have hord : analyticOrderAt (fun w : ℂ => xi (w+17/2)) (z-8) =
      analyticOrderAt xi (1/2+z) := by
    have he : analyticOrderAt (fun w : ℂ => xi (w+17/2)) (z-8) =
        analyticOrderAt xi (z-8+17/2) := by
      apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi)
        (g := fun w : ℂ => w+17/2) (by fun_prop)
      simp
    simpa only [show z-8+17/2 = (1:ℂ)/2+z by ring] using he
  change analyticOrderAt xi (1/2+z) ≤ analyticOrderAt
    ((fun w : ℂ => xi (w+17/2))*H) (z-8)
  rw [analyticOrderAt_mul hξ (hH.analyticAt _),hord]
  exact le_self_add


/-- The actual prime-side datum has one sign on no positive tail. -/
theorem criticalState_prime_side_not_eventually_signed {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s : ℝ} (hsign : s = 1 ∨ s = -1) (T : ℝ) :
    ¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ s*
      (leftContinuationDatum (criticalHalfLineEnergyDomain_of_groundState hF)
        (c := 1) (by norm_num) (by norm_num) W₀ v).re := by
  intro htail
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let D := leftContinuationDatum hd (c := 1) (by norm_num) (by norm_num) W₀
  let f := reflectedRealDatum D
  let G : ℂ → ℂ := fun w => stateMeromorphic W₀ F (-w-10)
  have hGa (x : ℝ) : AnalyticAt ℂ G (x : ℂ) := by
    have ha : AnalyticAt ℂ (stateMeromorphic W₀ F) (-(x:ℂ)-10) := by
      have he : -(x:ℂ)-10 = ((-x-10:ℝ):ℂ) := by push_cast; rfl
      rw [he]
      exact analyticAt_stateMeromorphic_real hd _
    exact ha.comp (f := fun w : ℂ => -w-10) (analyticAt_id.neg.sub analyticAt_const)
  have heq (x : ℝ) (hx : 0 < x) : negativeHalfLineLaplace (cx f) (x:ℂ) = G x := by
    rw [laplace_reflectedRealDatum D hx]
    have hL := stateMeromorphic_eq_laplaceRay_left (W₀ := W₀) hd
      (c := 1) (by norm_num) (by norm_num) (z := ((x+1:ℝ):ℂ))
      (by simp only [Complex.ofReal_re]; linarith only [hx])
    have he : -(((x+1:ℝ):ℂ)+(1:ℂ))-8 = ((-x-10:ℝ):ℂ) := by push_cast; ring
    rw [Complex.ofReal_one,he] at hL
    rw [← hL,← criticalState_stateMeromorphic_real hW ht hF]
    dsimp only [G]
    congr 1
    push_cast
    ring
  let T' := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  have hpos : ∀ᵐ u ∂volume.restrict (Iio (-T')), 0 ≤ s*f u := by
    change ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ s*(D v).re at htail
    exact signed_tail_reflectedRealDatum htail
  have habs (σ : ℝ) : Integrable fun u => |f u| * Real.exp (σ*u) :=
    integrable_exp_of_signed_tail_of_real_continuation
      (measurable_reflectedRealDatum D) (integrable_reflectedRealDatum D)
      (reflectedRealDatum_support D) (κ := σ-1) (fun x _ => hGa x)
      heq hsign hT' hpos (by linarith)
  have hLf : Differentiable ℂ (negativeHalfLineLaplace (cx f)) := by
    intro w
    exact (differentiableOn_laplace_of_abs (measurable_reflectedRealDatum D)
      (reflectedRealDatum_support D) (κ := w.re-1) (fun x _ => habs x)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))
  let H : ℂ → ℂ := fun w => negativeHalfLineLaplace (cx f) (-w-10)
  have hH : Differentiable ℂ H := hLf.comp (differentiable_id.neg.sub_const _)
  apply criticalState_no_entire_reflected_transform hW ht hF hH
  intro x hx
  have h := heq (-x-10) (by linarith only [hx])
  have hcast : ((-x-10:ℝ):ℂ) = -(x:ℂ)-10 := by push_cast; rfl
  rw [hcast] at h
  dsimp only [G] at h
  rw [show -(-(x:ℂ)-10)-10 = (x:ℂ) by ring] at h
  exact h

/-- Both signs occur on every tail of the explicit prime-side balance. -/
theorem criticalState_prime_side_changes_sign_on_every_ray {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ) :
    let D := leftContinuationDatum (criticalHalfLineEnergyDomain_of_groundState hF)
      (c := 1) (by norm_num) (by norm_num) W₀
    (¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ (D v).re) ∧
      ¬ ∀ᵐ v ∂volume.restrict (Ioi T), (D v).re ≤ 0 := by
  dsimp only
  constructor
  · intro h
    apply criticalState_prime_side_not_eventually_signed hW ht hF (s := 1) (Or.inl rfl) T
    simpa only [one_mul] using h
  · intro h
    apply criticalState_prime_side_not_eventually_signed hW ht hF (s := -1) (Or.inr rfl) T
    filter_upwards [h] with v hv
    simpa only [neg_one_mul] using neg_nonneg.mpr hv

/-- The unconditional critical-state alternative forces oscillation on the prime side of the wall. -/
theorem riemannHypothesis_or_criticalState_prime_side_changes_sign :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ) (hW : 0 < W₀)
      (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
      (hF : IsCriticalHalfLineGroundState W₀ F),
      let D := leftContinuationDatum (criticalHalfLineEnergyDomain_of_groundState hF)
        (c := 1) (by norm_num) (by norm_num) W₀
      ∀ T : ℝ, (¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ (D v).re) ∧
        ¬ ∀ᵐ v ∂volume.restrict (Ioi T), (D v).re ≤ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀,F,hW,ht,hF,criticalState_prime_side_changes_sign_on_every_ray hW ht hF⟩


private theorem archimedeanWallTail_real (F : ℝ → ℝ) (x : ℝ) :
    archimedeanWallTail F (x:ℂ) = ((archimedeanWallTail F (x:ℂ)).re : ℂ) := by
  have hc : (starRingEnd ℂ) (archimedeanWallTail F (x:ℂ)) = archimedeanWallTail F (x:ℂ) := by
    unfold archimedeanWallTail
    rw [Complex.conj_tsum]
    refine tsum_congr fun k => ?_
    have hr : (2*((k:ℂ)+1)+1/2) = ((2*((k:ℝ)+1)+1/2 : ℝ):ℂ) := by
      push_cast
      rfl
    rw [hr,negativeHalfLineLaplace_ofReal,← Complex.ofReal_sub,
      ← Complex.ofReal_div,Complex.conj_ofReal]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith only [hi]

/-- The prime-minus-pole wave of a critical state has one sign on no positive tail. -/
theorem criticalState_prime_wave_not_eventually_signed {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {s : ℝ} (hsign : s = 1 ∨ s = -1) (T : ℝ) :
    ¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ s*
      (wallPrimeWaveDatumLp (criticalHalfLineEnergyDomain_of_groundState hF)
        (c := 1) (by norm_num) (by norm_num) v).re := by
  intro htail
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let D := wallPrimeWaveDatumLp hd (c := 1) (by norm_num) (by norm_num)
  let f := reflectedRealDatum D
  let R : ℂ → ℂ := fun p => -(criticalAliasCoefficient W₀ : ℂ)*
    stateMeromorphic W₀ F (p-8) - archimedeanWallTail F p
  have hR_eq (p : ℂ) : R p = globalRemainder F p - archimedeanWallTail F p := by
    have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
    dsimp only [R,stateMeromorphic]
    rw [sub_add_cancel]
    field_simp [ha]
    <;> ring
  have hR_left (p : ℂ) (hp : p.re < -(1/2)) : R p = wallPrimeBalance F p := by
    rw [hR_eq,globalRemainder_eq_archimedeanWallTail_add_wallPrimeBalance hd hp]
    ring
  have hR_real (x : ℝ) : R (x:ℂ) = ((R (x:ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · change (R (x:ℂ)).im = 0
      dsimp only [R]
      rw [show (x:ℂ)-8 = ((x-8:ℝ):ℂ) by push_cast; rfl,
        criticalState_stateMeromorphic_real hW ht hF (x-8),archimedeanWallTail_real]
      simp only [Complex.sub_im,Complex.mul_im,Complex.neg_im,Complex.ofReal_im,
        neg_zero,zero_mul,mul_zero,add_zero,sub_zero]
  have hR_an (x : ℝ) (hx : x < 0) : AnalyticAt ℂ R (x:ℂ) := by
    have ha : AnalyticAt ℂ (stateMeromorphic W₀ F) ((x:ℂ)-8) := by
      rw [show (x:ℂ)-8 = ((x-8:ℝ):ℂ) by push_cast; rfl]
      exact analyticAt_stateMeromorphic_real hd _
    have harch : AnalyticAt ℂ (archimedeanWallTail F) (x:ℂ) :=
      (differentiableOn_archimedeanWallTail hd).analyticAt
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
          (by change x < 5/2; linarith only [hx]))
    exact (analyticAt_const.mul
      (ha.comp (f := fun p : ℂ => p-8) (analyticAt_id.sub analyticAt_const))).sub harch
  let G : ℂ → ℂ := fun w => R (-w-2)
  have hGa (x : ℝ) (hx : -2 < x) : AnalyticAt ℂ G (x:ℂ) := by
    have ha : AnalyticAt ℂ R (-(x:ℂ)-2) := by
      rw [show -(x:ℂ)-2 = ((-x-2:ℝ):ℂ) by push_cast; rfl]
      exact hR_an _ (by linarith only [hx])
    exact ha.comp (f := fun w : ℂ => -w-2) (analyticAt_id.neg.sub analyticAt_const)
  have heq (x : ℝ) (hx : 0 < x) : negativeHalfLineLaplace (cx f) (x:ℂ) = G x := by
    rw [laplace_reflectedRealDatum D hx]
    have hlap := laplaceRay_wallPrimeWaveDatumLp hd (c := 1)
      (by norm_num) (by norm_num) (z := ((x+1:ℝ):ℂ))
      (by simp only [Complex.ofReal_re]; linarith only [hx])
    have he : -(((x+1:ℝ):ℂ)+(1:ℂ)) = ((-x-2:ℝ):ℂ) := by push_cast; ring
    rw [Complex.ofReal_one,he] at hlap
    rw [hlap,← hR_left _ (by simp only [Complex.ofReal_re]; linarith only [hx]),← hR_real]
    dsimp only [G]
    congr 1
    push_cast
    ring
  let T' := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  have hpos : ∀ᵐ u ∂volume.restrict (Iio (-T')), 0 ≤ s*f u := by
    change ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ s*(D v).re at htail
    exact signed_tail_reflectedRealDatum htail
  have habs (σ : ℝ) (hσ : -2 < σ) : Integrable fun u => |f u| * Real.exp (σ*u) :=
    integrable_exp_of_signed_tail_of_real_continuation
      (measurable_reflectedRealDatum D) (integrable_reflectedRealDatum D)
      (reflectedRealDatum_support D) hGa heq hsign hT' hpos hσ
  have hLf := differentiableOn_laplace_of_abs (measurable_reflectedRealDatum D)
    (reflectedRealDatum_support D) habs
  let H : ℂ → ℂ := fun p => negativeHalfLineLaplace (cx f) (-p-2)
  have hH : DifferentiableOn ℂ H {p : ℂ | p.re < 0} :=
    hLf.comp (differentiable_id.neg.sub_const (2:ℂ)).differentiableOn
      (fun p hp => by
        change p.re < 0 at hp
        change -2 < -p.re-2
        linarith only [hp])
  have hreal (x : ℝ) (hx : x < -2) : H (x:ℂ) = wallPrimeBalance F (x:ℂ) := by
    have h := heq (-x-2) (by linarith only [hx])
    rw [show ((-x-2:ℝ):ℂ) = -(x:ℂ)-2 by push_cast; rfl] at h
    dsimp only [G] at h
    rw [show -(-(x:ℂ)-2)-2 = (x:ℂ) by ring] at h
    exact h.trans (hR_left _ (by simp only [Complex.ofReal_re]; linarith only [hx]))
  have hf : ∃ᶠ p : ℂ in 𝓝[≠] (-3:ℂ), H p = wallPrimeBalance F p := by
    have he : ∀ᶠ x : ℝ in 𝓝[≠] (-3:ℝ), H (x:ℂ) = wallPrimeBalance F (x:ℂ) := by
      filter_upwards [nhdsWithin_le_nhds
        (isOpen_Iio.mem_nhds (show (-3:ℝ) < -2 by norm_num))] with x hx
      exact hreal x hx
    simpa using (tendsto_ofReal_nhdsNE (-3)).frequently he.frequently
  have hU : IsOpen {p : ℂ | p.re < -(1/2)} := isOpen_lt Complex.continuous_re continuous_const
  have hA : AnalyticOnNhd ℂ H {p : ℂ | p.re < -(1/2)} :=
    (hH.mono fun p hp => by
      change p.re < -(1/2) at hp
      change p.re < 0
      linarith only [hp]).analyticOnNhd hU
  have hB : AnalyticOnNhd ℂ (wallPrimeBalance F) {p : ℂ | p.re < -(1/2)} :=
    (differentiableOn_wallPrimeBalance hd).analyticOnNhd hU
  exact criticalState_not_hasBeyondTheWallPrimeContinuation hW ht hF
    ⟨H,hH,hA.eqOn_of_preconnected_of_frequently_eq hB
      (convex_halfSpace_re_lt (-(1/2))).isPreconnected (by simp; norm_num) hf⟩

/-- Both signs occur on every tail after subtracting the continuum prime main term. -/
theorem criticalState_prime_wave_changes_sign_on_every_ray {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ) :
    let D := wallPrimeWaveDatumLp (criticalHalfLineEnergyDomain_of_groundState hF)
      (c := 1) (by norm_num) (by norm_num)
    (¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ (D v).re) ∧
      ¬ ∀ᵐ v ∂volume.restrict (Ioi T), (D v).re ≤ 0 := by
  dsimp only
  constructor
  · intro h
    apply criticalState_prime_wave_not_eventually_signed hW ht hF (s := 1) (Or.inl rfl) T
    simpa only [one_mul] using h
  · intro h
    apply criticalState_prime_wave_not_eventually_signed hW ht hF (s := -1) (Or.inr rfl) T
    filter_upwards [h] with v hv
    simpa only [neg_one_mul] using neg_nonneg.mpr hv

/-- Failure of RH supplies a critical state whose prime-minus-pole wave oscillates on every tail. -/
theorem riemannHypothesis_or_criticalState_prime_wave_changes_sign :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ) (hW : 0 < W₀)
      (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
      (hF : IsCriticalHalfLineGroundState W₀ F),
      let D := wallPrimeWaveDatumLp (criticalHalfLineEnergyDomain_of_groundState hF)
        (c := 1) (by norm_num) (by norm_num)
      ∀ T : ℝ, (¬ ∀ᵐ v ∂volume.restrict (Ioi T), 0 ≤ (D v).re) ∧
        ¬ ∀ᵐ v ∂volume.restrict (Ioi T), (D v).re ≤ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀,F,hW,ht,hF,criticalState_prime_wave_changes_sign_on_every_ray hW ht hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
