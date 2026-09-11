import GaloisForLFunctions.RHTower.BurnolCoPoissonNormalizedSourceRadialBias
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowNoncensorship
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowIndependence

/-!
# Joint original and Fourier jets from two prime windows

At an unchanged actual Xi divisor, at least one of two distinct prime
windows and its doubled window has an invertible matrix of original and
Fourier completed top jets. Literal Cramer combinations interpolate both
readings at one common aperture, before source closure. Full-strip weighted
integrability justifies the actual raw Mellin derivatives; all lower jets
retain the original exact multiplicity.

Arbitrary joint interpolation exposes a source-selection obligation:
Fourier unitarity does not impose equal top-jet amplitudes on every admitted
source. The chosen complete Green/BV source requires its own comparison.
-/

open Real Set Complex Filter MeasureTheory
namespace RHTower
noncomputable section

theorem burnolWindowCompletedTopJet_double {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) :
    burnolWindowCompletedTopJet (2 * L) (by positivity) rho =
      (Complex.exp ((L : ℂ) * (rho : ℂ)) + 1) *
        burnolWindowCompletedTopJet L hL rho := by
  unfold burnolWindowCompletedTopJet
  rw [iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq (by positivity),
    iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq hL]
  have he : Complex.exp (((2 * L : ℝ) : ℂ) * (rho : ℂ)) =
      Complex.exp ((L : ℂ) * (rho : ℂ)) ^ 2 := by
    push_cast
    rw [show (2 : ℂ) * L * (rho : ℂ) = (L : ℂ) * (rho : ℂ) + L * (rho : ℂ) by ring,
      Complex.exp_add, pow_two]
  rw [he]
  ring

theorem burnolWindowFourierCompletedTopJet_double {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) :
    burnolWindowFourierCompletedTopJet (2 * L) (by positivity) rho =
      (Complex.exp ((L : ℂ) * (1 - (rho : ℂ))) + 1) *
        burnolWindowFourierCompletedTopJet L hL rho := by
  unfold burnolWindowFourierCompletedTopJet
  rw [iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation (by positivity) rho le_rfl,
    iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation hL rho le_rfl]
  have he : Complex.exp (((2 * L : ℝ) : ℂ) * (1 - (rho : ℂ))) =
      Complex.exp ((L : ℂ) * (1 - (rho : ℂ))) ^ 2 := by
    push_cast
    rw [show (2 : ℂ) * L * (1 - (rho : ℂ)) =
      (L : ℂ) * (1 - (rho : ℂ)) + L * (1 - (rho : ℂ)) by ring,
      Complex.exp_add, pow_two]
  rw [he]
  ring

def burnolWindowJointTopJetDeterminant (L : ℝ) (hL : 0 < L)
    (rho : XiDivisorSupport) : ℂ :=
  burnolWindowCompletedTopJet L hL rho *
      burnolWindowFourierCompletedTopJet (2 * L) (by positivity) rho -
    burnolWindowFourierCompletedTopJet L hL rho *
      burnolWindowCompletedTopJet (2 * L) (by positivity) rho

theorem burnolWindowJointTopJetDeterminant_eq {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) :
    burnolWindowJointTopJetDeterminant L hL rho =
      burnolWindowCompletedTopJet L hL rho * burnolWindowFourierCompletedTopJet L hL rho *
        (Complex.exp ((L : ℂ) * (1 - (rho : ℂ))) -
          Complex.exp ((L : ℂ) * (rho : ℂ))) := by
  rw [burnolWindowJointTopJetDeterminant, burnolWindowCompletedTopJet_double hL rho,
    burnolWindowFourierCompletedTopJet_double hL rho]
  ring

theorem burnolWindowJointTopJetDeterminant_eq_zero_iff {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) :
    burnolWindowJointTopJetDeterminant L hL rho = 0 ↔
      rectangularWindowAmplitude L (2 * (rho : ℂ) - 1) = 0 := by
  have hz : 2 * (rho : ℂ) - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact xi_divisor_support_im_ne_zero rho (by linarith)
  have hne := burnolWindowCompletedTopJets_ne_zero hL rho
  rw [burnolWindowJointTopJetDeterminant_eq hL, mul_eq_zero]
  simp only [mul_ne_zero hne.1 hne.2, false_or]
  rw [rectangularWindowAmplitude_eq_div hz, div_eq_zero_iff]
  simp only [hz, or_false, sub_eq_zero]
  have he : Complex.exp (-(L : ℂ) * (2 * (rho : ℂ) - 1)) =
      Complex.exp ((L : ℂ) * (1 - (rho : ℂ))) /
        Complex.exp ((L : ℂ) * (rho : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  rw [he, eq_div_iff (Complex.exp_ne_zero _), one_mul]
  exact eq_comm

theorem burnolWindowJointTopJetDeterminant_two_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) :
    burnolWindowJointTopJetDeterminant (Real.log p)
        (Real.log_pos (by exact_mod_cast hp.one_lt)) rho ≠ 0 ∨
      burnolWindowJointTopJetDeterminant (Real.log q)
        (Real.log_pos (by exact_mod_cast hq.one_lt)) rho ≠ 0 := by
  have hpL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  rcases rectangularWindowAmplitude_pair_nonzero_of_irrational_ratio hpL hqL
      (GaloisForLFunctions.RHTower.irrational_log_ratio hq hp hpq.symm)
      (2 * (rho : ℂ) - 1) with h | h
  · exact Or.inl (fun hd => h ((burnolWindowJointTopJetDeterminant_eq_zero_iff hpL rho).mp hd))
  · exact Or.inr (fun hd => h ((burnolWindowJointTopJetDeterminant_eq_zero_iff hqL rho).mp hd))

private theorem joint_mellin_smul (c : ℂ) (f : SoninL2) (w : ℂ) :
    soninMellinEvaluation w (c • f : SoninL2) = c * soninMellinEvaluation w f := by
  unfold soninMellinEvaluation
  have hi : (∫ t in Ioi (0 : ℝ), (c • f : SoninL2) t * soninMellinKernel w t) =
      c * ∫ t in Ioi (0 : ℝ), f t * soninMellinKernel w t := by
    rw [← integral_const_mul]
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [Lp.coeFn_smul c f] with t ht
    intro _
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hi]
  ring

private theorem joint_mellin_smul_add (c d : ℂ) (f g : SoninL2) (w : ℂ)
    (hf : IntegrableOn (fun t : ℝ => f t * soninMellinKernel w t) (Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => g t * soninMellinKernel w t) (Ioi 0)) :
    soninMellinEvaluation w (c • f + d • g : SoninL2) =
      c * soninMellinEvaluation w f + d * soninMellinEvaluation w g := by
  have hcf : IntegrableOn (fun t : ℝ => (c • f : SoninL2) t * soninMellinKernel w t)
      (Ioi 0) := by
    apply (hf.const_mul c).congr
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c f)] with t ht
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hdg : IntegrableOn (fun t : ℝ => (d • g : SoninL2) t * soninMellinKernel w t)
      (Ioi 0) := by
    apply (hg.const_mul d).congr
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul d g)] with t ht
    rw [ht]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [← joint_mellin_smul c f w, ← joint_mellin_smul d g w]
  unfold soninMellinEvaluation
  rw [← mul_add, ← integral_add hcf hdg]
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards [Lp.coeFn_add (c • f) (d • g)] with t ht
  intro _
  rw [ht, Pi.add_apply]
  ring

private theorem joint_window_integrable {L : ℝ} (hL : 0 < L)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ =>
      (coPoissonSubWindowEven (Real.exp_pos (-L))
        (Real.exp_le_one_iff.mpr (by linarith)) : SoninL2) t * soninMellinKernel w t)
      (Ioi 0) := by
  apply (integrableOn_burnolCoPoisson_subWindow_cpow (Real.exp_pos (-L))
    (Real.exp_le_one_iff.mpr (by linarith)) hw0 hw1).congr
  filter_upwards [ae_restrict_of_ae (coPoissonSubWindowEven_coeFn (Real.exp_pos (-L))
    (Real.exp_le_one_iff.mpr (by linarith)))] with t ht
  rw [ht]
  rfl

private theorem joint_fourier_window_integrable {L : ℝ} (hL : 0 < L)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun t : ℝ =>
      (soninCosineUnitary (coPoissonSubWindowEven (Real.exp_pos (-L))
        (Real.exp_le_one_iff.mpr (by linarith))) : SoninL2) t * soninMellinKernel w t)
      (Ioi 0) := by
  have hc := Real.exp_pos (-L)
  have hcd : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hae := coeFn_soninCosineUnitary_coPoissonSubWindowEven hc hcd
  have hseed : coPoissonReciprocalSeed (coPoissonSubWindowSeed (Real.exp (-L)) 1) =
      coPoissonWindowIndicatorSeed 1 (Real.exp L) := by
    rw [coPoissonReciprocalSeed_subWindow_eq hc hcd, inv_one, Real.exp_neg, inv_inv]
  rw [hseed] at hae
  apply (integrableOn_burnolCoPoisson_windowIndicator_cpow (by norm_num : (0 : ℝ) < 1)
    (Real.one_le_exp hL.le) hw0 hw1).congr
  filter_upwards [ae_restrict_of_ae hae] with t ht
  rw [ht]
  rfl

private theorem joint_window_contDiff {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) := by
  have hr := xi_divisor_support_re_mem_open_unit rho
  have hn0 : (rho : ℂ) ≠ 0 := by intro h; simpa [h] using hr.1
  have hn1 : (rho : ℂ) ≠ 1 := by intro h; simpa [h] using hr.2
  have hc : ContDiffAt ℂ n mellinCompletionFactor (rho : ℂ) :=
    (analyticAt_mellinCompletionFactor_of_re_pos hr.1).contDiffAt
  have hz : ContDiffAt ℂ n riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hn1).contDiffAt
  have hg : ContDiffAt ℂ n (fun w : ℂ => (Complex.exp ((L : ℂ) * w) - 1) / w)
      (rho : ℂ) := by fun_prop
  apply (hc.mul (hz.mul hg)).congr_of_eventuallyEq
  have hU : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  filter_upwards [hU.mem_nhds hr] with w hw
  exact burnolCoPoissonExpWindowCompletedEvaluation_eq hL hw.1 hw.2

private theorem joint_fourier_window_contDiff {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (n : ℕ) :
    ContDiffAt ℂ n (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le)
      (rho : ℂ) := by
  have hr := xi_divisor_support_re_mem_open_unit rho
  have hn1 : (rho : ℂ) ≠ 1 := by intro h; simpa [h] using hr.2
  have hd : 1 - (rho : ℂ) ≠ 0 := sub_ne_zero.mpr hn1.symm
  have hc : ContDiffAt ℂ n mellinCompletionFactor (rho : ℂ) :=
    (analyticAt_mellinCompletionFactor_of_re_pos hr.1).contDiffAt
  have hz : ContDiffAt ℂ n riemannZeta (rho : ℂ) :=
    (analyticOn_riemannZeta (rho : ℂ) hn1).contDiffAt
  have hg : ContDiffAt ℂ n
      (fun w : ℂ => (Complex.exp ((L : ℂ) * (1 - w)) - 1) / (1 - w))
      (rho : ℂ) := by fun_prop
  apply ((hc.mul hz).mul hg).congr_of_eventuallyEq
  have hU : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  filter_upwards [hU.mem_nhds hr] with w hw
  exact burnolCoPoissonReciprocalWindowCompletedEvaluation_eq hL hw.1 hw.2

private theorem joint_mellin_deriv_smul_add (rho : XiDivisorSupport) (n : ℕ)
    (c d : ℂ) (f g : SoninL2)
    (hf : ∀ w : ℂ, 0 < w.re → w.re < 1 →
      IntegrableOn (fun t : ℝ => f t * soninMellinKernel w t) (Ioi 0))
    (hg : ∀ w : ℂ, 0 < w.re → w.re < 1 →
      IntegrableOn (fun t : ℝ => g t * soninMellinKernel w t) (Ioi 0))
    (hfd : ContDiffAt ℂ n (fun w => soninMellinEvaluation w f) (rho : ℂ))
    (hgd : ContDiffAt ℂ n (fun w => soninMellinEvaluation w g) (rho : ℂ)) :
    iteratedDeriv n (fun w => soninMellinEvaluation w (c • f + d • g : SoninL2))
        (rho : ℂ) =
      c * iteratedDeriv n (fun w => soninMellinEvaluation w f) (rho : ℂ) +
        d * iteratedDeriv n (fun w => soninMellinEvaluation w g) (rho : ℂ) := by
  have hU : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have he : Set.EqOn
      (fun w => soninMellinEvaluation w (c • f + d • g : SoninL2))
      (fun w => c * soninMellinEvaluation w f + d * soninMellinEvaluation w g)
      {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    intro w hw
    exact joint_mellin_smul_add c d f g w (hf w hw.1 hw.2) (hg w hw.1 hw.2)
  rw [he.iteratedDeriv_of_isOpen hU n (xi_divisor_support_re_mem_open_unit rho),
    iteratedDeriv_fun_add (contDiffAt_const.mul hfd) (contDiffAt_const.mul hgd),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

/-- Literal two-window source, retaining its two independent coefficients. -/
def burnolWindowJointSource (L : ℝ) (hL : 0 < L) (c d : ℂ) : evenSubspace :=
  c • coPoissonSubWindowEven (Real.exp_pos (-L))
      (Real.exp_le_one_iff.mpr (by linarith)) +
    d • coPoissonSubWindowEven (Real.exp_pos (-(2 * L)))
      (Real.exp_le_one_iff.mpr (by linarith))

/-- Both leading jets of the literal two-window source at the unchanged divisor. -/
theorem burnolWindowJointSource_top_jets {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (c d : ℂ) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (burnolWindowJointSource L hL c d : SoninL2))
        (rho : ℂ) =
      c * burnolWindowCompletedTopJet L hL rho +
        d * burnolWindowCompletedTopJet (2 * L) (by positivity) rho ∧
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowJointSource L hL c d) : SoninL2))
        (rho : ℂ) =
      c * burnolWindowFourierCompletedTopJet L hL rho +
        d * burnolWindowFourierCompletedTopJet (2 * L) (by positivity) rho := by
  constructor
  · exact joint_mellin_deriv_smul_add rho _ c d _ _
      (fun _ hw0 hw1 => joint_window_integrable hL hw0 hw1)
      (fun _ hw0 hw1 => joint_window_integrable (by positivity : 0 < 2 * L) hw0 hw1)
      (joint_window_contDiff hL rho _)
      (joint_window_contDiff (by positivity : 0 < 2 * L) rho _)
  · simp only [burnolWindowJointSource, map_add, map_smul]
    exact joint_mellin_deriv_smul_add rho _ c d _ _
      (fun _ hw0 hw1 => joint_fourier_window_integrable hL hw0 hw1)
      (fun _ hw0 hw1 => joint_fourier_window_integrable (by positivity : 0 < 2 * L) hw0 hw1)
      (joint_fourier_window_contDiff hL rho _)
      (joint_fourier_window_contDiff (by positivity : 0 < 2 * L) rho _)

/-- The original source and its Fourier image are admitted before source closure. -/
theorem burnolWindowJointSource_mem_algebraicSource {A L : ℝ} (hA : 0 < A)
    (hL : 0 < L) (hAL : A ≤ Real.exp (-(2 * L))) (c d : ℂ) :
    burnolWindowJointSource L hL c d ∈ burnolCoPoissonAlgebraicSourceSpace A ∧
      soninCosineUnitary (burnolWindowJointSource L hL c d) ∈
        burnolCoPoissonAlgebraicSourceSpace A := by
  have hm (T : ℝ) (hT : 0 < T) (hAT : A ≤ Real.exp (-T)) :
      coPoissonSubWindowEven (Real.exp_pos (-T))
        (Real.exp_le_one_iff.mpr (by linarith)) ∈ burnolCoPoissonAlgebraicSourceSpace A := by
    have h1 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    apply Submodule.subset_span
    apply coPoissonSubWindowEven_mem_burnolCoPoissonGeneratorSet hA (Real.exp_pos (-T)) h1
    simpa only [subWindowAperture, inv_one, min_eq_left h1] using hAT
  have hf : burnolWindowJointSource L hL c d ∈ burnolCoPoissonAlgebraicSourceSpace A :=
    (burnolCoPoissonAlgebraicSourceSpace A).add_mem
      ((burnolCoPoissonAlgebraicSourceSpace A).smul_mem _
        (hm L hL (hAL.trans (Real.exp_le_exp.mpr (by linarith)))))
      ((burnolCoPoissonAlgebraicSourceSpace A).smul_mem _ (hm (2 * L) (by positivity) hAL))
  exact ⟨hf, soninCosineUnitary_mem_coPoissonAlgebraicSourceSpace hf⟩

/-- An invertible doubled-window pair realizes arbitrary original/Fourier jets. -/
theorem burnolWindowJointSource_interpolate {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (hD : burnolWindowJointTopJetDeterminant L hL rho ≠ 0)
    (u v : ℂ) : ∃ c d : ℂ,
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (burnolWindowJointSource L hL c d : SoninL2))
        (rho : ℂ) = u ∧
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowJointSource L hL c d) : SoninL2))
        (rho : ℂ) = v := by
  let c := (u * burnolWindowFourierCompletedTopJet (2 * L) (by positivity) rho -
    v * burnolWindowCompletedTopJet (2 * L) (by positivity) rho) /
      burnolWindowJointTopJetDeterminant L hL rho
  let d := (v * burnolWindowCompletedTopJet L hL rho -
    u * burnolWindowFourierCompletedTopJet L hL rho) /
      burnolWindowJointTopJetDeterminant L hL rho
  refine ⟨c, d, ?_⟩
  rw [(burnolWindowJointSource_top_jets hL rho c d).1,
    (burnolWindowJointSource_top_jets hL rho c d).2]
  dsimp only [c, d]
  constructor <;> field_simp
  · dsimp only [burnolWindowJointTopJetDeterminant]
    ring
  · dsimp only [burnolWindowJointTopJetDeterminant]
    ring

/-- Every actual Xi divisor admits arbitrary joint leading jets on one of two
original prime-window pairs, at one fixed common aperture. -/
theorem burnolWindowJointSource_two_prime_interpolation
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) (u v : ℂ) :
    ∃ (L : ℝ) (hL : 0 < L) (c d : ℂ),
      (L = Real.log p ∨ L = Real.log q) ∧
      burnolWindowJointSource L hL c d ∈
        burnolCoPoissonAlgebraicSourceSpace (Real.exp (-2 * (Real.log p + Real.log q))) ∧
      soninCosineUnitary (burnolWindowJointSource L hL c d) ∈
        burnolCoPoissonAlgebraicSourceSpace (Real.exp (-2 * (Real.log p + Real.log q))) ∧
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (burnolWindowJointSource L hL c d : SoninL2))
        (rho : ℂ) = u ∧
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowJointSource L hL c d) : SoninL2))
        (rho : ℂ) = v := by
  have hpL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqL : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨L, hL, hwhich, hdet⟩ : ∃ (L : ℝ) (hL : 0 < L),
      (L = Real.log p ∨ L = Real.log q) ∧
        burnolWindowJointTopJetDeterminant L hL rho ≠ 0 := by
    rcases burnolWindowJointTopJetDeterminant_two_primes hp hq hpq rho with h | h
    · exact ⟨Real.log p, hpL, Or.inl rfl, h⟩
    · exact ⟨Real.log q, hqL, Or.inr rfl, h⟩
  obtain ⟨c, d, hu, hv⟩ := burnolWindowJointSource_interpolate hL rho hdet u v
  have hA : Real.exp (-2 * (Real.log p + Real.log q)) ≤ Real.exp (-(2 * L)) := by
    apply Real.exp_le_exp.mpr
    rcases hwhich with h | h <;> rw [h] <;> linarith
  obtain ⟨hf, hFf⟩ := burnolWindowJointSource_mem_algebraicSource (Real.exp_pos _) hL hA c d
  exact ⟨L, hL, c, d, hwhich, hf, hFf, hu, hv⟩

/-- The literal two-window construction retains every lower zero jet on both
Fourier sides, at the original exact Xi multiplicity. -/
theorem burnolWindowJointSource_lower_jets {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (c d : ℂ) {j : ℕ}
    (hj : j < burnolCoPoissonXiConormalOrder rho) :
    iteratedDeriv j
        (fun w => soninMellinEvaluation w (burnolWindowJointSource L hL c d : SoninL2))
        (rho : ℂ) = 0 ∧
    iteratedDeriv j
        (fun w => soninMellinEvaluation w
          (soninCosineUnitary (burnolWindowJointSource L hL c d) : SoninL2))
        (rho : ℂ) = 0 := by
  have h2L : 0 < 2 * L := by positivity
  constructor
  · have he := joint_mellin_deriv_smul_add rho j c d _ _
      (fun _ hw0 hw1 => joint_window_integrable hL hw0 hw1)
      (fun _ hw0 hw1 => joint_window_integrable h2L hw0 hw1)
      (joint_window_contDiff hL rho j) (joint_window_contDiff h2L rho j)
    change iteratedDeriv j
      (fun w => soninMellinEvaluation w (burnolWindowJointSource L hL c d : SoninL2))
        (rho : ℂ) =
      c * iteratedDeriv j (burnolCoPoissonExpWindowCompletedEvaluation L hL.le) (rho : ℂ) +
        d * iteratedDeriv j (burnolCoPoissonExpWindowCompletedEvaluation (2 * L) h2L.le)
          (rho : ℂ) at he
    simpa only [iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq_zero_of_lt L hL rho hj,
      iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq_zero_of_lt (2 * L) h2L rho hj,
      mul_zero, add_zero] using he
  · simp only [burnolWindowJointSource, map_add, map_smul]
    calc
      _ = c * iteratedDeriv j
            (burnolCoPoissonReciprocalWindowCompletedEvaluation L hL.le) (rho : ℂ) +
          d * iteratedDeriv j
            (burnolCoPoissonReciprocalWindowCompletedEvaluation (2 * L) h2L.le)
            (rho : ℂ) :=
        joint_mellin_deriv_smul_add rho j c d _ _
          (fun _ hw0 hw1 => joint_fourier_window_integrable hL hw0 hw1)
          (fun _ hw0 hw1 => joint_fourier_window_integrable h2L hw0 hw1)
          (joint_fourier_window_contDiff hL rho j) (joint_fourier_window_contDiff h2L rho j)
      _ = 0 := by
        rw [iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation_eq_zero_of_lt hL rho hj,
          iteratedDeriv_burnolCoPoissonReciprocalWindowCompletedEvaluation_eq_zero_of_lt h2L rho hj,
          mul_zero, mul_zero, add_zero]

/-- Fourier unitarity does not impose equal absolute leading-jet readings on
all literal sources, even at an arbitrary actual critical-line divisor. -/
theorem burnolCoPoissonAlgebraicSource_not_universal_topJet_norm_balance
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) :
    ¬ ∀ f : evenSubspace,
      f ∈ burnolCoPoissonAlgebraicSourceSpace (Real.exp (-2 * (Real.log p + Real.log q))) →
      ‖iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
          (fun w => soninMellinEvaluation w (f : SoninL2)) (rho : ℂ)‖ =
        ‖iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
          (fun w => soninMellinEvaluation w (soninCosineUnitary f : SoninL2)) (rho : ℂ)‖ := by
  intro h
  obtain ⟨L, hL, c, d, _, hf, _, hu, hv⟩ :=
    burnolWindowJointSource_two_prime_interpolation hp hq hpq rho 1 0
  have he := h (burnolWindowJointSource L hL c d) hf
  rw [hu, hv] at he
  norm_num at he

end
end RHTower
