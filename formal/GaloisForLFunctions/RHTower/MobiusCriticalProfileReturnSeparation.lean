import GaloisForLFunctions.RHTower.MobiusLaplaceLandauOscillation
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction

/-!
The two ends of the actual critical Mobius profile are not interchangeable.
Paper proof: G=sum exp(-n) bounds Phi(x) by G exp(-x) for x>=1.
For y<=0, exp(-y/2)<=exp(exp(-y)/2), so
||psi(y)||<=G exp(-exp(-y)/2), hence psi tends to zero at the left end.
Landau's source zeros near x=0 give exact zeros of psi arbitrarily far right.
Nevertheless psi cannot tend to zero at the right end: that would imply the
half-decay criterion and RH, put an existing strip zero on the critical line,
and contradict the corpus Abel-residue obstruction at that zero.
Thus genuine point returns coexist with nonvanishing excursions. These are
infinite-source point observations, not bounded integer-prefix energy returns.
This is a corpus interpretation bridge, not a new RH architecture.
-/

noncomputable section
open Filter Complex Set
open scoped Topology
namespace RHTower

/-- Left-tail decay uses only the elementary geometric envelope. -/
theorem norm_mobiusCriticalProfile_le_leftTail {y : ℝ} (hy : y ≤ 0) :
    ‖mobiusLaplaceCriticalProfile y‖ ≤
      (∑' n : ℕ, Real.exp (-(n : ℝ))) * Real.exp (-Real.exp (-y)/2) := by
  let G := ∑' n : ℕ, Real.exp (-(n : ℝ))
  have hG : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hz : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
  have hF := norm_mobiusDiscreteLaplaceTransform_le_exp_neg hz
  have hcoef : Real.exp (-y/2) ≤ Real.exp (Real.exp (-y)/2) := by
    apply Real.exp_le_exp.mpr
    linarith [Real.add_one_le_exp (-y)]
  rw [mobiusLaplaceCriticalProfile,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-y/2)*(Real.exp (-Real.exp (-y))*G) :=
      mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
    _ ≤ Real.exp (Real.exp (-y)/2)*(Real.exp (-Real.exp (-y))*G) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.exp_pos _).le hG)
    _ = G*Real.exp (-Real.exp (-y)/2) := by
      rw [← mul_assoc,← Real.exp_add]
      rw [show Real.exp (-y)/2 + -Real.exp (-y) = -Real.exp (-y)/2 by ring,mul_comm]

theorem tendsto_mobiusCriticalProfile_atBot_zero :
    Tendsto mobiusLaplaceCriticalProfile atBot (𝓝 0) := by
  have hz : Tendsto (fun y : ℝ => Real.exp (-y)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have hh : Tendsto (fun y : ℝ => Real.exp (-y)/2) atBot atTop := by
    simpa only [div_eq_mul_inv] using hz.atTop_mul_const (by norm_num : 0 < (2 : ℝ)⁻¹)
  have hm := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul
    (∑' n : ℕ, Real.exp (-(n : ℝ)))
  apply squeeze_zero_norm'
    ((eventually_le_atBot (0 : ℝ)).mono fun _ hy => norm_mobiusCriticalProfile_le_leftTail hy)
  simpa only [Function.comp_apply,mul_zero,neg_div] using hm

/-- Prime/integer dilations at fixed y go to the exponentially damped end. -/
theorem tendsto_mobiusCriticalProfile_fixedLog_dilation_zero (y : ℝ) :
    Tendsto (fun t : ℝ => mobiusLaplaceCriticalProfile (y-Real.log t)) atTop (𝓝 0) := by
  apply tendsto_mobiusCriticalProfile_atBot_zero.comp
  rw [tendsto_atBot]
  intro b
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (y-b)] with t ht
  linarith

/-- Exact point returns also occur at the opposite, genuinely critical end. -/
theorem exists_mobiusCriticalProfile_zero_above (Y : ℝ) :
    ∃ y : ℝ, Y < y ∧ mobiusLaplaceCriticalProfile y=0 := by
  obtain ⟨x,hx,hxd,hzero⟩ := exists_mobiusDiscreteLaplaceTransform_zero_below (Real.exp_pos (-Y))
  refine ⟨-Real.log x,?_,?_⟩
  · have hlog := Real.strictMonoOn_log hx (Real.exp_pos (-Y)) hxd
    rw [Real.log_exp] at hlog
    linarith
  · simp only [mobiusLaplaceCriticalProfile,neg_neg,Real.exp_log hx,hzero,mul_zero]

/-- Exact critical point returns do not mean the whole critical profile vanishes. -/
theorem not_tendsto_mobiusCriticalProfile_atTop_zero :
    ¬ Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0) := by
  intro hp
  have hevent : ∀ᶠ y : ℝ in atTop, ‖mobiusLaplaceCriticalProfile y‖ < 1 := by
    have h := hp.eventually (Metric.ball_mem_nhds 0 zero_lt_one)
    filter_upwards [h] with y hy
    simpa [Complex.dist_eq] using hy
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hevent
  have hd : MobiusDiscreteLaplaceHalfDecay := by
    refine ⟨1,Real.exp (-Y),zero_le_one,Real.exp_pos _,?_⟩
    intro x hx hxd
    have hlog := Real.strictMonoOn_log hx (Real.exp_pos (-Y)) hxd
    rw [Real.log_exp] at hlog
    have hb := (hY (-Real.log x) (by linarith)).le
    simp only [mobiusLaplaceCriticalProfile,norm_mul,Complex.norm_real,neg_neg,
      Real.exp_log hx,Real.norm_of_nonneg (Real.exp_pos _).le] at hb
    have hfac : x ^ (-(1/2 : ℝ))*Real.exp (Real.log x/2)=1 := by
      rw [Real.rpow_def_of_pos hx,← Real.exp_add]
      rw [show Real.log x * (-(1/2 : ℝ)) + Real.log x/2 = 0 by ring,Real.exp_zero]
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ =
          x ^ (-(1/2 : ℝ))*(Real.exp (Real.log x/2)*‖mobiusDiscreteLaplaceTransform x‖) := by
        rw [← mul_assoc,hfac,one_mul]
      _ ≤ x ^ (-(1/2 : ℝ))*1 := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le _)
      _ = _ := by ring
  have hRH := mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis hd
  obtain ⟨rho,hrho0,_,hzeta⟩ := exists_riemannZeta_zero_mem_openStrip
  have hrhoHalf : rho.re=1/2 := by
    apply hRH rho hzeta
    · rintro ⟨n,hn⟩
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hn] at hrho0
      norm_num [Complex.mul_re] at hrho0
      linarith
    · exact riemannZeta_zero_ne_one hzeta
  exact not_tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_zeta_zero hrhoHalf hzeta hp

/-- A fixed positive amplitude is reached arbitrarily far right despite exact zero returns. -/
theorem mobiusCriticalProfile_cofinal_positive_excursions :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ Y : ℝ, ∃ y : ℝ,
      Y ≤ y ∧ epsilon ≤ ‖mobiusLaplaceCriticalProfile y‖ := by
  by_contra h
  push Not at h
  apply not_tendsto_mobiusCriticalProfile_atTop_zero
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨Y,hY⟩ := h epsilon hepsilon
  refine ⟨Y,fun y hy => ?_⟩
  simpa only [dist_zero_right] using hY y hy

end RHTower
