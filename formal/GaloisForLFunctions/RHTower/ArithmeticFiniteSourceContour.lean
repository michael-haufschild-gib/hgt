import GaloisForLFunctions.RHTower.ArithmeticCenteredTailPhase
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteRouche

/-!
# Contour transport for the literal finite arithmetic source

The exact retained-tail identity gives a uniform inverse-square cutoff error on bounded
positive-half-plane sets away from the pole. Local Rouché comparison transports the actual
zeta multiplicity around every nontrivial zero to every sufficiently long finite head.
The complete-tail phase cone makes the finite residual nonzero at the original zero;
nevertheless a distinct finite-head zero lies arbitrarily nearby. These unconditional
approximation and contour results do not select the critical line or establish RH.
-/

noncomputable section
open Complex MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Literal finite Bernoulli approximation on the domain away from the pole. -/
def finiteCutoffZeta (N : ℕ) (s : ℂ) : ℂ := finiteCutoffResidual N s/(s-1)

/-- Exact approximation error retains the complete centered tail. -/
theorem finiteCutoffZeta_sub_zeta {N : ℕ} (hN : 1≤N) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) :
    finiteCutoffZeta N s-riemannZeta s=s*(s+1)*
      (∫ x in Ioi (N:ℝ), ((bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  apply (sub_eq_iff_eq_add).mpr
  apply (div_eq_iff (sub_ne_zero.mpr hs1)).mpr
  rw [finiteCutoffResidual_eq_zeta_add_tail hN hs hs1]
  ring

/-- Uniform quantitative approximation on any bounded positive-half-plane region away from 1. -/
theorem norm_finiteCutoffZeta_sub_zeta_le {N : ℕ} (hN : 1≤N) {s : ℂ}
    (hs : 0<s.re) (hs1 : s≠1) {M : ℝ} (hM : ‖s‖≤M) (hMN : M≤N) :
    ‖finiteCutoffZeta N s-riemannZeta s‖ ≤ (M+1)^2/(15*(N:ℝ)^2) := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hM0 : 0≤M := (norm_nonneg s).trans hM
  have ht := norm_centeredBernoulliTail_le_linear hNp (by linarith : -1<s.re)
    ((Complex.abs_im_le_norm s).trans (hM.trans hMN))
  have hp : (N:ℝ)^(-s.re-2) ≤ (N:ℝ)^(-2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hp2 : (N:ℝ)^(-2:ℝ) = 1/(N:ℝ)^2 := by
    rw [Real.rpow_neg hNp.le, Real.rpow_two, one_div]
  have hprod : ‖s*(s+1)‖ ≤ (M+1)^2 := by
    rw [norm_mul]
    have hsp : ‖s+1‖≤M+1 := (norm_add_le s 1).trans (by simpa using add_le_add_right hM 1)
    calc
      _ ≤ M*(M+1) := mul_le_mul hM hsp (norm_nonneg _) hM0
      _ ≤ (M+1)^2 := by nlinarith
  rw [finiteCutoffZeta_sub_zeta hN hs hs1,norm_mul]
  calc
    _ ≤ (M+1)^2*((N:ℝ)^(-s.re-2)/15) :=
      mul_le_mul hprod ht (norm_nonneg _) (sq_nonneg _)
    _ ≤ (M+1)^2*((N:ℝ)^(-2:ℝ)/15) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp (by norm_num)) (sq_nonneg _)
    _ = _ := by rw [hp2]; ring

/-- The finite source is analytic away from its explicit pole. -/
theorem analyticAt_finiteCutoffZeta {N : ℕ} (hN : 1≤N) {s : ℂ} (hs1 : s≠1) :
    AnalyticAt ℂ (finiteCutoffZeta N) s := by
  exact ((differentiable_finiteCutoffResidual hN).analyticAt s).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1)

/-- Bounded-domain convergence keeps the literal finite expression and all endpoint corrections. -/
theorem tendstoUniformlyOn_finiteCutoffZeta {K : Set ℂ} (hK : Bornology.IsBounded K)
    (hKU : ∀s∈K, 0<s.re ∧ s≠1) :
    TendstoUniformlyOn finiteCutoffZeta riemannZeta atTop K := by
  obtain ⟨M,hM,hbound⟩ := hK.exists_pos_norm_le
  have hlim : Tendsto (fun N : ℕ => ((M+1)^2/15)*(N:ℝ)^(-2:ℝ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2)).comp
      tendsto_natCast_atTop_atTop).const_mul ((M+1)^2/15)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall := (tendsto_order.1 hlim).2 ε hε
  have hcut : ∀ᶠN : ℕ in atTop, M≤(N:ℝ) :=
    tendsto_atTop.1 tendsto_natCast_atTop_atTop M
  filter_upwards [hsmall,hcut,eventually_ge_atTop 1] with N hsmall hcut hN
  intro s hs
  have he := norm_finiteCutoffZeta_sub_zeta_le hN (hKU s hs).1 (hKU s hs).2
    (hbound s hs) hcut
  have heq : (M+1)^2/(15*(N:ℝ)^2)=((M+1)^2/15)*(N:ℝ)^(-2:ℝ) := by
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤N),Real.rpow_two]
    ring
  rw [dist_eq_norm,norm_sub_rev]
  exact he.trans_lt (heq.symm ▸ hsmall)

/-- Local uniform convergence on the exact analytic domain. -/
theorem tendstoLocallyUniformlyOn_finiteCutoffZeta :
    TendstoLocallyUniformlyOn finiteCutoffZeta riemannZeta atTop {s : ℂ | 0<s.re ∧ s≠1} := by
  have hU : IsOpen {s : ℂ | 0<s.re ∧ s≠1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  exact tendstoUniformlyOn_finiteCutoffZeta hK.isBounded (fun s hs => hKU hs)

/-- Every zeta-free circle in the analytic domain eventually has exactly the finite-source winding. -/
theorem eventually_finiteCutoffZeta_circle_nonzero_and_logDeriv_eq
    {c : ℂ} {R : ℝ} (hR : 0≤R)
    (hgeometry : ∀z∈sphere c R, 0<z.re ∧ z≠1 ∧ riemannZeta z≠0) :
    ∀ᶠN : ℕ in atTop,
      (∀z∈sphere c R, finiteCutoffZeta N z≠0) ∧
      (∮z in C(c,R), logDeriv (finiteCutoffZeta N) z)=
        ∮z in C(c,R), logDeriv riemannZeta z := by
  let U := {s : ℂ | 0<s.re ∧ s≠1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hsub : sphere c R⊆U := fun z hz => ⟨(hgeometry z hz).1,(hgeometry z hz).2.1⟩
  have ha : AnalyticOnNhd ℂ riemannZeta U :=
    fun z hz => analyticOn_riemannZeta z hz.2
  have hb := RiemannGaussian.eventually_forall_norm_sub_lt_norm_on_compact_of_tendstoLocallyUniformlyOn
    tendstoLocallyUniformlyOn_finiteCutoffZeta hU (isCompact_sphere c R) hsub
    ha.continuousOn (fun z hz => (hgeometry z hz).2.2)
  filter_upwards [hb,eventually_ge_atTop 1] with N hbound hN
  refine ⟨?_,?_⟩
  · intro z hz heq
    have h := hbound z hz
    rw [heq,zero_sub,norm_neg] at h
    exact lt_irrefl _ h
  · exact RiemannGaussian.circleIntegral_logDeriv_eq_of_norm_sub_lt_of_analyticOnNhd
      ha (fun z hz => analyticAt_finiteCutoffZeta hN hz.2) hR hsub hbound

/-- A nonzero logarithmic-derivative winding of an analytic function forces an interior zero. -/
theorem exists_zero_in_ball_of_logDeriv_ne_zero {f : ℂ→ℂ} {c : ℂ} {R : ℝ}
    (hR : 0≤R) (ha : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀z∈sphere c R, f z≠0)
    (hw : (∮z in C(c,R), logDeriv f z)≠0) :
    ∃z∈ball c R, f z=0 := by
  by_contra h
  push Not at h
  have hne : ∀z∈closedBall c R, f z≠0 := by
    intro z hz
    rcases (mem_closedBall.mp hz).lt_or_eq with hlt | heq
    · exact h z (mem_ball.mpr hlt)
    · exact hb z (mem_sphere.mpr heq)
  have hlog : AnalyticOnNhd ℂ (logDeriv f) (closedBall c R) := by
    intro z hz
    exact (ha z hz).deriv.div (ha z hz) (hne z hz)
  apply hw
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
  · intro z hz
    exact (hlog z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact (hlog z (ball_subset_closedBall hz.1)).differentiableAt

/-- The literal finite arithmetic source transports the full multiplicity of every zeta zero,
while its nearby finite zeros are displaced from the original point. -/
theorem exists_lt_eventually_finiteCutoffZeta_displaced_zero_and_winding
    (rho : RiemannGaussian.NontrivialZetaZero) {r : ℝ} (hr : 0<r) :
    ∃R : ℝ, 0<R ∧ R<r ∧
      (∀z∈closedBall rho.1 R, z≠rho.1 → riemannZeta z≠0) ∧
      ∀ᶠN : ℕ in atTop,
        finiteCutoffZeta N rho.1≠0 ∧
        (∀z∈sphere rho.1 R, finiteCutoffZeta N z≠0) ∧
        (∮z in C(rho.1,R), logDeriv (finiteCutoffZeta N) z)=
          (RiemannGaussian.analyticZetaZeroMultiplicity rho:ℂ)*(2*Real.pi:ℝ)*Complex.I ∧
        ∃z∈ball rho.1 R, z≠rho.1 ∧ finiteCutoffResidual N z=0 := by
  have hrho := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hrho1 := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  have hrhone : rho.1≠1 := rho.2.2.2
  have hbound : 0 < min r (min (rho.1.re/2) ((1-rho.1.re)/2)) := by positivity
  obtain ⟨R,hR,hRb,hiso,hw⟩ :=
    RiemannGaussian.AnalyticAt.exists_lt_circleIntegral_logDeriv_eq_order
      (RiemannGaussian.analyticAt_riemannZeta_nontrivialZero rho)
      (RiemannGaussian.analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho) hbound
  have hRr : R<r := hRb.trans_le (min_le_left _ _)
  have hRre : R<rho.1.re/2 :=
    (hRb.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hRone : R<(1-rho.1.re)/2 :=
    (hRb.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hdomain : ∀z∈closedBall rho.1 R, 0<z.re ∧ z≠1 := by
    intro z hz
    have hd : |z.re-rho.1.re|≤R := by
      calc
        _ = |(z-rho.1).re| := by simp
        _ ≤ ‖z-rho.1‖ := Complex.abs_re_le_norm _
        _ ≤ R := by simpa only [dist_eq_norm] using mem_closedBall.mp hz
    have hzpos : 0<z.re := by linarith [neg_le_abs (z.re-rho.1.re)]
    have hzlt : z.re<1 := by linarith [le_abs_self (z.re-rho.1.re)]
    refine ⟨hzpos,?_⟩
    intro h
    rw [h] at hzlt
    norm_num at hzlt
  have hgeometry : ∀z∈sphere rho.1 R, 0<z.re ∧ z≠1 ∧ riemannZeta z≠0 := by
    intro z hz
    have hd := hdomain z (sphere_subset_closedBall hz)
    refine ⟨hd.1,hd.2,hiso z (sphere_subset_closedBall hz) ?_⟩
    intro heq
    subst z
    rw [mem_sphere,dist_self] at hz
    exact hR.ne' hz.symm
  have hcut : ∀ᶠN : ℕ in atTop, 2*‖rho.1+3‖≤(N:ℝ) :=
    tendsto_atTop.1 tendsto_natCast_atTop_atTop _
  refine ⟨R,hR,hRr,hiso,?_⟩
  filter_upwards [eventually_finiteCutoffZeta_circle_nonzero_and_logDeriv_eq hR.le hgeometry,
    hcut,eventually_ge_atTop 1] with N hN hcut hNpos
  have hcenter : finiteCutoffZeta N rho.1≠0 :=
    div_ne_zero (finiteCutoffResidual_ne_zero_at_zero_of_linear_cutoff hrho hrhone
      rho.2.1 hNpos hcut) (sub_ne_zero.mpr hrhone)
  have hwind : (∮z in C(rho.1,R), logDeriv (finiteCutoffZeta N) z)=
      (RiemannGaussian.analyticZetaZeroMultiplicity rho:ℂ)*(2*Real.pi:ℝ)*Complex.I :=
    hN.2.trans hw
  have hwindne : (∮z in C(rho.1,R), logDeriv (finiteCutoffZeta N) z)≠0 := by
    rw [hwind]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (RiemannGaussian.analyticZetaZeroMultiplicity_positive rho).ne'
      · exact_mod_cast (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos).ne'
    · exact Complex.I_ne_zero
  obtain ⟨z,hz,hzero⟩ := exists_zero_in_ball_of_logDeriv_ne_zero hR.le
    (fun z hz => analyticAt_finiteCutoffZeta hNpos (hdomain z hz).2) hN.1 hwindne
  have hres : finiteCutoffResidual N z=0 :=
    (div_eq_zero_iff.mp hzero).resolve_right
      (sub_ne_zero.mpr (hdomain z (ball_subset_closedBall hz)).2)
  refine ⟨hcenter,hN.1,hwind,z,hz,?_,hres⟩
  intro heq
  exact hcenter (heq ▸ hzero)

/-- Every nontrivial zeta zero is approached by distinct zeros of every sufficiently long
literal entire finite head, with no simplicity assumption. -/
theorem eventually_exists_finiteCutoffResidual_zero_near
    (rho : RiemannGaussian.NontrivialZetaZero) {r : ℝ} (hr : 0<r) :
    ∀ᶠN : ℕ in atTop, ∃z : ℂ, 0<dist z rho.1 ∧ dist z rho.1<r ∧
      finiteCutoffResidual N z=0 := by
  obtain ⟨R,_,hRr,_,hN⟩ :=
    exists_lt_eventually_finiteCutoffZeta_displaced_zero_and_winding rho hr
  filter_upwards [hN] with N hN
  obtain ⟨z,hz,hne,hzero⟩ := hN.2.2.2
  exact ⟨z,dist_pos.mpr hne,(mem_ball.mp hz).trans hRr,hzero⟩

end RHTower.DeletionMixedRefinement
