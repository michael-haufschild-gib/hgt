import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerExtendedTransfer

/-!
# Global continuation of actual signed Mayer solutions

The normally convergent transfer first continues a solution to `Re z>-1/2`.
The first-branch identity then gives its continuation to `Re z>-1`: both
arguments `z+1` and `1/(1+z)` lie in the first domain. The construction agrees
with the original holomorphic disc function and retains constant forcing.
-/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerExtendedTransfer
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGlobalPeriods

/-- The full rightward continuation domain of a signed disc solution. -/
def domain : Set ℂ := {z | -1<z.re}

private theorem domain_open : IsOpen domain := isOpen_lt continuous_const Complex.continuous_re
private theorem halfPlane_open : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re

private theorem inv_re_pos {z : ℂ} (hz : 0<z.re) : 0<(z⁻¹).re := by
  rw [Complex.inv_re]
  have hn : 0<Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith only [sq_pos_of_pos hz,sq_nonneg z.im]
  exact div_pos hz hn

private theorem pos_ne_zero {z : ℂ} (hz : 0<z.re) : z≠0 := by
  intro he
  rw [he,Complex.zero_re] at hz
  exact lt_irrefl 0 hz

private theorem shift_re_pos {z : ℂ} (hz : z ∈ domain) : 0<(1+z).re := by
  change -1<z.re at hz
  simp only [Complex.add_re,Complex.one_re]
  linarith only [hz]

private def first (w ε c : ℂ) (f : DiscSpace) (z : ℂ) : ℂ := ε*(transfer w f z-c)

private theorem first_differentiableAt {w : ℂ} (hw : 0<w.re) (ε c : ℂ) (f : DiscSpace)
    {z : ℂ} (hz : z ∈ halfPlane) : DifferentiableAt ℂ (first w ε c f) z := by
  have ht := (transfer_differentiableOn hw f).differentiableAt (halfPlane_open.mem_nhds hz)
  exact (differentiableAt_const ε).mul (ht.sub_const c)

private theorem first_eq {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c) (z : Disc) :
    first w ε c f z=evaluation z f := by
  rw [first,transfer_eq_source hw f z,hf,map_add,map_smul,smul_eq_mul]
  change ε*(ε*evaluation z f+c-c)=evaluation z f
  linear_combination evaluation z f*hε

private theorem first_eq_plane {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {z : ℂ} (hz : z ∈ outer) : first w ε c f z=plane f z := by
  exact (first_eq hw hε f hf ⟨z,hz⟩).trans (plane_eq f ⟨z,hz⟩).symm

private theorem reciprocal_outer {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    (1+z)⁻¹ ∈ outer := by
  have hi : dist ((1+z)⁻¹) (1 : ℂ)≤(1 : ℝ) := by
    simpa only [mem_closedBall,Nat.cast_one] using (inverse_mem (n := 1) le_rfl hz)
  change dist ((1+z)⁻¹) (1 : ℂ)≤(3/2 : ℝ)
  exact hi.trans (by norm_num)

/-- The first-branch formula continues the actual signed solution globally. -/
def extension (w ε c : ℂ) (f : DiscSpace) (z : ℂ) : ℂ :=
  first w ε c f (z+1)+ε*(1+z)^(-w)*first w ε c f ((1+z)⁻¹)

private theorem extension_eq_first {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {z : ℂ} (hz : z ∈ halfPlane) : extension w ε c f z=first w ε c f z := by
  have hq := first_eq_plane hw hε f hf (reciprocal_outer hz.le)
  have ht := transfer_shift hw f hz
  rw [extension,hq]
  change ε*(transfer w f (z+1)-c)+ε*(1+z)^(-w)*plane f ((1+z)⁻¹)=
    ε*(transfer w f z-c)
  rw [mul_assoc,← mul_add,← ht]
  congr 1
  ring

/-- The constructed extension is holomorphic on `Re z>-1`. -/
theorem extension_differentiableOn {w : ℂ} (hw : 0<w.re) (ε c : ℂ) (f : DiscSpace) :
    DifferentiableOn ℂ (extension w ε c f) domain := by
  intro z hz
  have hp := shift_re_pos hz
  have hi := inv_re_pos hp
  have h1 : z+1 ∈ halfPlane := by
    change -(1/2 : ℝ)<(z+1).re
    simpa only [add_comm] using (show -(1/2 : ℝ)<(1+z).re by linarith only [hp])
  have h2 : (1+z)⁻¹ ∈ halfPlane := by change -(1/2 : ℝ)<((1+z)⁻¹).re; linarith only [hi]
  have hd1 : DifferentiableAt ℂ (fun u : ℂ => u+1) z := by fun_prop
  have hd2 : DifferentiableAt ℂ (fun u : ℂ => (1+u)⁻¹) z :=
    ((differentiableAt_id).const_add 1).inv (pos_ne_zero hp)
  have hpow := ((hasDerivAt_id z).const_add 1).cpow_const (c := -w)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hp))
  exact (((first_differentiableAt hw ε c f h1).comp z hd1).add
    (((differentiableAt_const ε).mul hpow.differentiableAt).mul
      ((first_differentiableAt hw ε c f h2).comp z hd2))).differentiableWithinAt

private theorem inner_halfPlane {z : ℂ} (hz : z ∈ MayerCutoff.inner) : z ∈ halfPlane := by
  have hn : ‖z-1‖<3/2 := by simpa only [MayerCutoff.inner,mem_ball,dist_eq_norm] using hz
  have hr := (neg_le_abs (z-1).re).trans (Complex.abs_re_le_norm (z-1))
  simp only [Complex.sub_re,Complex.one_re] at hr
  change -(1/2 : ℝ)<z.re
  linarith only [hn,hr]

/-- The extension agrees with the original actual holomorphic function on its disc interior. -/
theorem extension_eq_plane {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {z : ℂ} (hz : z ∈ MayerCutoff.inner) : extension w ε c f z=plane f z := by
  rw [extension_eq_first hw hε f hf (inner_halfPlane hz)]
  exact first_eq_plane hw hε f hf (ball_subset_closedBall hz)

/-- The original renewal identity holds on the entire continuation domain. -/
theorem extension_renewal {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    {z : ℂ} (hz : z ∈ domain) :
    extension w ε c f z=extension w ε c f (z+1)+
      ε*(1+z)^(-w)*extension w ε c f ((1+z)⁻¹) := by
  have hp := shift_re_pos hz
  have hi := inv_re_pos hp
  have h1 : z+1 ∈ halfPlane := by
    change -(1/2 : ℝ)<(z+1).re
    simpa only [add_comm] using (show -(1/2 : ℝ)<(1+z).re by linarith only [hp])
  have h2 : (1+z)⁻¹ ∈ halfPlane := by change -(1/2 : ℝ)<((1+z)⁻¹).re; linarith only [hi]
  rw [extension_eq_first hw hε f hf h1,extension_eq_first hw hε f hf h2]
  rfl

/-- The globally continued period coordinate. -/
def period (w ε c : ℂ) (f : DiscSpace) (a : ℂ) : ℂ := extension w ε c f (a-1)

private theorem period_analytic {w : ℂ} (hw : 0<w.re) (ε c : ℂ) (f : DiscSpace) :
    AnalyticOnNhd ℂ (period w ε c f) {a : ℂ | 0<a.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro a ha
  change 0<a.re at ha
  have hd : a-1 ∈ domain := by
    change -1<(a-1).re
    simp only [Complex.sub_re,Complex.one_re]
    linarith only [ha]
  have hh := (extension_differentiableOn hw ε c f).differentiableAt (domain_open.mem_nhds hd)
  exact (hh.comp a (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u-1) a)).differentiableWithinAt

/-- Renewal in period coordinates throughout the right half-plane. -/
theorem period_shift {w ε c a : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c) (ha : 0<a.re) :
    period w ε c f a=period w ε c f (a+1)+ε*a^(-w)*period w ε c f (1+a⁻¹) := by
  have hd : a-1 ∈ domain := by
    change -1<(a-1).re
    simp only [Complex.sub_re,Complex.one_re]
    linarith only [ha]
  have h := extension_renewal hw hε f hf hd
  simpa only [period,sub_add_cancel,show 1+(a-1)=a by ring,
    add_sub_cancel_right,add_sub_cancel_left] using h

private theorem mul_cpow_pos {a b : ℂ} (ha : 0<a.re) (hb : 0<b.re) (v : ℂ) :
    (a*b)^v=a^v*b^v := by
  -- The argument sum stays in the interval defining the principal logarithm.
  have ha0 := pos_ne_zero ha
  have hb0 := pos_ne_zero hb
  have hla : -(Real.pi/2)<a.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl ha)
  have hlb : -(Real.pi/2)<b.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hb)
  have hua : a.arg≤Real.pi/2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl ha.le)
  have hub : b.arg≤Real.pi/2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hb.le)
  have hl : Complex.log (a*b)=Complex.log a+Complex.log b :=
    Complex.log_mul ha0 hb0 ⟨by linarith only [hla,hlb],by linarith only [hua,hub]⟩
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha0 hb0),hl,add_mul,Complex.exp_add,
    Complex.cpow_def_of_ne_zero ha0,Complex.cpow_def_of_ne_zero hb0]

/-- Signed inversion parity follows by subtracting renewal at `a` and `1/a`. -/
theorem reciprocity {w ε c a : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c) (ha : 0<a.re) :
    period w ε c f a=ε*a^(-w)*period w ε c f a⁻¹ := by
  have hi := inv_re_pos ha
  have ht := period_shift hw hε f hf ha
  have ht' := period_shift hw hε f hf hi
  rw [inv_inv,add_comm a⁻¹ 1,add_comm 1 a] at ht'
  have hm : a^(-w)*(a⁻¹)^(-w)=1 := by
    rw [← mul_cpow_pos ha hi,mul_inv_cancel₀ (pos_ne_zero ha),Complex.one_cpow]
  linear_combination ht-ε*a^(-w)*ht'-period w ε c f (a+1)*(ε^2*hm+hε)

/-- Every continued actual signed solution satisfies the global Lewis relation. -/
theorem three_term {w ε c a : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c) (ha : 0<a.re) :
    period w ε c f a=period w ε c f (a+1)+(a+1)^(-w)*period w ε c f (a/(a+1)) := by
  have hi := inv_re_pos ha
  have hb : 0<(1+a⁻¹).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [hi]
  have ha1 : 0<(a+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [ha]
  have hr : (1+a⁻¹)⁻¹=a/(a+1) := by
    field_simp [pos_ne_zero ha,pos_ne_zero hb,pos_ne_zero ha1]
  have hp : a*(1+a⁻¹)=a+1 := by field_simp [pos_ne_zero ha]
  have hm : a^(-w)*(1+a⁻¹)^(-w)=(a+1)^(-w) := by
    rw [← mul_cpow_pos ha hb,hp]
  rw [period_shift hw hε f hf ha,reciprocity hw hε f hf hb,hr]
  linear_combination period w ε c f (a/(a+1))*(ε^2*hm+(a+1)^(-w)*hε)

/-- Any holomorphic continuation of the original disc function agrees with this one. -/
theorem extension_unique {w ε c : ℂ} (hw : 0<w.re) (hε : ε^2=1)
    (f : DiscSpace) (hf : regularized w hw f=ε • f+constant c)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g domain)
    (heq : EqOn g (plane f) MayerCutoff.inner) :
    EqOn g (extension w ε c f) domain := by
  have hd : AnalyticOnNhd ℂ (fun z => g z-extension w ε c f z) domain :=
    (hg.sub (extension_differentiableOn hw ε c f)).analyticOnNhd domain_open
  have hevent : (fun z => g z-extension w ε c f z) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have h0 : (0 : ℂ) ∈ MayerCutoff.inner := by
      norm_num [MayerCutoff.inner,mem_ball,dist_eq_norm]
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    change g z-extension w ε c f z=0
    rw [heq hz,extension_eq_plane hw hε f hf hz,sub_self]
  have hc : IsPreconnected domain := (convex_halfSpace_re_gt (-1)).isPreconnected
  intro z hz
  have he := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc
    (by norm_num [domain] : (0 : ℂ) ∈ domain) hevent hz
  change g z-extension w ε c f z=0 at he
  exact sub_eq_zero.mp he

#print axioms reciprocity
#print axioms three_term
#print axioms extension_unique

#print axioms extension_differentiableOn
#print axioms extension_eq_plane
#print axioms extension_renewal
#print axioms period_shift

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGlobalPeriods
