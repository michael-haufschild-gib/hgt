import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerSignedPeriods

/-!
# The actual Mayer transfer beyond its defining disc

Subtracting the constant branch value leaves a normally convergent series
on `Re z > -1/2`. Every inverse branch remains in the original disc, so this
continuation uses the given disc-algebra function and agrees with the actual
regularized transfer. Its estimates retain the original boundary value.
-/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerExtendedTransfer

/-- Common domain where every inverse branch stays in the original disc. -/
def halfPlane : Set ℂ := {z | -(1/2 : ℝ)<z.re}

private theorem halfPlane_open : IsOpen halfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem shift_re {n : ℕ} (hn : 1≤n) {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    (n : ℝ)/2≤((n : ℂ)+z).re := by
  have hn' : (1 : ℝ)≤n := by exact_mod_cast hn
  simp only [Complex.add_re,Complex.natCast_re]
  linarith only [hn',hz]

private theorem shift_slit {n : ℕ} (hn : 1≤n) {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    (n : ℂ)+z ∈ Complex.slitPlane := by
  have hn' : (0 : ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl ((half_pos hn').trans_le (shift_re hn hz)))

private theorem shift_ne_zero {n : ℕ} (hn : 1≤n) {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    (n : ℂ)+z ≠ 0 := by
  have hp := shift_re hn hz
  have hn' : (0 : ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  intro he
  rw [he,Complex.zero_re] at hp
  linarith only [hp,hn']

/-- The half-plane geometry supplies the same interior disc for all Gauss branches. -/
theorem inverse_mem {n : ℕ} (hn : 1≤n) {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ((n : ℂ)+z)⁻¹ ∈ closedBall (1 : ℂ) 1 := by
  let a := (n : ℂ)+z
  have hn' : (1 : ℝ)≤n := by exact_mod_cast hn
  have hre : 1/2≤a.re := by
    have h := shift_re hn hz
    dsimp only [a]
    linarith only [hn',h]
  have ha : a≠0 := shift_ne_zero hn hz
  have hs : ‖1-a‖^2≤‖a‖^2 := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im]
    nlinarith only [hre]
  have hb : ‖1-a‖≤‖a‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  have he : a⁻¹-1=(1-a)/a := by field_simp [ha]
  rw [mem_closedBall,dist_eq_norm]
  change ‖a⁻¹-1‖≤1
  rw [he,norm_div]
  exact (div_le_one (norm_pos_iff.mpr ha)).mpr hb

private theorem inverse_norm {n : ℕ} (hn : 1≤n) {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ‖((n : ℂ)+z)⁻¹‖≤2/(n : ℝ) := by
  have hn' : (0 : ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnorm := (shift_re hn hz).trans (Complex.re_le_norm _)
  rw [norm_inv]
  calc ‖(n : ℂ)+z‖⁻¹≤((n : ℝ)/2)⁻¹ :=
      (inv_le_inv₀ ((half_pos hn').trans_le hnorm) (half_pos hn')).mpr hnorm
    _=2/(n : ℝ) := by rw [inv_div]

private theorem norm_cpow_bound {a : ℂ} (ha : a≠0) (w : ℂ) :
    ‖a^(-w)‖≤‖a‖^(-w.re)*Real.exp (Real.pi*|w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero ha,Complex.neg_re,Complex.neg_im,
    mul_neg,Real.exp_neg,div_inv_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  calc a.arg*w.im≤|a.arg*w.im| := le_abs_self _
    _=|a.arg| * |w.im| := abs_mul _ _
    _≤Real.pi*|w.im| := mul_le_mul_of_nonneg_right
      (abs_le.mpr ⟨(Complex.neg_pi_lt_arg a).le,Complex.arg_le_pi a⟩) (abs_nonneg _)

private theorem weight_bound {w : ℂ} (hw : 0<w.re) {n : ℕ} (hn : 1≤n)
    {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ‖((n : ℂ)+z)^(-w)‖≤powerBound w*(n : ℝ)^(-w.re) := by
  have hn' : (0 : ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnorm := (shift_re hn hz).trans (Complex.re_le_norm _)
  refine (norm_cpow_bound (shift_ne_zero hn hz) w).trans ?_
  have hp := Real.rpow_le_rpow_of_nonpos (half_pos hn') hnorm (neg_nonpos.mpr hw.le)
  calc ‖(n : ℂ)+z‖^(-w.re)*Real.exp (Real.pi*|w.im|)
      ≤((n : ℝ)/2)^(-w.re)*Real.exp (Real.pi*|w.im|) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _=powerBound w*(n : ℝ)^(-w.re) := by
      rw [Real.div_rpow hn'.le (by norm_num),Real.rpow_neg (by norm_num : (0 : ℝ)≤2),
        div_inv_eq_mul]
      unfold powerBound
      ring

private theorem weight_deriv (w : ℂ) {n : ℕ} (hn : 1≤n)
    {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    HasDerivAt (fun u : ℂ => ((n : ℂ)+u)^(-w))
      (-w*((n : ℂ)+z)^(-(w+1))) z := by
  have h := ((hasDerivAt_id z).const_add (n : ℂ)).cpow_const (c := -w) (shift_slit hn hz)
  simpa only [id_eq,mul_one,show -w-1=-(w+1) by ring] using h

private theorem weight_deriv_bound {w : ℂ} (hw : 0<w.re) {n : ℕ} (hn : 1≤n)
    {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ‖deriv (fun u : ℂ => ((n : ℂ)+u)^(-w)) z‖≤
      ‖w‖*powerBound (w+1)*(n : ℝ)^(-w.re-1) := by
  rw [(weight_deriv w hn hz).deriv,norm_mul,norm_neg]
  have hw' : 0<(w+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith only [hw]
  have h := mul_le_mul_of_nonneg_left (weight_bound hw' hn hz) (norm_nonneg w)
  simpa only [Complex.add_re,Complex.one_re,neg_add,sub_eq_add_neg,mul_assoc] using h

private theorem weight_difference {w : ℂ} (hw : 0<w.re) {n : ℕ} (hn : 1≤n)
    {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ‖((n : ℂ)+z)^(-w)-(n : ℂ)^(-w)‖≤
      (‖w‖*powerBound (w+1)*(n : ℝ)^(-w.re-1))*‖z‖ := by
  have hc : Convex ℝ {u : ℂ | -(1/2 : ℝ)≤u.re} := convex_halfSpace_re_ge _
  have h := hc.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (weight_deriv w hn hu).differentiableAt)
    (fun u hu => weight_deriv_bound hw hn hu)
    (by norm_num : (0 : ℂ) ∈ {u : ℂ | -(1/2 : ℝ)≤u.re}) hz
  simpa only [add_zero,sub_zero] using h

private theorem deriv_plane_bound (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) : ‖deriv (plane f) z‖≤4*‖f‖ := by
  have hsub : closedBall z (1/4) ⊆ MayerCutoff.inner := by
    intro u hu
    have hz' : ‖z-1‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hu' : ‖u-z‖≤(1/4 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hu
    rw [MayerCutoff.inner,mem_ball,dist_eq_norm,show u-1=(u-z)+(z-1) by ring]
    exact (norm_add_le _ _).trans_lt (by linarith only [hz',hu'])
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ)<1/4)
    ((differentiableOn_plane f).diffContOnCl_ball hsub)
    (fun u hu => norm_plane_le f (ball_subset_closedBall (hsub (sphere_subset_closedBall hu))))
  convert h using 1
  ring

private theorem plane_difference (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) : ‖plane f z-plane f 0‖≤4*‖f‖*‖z‖ := by
  have h := (convex_closedBall (1 : ℂ) (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (differentiableOn_plane f).differentiableAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num : (1 : ℝ)<3/2) hu)))
    (fun u hu => deriv_plane_bound f hu)
    (by norm_num [mem_closedBall,dist_eq_norm] : (0 : ℂ) ∈ closedBall (1 : ℂ) 1) hz
  simpa only [sub_zero] using h

/-- One literal branch with its constant divergence removed. -/
def term (w : ℂ) (f : DiscSpace) (n : ℕ) (z : ℂ) : ℂ :=
  (((n+1 : ℕ) : ℂ)+z)^(-w)*plane f ((((n+1 : ℕ) : ℂ)+z)⁻¹)-
    ((n+1 : ℕ) : ℂ)^(-w)*plane f 0

private def localBound (w : ℂ) (f : DiscSpace) (z : ℂ) : ℝ :=
  (8*powerBound w+‖z‖*‖w‖*powerBound (w+1))*‖f‖

private theorem term_bound {w : ℂ} (hw : 0<w.re) (f : DiscSpace) (n : ℕ)
    {z : ℂ} (hz : -(1/2 : ℝ)≤z.re) :
    ‖term w f n z‖≤localBound w f z*((n+1 : ℕ) : ℝ)^(-w.re-1) := by
  have hn : 1≤n+1 := Nat.succ_pos n
  have hn' : (0 : ℝ)<(n+1 : ℕ) := by positivity
  have hdiff := (plane_difference f (inverse_mem hn hz)).trans
    (mul_le_mul_of_nonneg_left (inverse_norm hn hz) (by positivity))
  have hout : (0 : ℂ) ∈ outer := zeroPoint.2
  have hzero := norm_plane_le f hout
  have he : term w f n z=
      (((n+1 : ℕ) : ℂ)+z)^(-w)*(plane f ((((n+1 : ℕ) : ℂ)+z)⁻¹)-plane f 0)+
      ((((n+1 : ℕ) : ℂ)+z)^(-w)-((n+1 : ℕ) : ℂ)^(-w))*plane f 0 := by
    unfold term
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_mul]
  have hfirst := mul_le_mul (weight_bound hw hn hz) hdiff (norm_nonneg _)
    (mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hp1 := (powerBound_pos (w+1)).le
  have hsecond := mul_le_mul (weight_difference hw hn hz) hzero (norm_nonneg _)
    (by positivity : 0≤(‖w‖*powerBound (w+1)*((n+1 : ℕ) : ℝ)^(-w.re-1))*‖z‖)
  refine (add_le_add hfirst hsecond).trans_eq ?_
  rw [Real.rpow_sub hn',Real.rpow_one]
  unfold localBound
  ring

private theorem term_differentiable (w : ℂ) (f : DiscSpace) (n : ℕ)
    {z : ℂ} (hz : z ∈ halfPlane) : DifferentiableAt ℂ (term w f n) z := by
  have hn : 1≤n+1 := Nat.succ_pos n
  have hz' : -(1/2 : ℝ)≤z.re := hz.le
  have hin := inverse_mem hn hz'
  have hf := (differentiableOn_plane f).differentiableAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num : (1 : ℝ)<3/2) hin))
  have hi : DifferentiableAt ℂ (fun u : ℂ => (((n+1 : ℕ) : ℂ)+u)⁻¹) z :=
    ((differentiableAt_id).const_add ((n+1 : ℕ) : ℂ)).inv (shift_ne_zero hn hz')
  exact (((weight_deriv w hn hz').differentiableAt.mul (hf.comp z hi)).sub_const _)

/-- The literal branch correction converges normally on its full half-plane. -/
theorem term_locallyUniform {w : ℂ} (hw : 0<w.re) (f : DiscSpace) :
    SummableLocallyUniformlyOn (term w f) halfPlane := by
  apply SummableLocallyUniformlyOn_of_locally_bounded halfPlane_open
  intro K hK hKc
  have hc : Continuous (localBound w f) := by unfold localBound; fun_prop
  obtain ⟨C,hC⟩ := hKc.bddAbove_image hc.continuousOn
  have hs : Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-w.re-1)) := by
    rw [show -w.re-1=-(w.re+1) by ring]
    exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(w.re+1))) 1).mpr
      (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))
  refine ⟨fun n => C*((n+1 : ℕ) : ℝ)^(-w.re-1),hs.mul_left C,?_⟩
  intro n z hzK
  exact (term_bound hw f n (hK hzK).le).trans
    (mul_le_mul_of_nonneg_right (hC ⟨z,hzK,rfl⟩) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The extended transfer uses the original disc function in every branch. -/
def transfer (w : ℂ) (f : DiscSpace) (z : ℂ) : ℂ :=
  riemannZeta w*plane f 0+∑' n, term w f n z

/-- The actual regularized transfer has a holomorphic continuation to `Re z>-1/2`. -/
theorem transfer_differentiableOn {w : ℂ} (hw : 0<w.re) (f : DiscSpace) :
    DifferentiableOn ℂ (transfer w f) halfPlane := by
  have hs := SummableLocallyUniformlyOn.differentiableOn halfPlane_open
    (term_locallyUniform hw f) (fun n z hz => term_differentiable w f n hz)
  exact (differentiableOn_const (riemannZeta w*plane f 0)).add hs

/-- The extended value is the original source operator on its defining disc. -/
theorem transfer_eq_source {w : ℂ} (hw : 0<w.re) (f : DiscSpace) (z : Disc) :
    transfer w f z=evaluation z (regularized w hw f) := by
  have hz0 : plane f 0=f.1 zeroPoint := plane_eq f zeroPoint
  have hs := ((evaluation z).comp (ContinuousLinearMap.apply ℂ DiscSpace f)).hasSum
    (remainder_locallyUniform.summable hw).hasSum
  change HasSum (fun n => evaluation z (entireRemainder n w f))
    (evaluation z (remainder w f)) at hs
  have he (n : ℕ) : evaluation z (entireRemainder n w f)=term w f n z := by
    rw [entireRemainder_eq hw,branchRemainder]
    change evaluation z (branch w hw (n+1) (Nat.succ_pos n) f)-
      ((n+1 : ℕ) : ℂ)^(-w)*f.1 zeroPoint=term w f n z
    rw [evaluation_apply,branch_apply]
    unfold term
    rw [hz0]
  have hs' : HasSum (fun n => term w f n z) (evaluation z (remainder w f)) := by
    simpa only [he] using hs
  have hsum : (∑' n,term w f n z)=evaluation z (remainder w f) := hs'.tsum_eq
  rw [transfer,hsum,← source_eq hw,source]
  change riemannZeta w*plane f 0+evaluation z (remainder w f)=
    riemannZeta w*f.1 zeroPoint+evaluation z (remainder w f)
  rw [hz0]

private theorem first_term (w : ℂ) (f : DiscSpace) (z : ℂ) :
    term w f 0 z=(1+z)^(-w)*plane f ((1+z)⁻¹)-plane f 0 := by
  simp only [term,Nat.zero_add,Nat.cast_one,Complex.one_cpow,one_mul]

/-- The first-branch renewal identity persists on the whole continuation domain. -/
theorem transfer_shift {w : ℂ} (hw : 0<w.re) (f : DiscSpace)
    {z : ℂ} (hz : z ∈ halfPlane) :
    transfer w f z-transfer w f (z+1)=(1+z)^(-w)*plane f ((1+z)⁻¹) := by
  let D : ℂ → ℂ := fun u => transfer w f u-transfer w f (u+1)-term w f 0 u-plane f 0
  have hd : AnalyticOnNhd ℂ D halfPlane := by
    apply DifferentiableOn.analyticOnNhd _ halfPlane_open
    intro u hu
    have hu1 : u+1 ∈ halfPlane := by
      change -(1/2 : ℝ)<(u+1).re
      have hu' : -(1/2 : ℝ)<u.re := hu
      simp only [Complex.add_re,Complex.one_re]
      linarith only [hu']
    have h0 := (transfer_differentiableOn hw f).differentiableAt (halfPlane_open.mem_nhds hu)
    have h1 := (transfer_differentiableOn hw f).differentiableAt (halfPlane_open.mem_nhds hu1)
    have hi : DifferentiableAt ℂ (fun v : ℂ => v+1) u := by fun_prop
    simpa only [D,Function.comp_def] using!
      (((h0.sub (h1.comp u hi)).sub (term_differentiable w f 0 hu)).sub_const (plane f 0)).differentiableWithinAt
  have hevent : D =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ)<1/4)] with u hu
    have hn : ‖u‖<1/4 := by simpa only [mem_ball,dist_zero_right] using hu
    have hu0 : u ∈ outer := by
      rw [outer,mem_closedBall,dist_eq_norm]
      have h := norm_sub_le u (1 : ℂ)
      rw [norm_one] at h
      linarith only [h,hn]
    have hu1 : u+1 ∈ outer := by
      rw [outer,mem_closedBall,dist_eq_norm,add_sub_cancel_right]
      linarith only [hn]
    let q : Disc := ⟨u,hu0⟩
    let q' : Disc := ⟨u+1,hu1⟩
    have ht := MayerSignedPeriods.operator_shift hw f q q' rfl
    have hq : transfer w f u=evaluation q (regularized w hw f) := transfer_eq_source hw f q
    have hq' : transfer w f (u+1)=evaluation q' (regularized w hw f) := transfer_eq_source hw f q'
    change evaluation q (regularized w hw f)-evaluation q' (regularized w hw f)=
      (1+u)^(-w)*plane f ((1+u)⁻¹) at ht
    change D u=0
    dsimp only [D]
    rw [hq,hq',first_term]
    linear_combination ht
  have hc : IsPreconnected halfPlane := (convex_halfSpace_re_gt (-(1/2 : ℝ))).isPreconnected
  have he := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc
    (by norm_num [halfPlane] : (0 : ℂ) ∈ halfPlane) hevent hz
  change D z=0 at he
  dsimp only [D] at he
  rw [first_term] at he
  linear_combination he

#print axioms transfer_shift

#print axioms inverse_mem
#print axioms term_locallyUniform
#print axioms transfer_differentiableOn
#print axioms transfer_eq_source

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerExtendedTransfer
