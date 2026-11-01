import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRawNegativeUnitDeterminants

/-!
# Positive derivative cone for the actual Mayer remainder

For real `w>0`, the exact response has positive derivative
`h_w(x)=w(1+x)^(-w-1)` on `[0,1]`. The negative derivative of the
actual remainder, normalized by `h_w`, contains the same first-branch
contribution `f(1/2)` at every source point. Its remaining mass is exactly
`(3/2)^(-w)`.

Bounded Cauchy derivative evaluation justifies the actual branch derivative
series. Positivity and compact extrema force every centered real derivative
eigenmode with eigenvalue greater than this remaining mass to vanish.
Both complex components are treated, and the analytic identity principle
recovers equality on the original closed-disc Banach space.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRaw
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDerivative

private theorem smaller_interior {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) : z ∈ MayerCutoff.inner :=
  closedBall_subset_ball (by norm_num : (1 : ℝ) < 3/2) hz

private theorem differentiableAt_plane (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) : DifferentiableAt ℂ (plane f) z :=
  (differentiableOn_plane f).differentiableAt (isOpen_ball.mem_nhds (smaller_interior hz))

/-- Cauchy's estimate bounds interior derivative evaluation on the actual disc algebra. -/
theorem norm_deriv_plane_le (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) : ‖deriv (plane f) z‖ ≤ 4*‖f‖ := by
  have hsub : closedBall z (1/4 : ℝ) ⊆ MayerCutoff.inner := by
    intro v hv
    have hz' : ‖z-1‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hv' : ‖v-z‖ ≤ (1/4 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hv
    rw [mem_ball,dist_eq_norm,show v-1=(v-z)+(z-1) by ring]
    exact (norm_add_le _ _).trans_lt (by linarith only [hz',hv'])
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1/4)
    ((differentiableOn_plane f).diffContOnCl_ball hsub)
    (fun v hv => norm_plane_le f (ball_subset_closedBall (hsub (sphere_subset_closedBall hv))))
  exact h.trans_eq (by ring)

private theorem plane_add (f g : DiscSpace) : plane (f+g) = plane f+plane g :=
  holoExtend_add _ _

private theorem plane_smul (c : ℂ) (f : DiscSpace) : plane (c • f) = c • plane f :=
  holoExtend_smul c _

/-- Bounded derivative evaluation permits passage from finite branch sums to the actual operator. -/
def derivativeEvaluation (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) 1) : DiscSpace →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => deriv (plane f) z
      map_add' := fun f g => by
        rw [plane_add,deriv_add (differentiableAt_plane f hz) (differentiableAt_plane g hz)]
      map_smul' := fun c f => by
        rw [plane_smul]
        exact ((differentiableAt_plane f hz).hasDerivAt.const_smul c).deriv }
    4 (fun f => norm_deriv_plane_le f hz)

@[simp] theorem derivativeEvaluation_apply (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) 1)
    (f : DiscSpace) : derivativeEvaluation z hz f = deriv (plane f) z := rfl

/-- The real unit interval lies strictly inside the source disc. -/
theorem interval_mem_smallDisc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (x : ℂ) ∈ closedBall (1 : ℂ) 1 := by
  rw [mem_closedBall,dist_eq_norm,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx.2)]
  linarith only [hx.1]

/-- Holomorphy makes the source derivative continuous on the interior disc. -/
theorem continuousOn_deriv_plane (f : DiscSpace) :
    ContinuousOn (deriv (plane f)) MayerCutoff.inner := by
  have ha := (differentiableOn_plane f).analyticOnNhd isOpen_ball
  exact fun z hz => (ha.deriv z hz).continuousAt.continuousWithinAt

/-- Nonnegative real derivative gives monotonicity along the source interval. -/
theorem monotoneOn_real_plane (f : DiscSpace)
    (hderiv : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (x : ℂ)).re) :
    MonotoneOn (fun x : ℝ => (plane f (x : ℂ)).re) (Icc (0 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => (plane f (t : ℂ)).re)
        (deriv (plane f) (x : ℂ)).re x :=
    (differentiableAt_plane f (interval_mem_smallDisc hx)).hasDerivAt.real_of_complex
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hderiv x (interior_subset hx)

private theorem digit_re_pos {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) : 0 < ((n : ℂ)+z).re := by
  have hr := (neg_le_abs (z-1).re).trans (Complex.abs_re_le_norm (z-1))
  have hd : ‖z-1‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Complex.sub_re,Complex.one_re] at hr
  simp only [Complex.add_re,Complex.natCast_re]
  linarith only [hr,hd,hn']

/-- Differentiating a genuine Gauss branch retains both positive real source terms. -/
theorem deriv_branch {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n)
    (f : DiscSpace) {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    deriv (plane (branch w hw n hn f)) z =
      -w*((n : ℂ)+z)^(-w-1)*plane f (((n : ℂ)+z)⁻¹) -
        (((n : ℂ)+z)^(-w)/((n : ℂ)+z)^2)*deriv (plane f) (((n : ℂ)+z)⁻¹) := by
  have hzout := ball_subset_closedBall (smaller_interior hz)
  have hr := digit_re_pos hn hz
  have ha : (n : ℂ)+z ≠ 0 := by
    intro he
    rw [he,Complex.zero_re] at hr
    exact lt_irrefl _ hr
  have hweight := ((hasDerivAt_id z).const_add (n : ℂ)).cpow_const
    (c := -w) (Complex.mem_slitPlane_iff.mpr (Or.inl hr))
  have hinv := ((hasDerivAt_id z).const_add (n : ℂ)).inv ha
  have hf := (differentiableAt_plane f (inverse_branch_inner hn hzout)).hasDerivAt
  have he : plane (branch w hw n hn f) =ᶠ[𝓝 z]
      (fun y : ℂ => ((n : ℂ)+y)^(-w)*plane f (((n : ℂ)+y)⁻¹)) := by
    filter_upwards [isOpen_ball.mem_nhds (smaller_interior hz)] with y hy
    rw [plane_eq (branch w hw n hn f) ⟨y,ball_subset_closedBall hy⟩,branch_apply]
  have hd := (hweight.mul (hf.comp z hinv)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [id_eq,mul_one,Function.comp_apply,Pi.inv_apply]
  change -w*((n : ℂ)+z)^(-w-1)*plane f (((n : ℂ)+z)⁻¹) +
    ((n : ℂ)+z)^(-w)*(deriv (plane f) (((n : ℂ)+z)⁻¹)*(-1/((n : ℂ)+z)^2)) = _
  ring

/-- Derivative of the exact successor response. -/
theorem deriv_response (w : ℂ) {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    deriv (plane (MayerCancellation.response w)) z = w*(1+z)^(-w-1) := by
  have hr : 0 < (1+z).re := by
    simpa only [Nat.cast_one] using digit_re_pos (n := 1) le_rfl hz
  have hweight := ((hasDerivAt_id z).const_add 1).cpow_const
    (c := -w) (Complex.mem_slitPlane_iff.mpr (Or.inl hr))
  have he : plane (MayerCancellation.response w) =ᶠ[𝓝 z]
      (fun y : ℂ => 1-(1+y)^(-w)) := by
    filter_upwards [isOpen_ball.mem_nhds (smaller_interior hz)] with y hy
    rw [plane_eq (MayerCancellation.response w) ⟨y,ball_subset_closedBall hy⟩,
      MayerCancellation.response_apply]
  have hd := (hweight.const_sub 1).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [id_eq,mul_one]
  ring

/-- Interior derivative evaluation annihilates the scalar constant mode. -/
theorem derivativeEvaluation_constant (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) 1) (c : ℂ) :
    derivativeEvaluation z hz (constant c) = 0 := by
  have he : plane (constant c) =ᶠ[𝓝 z] (fun _ : ℂ => c) := by
    filter_upwards [isOpen_ball.mem_nhds (smaller_interior hz)] with y hy
    rw [plane_eq (constant c) ⟨y,ball_subset_closedBall hy⟩]
    rfl
  exact ((hasDerivAt_const z c).congr_of_eventuallyEq he).deriv

private theorem derivativeEvaluation_branchRemainder {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) 1) :
    derivativeEvaluation z hz (branchRemainder w hw n hn f) =
      derivativeEvaluation z hz (branch w hw n hn f) := by
  change derivativeEvaluation z hz
    (branch w hw n hn f-(n : ℂ)^(-w) • constant (f.1 zeroPoint)) = _
  rw [map_sub,map_smul,derivativeEvaluation_constant,smul_zero,sub_zero]

/-- The actual branch derivative series converges by bounded interior derivative evaluation. -/
theorem hasSum_deriv_branch {w : ℂ} (hw : 0 < w.re) (f : DiscSpace)
    (z : ℂ) (hz : z ∈ closedBall (1 : ℂ) 1) :
    HasSum (fun n : ℕ => deriv (plane (branch w hw (n+1) (Nat.succ_pos n) f)) z)
      (deriv (plane (remainder w f)) z) := by
  have hs := (derivativeEvaluation z hz).hasSum
    ((ContinuousLinearMap.apply ℂ DiscSpace f).hasSum
      (remainder_locallyUniform.summable hw).hasSum)
  change HasSum (fun n : ℕ => derivativeEvaluation z hz (entireRemainder n w f))
    (derivativeEvaluation z hz (remainder w f)) at hs
  simpa only [entireRemainder_eq hw,derivativeEvaluation_branchRemainder hw,
    derivativeEvaluation_apply] using hs

#print axioms derivativeEvaluation_constant
#print axioms hasSum_deriv_branch
#print axioms norm_deriv_plane_le
#print axioms derivativeEvaluation
#print axioms monotoneOn_real_plane
#print axioms deriv_branch
#print axioms deriv_response
theorem plane_zero (f : DiscSpace) : plane f (0 : ℂ) = f.1 zeroPoint :=
  plane_eq f zeroPoint

/-- Zero real derivative on the source interval fixes the real part by its value at zero. -/
theorem real_plane_zero_of_real_deriv_zero (f : DiscSpace)
    (hf0 : (plane f (0 : ℂ)).re = 0)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, (deriv (plane f) (x : ℂ)).re = 0)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (plane f (y : ℂ)).re = 0 := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => (plane f (t : ℂ)).re) 0 x := by
    have h := (differentiableAt_plane f (interval_mem_smallDisc hx)).hasDerivAt.real_of_complex
    rwa [hf x hx] at h
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hd x hx).differentiableAt)
    (fun x hx => by rw [(hd x hx).deriv,norm_zero])
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hy
  have he : (plane f (y : ℂ)).re-(plane f (0 : ℂ)).re = 0 :=
    norm_le_zero_iff.mp (by simpa only [zero_mul,Complex.ofReal_zero] using h)
  exact (sub_eq_zero.mp he).trans hf0

private theorem continuousOn_plane_outer (f : DiscSpace) : ContinuousOn (plane f) outer := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun z : Disc => plane f z.1)
  have he : (fun z : Disc => plane f z.1) = (fun z : Disc => f.1 z) :=
    funext fun z => plane_eq f z
  rw [he]
  exact f.1.continuous

/-- Restriction to the real unit interval is injective on the actual Banach disc algebra. -/
theorem eq_zero_of_real_interval (f : DiscSpace)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, plane f (x : ℂ) = 0) : f = 0 := by
  have hbase : Tendsto (fun n : ℕ => ((1/(n+1 : ℝ) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    have hr : Tendsto (fun n : ℕ => (1/(n+1 : ℝ))) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    rw [Complex.ofReal_zero] at hc
    change Tendsto (fun n : ℕ => ((1/((n : ℝ)+1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) at hc
    exact hc
  have hpunc : Tendsto (fun n : ℕ => ((1/(n+1 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase ?_
    filter_upwards with n
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff,Complex.ofReal_eq_zero]
    positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), plane f z = 0 :=
    hpunc.frequently (Filter.Frequently.of_forall fun n => hf _ (by
      constructor
      · positivity
      · apply (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr
        linarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]))
  have ha := (differentiableOn_plane f).analyticOnNhd isOpen_ball
  have hinner : EqOn (plane f) (fun _ => (0 : ℂ)) MayerCutoff.inner :=
    ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (1 : ℂ) (3/2 : ℝ)).isPreconnected
      (by norm_num [MayerCutoff.inner,mem_ball,dist_eq_norm]) hfreq
  have hclosure : outer ⊆ closure MayerCutoff.inner := by
    rw [show closure MayerCutoff.inner = outer from closure_ball (1 : ℂ) (by norm_num)]
  have houter := hinner.of_subset_closure (continuousOn_plane_outer f) continuousOn_const
    ball_subset_closedBall hclosure
  apply Subtype.ext
  ext z
  change f.1 z = 0
  rw [← plane_eq f z]
  exact houter z.property

#print axioms real_plane_zero_of_real_deriv_zero
#print axioms eq_zero_of_real_interval
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDerivative

open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDerivative
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive

/-- Positive derivative of the exact real successor response. -/
def ground (w x : ℝ) : ℝ := w*(1+x)^(-w-1)

theorem ground_pos {w x : ℝ} (hw : 0 < w) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < ground w x :=
  mul_pos hw (Real.rpow_pos_of_pos (by linarith only [hx.1]) _)

private theorem digit_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < (n : ℝ)+x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith only [hn',hx.1]

private theorem inverse_mem_interval {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ((n : ℝ)+x)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  have ha := digit_pos hn hx
  refine ⟨(inv_pos.mpr ha).le,?_⟩
  apply (inv_le_one₀ ha).mpr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith only [hn',hx.1]

private theorem half_le_first_inverse {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (1/2 : ℝ) ≤ (1+x)⁻¹ := by
  have ha : 0 < 1+x := by linarith only [hx.1]
  rw [← one_div (1+x)]
  apply (le_div_iff₀ ha).mpr
  linarith only [hx.2]

/-- Actual branch differentiation becomes a positive real combination of source values and jets. -/
theorem neg_deriv_branch_real {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n)
    (f : DiscSpace) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    -deriv (plane (branch (w : ℂ) (by simpa only [Complex.ofReal_re] using hw) n hn f))
      (x : ℂ) =
      ((w*((n : ℝ)+x)^(-w-1) : ℝ) : ℂ)*plane f ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ) +
      ((((n : ℝ)+x)^(-w)/((n : ℝ)+x)^2 : ℝ) : ℂ)*
        deriv (plane f) ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ) := by
  have ha := digit_pos hn hx
  have hc : (n : ℂ)+(x : ℂ) = (((n : ℝ)+x : ℝ) : ℂ) := by push_cast; rfl
  rw [deriv_branch _ hn f (interval_mem_smallDisc hx),hc,
    show -(w : ℂ)-1 = ((-w-1 : ℝ) : ℂ) by push_cast; rfl,
    show -(w : ℂ) = ((-w : ℝ) : ℂ) by simp only [Complex.ofReal_neg],
    ← Complex.ofReal_cpow ha.le,← Complex.ofReal_cpow ha.le,
    ← Complex.ofReal_inv]
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg]
  ring

private theorem neg_deriv_branch_re {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n)
    (f : DiscSpace) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (-deriv (plane (branch (w : ℂ) (by simpa only [Complex.ofReal_re] using hw) n hn f))
      (x : ℂ)).re =
      (w*((n : ℝ)+x)^(-w-1))*(plane f ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ)).re +
      (((n : ℝ)+x)^(-w)/((n : ℝ)+x)^2)*
        (deriv (plane f) ((((n : ℝ)+x)⁻¹ : ℝ) : ℂ)).re := by
  simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using congrArg Complex.re (neg_deriv_branch_real hw hn f hx)

private theorem real_plane_nonneg (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (x : ℂ)).re)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ (plane f (y : ℂ)).re := by
  have hzero : plane f (0 : ℂ) = 0 := (plane_eq f zeroPoint).trans hf0
  have h := monotoneOn_real_plane f hf (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hy hy.1
  simpa only [Complex.ofReal_zero,hzero,Complex.zero_re] using h

private theorem branch_real_nonneg {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n)
    (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (x : ℂ)).re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ (-deriv (plane (branch (w : ℂ) (by simpa only [Complex.ofReal_re] using hw) n hn f))
      (x : ℂ)).re := by
  rw [neg_deriv_branch_re hw hn f hx]
  have ha := digit_pos hn hx
  have hu := inverse_mem_interval hn hx
  exact add_nonneg
    (mul_nonneg (mul_nonneg hw.le (Real.rpow_nonneg ha.le _)) (real_plane_nonneg f hf0 hf hu))
    (mul_nonneg (div_nonneg (Real.rpow_nonneg ha.le _) (sq_nonneg _)) (hf _ hu))

private theorem first_branch_minorization {w : ℝ} (hw : 0 < w)
    (f : DiscSpace)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (x : ℂ)).re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ground w x*(plane f (1/2 : ℂ)).re ≤
      (-deriv (plane (branch (w : ℂ) (by simpa only [Complex.ofReal_re] using hw) 1 le_rfl f))
        (x : ℂ)).re := by
  rw [neg_deriv_branch_re hw le_rfl f hx]
  simp only [Nat.cast_one]
  have hu : (1+x)⁻¹ ∈ Icc (0 : ℝ) 1 := by
    simpa only [Nat.cast_one] using inverse_mem_interval (n := 1) le_rfl hx
  have hm := monotoneOn_real_plane f hf (by norm_num : (1/2 : ℝ) ∈ Icc (0 : ℝ) 1)
    hu (half_le_first_inverse hx)
  have hm' : (plane f (1/2 : ℂ)).re ≤ (plane f (((1+x)⁻¹ : ℝ) : ℂ)).re := by
    simpa using hm
  have ha : 0 < 1+x := by linarith only [hx.1]
  exact (mul_le_mul_of_nonneg_left hm' (ground_pos hw hx).le).trans
    (le_add_of_nonneg_right
      (mul_nonneg (div_nonneg (Real.rpow_nonneg ha.le _) (sq_nonneg _)) (hf _ hu)))

/-- The actual remainder derivative dominates one common interior evaluation on the derivative cone. -/
theorem source_minorization {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (hf0 : f.1 zeroPoint = 0)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (x : ℂ)).re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ground w x*(plane f (1/2 : ℂ)).re ≤ (-deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re := by
  have hwC : 0 < (w : ℂ).re := by simpa only [Complex.ofReal_re] using hw
  have hs := Complex.reCLM.hasSum
    (hasSum_deriv_branch hwC f (x : ℂ) (interval_mem_smallDisc hx)).neg
  have hsplit := hs.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [hs.tsum_eq] at hsplit
  have htail : 0 ≤ ∑' k : ℕ,
      (-deriv (plane (branch (w : ℂ) hwC (k+1+1) (Nat.succ_pos (k+1)) f)) (x : ℂ)).re :=
    tsum_nonneg fun k => branch_real_nonneg hw (Nat.succ_pos (k+1)) f hf0 hf hx
  have hfirst := first_branch_minorization hw f hf hx
  change (-deriv (plane (branch (w : ℂ) hwC 1 le_rfl f)) (x : ℂ)).re +
    (∑' k : ℕ, (-deriv (plane (branch (w : ℂ) hwC (k+1+1) (Nat.succ_pos (k+1)) f))
      (x : ℂ)).re) = (-deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re at hsplit
  linarith only [hfirst,hsplit,htail]

/-- The successor response on the real source interval is the real power difference. -/
theorem response_real (w : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    plane (MayerCancellation.response (w : ℂ)) (x : ℂ) =
      ((1-(1+x)^(-w) : ℝ) : ℂ) := by
  have hxout : (x : ℂ) ∈ outer := closedBall_subset_closedBall
    (by norm_num : (1 : ℝ) ≤ 3/2) (interval_mem_smallDisc hx)
  have ha : 0 < 1+x := by linarith only [hx.1]
  rw [plane_eq (MayerCancellation.response (w : ℂ)) ⟨x,hxout⟩,
    MayerCancellation.response_apply]
  rw [show (1 : ℂ)+(x : ℂ) = ((1+x : ℝ) : ℂ) by push_cast; rfl,
    show -(w : ℂ) = ((-w : ℝ) : ℂ) by simp only [Complex.ofReal_neg],← Complex.ofReal_cpow ha.le]
  simp only [Complex.ofReal_sub,Complex.ofReal_one]

/-- The actual response derivative equals the positive real ground weight. -/
theorem deriv_response_real (w : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (plane (MayerCancellation.response (w : ℂ))) (x : ℂ) = (ground w x : ℂ) := by
  have ha : 0 < 1+x := by linarith only [hx.1]
  rw [deriv_response (w : ℂ) (interval_mem_smallDisc hx)]
  rw [show (1 : ℂ)+(x : ℂ) = ((1+x : ℝ) : ℂ) by push_cast; rfl,
    show -(w : ℂ)-1 = ((-w-1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ha.le]
  simp only [ground,Complex.ofReal_mul]

private theorem response_zero (w : ℝ) : (MayerCancellation.response (w : ℂ)).1 zeroPoint = 0 := by
  rw [MayerCancellation.response_apply]
  change (1 : ℂ)-(1+0)^(-(w : ℂ))=0
  rw [add_zero,Complex.one_cpow,sub_self]

/-- Real derivative divided by the exact response weight. -/
def normalizedDerivative (w : ℝ) (f : DiscSpace) (x : ℝ) : ℝ :=
  (deriv (plane f) (x : ℂ)).re/ground w x

private theorem real_deriv_continuous (f : DiscSpace) :
    ContinuousOn (fun x : ℝ => (deriv (plane f) (x : ℂ)).re) (Icc (0 : ℝ) 1) := by
  have hs : ∀ x ∈ Icc (0 : ℝ) 1, (x : ℂ) ∈ MayerCutoff.inner :=
    fun x hx => closedBall_subset_ball (by norm_num : (1 : ℝ) < 3/2)
      (interval_mem_smallDisc hx)
  have hd := (continuousOn_deriv_plane f).comp Complex.continuous_ofReal.continuousOn hs
  exact Complex.continuous_re.comp_continuousOn hd

/-- The normalized real source derivative attains both extrema on the unit interval. -/
theorem normalizedDerivative_continuous {w : ℝ} (hw : 0 < w) (f : DiscSpace) :
    ContinuousOn (normalizedDerivative w f) (Icc (0 : ℝ) 1) := by
  have hg : ContinuousOn (ground w) (Icc (0 : ℝ) 1) := by
    apply (real_deriv_continuous (MayerCancellation.response (w : ℂ))).congr
    intro x hx
    change ground w x = (deriv (plane (MayerCancellation.response (w : ℂ))) (x : ℂ)).re
    rw [deriv_response_real w hx,Complex.ofReal_re]
  exact (real_deriv_continuous f).div hg (fun x hx => (ground_pos hw hx).ne')

#print axioms response_real
#print axioms deriv_response_real
#print axioms normalizedDerivative_continuous
private theorem deriv_plane_sub (f g : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) :
    deriv (plane (f-g)) z = deriv (plane f) z-deriv (plane g) z :=
  (derivativeEvaluation z hz).map_sub f g

private theorem deriv_plane_smul (c : ℂ) (f : DiscSpace) {z : ℂ}
    (hz : z ∈ closedBall (1 : ℂ) 1) :
    deriv (plane (c • f)) z = c*deriv (plane f) z :=
  (derivativeEvaluation z hz).map_smul c f

private theorem deriv_remainder_response {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (plane (remainder (w : ℂ) (MayerCancellation.response (w : ℂ)))) (x : ℂ) =
      -(ground w x : ℂ) := by
  change derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)
    (remainder (w : ℂ) (MayerCancellation.response (w : ℂ))) = _
  rw [MayerCancellation.remainder_response (by simpa only [Complex.ofReal_re] using hw),
    map_sub,derivativeEvaluation_constant,zero_sub,derivativeEvaluation_apply,deriv_response_real w hx]

/-- Residual row mass after removing the common first-branch interval. -/
def contraction (w : ℝ) : ℝ := (3/2 : ℝ)^(-w)

private def halfPoint : Disc := ⟨1/2,by norm_num [outer,mem_closedBall,dist_eq_norm]⟩

private theorem plane_half (f : DiscSpace) : plane f (1/2 : ℂ) = f.1 halfPoint :=
  plane_eq f halfPoint

/-- The actual normalized negative derivative after removing its common evaluation at one half. -/
def minorizedDerivative (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : DiscSpace →L[ℂ] ℂ :=
  (-(ground w x : ℂ)⁻¹) •
    ((derivativeEvaluation (x : ℂ) (interval_mem_smallDisc hx)).comp (remainder (w : ℂ))) -
      evaluation halfPoint

theorem minorizedDerivative_apply (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (f : DiscSpace) :
    minorizedDerivative w x hx f =
      -(ground w x : ℂ)⁻¹*deriv (plane (remainder (w : ℂ) f)) (x : ℂ)-plane f (1/2 : ℂ) := by
  have hp : plane f (1/2 : ℂ) = f.1 halfPoint := plane_eq f halfPoint
  rw [hp]
  rfl

private theorem minorizedDerivative_real (w x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (f : DiscSpace) :
    (minorizedDerivative w x hx f).re =
      -(ground w x)⁻¹*(deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re-
        (plane f (1/2 : ℂ)).re := by
  rw [minorizedDerivative_apply]
  have hi : -(ground w x : ℂ)⁻¹ = ((-(ground w x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hi]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- The residual derivative functional is positive on the actual real derivative cone. -/
theorem minorizedDerivative_nonneg {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (hf0 : f.1 zeroPoint = 0)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (deriv (plane f) (t : ℂ)).re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ (minorizedDerivative w x hx f).re := by
  have hc := source_minorization hw f hf0 hf hx
  have hh : (plane f (1/2 : ℂ)).re ≤
      -(deriv (plane (remainder (w : ℂ) f)) (x : ℂ)).re/ground w x :=
    (le_div_iff₀ (ground_pos hw hx)).mpr (by simpa only [mul_comm,Complex.neg_re] using hc)
  rw [minorizedDerivative_real]
  exact sub_nonneg.mpr (hh.trans_eq (by ring))

/-- The residual functional has the same exact mass at every source point. -/
theorem minorizedDerivative_response {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    minorizedDerivative w x hx (MayerCancellation.response (w : ℂ)) = (contraction w : ℂ) := by
  rw [minorizedDerivative_apply,deriv_remainder_response hw hx,neg_mul_neg,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ground_pos hw hx).ne')]
  have hr : plane (MayerCancellation.response (w : ℂ)) (1/2 : ℂ) =
      ((1-contraction w : ℝ) : ℂ) := by
    convert response_real w (x := 1/2) (by norm_num) using 1 <;> norm_num [contraction]
  rw [hr]
  simp only [Complex.ofReal_sub,Complex.ofReal_one]
  ring

/-- Common source minorization contracts the interval of normalized real derivatives. -/
theorem minorizedDerivative_bounds {w : ℝ} (hw : 0 < w) (f : DiscSpace)
    (hf0 : f.1 zeroPoint = 0) {m M : ℝ}
    (hbounds : ∀ t ∈ Icc (0 : ℝ) 1,
      m ≤ normalizedDerivative w f t ∧ normalizedDerivative w f t ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    m*contraction w ≤ (minorizedDerivative w x hx f).re ∧
      (minorizedDerivative w x hx f).re ≤ M*contraction w := by
  have hzeroLower : (f-(m : ℂ) • MayerCancellation.response (w : ℂ)).1 zeroPoint = 0 := by
    change f.1 zeroPoint-(m : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint = 0
    rw [hf0,response_zero,mul_zero,sub_zero]
  have hzeroUpper : ((M : ℂ) • MayerCancellation.response (w : ℂ)-f).1 zeroPoint = 0 := by
    change (M : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint-f.1 zeroPoint = 0
    rw [hf0,response_zero,mul_zero,sub_zero]
  have hderivLower : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ (deriv (plane (f-(m : ℂ) • MayerCancellation.response (w : ℂ))) (t : ℂ)).re := by
    intro t ht
    have hb : m*ground w t ≤ (deriv (plane f) (t : ℂ)).re :=
      (le_div_iff₀ (ground_pos hw ht)).mp ((hbounds t ht).1)
    rw [deriv_plane_sub _ _ (interval_mem_smallDisc ht),
      deriv_plane_smul _ _ (interval_mem_smallDisc ht),deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_nonneg.mpr hb
  have hderivUpper : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ (deriv (plane ((M : ℂ) • MayerCancellation.response (w : ℂ)-f)) (t : ℂ)).re := by
    intro t ht
    have hb : (deriv (plane f) (t : ℂ)).re ≤ M*ground w t :=
      (div_le_iff₀ (ground_pos hw ht)).mp ((hbounds t ht).2)
    rw [deriv_plane_sub _ _ (interval_mem_smallDisc ht),
      deriv_plane_smul _ _ (interval_mem_smallDisc ht),deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_nonneg.mpr hb
  have hlo := minorizedDerivative_nonneg hw _ hzeroLower hderivLower hx
  have hhi := minorizedDerivative_nonneg hw _ hzeroUpper hderivUpper hx
  rw [map_sub,map_smul,minorizedDerivative_response hw hx] at hlo hhi
  simp only [smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hlo hhi
  exact ⟨by linarith only [hlo],by linarith only [hhi]⟩

#print axioms minorizedDerivative_nonneg
#print axioms minorizedDerivative_response
#print axioms minorizedDerivative_bounds
theorem contraction_pos (w : ℝ) : 0 < contraction w :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3/2) _

private theorem minorizedDerivative_eigen_real {w μ : ℝ} (f : DiscSpace) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1)
    (heig : deriv (plane (remainder (w : ℂ) f)) (x : ℂ) =
      (μ : ℂ)*deriv (plane f) (x : ℂ)) :
    (minorizedDerivative w x hx f).re =
      -μ*normalizedDerivative w f x-(plane f (1/2 : ℂ)).re := by
  rw [minorizedDerivative_real,heig]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  unfold normalizedDerivative
  rw [div_eq_mul_inv]
  ring

/-- An actual positive derivative eigenmode beyond the residual mass has constant normalized real jet. -/
theorem normalizedDerivative_constant_of_eigen {w μ : ℝ} (hw : 0 < w)
    (hμ : contraction w < μ) (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (heig : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = (μ : ℂ)*deriv (plane f) (x : ℂ)) :
    ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, normalizedDerivative w f x = c := by
  have hn : (Icc (0 : ℝ) 1).Nonempty := ⟨0,by norm_num⟩
  have hc := normalizedDerivative_continuous hw f
  obtain ⟨a,ha,hmin⟩ := isCompact_Icc.exists_isMinOn hn hc
  obtain ⟨b,hb,hmax⟩ := isCompact_Icc.exists_isMaxOn hn hc
  have hbounds (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      normalizedDerivative w f a ≤ normalizedDerivative w f x ∧
        normalizedDerivative w f x ≤ normalizedDerivative w f b := ⟨hmin hx,hmax hx⟩
  have hlo := (minorizedDerivative_bounds hw f hf0 hbounds hb).1
  have hhi := (minorizedDerivative_bounds hw f hf0 hbounds ha).2
  rw [minorizedDerivative_eigen_real f hb (heig b hb)] at hlo
  rw [minorizedDerivative_eigen_real f ha (heig a ha)] at hhi
  have hle : normalizedDerivative w f b ≤ normalizedDerivative w f a := by
    by_contra hh
    have hp := mul_pos (sub_pos.mpr hμ) (sub_pos.mpr (lt_of_not_ge hh))
    nlinarith only [hlo,hhi,hp]
  have heq := le_antisymm hle (hmin hb)
  exact ⟨normalizedDerivative w f a,fun x hx =>
    le_antisymm ((hmax hx).trans_eq heq) (hmin hx)⟩

private theorem real_half_value_of_constant_jet {w : ℝ} (hw : 0 < w)
    (f : DiscSpace) (hf0 : f.1 zeroPoint = 0) (c : ℝ)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, normalizedDerivative w f t = c) :
    (plane f (1/2 : ℂ)).re = c*(1-contraction w) := by
  have hu0 : (plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ)) (0 : ℂ)).re = 0 := by
    rw [plane_zero]
    change (f.1 zeroPoint-(c : ℂ)*(MayerCancellation.response (w : ℂ)).1 zeroPoint).re = 0
    rw [hf0,response_zero,mul_zero,sub_zero,Complex.zero_re]
  have hu : ∀ t ∈ Icc (0 : ℝ) 1,
      (deriv (plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ))) (t : ℂ)).re = 0 := by
    intro t ht
    have hd : (deriv (plane f) (t : ℂ)).re = c*ground w t :=
      (div_eq_iff (ground_pos hw ht).ne').mp (hc t ht)
    rw [deriv_plane_sub _ _ (interval_mem_smallDisc ht),
      deriv_plane_smul _ _ (interval_mem_smallDisc ht),deriv_response_real w ht]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact sub_eq_zero.mpr hd
  have hv := real_plane_zero_of_real_deriv_zero _ hu0 hu (y := 1/2) (by norm_num)
  have hr : plane (MayerCancellation.response (w : ℂ)) (1/2 : ℂ) =
      ((1-contraction w : ℝ) : ℂ) := by
    convert response_real w (x := 1/2) (by norm_num) using 1 <;> norm_num [contraction]
  have hv' : (plane (f-(c : ℂ) • MayerCancellation.response (w : ℂ)) (1/2 : ℂ)).re = 0 := by
    simpa using hv
  rw [plane_half] at hv'
  change (f.1 halfPoint-(c : ℂ)*(MayerCancellation.response (w : ℂ)).1 halfPoint).re = 0 at hv'
  rw [← plane_half f,← plane_half (MayerCancellation.response (w : ℂ)),hr] at hv'
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hv'
  exact sub_eq_zero.mp hv'

private theorem real_deriv_zero_of_eigen {w μ : ℝ} (hw : 0 < w)
    (hμ : contraction w < μ) (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (heig : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = (μ : ℂ)*deriv (plane f) (x : ℂ)) :
    ∀ x ∈ Icc (0 : ℝ) 1, (deriv (plane f) (x : ℂ)).re = 0 := by
  obtain ⟨c,hc⟩ := normalizedDerivative_constant_of_eigen hw hμ f hf0 heig
  have hv := real_half_value_of_constant_jet hw f hf0 c hc
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      c ≤ normalizedDerivative w f x ∧ normalizedDerivative w f x ≤ c := by
    rw [hc x hx]
    exact ⟨le_rfl,le_rfl⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hbounds := minorizedDerivative_bounds hw f hf0 hb hzero
  have he := le_antisymm hbounds.2 hbounds.1
  rw [minorizedDerivative_eigen_real f hzero (heig 0 hzero),hc 0 hzero,hv] at he
  have hm : 0 < μ := (contraction_pos w).trans hμ
  have he' : (μ+1)*c = 0 := by nlinarith only [he]
  have hc0 : c = 0 := (mul_eq_zero.mp he').resolve_left (by linarith only [hm])
  intro x hx
  have h := (div_eq_iff (ground_pos hw hx).ne').mp (hc x hx)
  simpa only [hc0,zero_mul] using h

/-- The genuine remainder has no nonzero centered positive derivative eigenmode beyond its residual mass. -/
theorem derivative_eigen_eq_zero {w μ : ℝ} (hw : 0 < w)
    (hμ : contraction w < μ) (f : DiscSpace) (hf0 : f.1 zeroPoint = 0)
    (heig : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) f)) (x : ℂ) = (μ : ℂ)*deriv (plane f) (x : ℂ)) :
    f = 0 := by
  have hr := real_deriv_zero_of_eigen hw hμ f hf0 heig
  have hI0 : (I • f).1 zeroPoint = 0 := by
    change I*f.1 zeroPoint = 0
    rw [hf0,mul_zero]
  have hIeig : ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (plane (remainder (w : ℂ) (I • f))) (x : ℂ) =
        (μ : ℂ)*deriv (plane (I • f)) (x : ℂ) := by
    intro x hx
    rw [map_smul,deriv_plane_smul I _ (interval_mem_smallDisc hx),
      deriv_plane_smul I _ (interval_mem_smallDisc hx),heig x hx]
    ring
  have hi := real_deriv_zero_of_eigen hw hμ (I • f) hI0 hIeig
  have hzero : (plane f (0 : ℂ)).re = 0 := by
    rw [plane_zero,hf0,Complex.zero_re]
  have hzeroI : (plane (I • f) (0 : ℂ)).re = 0 := by
    rw [plane_zero,hI0,Complex.zero_re]
  apply eq_zero_of_real_interval f
  intro x hx
  have hfr := real_plane_zero_of_real_deriv_zero f hzero hr hx
  have hfi := real_plane_zero_of_real_deriv_zero (I • f) hzeroI hi hx
  have hxout : (x : ℂ) ∈ outer := closedBall_subset_closedBall
    (by norm_num : (1 : ℝ) ≤ 3/2) (interval_mem_smallDisc hx)
  have hs : plane (I • f) (x : ℂ) = I*plane f (x : ℂ) := by
    rw [plane_eq (I • f) ⟨x,hxout⟩,plane_eq f ⟨x,hxout⟩]
    rfl
  rw [hs,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hfi
  exact Complex.ext hfr (neg_eq_zero.mp hfi)

#print axioms normalizedDerivative_constant_of_eigen
#print axioms derivative_eigen_eq_zero
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive.neg_deriv_branch_real
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPositive.source_minorization
