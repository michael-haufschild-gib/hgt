import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeLambdaMeromorphy
import GaloisForLFunctions.RHTower.ZetaTrivialZeroSimple
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinFullCuspSectorAssembly

/-!
# Cusp residue and regularized equal-reader zero at a Xi source

For an actual Xi occurrence `rho`, the two reader parameters are
`(2-rho+e+d)/2` and `(2-rho+e-d)/2`. The displayed meromorphic coefficient is

`T(e,d) = Lambda(1+e) Lambda(rho-d) Lambda(rho+d) Lambda(2*rho-1-e)`.

Its residue in `e` is the literal all-lower-Weyl cusp coefficient at `e=0`.
For every Xi occurrence, one member of its functional-equation orbit has nonzero
residue at every sufficiently small nonzero reader split. Consequently that
coefficient has no finite joint limit, despite its exact equal-reader zero.

Subtracting the computed principal part gives an explicit continuous remainder
with the same equal-reader zero. Thus the singularity obstructs an unrenormalized
continuity argument, while identifying the precise subtraction that removes it.

The four-Lambda expression is the completed triple-Eisenstein meromorphic family
in Huang--Li, arXiv:2510.12322, Lemma 4.2. The theorems here concern that expression
and the corpus's literal Weyl coefficients; they do not assert an integration
or complete causal-action identification. This cubic has one source and two
readers. The forward `++` forcing has two sources and one reader. Its other
channels, time boundaries, metric weights and source contacts remain separate.
The original physical clock is not replaced by either reader probe.
-/

open Complex Set Filter Topology
namespace RHTower.BMReaderSplit
noncomputable section

/-- Completed meromorphic cubic coefficient with independently varied reader legs. -/
def coefficient (q : XiZeroCopy) (e d : ℂ) : ℂ :=
  completedRiemannZeta (1+e) * completedRiemannZeta ((q.1:ℂ)-d) *
    completedRiemannZeta ((q.1:ℂ)+d) * completedRiemannZeta (2*(q.1:ℂ)-1-e)

/-- Exact coefficient of the transverse simple pole. -/
def residue (q : XiZeroCopy) (d : ℂ) : ℂ :=
  completedRiemannZeta ((q.1:ℂ)-d) * completedRiemannZeta ((q.1:ℂ)+d) *
    completedRiemannZeta (2*(q.1:ℂ)-1)

private theorem affine_punctured (a b : ℂ) (hb : b ≠ 0) :
    Tendsto (fun z : ℂ => a+b*z) (𝓝[≠] 0) (𝓝[≠] a) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Continuous (fun z : ℂ => a+b*z) :=
      continuous_const.add (continuous_const.mul continuous_id)
    simpa only [mul_zero,add_zero] using (h.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz ⊢
    simpa [hb] using hz

/-- The transverse residue is obtained from the completed-zeta residue at one. -/
theorem residue_limit (q : XiZeroCopy) (d : ℂ) :
    Tendsto (fun e : ℂ => e*coefficient q e d) (𝓝[≠] 0) (𝓝 (residue q d)) := by
  have hp := completedRiemannZeta_residue_one.comp (affine_punctured 1 1 one_ne_zero)
  have hp' : Tendsto (fun e : ℂ => e*completedRiemannZeta (1+e))
      (𝓝[≠] 0) (𝓝 1) := by simpa [Function.comp_def] using hp
  have hi : (2*(q.1:ℂ)-1).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (xi_divisor_support_im_ne_zero q.1)
  have h0 : 2*(q.1:ℂ)-1 ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have h1 : 2*(q.1:ℂ)-1 ≠ 1 := by intro h; exact hi (by rw [h]; rfl)
  have hc := (differentiableAt_completedZeta h0 h1).continuousAt
  have ha : Tendsto (fun e : ℂ => 2*(q.1:ℂ)-1-e) (𝓝[≠] 0)
      (𝓝 (2*(q.1:ℂ)-1)) := by
    have h : Continuous (fun e : ℂ => 2*(q.1:ℂ)-1-e) := continuous_const.sub continuous_id
    simpa only [sub_zero] using (h.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
  have h := ((hp'.mul_const (completedRiemannZeta ((q.1:ℂ)-d))).mul_const
    (completedRiemannZeta ((q.1:ℂ)+d))).mul (hc.tendsto.comp ha)
  simpa only [coefficient,residue,one_mul,mul_assoc,Function.comp_apply] using h

private theorem completed_at_xi (q : XiZeroCopy) : completedRiemannZeta (q.1:ℂ) = 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1:ℂ) ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have he : reflectedCompletedLambda (q.1:ℂ) = completedRiemannZeta (q.1:ℂ) := by
    rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
    exact mul_div_cancel₀ _ (gammaR_ne_zero_of_im_ne hi)
  rw [← he]
  exact D4BMJointSource.nativeCompletedLambda_at_xi q

/-- The actual Xi source makes the equal-reader coefficient vanish identically. -/
theorem diagonal_zero (q : XiZeroCopy) (e : ℂ) : coefficient q e 0 = 0 := by
  simp [coefficient,completed_at_xi]

private theorem completed_punctured (q : XiZeroCopy) :
    ∀ᶠ z in 𝓝[≠] (q.1:ℂ), completedRiemannZeta z ≠ 0 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have h0 : (q.1:ℂ) ≠ 0 := by
    intro h
    simpa [h] using hs.1
  filter_upwards [eventually_riemannZeta_ne_zero_nhdsNE hs.1 hs.2,
    (eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds] with z hz hz0
  intro h
  apply hz
  rw [riemannZeta_def_of_ne_zero hz0,h,zero_div]

private theorem lower_weyl_ne_zero (q : XiZeroCopy) (hq : (q.1:ℂ).re ≤ 1/2) :
    completedRiemannZeta (2*(q.1:ℂ)-1) ≠ 0 := by
  rw [← completedRiemannZeta_one_sub (2*(q.1:ℂ)-1)]
  apply completedRiemannZeta_ne_zero_of_one_le_re
  norm_num [Complex.sub_re,Complex.mul_re]
  linarith

private theorem split_residue_ne_zero (q : XiZeroCopy) (hq : (q.1:ℂ).re ≤ 1/2) :
    ∀ᶠ d in 𝓝[≠] (0:ℂ), residue q d ≠ 0 := by
  have hm := (affine_punctured (q.1:ℂ) (-1) (neg_ne_zero.mpr one_ne_zero)).eventually (completed_punctured q)
  have hp := (affine_punctured (q.1:ℂ) 1 one_ne_zero).eventually (completed_punctured q)
  filter_upwards [hm,hp] with d hm hp
  exact mul_ne_zero (mul_ne_zero (by simpa [sub_eq_add_neg] using hm) (by simpa using hp))
    (lower_weyl_ne_zero q hq)

/-- At least one member of every actual Xi orbit has nonzero nearby split residues. -/
theorem orbit_split_residue_ne_zero (q : XiZeroCopy) :
    ∃ r : XiZeroCopy, (r=q ∨ r=xiZeroCopyReflectEquiv q) ∧
      ∀ᶠ d in 𝓝[≠] (0:ℂ), residue r d ≠ 0 := by
  by_cases hq : (q.1:ℂ).re ≤ 1/2
  · exact ⟨q,Or.inl rfl,split_residue_ne_zero q hq⟩
  · refine ⟨xiZeroCopyReflectEquiv q,Or.inr rfl,split_residue_ne_zero _ ?_⟩
    change (1-(q.1:ℂ)).re ≤ 1/2
    simp only [Complex.sub_re,Complex.one_re]
    linarith

/-- Nearby split readers retain a genuine pole for one member of every Xi orbit. -/
theorem orbit_split_no_finite_slice_limit (q : XiZeroCopy) :
    ∃ r : XiZeroCopy, (r=q ∨ r=xiZeroCopyReflectEquiv q) ∧
      ∀ᶠ d in 𝓝[≠] (0:ℂ), ¬ ∃ c : ℂ,
        Tendsto (fun e : ℂ => coefficient r e d) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨r,hr,he⟩ := orbit_split_residue_ne_zero q
  refine ⟨r,hr,?_⟩
  filter_upwards [he] with d hd
  rintro ⟨c,hc⟩
  have hz : Tendsto (fun e : ℂ => e*coefficient r e d) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).mul hc
  exact hd (tendsto_nhds_unique (residue_limit r d) hz)

private theorem bounded_slices (F : ℂ × ℂ → ℝ) (l m : Filter ℂ)
    (h : IsBoundedUnder (· ≤ ·) (l ×ˢ m) F) :
    ∀ᶠ d in m, IsBoundedUnder (· ≤ ·) l (fun e => F (e,d)) := by
  obtain ⟨C,hC⟩ := h
  change {p | F p ≤ C} ∈ l ×ˢ m at hC
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_prod_iff.mp hC
  filter_upwards [hV] with d hd
  refine ⟨C,?_⟩
  change ∀ᶠ e in l, F (e,d) ≤ C
  filter_upwards [hU] with e he
  exact hUV (show (e,d) ∈ U ×ˢ V from ⟨he,hd⟩)

/-- Equal-reader vanishing does not provide a bounded joint reader family. -/
theorem orbit_unbounded (q : XiZeroCopy) :
    ∃ r : XiZeroCopy, (r=q ∨ r=xiZeroCopyReflectEquiv q) ∧
      ¬ IsBoundedUnder (· ≤ ·) ((𝓝[≠] (0:ℂ)) ×ˢ (𝓝[≠] (0:ℂ)))
        (fun p : ℂ × ℂ => ‖coefficient r p.1 p.2‖) := by
  obtain ⟨r,hr,he⟩ := orbit_split_residue_ne_zero q
  refine ⟨r,hr,?_⟩
  intro h
  have hs : ∀ᶠ d in 𝓝[≠] (0:ℂ), IsBoundedUnder (· ≤ ·) (𝓝[≠] (0:ℂ))
      (fun e => ‖coefficient r e d‖) :=
    bounded_slices (fun p : ℂ × ℂ => ‖coefficient r p.1 p.2‖) _ _ h
  obtain ⟨d,hd,hb⟩ := (he.and hs).exists
  have hz : Tendsto (fun e : ℂ => e*coefficient r e d) (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).zero_mul_isBoundedUnder_le
      (g := fun e : ℂ => coefficient r e d) hb
  exact hd (tendsto_nhds_unique (residue_limit r d) hz)

/-- The unrenormalized coefficient has no finite joint limit on that orbit member. -/
theorem orbit_no_joint_limit (q : XiZeroCopy) :
    ∃ r : XiZeroCopy, (r=q ∨ r=xiZeroCopyReflectEquiv q) ∧
      ¬ ∃ c : ℂ, Tendsto (fun p : ℂ × ℂ => coefficient r p.1 p.2)
        ((𝓝[≠] (0:ℂ)) ×ˢ (𝓝[≠] (0:ℂ))) (𝓝 c) := by
  obtain ⟨r,hr,hb⟩ := orbit_unbounded q
  refine ⟨r,hr,?_⟩
  rintro ⟨c,hc⟩
  exact hb hc.norm.isBoundedUnder_le

/-- Product of the three literal lower-Weyl coefficients, before specialization. -/
def cuspCoefficient (q : XiZeroCopy) (e d : ℂ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantCoefficient ((q.1:ℂ)-1/2) false *
    d4BMCompletedEisensteinCuspConstantCoefficient ((1-(q.1:ℂ)+e+d)/2) false *
    d4BMCompletedEisensteinCuspConstantCoefficient ((1-(q.1:ℂ)+e-d)/2) false

/-- The all-lower-Weyl product has height exponent one at the original reader. -/
theorem cusp_exponent (q : XiZeroCopy) (e d : ℂ) :
    d4BMCompletedEisensteinCuspWeylExponent ((q.1:ℂ)-1/2) false +
      d4BMCompletedEisensteinCuspWeylExponent ((1-(q.1:ℂ)+e+d)/2) false +
      d4BMCompletedEisensteinCuspWeylExponent ((1-(q.1:ℂ)+e-d)/2) false = 1-e := by
  simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
    Bool.false_eq_true,↓reduceIte]
  push_cast
  ring

private theorem native_eq_completed {s : ℂ} (hi : s.im ≠ 0) :
    reflectedCompletedLambda s = completedRiemannZeta s := by
  have h0 : s ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
  exact mul_div_cancel₀ _ (gammaR_ne_zero_of_im_ne hi)

/-- The literal cusp coefficient and the meromorphic residue agree near the original reader. -/
theorem cusp_residue (q : XiZeroCopy) :
    ∀ᶠ d in 𝓝 (0:ℂ), cuspCoefficient q 0 d = residue q d := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hi' : (1-(q.1:ℂ)).im ≠ 0 := by simpa using neg_ne_zero.mpr hi
  have hm : Continuous (fun d : ℂ => (1-(q.1:ℂ)-d).im) :=
    Complex.continuous_im.comp (continuous_const.sub continuous_id)
  have hp : Continuous (fun d : ℂ => (1-(q.1:ℂ)+d).im) :=
    Complex.continuous_im.comp (continuous_const.add continuous_id)
  have hem : ∀ᶠ d in 𝓝 (0:ℂ), (1-(q.1:ℂ)-d).im ≠ 0 :=
    (hm.tendsto 0).eventually (by simpa using eventually_ne_nhds hi')
  have hep : ∀ᶠ d in 𝓝 (0:ℂ), (1-(q.1:ℂ)+d).im ≠ 0 :=
    (hp.tendsto 0).eventually (by simpa using eventually_ne_nhds hi')
  filter_upwards [hem,hep] with d hdm hdp
  have hi2 : (2*(q.1:ℂ)-1).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hi
  simp only [cuspCoefficient,d4BMCompletedEisensteinCuspConstantCoefficient,
    Bool.false_eq_true,↓reduceIte,add_zero]
  rw [show 2*((q.1:ℂ)-1/2)=2*(q.1:ℂ)-1 by ring,
    show 2*((1-(q.1:ℂ)+d)/2)=1-(q.1:ℂ)+d by ring,
    show 2*((1-(q.1:ℂ)-d)/2)=1-(q.1:ℂ)-d by ring,
    native_eq_completed hi2,native_eq_completed hdp,native_eq_completed hdm,
    show 1-(q.1:ℂ)+d=1-((q.1:ℂ)-d) by ring,
    show 1-(q.1:ℂ)-d=1-((q.1:ℂ)+d) by ring,
    completedRiemannZeta_one_sub,completedRiemannZeta_one_sub]
  dsimp [residue]
  ring

/-- Regular factor after subtracting the explicitly computed principal part. -/
def regularPart (q : XiZeroCopy) (e : ℂ) : ℂ :=
  (completedRiemannZeta₀ (1+e)-1/(1+e))*completedRiemannZeta (2*(q.1:ℂ)-1-e) +
    dslope (fun t : ℂ => completedRiemannZeta (2*(q.1:ℂ)-1-t)) 0 e

/-- Residue-subtracted coefficient, with its continuous value supplied at the pole. -/
def regularized (q : XiZeroCopy) (e d : ℂ) : ℂ :=
  completedRiemannZeta ((q.1:ℂ)-d)*completedRiemannZeta ((q.1:ℂ)+d)*regularPart q e

/-- The subtraction is an exact identity on the punctured source parameter. -/
theorem pole_subtraction (q : XiZeroCopy) (d : ℂ) :
    ∀ᶠ e in 𝓝[≠] (0:ℂ), coefficient q e d-residue q d/e = regularized q e d := by
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e ≠ 0 := he
  dsimp [coefficient,residue,regularized,regularPart]
  rw [completedRiemannZeta_eq (1+e),dslope_of_ne _ he0,slope_def_field]
  simp only [sub_zero,show (1:ℂ)-(1+e)=-e by ring,div_neg]
  ring

private theorem shiftedCompletion_differentiable (q : XiZeroCopy) :
    DifferentiableAt ℂ (fun e : ℂ => completedRiemannZeta (2*(q.1:ℂ)-1-e)) 0 := by
  have hi : (2*(q.1:ℂ)-1).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (xi_divisor_support_im_ne_zero q.1)
  have h0 : 2*(q.1:ℂ)-1 ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have h1 : 2*(q.1:ℂ)-1 ≠ 1 := by intro h; exact hi (by rw [h]; rfl)
  have h := differentiableAt_completedZeta h0 h1
  have ha : Differentiable ℂ (fun e : ℂ => 2*(q.1:ℂ)-1-e) :=
    (differentiable_const (2*(q.1:ℂ)-1)).sub differentiable_id
  have h' : DifferentiableAt ℂ completedRiemannZeta (2*(q.1:ℂ)-1-(0:ℂ)) := by
    simpa only [sub_zero] using h
  exact h'.comp 0 ha.differentiableAt

private theorem regularPart_continuousAt (q : XiZeroCopy) : ContinuousAt (regularPart q) 0 := by
  have ha : ContinuousAt (fun e : ℂ => 1+e) 0 := continuous_const.add continuous_id |>.continuousAt
  have hc : ContinuousAt (fun e : ℂ => completedRiemannZeta₀ (1+e)-1/(1+e)) 0 :=
    ((differentiable_completedZeta₀.continuous.continuousAt).comp ha).sub
      (continuousAt_const.div ha (by norm_num))
  exact (hc.mul (shiftedCompletion_differentiable q).continuousAt).add
    (continuousAt_dslope_same.mpr (shiftedCompletion_differentiable q))

/-- The explicit subtraction preserves the actual equal-reader zero. -/
theorem regularized_diagonal_zero (q : XiZeroCopy) (e : ℂ) : regularized q e 0 = 0 := by
  simp [regularized,completed_at_xi]

/-- After the source-derived principal subtraction the joint family is continuous. -/
theorem regularized_continuousAt (q : XiZeroCopy) :
    ContinuousAt (fun p : ℂ × ℂ => regularized q p.1 p.2) (0,0) := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have h0 : (q.1:ℂ) ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
  have h1 : (q.1:ℂ) ≠ 1 := by intro h; exact hi (by rw [h]; rfl)
  have hc := (differentiableAt_completedZeta h0 h1).continuousAt
  have hm : ContinuousAt (fun p : ℂ × ℂ => (q.1:ℂ)-p.2) (0,0) :=
    continuous_const.sub continuous_snd |>.continuousAt
  have hp : ContinuousAt (fun p : ℂ × ℂ => (q.1:ℂ)+p.2) (0,0) :=
    continuous_const.add continuous_snd |>.continuousAt
  have hcm : ContinuousAt (fun p : ℂ × ℂ => completedRiemannZeta ((q.1:ℂ)-p.2)) (0,0) :=
    hc.comp_of_eq hm (by simp)
  have hcp : ContinuousAt (fun p : ℂ × ℂ => completedRiemannZeta ((q.1:ℂ)+p.2)) (0,0) :=
    hc.comp_of_eq hp (by simp)
  have hf : ContinuousAt (fun p : ℂ × ℂ => p.1) (0,0) := continuous_fst.continuousAt
  exact (hcm.mul hcp).mul ((regularPart_continuousAt q).comp_of_eq hf rfl)

/-- The regularized joint limit at the unchanged equal reader is zero. -/
theorem regularized_joint_zero_limit (q : XiZeroCopy) :
    Tendsto (fun p : ℂ × ℂ => regularized q p.1 p.2) (𝓝 (0,0)) (𝓝 0) := by
  simpa only [regularized_diagonal_zero] using (regularized_continuousAt q).tendsto

end
end RHTower.BMReaderSplit
