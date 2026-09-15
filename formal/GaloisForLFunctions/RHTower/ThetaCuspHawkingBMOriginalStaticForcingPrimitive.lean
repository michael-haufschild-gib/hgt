import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalFullMetricDifference

open Set Filter Topology Metric MeasureTheory Complex
namespace RHTower.D4BMOriginalStaticForcingPrimitive
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
open D4BMOriginalCornerForcing D4BMOriginalMetricHorizon D4BMOriginalCanonicalHorizon
open D4BMOriginalCanonicalRestoration D4BMOriginalCanonicalForcingMatch D4BMOriginalForcingJointHorizon
noncomputable section
set_option autoImplicit false

theorem forcing_kernel_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (forcingKernel q br amp K w) (Iio (0:ℝ)) := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_ofReal_cpow_const (1+radialUnit x) (2*physicalRate q br)
      (Or.inr (radialUnit_add_one_pos x).ne')).comp_of_eq
        (continuous_const.add hu).continuousAt rfl
  have hF : Continuous (fun x : ℝ => forcingProfile (physicalRate q br) amp 1 K (radialUnit x)) := by
    unfold forcingProfile
    fun_prop
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp_of_eq
      (horizonCoordinate_hasDerivAt x).continuousAt rfl
  exact (((show Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ))) by fun_prop).continuousAt.mul
    hF.continuousAt).mul hn).continuousWithinAt

private theorem bounded_of_left_limit (f : ℝ → ℂ) (b : ℝ) (z : ℂ)
    (hc : ContinuousOn f (Ioc 0 b)) (ht : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 z)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ e ∈ Ioc 0 b, ‖f e‖ ≤ M := by
  have hv : {e : ℝ | ‖f e‖ < ‖z‖+1} ∈ 𝓝[>] (0:ℝ) :=
    ht.norm.eventually (Iio_mem_nhds (by linarith : ‖z‖ < ‖z‖+1))
  obtain ⟨d,hd,hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hv
  have hd0 : 0 < d := hd
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.mono (show Icc (d/2) b ⊆ Ioc 0 b from fun e he => ⟨(half_pos hd0).trans_le he.1,he.2⟩))
  refine ⟨max (‖z‖+1) C,le_max_of_le_left (by positivity),?_⟩
  intro e he
  by_cases hed : e < d
  · exact (hδ ⟨he.1,hed⟩).le.trans (le_max_left _ _)
  · exact (hC e ⟨by linarith,he.2⟩).trans (le_max_right _ _)

/-- The original canonical radial primitive, retaining both power counterterms
and the logarithm with their fixed source coefficients. -/
def forcingPrimitive (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (b e : ℝ) : ℂ :=
  (∫ x in tortoiseOf e..tortoiseOf b,forcingKernel q br amp K w x)-
    canonicalForcingCounterterm q br amp K w e

theorem forcing_counterterm_continuousAt (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {e : ℝ} (he : 0 < e) :
    ContinuousAt (canonicalForcingCounterterm q br amp K w) e := by
  have hp (v : ℂ) : ContinuousAt (fun t : ℝ => (t:ℂ)^v) e :=
    continuousAt_ofReal_cpow_const e v (Or.inr he.ne')
  have hl : ContinuousAt (fun t : ℝ => (Real.log t:ℂ)) e :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log he.ne')
  unfold canonicalForcingCounterterm D4BMOriginalMetricRadial.forcingCounterterm
  exact (((continuousAt_const.mul (hp w)).div_const w).add
    ((continuousAt_const.mul (hp (w+1))).div_const (w+1))).add (continuousAt_const.mul hl)

theorem forcing_primitive_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) :
    ContinuousOn (forcingPrimitive q br amp K w b) (Ioo (0:ℝ) 1) := by
  have hc := forcing_kernel_continuous q br amp K w
  intro e he
  have hte := tortoiseOf_neg he
  have htb := tortoiseOf_neg hb
  have hi : IntervalIntegrable (forcingKernel q br amp K w) volume (tortoiseOf e) (tortoiseOf b) :=
    (hc.mono (fun x hx => hx.2.trans_lt (max_lt hte htb))).intervalIntegrable
  have hder := intervalIntegral.integral_hasDerivAt_left hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Iio hc _ hte)
    ((hc _ hte).continuousAt (Iio_mem_nhds hte))
  have htc : ContinuousAt tortoiseOf e := by
    unfold tortoiseOf
    have hs : 0 < Real.sqrt e := Real.sqrt_pos.mpr he.1
    fun_prop (disch := positivity)
  exact ((hder.continuousAt.comp htc).sub
    (forcing_counterterm_continuousAt q br amp K w he.1)).continuousWithinAt

/-- Finite canonical horizon restoration gives a bound on the entire original
radial primitive, uniformly over every lower cutoff below a fixed interface. -/
theorem forcing_primitive_bounded (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hwi : w.im ≠ 0) (hwr : -2 < w.re) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 1/2 ∧ ∀ b : ℝ, 0 < b → b ≤ B →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ e ∈ Ioc (0:ℝ) b, ‖forcingPrimitive q br amp K w b e‖ ≤ M := by
  obtain ⟨R,B,hR,hB,hBh,h⟩ := canonical_radial_restoration q br amp K w hwi hwr
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB
  have hb1 : b < 1 := by linarith
  have ht : Tendsto (forcingPrimitive q br amp K w b) (𝓝[>] (0:ℝ))
      (𝓝 (horizonFinitePart q br amp K (incomingValue q br amp K)
        (incomingSlope q br amp K) (oppositeValue q br amp K) b w)) := by
    apply ((h b hb hbB).2 w (mem_ball_self hR)).congr'
    filter_upwards [] with e
    unfold forcingPrimitive canonicalForcingCounterterm D4BMOriginalMetricRadial.forcingCounterterm
    ring
  exact bounded_of_left_limit _ b _
    ((forcing_primitive_continuous q br amp K w ⟨hb,hb1⟩).mono (fun e he => ⟨he.1,he.2.trans_lt hb1⟩)) ht

/-- The literal finite-cusp discrepancy is uniformly small on the whole
renormalized radial collar, not only along each fixed lower-cutoff sequence. -/
theorem forcing_primitive_uniform_restoration (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im ≠ 0) (hwr : -2 < w.re) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 1/2 ∧ ∀ b : ℝ, 0 < b → b ≤ B →
      ∃ η : ℝ → ℝ, (∀ k, 0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ k e : ℝ, e ∈ Ioc (0:ℝ) b →
          ‖canonicalForcingDifferenceCut q br amp w b (e,k)‖ ≤ η k := by
  let K := gradient q br
  obtain ⟨B₁,hB₁,hB₁h,h₁⟩ := forcing_primitive_bounded q br amp K w hwi hwr
  obtain ⟨B₂,hB₂,hB₂h,h₂⟩ := forcing_primitive_bounded q br amp (K+1) w hwi hwr
  refine ⟨min B₁ B₂,lt_min hB₁ hB₂,(min_le_left _ _).trans hB₁h,?_⟩
  intro b hb hbB
  obtain ⟨M,hM,hm⟩ := h₁ b hb (hbB.trans (min_le_left _ _))
  obtain ⟨P,hP,hp⟩ := h₂ b hb (hbB.trans (min_le_right _ _))
  let η := fun k : ℝ => ‖firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q‖*M+
    ‖secondWeight q (Real.exp k)‖*P
  refine ⟨η,fun k => by dsimp [η];positivity,?_,?_⟩
  · have ht := (((weights_limit q).1.sub_const (physicalSelfSourceCoefficient q)).norm.mul_const M).add
      ((weights_limit q).2.norm.mul_const P)
    simpa only [sub_self,norm_zero,zero_mul,zero_add] using ht
  · intro k e he
    have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨hb,by linarith [hbB.trans (min_le_left B₁ B₂),hB₁h]⟩
    have heI : e ∈ Ioo (0:ℝ) 1 := ⟨he.1,he.2.trans_lt hbI.2⟩
    have hdecomp : canonicalForcingDifferenceCut q br amp w b (e,k)=
        (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*forcingPrimitive q br amp K w b e+
          secondWeight q (Real.exp k)*forcingPrimitive q br amp (K+1) w b e := by
      rw [canonicalForcingDifferenceCut,integral_two_kernels q br amp w _ _ _ (tortoiseOf_neg heI) (tortoiseOf_neg hbI)]
      unfold forcingPrimitive
      dsimp only [K,D4BMOriginalForcingJointHorizon.gradient]
      ring
    rw [hdecomp]
    apply (norm_add_le _ _).trans
    dsimp [η]
    rw [norm_mul,norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hm e he) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hp e he) (norm_nonneg _))

end
end RHTower.D4BMOriginalStaticForcingPrimitive
