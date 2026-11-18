import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.UnheatedZeroModeSynthesis
import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskHalfLineCayley
import GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit
import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitAtomicWall

/-!
# The unheated state and its right-zero layer

The Laplace transform identifies the Hilbert sum of the exponentials with
the reflected state. Removing a finite layer leaves a remainder in weighted
square mean at every exponent strictly beyond the remaining zeros.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem memLp_reflected_state {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F) :
    MemLp (fun t : ℝ => (F (-t):ℂ)) 2 halfLineLaplaceMeasure :=
  (memLp_cx_of_sq hd.integrable.comp_neg hd.sq.comp_neg).restrict (Ioi (0:ℝ))

/-- Reflection of the half-line state as a positive-ray square-integrable datum. -/
def reflectedStateDatum {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F) : HalfLineLaplaceL2 :=
  (memLp_reflected_state hd).toLp _

private theorem re_centredZero_lt_eight (q : XiZeroCopy) : (centredZero q).re < 8 :=
  (abs_lt.mp (abs_re_centredZero_lt q)).2.trans (by norm_num)

/-- A Cauchy feature reads the resolvent of a single unheated zero mode. -/
theorem inner_zeroRayFeature (s : ℝ) (q : XiZeroCopy) (hq : (centredZero q).re < s)
    (w : ℂ) (hw : 0 < w.re) :
    inner ℂ (halfLineLaplaceFeature w hw) (zeroRayFeature s q hq) =
      (w+(s:ℂ)-centredZero q)⁻¹ := by
  simp [zeroRayFeature,inner_halfLineLaplaceFeature,one_div,sub_eq_add_neg,add_assoc]

private theorem laplace_reflectedStateDatum {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (w : ℂ) (hw : 0 < w.re) :
    inner ℂ (halfLineLaplaceFeature w hw) (reflectedStateDatum hd) = negativeHalfLineLaplace (cx F) w := by
  rw [← halfLineLaplaceTransform,halfLineLaplaceTransform_eq_laplaceRay,
    negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F) (fun u hu => by simp [cx,hd.support u hu])]
  apply integral_congr_ae
  filter_upwards [(memLp_reflected_state hd).coeFn_toLp] with x hx
  exact congrArg (· * expRay w x) hx

/-- All positive-depth Laplace readings determine a ray datum in square mean. -/
theorem halfLine_eq_of_feature_readings {U V : HalfLineLaplaceL2}
    (h : ∀ (w : ℂ) (hw : 0 < w.re), inner ℂ (halfLineLaplaceFeature w hw) U =
      inner ℂ (halfLineLaplaceFeature w hw) V) : U = V := by
  have hzero : ∀ᵐ t ∂halfLineLaplaceMeasure, (U-V) t = 0 := by
    apply ae_eq_zero_of_laplaceRay_eq_zero (Lp.memLp (U-V))
    intro w hw
    rw [← halfLineLaplaceTransform_eq_laplaceRay _ hw,halfLineLaplaceTransform,inner_sub_right,h w hw,sub_self]
  apply sub_eq_zero.mp
  apply Lp.ext
  filter_upwards [hzero,Lp.coeFn_zero ℂ 2 halfLineLaplaceMeasure] with t ht h0
  exact ht.trans h0.symm

/-- The exponential expansion converges in the norm of unweighted ray L² to
the actual reflected state multiplied by the negative confinement coefficient. -/
theorem criticalState_hasSum_unheated_zero_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) •
      zeroRayFeature 8 q (re_centredZero_lt_eight q))
      (-(criticalAliasCoefficient W₀ : ℂ) • reflectedStateDatum (criticalHalfLineEnergyDomain_of_groundState hF)) := by
  obtain ⟨U,hU⟩ := criticalState_summable_zeroRayFeature hW ht hF (Function.Embedding.refl XiZeroCopy)
    (b := 1/2) (s := 8) (by norm_num) (fun q => (abs_lt.mp (abs_re_centredZero_lt q)).2.le)
  let D := reflectedStateDatum (criticalHalfLineEnergyDomain_of_groundState hF)
  let a : ℂ := criticalAliasCoefficient W₀
  have he (w : ℂ) (hw : 0 < w.re) : inner ℂ (halfLineLaplaceFeature w hw) U =
      -(a*negativeHalfLineLaplace (cx F) w) := by
    have hh := hU.mapL (innerSL ℂ (halfLineLaplaceFeature w hw))
    have hs : HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        (w+8-centredZero q)⁻¹) (inner ℂ (halfLineLaplaceFeature w hw) U) := by
      refine hh.congr_fun fun q => ?_
      symm
      change inner ℂ (halfLineLaplaceFeature w hw)
        (negativeHalfLineLaplace (cx F) (centredZero q) • zeroRayFeature 8 q (re_centredZero_lt_eight q)) = _
      rw [inner_smul_right,inner_zeroRayFeature]; norm_num
    exact hs.unique (criticalState_hasSum_starEquation hW ht hF (by linarith))
  have hval : U = (-a) • D := halfLine_eq_of_feature_readings fun w hw => by
    rw [inner_smul_right,he w hw,laplace_reflectedStateDatum]
    ring
  rw [← hval]
  exact hU

private theorem zeroRayFeature_ae (s : ℝ) (q : XiZeroCopy) (hq : (centredZero q).re < s) :
    (zeroRayFeature s q hq : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure]
      fun t => Complex.exp ((centredZero q-(s:ℂ))*(t:ℂ)) := by
  let w := (s:ℂ)-star (centredZero q)
  have hw : 0 < w.re := by simpa [w] using sub_pos.mpr hq
  filter_upwards [(halfLineLaplaceFeatureRaw_memLp hw).coeFn_toLp] with t ht
  change halfLineLaplaceFeature w hw t = _
  rw [show halfLineLaplaceFeature w hw t = halfLineLaplaceFeatureRaw w t from ht]
  simp [halfLineLaplaceFeatureRaw,w,sub_eq_add_neg,add_comm]

/-- The bounded exponential multiplier on the native Laplace-feature space. -/
private abbrev rayDampingMap {d : ℝ} (hd : 0 ≤ d) :
    HalfLineLaplaceL2 →L[ℂ] HalfLineLaplaceL2 :=
  lpBoundedMulCLM (p := 2) (μ := halfLineLaplaceMeasure) (measurable_expDampingMultiplier d)
    zero_le_one (norm_expDampingMultiplier_le hd)

private theorem rayDampingMap_zeroRayFeature {s r : ℝ} (hsr : s ≤ r)
    (q : XiZeroCopy) (hq : (centredZero q).re < s) :
    rayDampingMap (sub_nonneg.mpr hsr) (zeroRayFeature s q hq) =
      zeroRayFeature r q (hq.trans_le hsr) := by
  apply Lp.ext
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := halfLineLaplaceMeasure)
    (measurable_expDampingMultiplier _) zero_le_one (norm_expDampingMultiplier_le (sub_nonneg.mpr hsr))
    (zeroRayFeature s q hq), zeroRayFeature_ae s q hq,zeroRayFeature_ae r q (hq.trans_le hsr),
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht h1 h2 ht0
  rw [show rayDampingMap (sub_nonneg.mpr hsr) (zeroRayFeature s q hq) t =
      expDampingMultiplier (r-s) t * zeroRayFeature s q hq t from ht, h1,h2,
    expDampingMultiplier,max_eq_left (le_of_lt ht0),Complex.ofReal_exp,← Complex.exp_add]
  congr 1; push_cast; ring

/-- Subtracting an arbitrary subseries leaves precisely the damped sum of
the complementary modes. No finiteness or separation of the removed zeros
is required. -/
theorem memLp_sub_zero_layer (q : XiZeroCopy ↪ XiZeroCopy) (c : XiZeroCopy → ℂ)
    {r s b : ℝ} (hs : s ≤ r) (hr : ∀ i, (centredZero (q i)).re < r)
    (P : Set XiZeroCopy) (hbs : b < s) (hb : ∀ i ∉ P, (centredZero (q i)).re ≤ b)
    (hc : Summable fun i => (xiLineTwoLogDerivConstant+Real.log (|(centredZero (q i)).im|+4))*‖c i‖^2)
    {D : HalfLineLaplaceL2} (hD : HasSum (fun i => c i • zeroRayFeature r (q i) (hr i)) D) :
    MemLp (fun t : ℝ => (Real.exp ((r-s)*t):ℂ) *
      (D t - (∑' i : P, c i • zeroRayFeature r (q i) (hr i) : HalfLineLaplaceL2) t))
      2 halfLineLaplaceMeasure := by
  classical
  let v := fun i => zeroRayFeature r (q i) (hr i)
  let T := Pᶜ
  let incl : T ↪ XiZeroCopy := Function.Embedding.subtype _
  have hz (i : T) : (centredZero (q i)).re ≤ b := hb i i.property
  obtain ⟨U,hU⟩ := summable_zeroRayFeature_of_log_mass (incl.trans q) (fun i => c i)
    hbs hz (hc.comp_injective incl.injective)
  let A := rayDampingMap (sub_nonneg.mpr hs)
  have hT : HasSum (fun i : T => c i • v i) (A U) := by
    refine (hU.mapL A).congr_fun fun i => ?_
    symm
    change A (c i • zeroRayFeature s (q i) ((hz i).trans_lt hbs)) = _
    rw [map_smul, show A (zeroRayFeature s (q i) ((hz i).trans_lt hbs)) = v i from
      rayDampingMap_zeroRayFeature hs (q i) ((hz i).trans_lt hbs)]
  let H := ∑' i : P, c i • v i
  have he : H + A U = D := by
    rw [← hT.tsum_eq]
    exact (hD.summable.tsum_subtype_add_tsum_subtype_compl P).trans hD.tsum_eq
  refine MemLp.ae_eq ?_ (Lp.memLp U)
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := halfLineLaplaceMeasure) (measurable_expDampingMultiplier _)
      zero_le_one (norm_expDampingMultiplier_le (sub_nonneg.mpr hs)) U,
    Lp.coeFn_add H (A U),
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t hA hadd ht0
  have e := congrArg (fun f : HalfLineLaplaceL2 => f t) he
  change (H + A U : HalfLineLaplaceL2) t = D t at e
  change A U t = expDampingMultiplier (r-s) t * U t at hA
  rw [hadd,Pi.add_apply,hA] at e
  have htpos : 0 < t := ht0
  simp only [expDampingMultiplier,max_eq_left htpos.le] at e
  have h := congrArg (fun x : ℂ => (Real.exp ((r-s)*t):ℂ)*x) e
  have hi : (Real.exp ((r-s)*t):ℂ)*(Real.exp (-((r-s)*t)):ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  change U t = (Real.exp ((r-s)*t):ℂ)*(D t - H t)
  linear_combination h - (U t)*hi

/-- Finite-layer subtraction in the physical variable. A Hilbert sum at depth
`r` splits into the selected exponentials and the damped complement at depth `s`. -/
theorem memLp_sub_finite_zero_layer (q : XiZeroCopy ↪ XiZeroCopy) (c : XiZeroCopy → ℂ)
    {r s b : ℝ} (hs : s ≤ r) (hr : ∀ i, (centredZero (q i)).re < r)
    (S : Finset XiZeroCopy) (hbs : b < s) (hb : ∀ i ∉ S, (centredZero (q i)).re ≤ b)
    (hc : Summable fun i => (xiLineTwoLogDerivConstant+Real.log (|(centredZero (q i)).im|+4))*‖c i‖^2)
    {D : HalfLineLaplaceL2} (hD : HasSum (fun i => c i • zeroRayFeature r (q i) (hr i)) D) :
    MemLp (fun t : ℝ => (Real.exp ((r-s)*t):ℂ) *
      (D t - ∑ i ∈ S, c i * Complex.exp ((centredZero (q i)-(r:ℂ))*(t:ℂ))))
      2 halfLineLaplaceMeasure := by
  classical
  let v := fun i => zeroRayFeature r (q i) (hr i)
  have h := memLp_sub_zero_layer q c hs hr (↑S : Set XiZeroCopy) hbs hb hc hD
  have he : (∑' i : (↑S : Set XiZeroCopy), c i • v i) = ∑ i ∈ S, c i • v i := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort S (fun i => c i • v i)
  have hv : ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ i, v i t =
      Complex.exp ((centredZero (q i)-(r:ℂ))*(t:ℂ)) :=
    ae_all_iff.mpr fun i => zeroRayFeature_ae r (q i) (hr i)
  have hsum : ((∑ i ∈ S, c i • v i : HalfLineLaplaceL2) : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure]
      fun t => ∑ i ∈ S, c i * v i t := HeatSource.halfLineL2_coeFn_finset_sum_smul S c v
  apply MemLp.ae_eq _ h
  filter_upwards [hsum,hv] with t hS hv
  change _ * (D t - (∑' i : (↑S : Set XiZeroCopy), c i • v i : HalfLineLaplaceL2) t) = _
  simp only [he,hS,hv]

/-- Removing the complete right-zero subseries, however large, leaves a
remainder with every square decay rate strictly below eight. -/
theorem criticalState_memLp_sub_right_zero_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 8) :
    MemLp (fun t : ℝ => (Real.exp ((8-s)*t):ℂ) *
      (-(criticalAliasCoefficient W₀ : ℂ)*(F (-t):ℂ) -
        (∑' q : {q : XiZeroCopy // 0 < (centredZero q).re},
          negativeHalfLineLaplace (cx F) (centredZero q) •
            zeroRayFeature 8 q (re_centredZero_lt_eight q) : HalfLineLaplaceL2) t))
      2 halfLineLaplaceMeasure := by
  let hd := criticalHalfLineEnergyDomain_of_groundState hF
  let a : ℂ := criticalAliasCoefficient W₀
  have h := memLp_sub_zero_layer (Function.Embedding.refl XiZeroCopy) _ hs re_centredZero_lt_eight
    {q | 0 < (centredZero q).re} hs0 (fun q hq => le_of_not_gt hq)
    (criticalState_summable_zero_density_mass hW ht hF) (criticalState_hasSum_unheated_zero_modes hW ht hF)
  refine MemLp.ae_eq ?_ h
  filter_upwards [Lp.coeFn_smul (-a) (reflectedStateDatum hd),
    (memLp_reflected_state hd).coeFn_toLp] with t ht hD
  change reflectedStateDatum hd t = (F (-t):ℂ) at hD
  simp only [Pi.smul_apply,smul_eq_mul,hD] at ht
  dsimp only [a,hd] at ht
  simp only [Function.Embedding.refl_apply]
  exact congrArg (fun z : ℂ => (Real.exp ((8-s)*t):ℂ)*(z-_)) ht

/-- Removing any finite zero layer gives square-integrable remainder with
weight `exp(2(8-s)t)` whenever the remaining real parts are bounded by `b<s≤8`. -/
theorem criticalState_memLp_sub_finite_unheated_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (S : Finset XiZeroCopy) {b s : ℝ} (hbs : b < s) (hs : s ≤ 8)
    (hb : ∀ q ∉ S, (centredZero q).re ≤ b) :
    MemLp (fun t : ℝ => (Real.exp ((8-s)*t):ℂ) *
      (-(criticalAliasCoefficient W₀ : ℂ)*(F (-t):ℂ) -
        ∑ q ∈ S, negativeHalfLineLaplace (cx F) (centredZero q) *
          Complex.exp ((centredZero q-8)*(t:ℂ)))) 2 halfLineLaplaceMeasure := by
  let hd := criticalHalfLineEnergyDomain_of_groundState hF
  let a : ℂ := criticalAliasCoefficient W₀
  have h := memLp_sub_finite_zero_layer (Function.Embedding.refl XiZeroCopy) _ hs
    re_centredZero_lt_eight S hbs hb (criticalState_summable_zero_density_mass hW ht hF)
    (criticalState_hasSum_unheated_zero_modes hW ht hF)
  refine MemLp.ae_eq ?_ h
  filter_upwards [Lp.coeFn_smul (-a) (reflectedStateDatum hd),
    (memLp_reflected_state hd).coeFn_toLp] with t ht hD
  change reflectedStateDatum hd t = (F (-t):ℂ) at hD
  simp only [Pi.smul_apply,smul_eq_mul,hD] at ht
  dsimp only [a,hd] at ht
  simp only [Function.Embedding.refl_apply,Complex.ofReal_ofNat]
  exact congrArg (fun z : ℂ => (Real.exp ((8-s)*t):ℂ)*(z-_)) ht

#print axioms criticalState_hasSum_unheated_zero_modes
#print axioms criticalState_memLp_sub_right_zero_modes
#print axioms criticalState_memLp_sub_finite_unheated_modes

end GaloisForLFunctions.ExclusionOfTheCriticalState
