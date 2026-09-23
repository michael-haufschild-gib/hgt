import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightCore

/-! Exact compact angular localization of the actual native primitive's energy.
The full product-rule cross terms recombine into the original Green pairing and
one nonnegative cutoff-gradient error. No global native energy premise is used. -/
open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem cutoff_square_identity (c d w a : ℂ) (hc : conj c = c) :
    ‖d*w+c*a‖^(2 : ℕ) = (conj a*((d*c+c*d)*w+c*c*a)).re + ‖d*w‖^(2 : ℕ) := by
  have hc0 : c.im = 0 := by
    have h := congrArg Complex.im hc
    simp only [Complex.conj_im] at h
    linarith
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,hc0]
  ring

private theorem nativeCutoff_energy_pointwise (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (n : ℕ) (z : UpperHalfPlane) :
    (∑ i : Fin 2, ‖weightedDeriv (direction i)
      (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖^(2 : ℕ)) =
    (frameEnergy (globalNativeTimePrimitive q s amplitude t x)
      (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z).re +
    ∑ i : Fin 2, ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) z *
      globalNativeTimePrimitive q s amplitude t x z‖^(2 : ℕ) := by
  let eta := modularCuspCutoff ((n:ℝ)+1)
  let W := globalNativeTimePrimitive q s amplitude t x
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have heta : ChartSmooth eta := modularCuspCutoff_smooth _ hN
  have hW : ChartSmooth W := globalNativeTimePrimitive_smooth q s amplitude t x
  have hf (v : ℂ) : weightedDeriv v (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z =
      weightedDeriv v eta z*W z+eta z*weightedDeriv v W z := by
    change weightedDeriv v (fun z => eta z^(0+1)*W z) z = _
    simpa only [Nat.zero_add,pow_one] using weightedDeriv_mul eta W heta hW v z
  have hg (v : ℂ) : weightedDeriv v (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z =
      (weightedDeriv v eta z*eta z+eta z*weightedDeriv v eta z)*W z+
        eta z*eta z*weightedDeriv v W z := by
    change weightedDeriv v (fun z => eta z^(1+1)*W z) z = _
    have h := weightedDeriv_mul (fun z => eta z*eta z) W
      (fun z => (heta z).mul (heta z)) hW v z
    rw [weightedDeriv_mul eta eta heta heta] at h
    simpa only [Nat.reduceAdd,pow_two] using h
  have hs (v : ℂ) :
      ‖weightedDeriv v (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖^(2 : ℕ) =
      (conj (weightedDeriv v W z)*
        weightedDeriv v (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z).re +
      ‖weightedDeriv v eta z*W z‖^(2 : ℕ) := by
    rw [hf,hg]
    exact cutoff_square_identity _ _ _ _ (modularCuspCutoff_real _ z)
  change (∑ i : Fin 2, ‖weightedDeriv (direction i)
      (nativeTimePrimitiveCutoff q s amplitude t x n 0).field z‖^(2 : ℕ)) =
    (frameEnergy W (nativeTimePrimitiveCutoff q s amplitude t x n 1).field z).re +
      ∑ i : Fin 2, ‖weightedDeriv (direction i) eta z*W z‖^(2 : ℕ)
  simp only [frameEnergy,Fin.sum_univ_two,Complex.add_re]
  rw [hs,hs]
  ring

/-- Exact angular energy localization for the literal native primitive. The cutoff
energy and its nonnegative error are integrable in the original modular measure;
the full mixed derivative contributions are retained by completing the square. -/
theorem nativeTimePrimitive_compact_angular_localization (q : XiZeroCopy) (s amplitude : ℂ)
    (t x : ℝ) (n : ℕ) :
    let W := globalNativeTimePrimitive q s amplitude t x
    let f := nativeTimePrimitiveCutoff q s amplitude t x n 0
    let g := nativeTimePrimitiveCutoff q s amplitude t x n 1
    let err := fun z : UpperHalfPlane => ∑ i : Fin 2,
      ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) z*W z‖^(2 : ℕ)
    Integrable (fun z => ∑ i : Fin 2, ‖weightedDeriv (direction i) f.field z‖^(2 : ℕ))
      D4BMModularCore.measure ∧
    Integrable err D4BMModularCore.measure ∧
    (∫ z : UpperHalfPlane, ∑ i : Fin 2, ‖weightedDeriv (direction i) f.field z‖^(2 : ℕ)
      ∂D4BMModularCore.measure) =
      -(∫ z : UpperHalfPlane, conj (chartLaplacian W z)*g.field z
        ∂D4BMModularCore.measure).re + ∫ z, err z ∂D4BMModularCore.measure := by
  dsimp only
  let f := nativeTimePrimitiveCutoff q s amplitude t x n 0
  let g := nativeTimePrimitiveCutoff q s amplitude t x n 1
  let W := globalNativeTimePrimitive q s amplitude t x
  let E := fun z : UpperHalfPlane => ∑ i : Fin 2, ‖weightedDeriv (direction i) f.field z‖^(2 : ℕ)
  let H := fun z : UpperHalfPlane => (frameEnergy W g.field z).re
  let err := fun z : UpperHalfPlane => ∑ i : Fin 2,
    ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) z*W z‖^(2 : ℕ)
  have hE : Integrable E D4BMModularCore.measure := by
    apply integrable_finsetSum
    intro i hi
    exact (weightedDeriv_memLp (direction i) f.field f.smooth f.compact).norm.integrable_sq
  obtain ⟨hgreen,hforce,heq⟩ := nativeTimePrimitive_compact_angular_green q s amplitude t x n
  have hH : Integrable H D4BMModularCore.measure := hgreen.re
  have hp (z : UpperHalfPlane) : E z = H z+err z :=
    nativeCutoff_energy_pointwise q s amplitude t x n z
  have herr : Integrable err D4BMModularCore.measure := by
    apply (hE.sub hH).congr
    exact Filter.Eventually.of_forall (fun z => by change E z-H z=err z; linarith [hp z])
  refine ⟨hE,herr,?_⟩
  change (∫ z, E z ∂D4BMModularCore.measure) = _
  rw [show E = fun z => H z+err z by funext z; exact hp z,
    integral_add hH herr]
  have hi := integral_re hgreen
  have hr := congrArg Complex.re heq
  change (∫ z, H z ∂D4BMModularCore.measure) =
    (∫ z, frameEnergy W g.field z ∂D4BMModularCore.measure).re at hi
  rw [hi,hr]
  rfl


private theorem cutoff_frame_formula (N : ℝ) (hN : 1 ≤ N) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (v : ℂ) :
    weightedDeriv v (modularCuspCutoff N) z =
      (z.im:ℂ)*((deriv (scaledCuspCutoff N) z.im:ℝ):ℂ)*(v.im:ℂ) := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hg : modularCuspCutoff N ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      fun w : ℂ => (scaledCuspCutoff N w.im:ℂ) := by
    have he : ∀ᶠ w : ℂ in 𝓝 (z:ℂ), modularCuspCutoff N (ofComplex w) =
        (scaledCuspCutoff N (ofComplex w).im:ℂ) := by
      apply hc.eventually (p := fun u : UpperHalfPlane =>
        modularCuspCutoff N u = (scaledCuspCutoff N u.im:ℂ))
      rw [ofComplex_apply]
      exact modularCuspCutoff_germ N hN z hz
    filter_upwards [he,isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw hp
    simpa only [Function.comp_apply,ofComplex_apply_of_im_pos hp,UpperHalfPlane.im] using! hw
  have hp := ((scaledCuspCutoff_smooth N).differentiable (by simp)).differentiableAt.hasDerivAt
    (x := z.im)
  have hF := Complex.ofRealCLM.hasFDerivAt.comp (z:ℂ)
    (hp.hasFDerivAt.comp (z:ℂ) Complex.imCLM.hasFDerivAt)
  unfold weightedDeriv
  rw [hg.fderiv_eq]
  change (z.im:ℂ)*(fderiv ℝ (Complex.ofRealCLM ∘ scaledCuspCutoff N ∘ Complex.im) (z:ℂ)) v = _
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply,Complex.ofRealCLM_apply,smul_eq_mul]
  push_cast
  ring

private theorem frame_zero_of_constant_germ {f : UpperHalfPlane → ℂ} {z : UpperHalfPlane}
    (h : f =ᶠ[𝓝 z] fun _ => (1:ℂ)) (v : ℂ) : weightedDeriv v f z = 0 := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have he : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] fun _ => (1:ℂ) := by
    apply hc.eventually (p := fun u : UpperHalfPlane => f u = 1)
    rw [ofComplex_apply]
    exact h
  unfold weightedDeriv
  rw [he.fderiv_eq]
  simp

/-- The complete localization error in the original joint measure, using the literal
native primitive and both original hyperbolic frame derivatives of the cusp cutoff. -/
def nativeJointCutoffError (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ)
    (p : ℝ × UpperHalfPlane) : ℝ :=
  ∑ i : Fin 2, ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) p.2 *
    nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ)

private theorem nativeJointCutoffError_measurable (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n : ℕ) : AEStronglyMeasurable (nativeJointCutoffError q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have hi (i : Fin 2) : AEStronglyMeasurable (fun p : ℝ × UpperHalfPlane =>
      ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) p.2 *
        nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ))
      (radialMeasure.prod D4BMModularCore.measure) := by
    have hd := ((weightedDeriv_continuous (direction i) _ (modularCuspCutoff_smooth _ hN)).comp
      (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))).aestronglyMeasurable
        (μ := radialMeasure.prod D4BMModularCore.measure)
    have hm := hd.mul (nativeJointTimePrimitiveField_memLp q s amplitude t).aestronglyMeasurable
    apply (hm.norm.mul hm.norm).congr
    filter_upwards [] with p
    change ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) p.2 *
      nativeJointTimePrimitiveField q s amplitude t p‖ *
      ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) p.2 *
        nativeJointTimePrimitiveField q s amplitude t p‖ = _
    rw [pow_two]
  change AEStronglyMeasurable (fun p : ℝ × UpperHalfPlane => ∑ i : Fin 2,
    ‖weightedDeriv (direction i) (modularCuspCutoff ((n:ℝ)+1)) p.2 *
      nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ)) _
  apply ((hi 0).add (hi 1)).congr
  filter_upwards [] with p
  simp only [Pi.add_apply,Fin.sum_univ_two]

private theorem nativeJointCutoffError_bound (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (p : ℝ × UpperHalfPlane), p.2 ∈ ModularGroup.fd →
      ‖nativeJointCutoffError q s amplitude t n p‖ ≤
        C^(2 : ℕ)*‖nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ) := by
  obtain ⟨C,hC,hbound⟩ := scaledCuspCutoff_derivative_bounds
  refine ⟨C,hC,?_⟩
  intro n p hp
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have hd : ‖weightedDeriv Complex.I (modularCuspCutoff ((n:ℝ)+1)) p.2‖ ≤ C := by
    rw [cutoff_frame_formula _ hN _ hp]
    simpa only [Complex.I_im,Complex.ofReal_one,mul_one,← Complex.ofReal_mul,
      Complex.norm_real,Real.norm_eq_abs] using (hbound ((n:ℝ)+1) p.2.im).1
  have hz : weightedDeriv 1 (modularCuspCutoff ((n:ℝ)+1)) p.2 = 0 := by
    simp only [cutoff_frame_formula _ hN _ hp,Complex.one_im,Complex.ofReal_zero,mul_zero]
  have hpos : 0 ≤ nativeJointCutoffError q s amplitude t n p := by
    unfold nativeJointCutoffError
    positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hpos]
  simp only [nativeJointCutoffError,Fin.sum_univ_two,direction,Matrix.cons_val_zero,
    Matrix.cons_val_one,hz,zero_mul,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add]
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (by gcongr) (sq_nonneg _)

/-- The actual joint cutoff-gradient error is integrable at every scale and its
integral tends to zero. The domination uses only the now-proved native L² admission,
never the still-unproved global gradient energy. -/
theorem nativeJointCutoffError_tendsto_zero (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    (∀ n : ℕ, Integrable (nativeJointCutoffError q s amplitude t n)
      (radialMeasure.prod D4BMModularCore.measure)) ∧
    Tendsto (fun n : ℕ => ∫ p, nativeJointCutoffError q s amplitude t n p
      ∂radialMeasure.prod D4BMModularCore.measure) atTop (𝓝 (0:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := nativeJointCutoffError_bound q s amplitude t
  have hdom := (nativeJointTimePrimitiveField_memLp q s amplitude t).norm.integrable_sq.const_mul (C^(2 : ℕ))
  have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      p.2 ∈ ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  have hb (n : ℕ) : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
      ‖nativeJointCutoffError q s amplitude t n p‖ ≤
        C^(2 : ℕ)*‖nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ) := by
    filter_upwards [hfd] with p hp
    exact hbound n p hp
  refine ⟨fun n => hdom.mono' (nativeJointCutoffError_measurable q s amplitude t n) (hb n),?_⟩
  have h := tendsto_integral_of_dominated_convergence
    (fun p => C^(2 : ℕ)*‖nativeJointTimePrimitiveField q s amplitude t p‖^(2 : ℕ))
    (nativeJointCutoffError_measurable q s amplitude t) hdom hb
    (f := fun _ => (0:ℝ)) ?_
  · simpa only [integral_zero] using h
  filter_upwards [hfd] with p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [modularCuspCutoff_eventually_one p.2 hp] with n hn
  simp only [nativeJointCutoffError,frame_zero_of_constant_germ hn,zero_mul,norm_zero,
    zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero]


/-- The cutoff error also vanishes with the exact physical radial factor sech²(x).
Its integrability and limit are consequences of the stronger unweighted estimate. -/
theorem nativeJointCutoffError_weighted_tendsto_zero (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    (∀ n : ℕ, Integrable (fun p : ℝ × UpperHalfPlane =>
      nativeJointCutoffError q s amplitude t n p/(Real.cosh p.1)^(2 : ℕ))
      (radialMeasure.prod D4BMModularCore.measure)) ∧
    Tendsto (fun n : ℕ => ∫ p : ℝ × UpperHalfPlane,
      nativeJointCutoffError q s amplitude t n p/(Real.cosh p.1)^(2 : ℕ)
      ∂radialMeasure.prod D4BMModularCore.measure) atTop (𝓝 (0:ℝ)) := by
  obtain ⟨hi,ht⟩ := nativeJointCutoffError_tendsto_zero q s amplitude t
  have hpos (n : ℕ) (p : ℝ × UpperHalfPlane) : 0 ≤ nativeJointCutoffError q s amplitude t n p := by
    unfold nativeJointCutoffError
    positivity
  have hcosh (p : ℝ × UpperHalfPlane) : (1:ℝ) ≤ (Real.cosh p.1)^(2 : ℕ) := by
    nlinarith [Real.one_le_cosh p.1]
  have hle (n : ℕ) (p : ℝ × UpperHalfPlane) :
      nativeJointCutoffError q s amplitude t n p/(Real.cosh p.1)^(2 : ℕ) ≤
        nativeJointCutoffError q s amplitude t n p := div_le_self (hpos n p) (hcosh p)
  have hw (n : ℕ) : Integrable (fun p : ℝ × UpperHalfPlane =>
      nativeJointCutoffError q s amplitude t n p/(Real.cosh p.1)^(2 : ℕ))
      (radialMeasure.prod D4BMModularCore.measure) := by
    apply (hi n).mono'
    · have hc : Continuous (fun p : ℝ × UpperHalfPlane => (Real.cosh p.1)^(2 : ℕ)) := by fun_prop
      exact ((nativeJointCutoffError_measurable q s amplitude t n).aemeasurable.div
        hc.aemeasurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_of_nonneg (div_nonneg (hpos n p) (sq_nonneg _))]
        exact hle n p)
  refine ⟨hw,squeeze_zero ?_ ?_ ht⟩
  · intro n
    exact integral_nonneg (fun p => div_nonneg (hpos n p) (sq_nonneg _))
  · intro n
    exact integral_mono (hw n) (hi n) (hle n)

end
end RHTower.D4BMNativeResponse
