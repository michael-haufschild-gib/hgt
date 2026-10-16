import GaloisForLFunctions.RHTower.PaperThetaCompactNativeResolvent

/-! # Complete nonzero spectrum of the literal theta resolvent

Compact Fredholm theory closes the gap between the source-defined operator
and its admitted modes. The only extra spectral mode is the constant at zero
for the differential generator; every other mode is selected by Xi itself.
-/

noncomputable section
open Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def nativeDivisorMode (w : {w : ℂ // w = 0 ∨ XiC w = 0}) : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (flatQuotient w.val)
    (differentiable_flatQuotient w.val).continuous
    ((bounded_flatQuotient_iff w.val).mpr w.property).choose
    ((bounded_flatQuotient_iff w.val).mpr w.property).choose_spec

@[simp] theorem nativeDivisorMode_apply (w : {w : ℂ // w = 0 ∨ XiC w = 0}) (x : ℝ) :
    nativeDivisorMode w x = flatQuotient w.val x := rfl

theorem nativeDivisorMode_ne_zero (w : {w : ℂ // w = 0 ∨ XiC w = 0}) :
    nativeDivisorMode w ≠ 0 := by
  intro h
  have hf : flatQuotient w.val = 0 := by
    funext x
    exact congrArg (fun f : NativeContinuousSpace => f x) h
  have ht := tendsto_flatQuotient_atTop w.val
  rw [hf] at ht
  have hn := tendsto_nhds_unique ht
    (tendsto_const_nhds : Tendsto (0 : ℝ → ℂ) atTop (𝓝 0))
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) hn

theorem boundedNativeResolvent_eigenvalue_iff (z : ThetaRegularParameter)
    (μ : ℂ) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (boundedNativeResolvent z).toLinearMap μ ↔
      z.val+μ⁻¹ = 0 ∨ XiC (z.val+μ⁻¹) = 0 := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := h.exists_hasEigenvector
    have heig : boundedNativeResolvent z g = μ • g := hg.apply_eq_smul
    by_contra hn
    obtain ⟨hw, hXi⟩ := not_or.mp hn
    have hode (x : ℝ) :
        deriv (boundedNativeResolvent z g) x+
          sourceLogDerivative x*(boundedNativeResolvent z g x-boundedResolventTrace z g)+
          I*(z.val+μ⁻¹)*boundedNativeResolvent z g x = 0 := by
      have hx : boundedNativeResolvent z g x = μ*g x := congrArg
        (fun f : NativeContinuousSpace => f x) heig
      have hc : μ⁻¹*boundedNativeResolvent z g x = g x := by
        rw [hx, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
      linear_combination boundedNativeResolvent_ode z g x+I*hc
    have hz := nativeHomogeneous_zero hw hXi (boundedNativeResolvent z g)
      (boundedResolventTrace z g)
      (fun x => (hasDerivAt_boundedNativeResolvent z g x).differentiableAt)
      (boundedNativeResolvent_atTop z g)
      ⟨‖boundedNativeResolvent z g‖, (boundedNativeResolvent z g).norm_coe_le_norm⟩ hode
    apply hg.2
    ext x
    have hx : μ*g x = 0 := (congrArg (fun f : NativeContinuousSpace => f x) heig).symm.trans
      (congrFun hz x)
    exact (mul_eq_zero.mp hx).resolve_left hμ
  · intro hw
    let w : {w : ℂ // w = 0 ∨ XiC w = 0} := ⟨z.val+μ⁻¹, hw⟩
    let f := nativeDivisorMode w
    have hf : Differentiable ℝ f := differentiable_flatQuotient w.val
    have ht : Tendsto f atTop (𝓝 (-1)) := tendsto_flatQuotient_atTop w.val
    have hode (x : ℝ) : deriv f x+sourceLogDerivative x*(f x-(-1))+
        I*z.val*f x = -I*(μ⁻¹ • f) x := by
      change deriv (flatQuotient (z.val+μ⁻¹)) x+
        sourceLogDerivative x*(flatQuotient (z.val+μ⁻¹) x-(-1))+
        I*z.val*flatQuotient (z.val+μ⁻¹) x = -I*(μ⁻¹*flatQuotient (z.val+μ⁻¹) x)
      linear_combination flatQuotient_source_equation (z.val+μ⁻¹) x
    have hsol := boundedNativeResolvent_unique z (μ⁻¹ • f) f (-1) hf ht hode
    rw [map_smul] at hsol
    have heig : boundedNativeResolvent z f = μ • f := by
      have hh := congrArg (fun v : NativeContinuousSpace => μ • v) hsol
      simpa only [smul_smul, mul_inv_cancel₀ hμ, one_smul] using hh.symm
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr heig, nativeDivisorMode_ne_zero w⟩

theorem boundedNativeResolvent_mem_spectrum_iff (z : ThetaRegularParameter)
    (μ : ℂ) (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ (boundedNativeResolvent z) ↔
      z.val+μ⁻¹ = 0 ∨ XiC (z.val+μ⁻¹) = 0 :=
  ((isCompactOperator_boundedNativeResolvent z).hasEigenvalue_iff_mem_spectrum hμ).symm.trans
    (boundedNativeResolvent_eigenvalue_iff z μ hμ)

/-- The complete nonzero spectrum of the actual compact native operator. -/
theorem nativeCompactResolvent_nonzero_spectrum :
    spectrum ℂ nativeCompactResolvent \ {0} =
      {μ : ℂ | μ ≠ 0 ∧ (I+μ⁻¹ = 0 ∨ XiC (I+μ⁻¹) = 0)} := by
  ext μ
  simp only [Set.mem_sdiff, mem_singleton_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h, hμ⟩
    exact ⟨hμ, by simpa only [nativeCompactParameter_val] using
      (boundedNativeResolvent_mem_spectrum_iff nativeCompactParameter μ hμ).mp h⟩
  · rintro ⟨hμ, h⟩
    refine ⟨?_, hμ⟩
    apply (boundedNativeResolvent_mem_spectrum_iff nativeCompactParameter μ hμ).mpr
    simpa only [nativeCompactParameter_val] using h

end RHTower.PaperThetaEndpoint
