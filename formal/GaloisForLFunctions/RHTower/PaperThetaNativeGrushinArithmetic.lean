import GaloisForLFunctions.RHTower.PaperThetaNativeScalarReduction
import GaloisForLFunctions.RHTower.PaperThetaNativeArithmeticResolvent

/-! # Resonant block solving in the full native arithmetic domain

Every continuous BV forcing and prescribed trace have a unique corrected
native solution at every complex parameter. Its compact AC representative
retains the full signed arithmetic form.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph GaloisForLFunctions.HTGeometry

private theorem bv_add_complex {f h : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (hh : BoundedVariationOn h univ) : BoundedVariationOn (fun x => f x+h x) univ := by
  have hb : eVariationOn (fun x => f x+h x) univ ≤
      ENNReal.ofReal ((eVariationOn f univ).toReal+(eVariationOn h univ).toReal) := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, _⟩⟩
    rw [show (∑ i ∈ Finset.range n, edist (f (u (i+1))+h (u (i+1))) (f (u i)+h (u i))) =
        ENNReal.ofReal (∑ i ∈ Finset.range n,
          ‖(f (u (i+1))+h (u (i+1)))-(f (u i)+h (u i))‖) by
      simp only [edist_dist, dist_eq_norm]
      exact (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).symm]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∑ i ∈ Finset.range n, (‖f (u (i+1))-f (u i)‖+‖h (u (i+1))-h (u i)‖) := by
        apply Finset.sum_le_sum
        intro i _
        rw [show (f (u (i+1))+h (u (i+1)))-(f (u i)+h (u i)) =
          (f (u (i+1))-f (u i))+(h (u (i+1))-h (u i)) by ring]
        exact norm_add_le _ _
      _ = (∑ i ∈ Finset.range n, ‖f (u (i+1))-f (u i)‖)+
          ∑ i ∈ Finset.range n, ‖h (u (i+1))-h (u i)‖ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (bv_partition_norm_le hf u hu n) (bv_partition_norm_le hh u hu n)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

private theorem nativeCounterSource_zero {x : ℝ} (hx : 2 ≤ |x|) (z : ℂ) :
    nativeCounterSource z x = 0 := by
  rw [nativeCounterSource_apply, baseCutoff.zero_of_le_dist
    (by simpa only [baseCutoff, Real.dist_eq, sub_zero] using hx), Complex.ofReal_zero, mul_zero]

private theorem nativeCounterSource_clamp (z : ℂ) (x : ℝ) :
    nativeCounterSource z (nativeClampedCoordinate x) = nativeCounterSource z x := by
  rcases le_total x (-2) with hx | hx
  · have hc : nativeClampedCoordinate x = -2 := by
      rw [nativeClampedCoordinate, min_eq_right (by linarith), max_eq_left hx]
    rw [hc, nativeCounterSource_zero (by norm_num),
      nativeCounterSource_zero ((neg_le_abs x).trans' (by linarith))]
  · rcases le_total 2 x with hy | hy
    · have hc : nativeClampedCoordinate x = 2 := by
        rw [nativeClampedCoordinate, min_eq_left hy, max_eq_right (by norm_num)]
      rw [hc, nativeCounterSource_zero (by norm_num), nativeCounterSource_zero (hy.trans (le_abs_self x))]
    · rw [nativeClampedCoordinate_eq ⟨hx,hy⟩]

theorem nativeCounterSource_boundedVariation (z : ℂ) :
    BoundedVariationOn (nativeCounterSource z) univ := by
  have hc : Monotone nativeClampedCoordinate := fun _ _ h =>
    max_le_max le_rfl (min_le_min le_rfl h)
  have hb := hc.monotoneOn.boundedVariationOn (fun x _ => nativeClampedCoordinate_bound x)
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (nativeCounterSource_hasCompactSupport z) (nativeCounterSource_contDiff z) (by norm_num)
  have h := hC.comp_boundedVariationOn hb
  have he : (nativeCounterSource z : ℝ → ℂ) ∘ nativeClampedCoordinate = nativeCounterSource z :=
    funext (nativeCounterSource_clamp z)
  rwa [he] at h

def nativeBVUniform (g : ThetaContinuousBV) : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup g g.continuous g.bound g.norm_le

def nativeCorrectedBVForcing (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) : ThetaContinuousBV where
  toFun := nativeCorrectedForcing z (nativeBVUniform g) t
  continuous := (nativeCorrectedForcing z (nativeBVUniform g) t).continuous
  bv := by
    have hb := boundedVariation_affine
      (bv_add_complex g.bv (boundedVariation_affine (nativeCounterSource_boundedVariation z)
        0 (-nativeBoundaryCorrection z (nativeBVUniform g) t))) (z*t) 1
    convert hb using 1
    funext x
    change g x-nativeBoundaryCorrection z (nativeBVUniform g) t*nativeCounterSource z x+z*t*1 =
      z*t+1*(g x+(0+-nativeBoundaryCorrection z (nativeBVUniform g) t*nativeCounterSource z x))
    ring

def nativeGrushinBV (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) : ThetaNativeDomain :=
  nativeZeroMomentSolution z (nativeCorrectedBVForcing z g t) t
    (nativeCorrectedForcing_moment z (nativeBVUniform g) t)

@[simp] theorem nativeGrushinBV_apply (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) (x : ℝ) :
    nativeGrushinBV z g t x = nativeGrushinSolution z (nativeBVUniform g) t x := rfl

theorem nativeGrushinBV_trace (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) :
    thetaTailTrace (nativeGrushinBV z g t) = t := nativeZeroMomentSolution_trace _ _ _ _

theorem nativeGrushinBV_equation (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) (x : ℝ) :
    thetaSpatialAction (nativeGrushinBV z g t) x-z*nativeGrushinBV z g t x+
      nativeBoundaryCorrection z (nativeBVUniform g) t*nativeCounterSource z x = g x := by
  have he := nativeZeroMomentSolution_equation z (nativeCorrectedBVForcing z g t) t
    (nativeCorrectedForcing_moment z (nativeBVUniform g) t) x
  change thetaSpatialAction (nativeGrushinBV z g t) x-z*nativeGrushinBV z g t x =
    (g x-nativeBoundaryCorrection z (nativeBVUniform g) t*nativeCounterSource z x+z*t*1)-z*t at he
  linear_combination he

theorem nativeGrushinBV_unique (z : ℂ) (g : ThetaContinuousBV) (t : ℂ)
    (f : ThetaNativeDomain) (c : ℂ) (ht : thetaTailTrace f = t)
    (he : ∀ x, thetaSpatialAction f x-z*f x+c*nativeCounterSource z x = g x) :
    f = nativeGrushinBV z g t ∧ c = nativeBoundaryCorrection z (nativeBVUniform g) t := by
  have ho (x : ℝ) : deriv f x+sourceLogDerivative x*(f x-t)+I*z*f x =
      -I*(g x-c*nativeCounterSource z x) := by
    have h := he x
    rw [thetaSpatialAction, ht] at h
    linear_combination (norm := ring_nf) -I*h
    simp only [Complex.I_sq]
    ring
  have hm := boundedThetaMoment_source_equation z (nativeBVUniform f.toThetaContinuousBV)
    (nativeBVUniform g-c • nativeCounterSource z) t f.differentiable ho
  rw [map_sub, map_smul, nativeCounterSource_moment] at hm
  have hc : c = nativeBoundaryCorrection z (nativeBVUniform g) t := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')).2
    linear_combination -hm
  refine ⟨?_,hc⟩
  let F := nativeGrushinBV z g t
  let v : ℝ → ℂ := fun x => f x-F x
  have hv : Differentiable ℝ v := f.differentiable.sub F.differentiable
  have hr : Tendsto v atTop (𝓝 0) := by
    have h := f.rightTrace.sub F.rightTrace
    rw [ht, nativeGrushinBV_trace, sub_self] at h
    exact h
  have hode (x : ℝ) : deriv v x+(sourceLogDerivative x+I*z)*v x = 0 := by
    rw [show deriv v x = deriv f x-deriv F x from
      deriv_sub (f.differentiable x) (F.differentiable x)]
    have hh := nativeGrushinSolution_ode z (nativeBVUniform g) t x
    change deriv F x+sourceLogDerivative x*(F x-t)+I*z*F x =
      -I*(g x-nativeBoundaryCorrection z (nativeBVUniform g) t*nativeCounterSource z x) at hh
    have h := ho x
    rw [hc] at h
    dsimp only [v]
    linear_combination h-hh
  have hz := nativeODE_zero_of_trace_zero z v hv hr hode
  apply ThetaNativeDomain.ext
  intro x
  exact sub_eq_zero.mp (congrFun hz x)

/-- Every actual BV forcing has a unique full-arithmetic corrected solution,
including at every multiple Xi resonance. -/
theorem nativeGrushin_full_arithmetic (z : ℂ) (g : ThetaContinuousBV) (t : ℂ) :
    ∃! p : ThetaNativeDomain × ℂ,
      thetaTailTrace p.1 = t ∧
      (∀ x, thetaSpatialAction p.1 x-z*p.1 x+p.2*nativeCounterSource z x = g x) ∧
      AbsolutelyContinuousOnInterval (nativeClosedQuantile p.1) 0 1 ∧
      ∀ L : ℂ →L[ℝ] ℝ,
        (nativeWeilGraph p.1 L).val.fst =ᵐ[massMeasure] (fun x => L (p.1 x)) ∧
        sourceWeilEnergy (nativeWeilGraph p.1 L) =
          ThetaQuantileArithmetic.weilEnergy (fun u => L (nativeClosedQuantile p.1 u)) := by
  refine ⟨(nativeGrushinBV z g t,nativeBoundaryCorrection z (nativeBVUniform g) t),
    ⟨nativeGrushinBV_trace z g t, nativeGrushinBV_equation z g t,
      absolutelyContinuousOnInterval_nativeClosedQuantile _,
      fun L => ⟨nativeWeilGraph_source _ L,nativeWeilGraph_quantile _ L⟩⟩, ?_⟩
  rintro ⟨f,c⟩ ⟨ht,he,_⟩
  exact Prod.ext (nativeGrushinBV_unique z g t f c ht he).1
    (nativeGrushinBV_unique z g t f c ht he).2

end RHTower.PaperThetaEndpoint
