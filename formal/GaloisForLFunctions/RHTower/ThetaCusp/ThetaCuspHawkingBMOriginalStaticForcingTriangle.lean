import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticForcingPrimitive

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalStaticForcingTriangle
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
open D4BMOriginalCornerForcing D4BMOriginalMetricHorizon D4BMOriginalCanonicalForcingMatch
open D4BMOriginalForcingJointHorizon D4BMOriginalStaticForcingPrimitive
noncomputable section
set_option autoImplicit false

private theorem closed_interval_integral (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b,f x)=∫ x in a..b,f x := by
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]

private theorem upper_clip (f : ℝ → ℂ) (a u c : ℝ) (hcu : c ≤ u) :
    (∫ p in Icc a u,if p ≤ c then f p else 0)=∫ p in a..max a c,f p := by
  have he : (fun p : ℝ => if p ≤ c then f p else 0)=(Iic c).indicator f := rfl
  rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic c ∩ Icc a u=Icc a c := by
    ext p
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.trans hcu⟩⟩
  rw [hs]
  by_cases hac : a ≤ c
  · rw [max_eq_right hac]
    exact closed_interval_integral f a c hac
  · rw [max_eq_left (le_of_not_ge hac),Icc_eq_empty hac]
    simp

private theorem lower_clip (g : ℝ → ℂ) (ξ b c : ℝ) (hξ : ξ ≤ b) (hcb : c ≤ b) :
    (∫ x in Icc ξ b,if c ≤ x then g x else 0)=∫ x in max ξ c..b,g x := by
  have he : (fun x : ℝ => if c ≤ x then g x else 0)=(Ici c).indicator g := rfl
  rw [he,integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici c ∩ Icc ξ b=Icc (max ξ c) b := by
    ext x
    simp only [mem_inter_iff,mem_Ici,mem_Icc,max_le_iff]
    tauto
  rw [hs]
  exact closed_interval_integral g _ b (max_le hξ hcb)

private theorem causal_triangle_swap (f g : ℝ → ℂ) (a ξ b T : ℝ)
    (hξ : ξ ≤ b) (hf : Continuous f) (hg : ContinuousOn g (Icc ξ b)) :
    (∫ x in ξ..b,g x*(∫ p in a..max a (T+x),f p))=
      ∫ p in a..max a (T+b),f p*(∫ x in max ξ (p-T)..b,g x) := by
  by_cases hT : T+b ≤ a
  · rw [max_eq_left hT,intervalIntegral.integral_same]
    calc
      _ = ∫ x in ξ..b,(0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc ξ b := by simpa only [uIcc_of_le hξ] using hx
        dsimp only
        rw [max_eq_left (by linarith [hx'.2] : T+x ≤ a),intervalIntegral.integral_same,mul_zero]
      _ = 0 := by simp
  · have hau : a ≤ T+b := (lt_of_not_ge hT).le
    rw [max_eq_right hau]
    have hc : ContinuousOn (fun z : ℝ×ℝ => g z.1*f z.2) ((Icc ξ b).prod (Icc a (T+b))) :=
      (hg.comp continuous_fst.continuousOn (fun _ h => h.1)).mul
        (hf.comp continuous_snd).continuousOn
    have hi : Integrable (fun z : ℝ×ℝ => g z.1*f z.2)
        ((volume.restrict (Icc ξ b)).prod (volume.restrict (Icc a (T+b)))) := by
      rw [Measure.prod_restrict,← Measure.volume_eq_prod]
      exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hregion : MeasurableSet {z : ℝ×ℝ | z.2 ≤ T+z.1} :=
      measurableSet_le measurable_snd (measurable_const.add measurable_fst)
    have hV : Integrable (fun z : ℝ×ℝ => if z.2 ≤ T+z.1 then g z.1*f z.2 else 0)
        ((volume.restrict (Icc ξ b)).prod (volume.restrict (Icc a (T+b)))) :=
      hi.indicator hregion
    have hrow (x : ℝ) (hx : x ∈ Icc ξ b) :
        (∫ p in Icc a (T+b),if p ≤ T+x then g x*f p else 0)=g x*(∫ p in a..max a (T+x),f p) := by
      have he : (fun p : ℝ => if p ≤ T+x then g x*f p else 0)=
          fun p => g x*(if p ≤ T+x then f p else 0) := by
        funext p
        split_ifs <;> simp
      rw [he,integral_const_mul,upper_clip f a (T+b) (T+x) (by linarith [hx.2])]
    have hcol (p : ℝ) (hp : p ∈ Icc a (T+b)) :
        (∫ x in Icc ξ b,if p ≤ T+x then g x*f p else 0)=f p*(∫ x in max ξ (p-T)..b,g x) := by
      have he : (fun x : ℝ => if p ≤ T+x then g x*f p else 0)=
          fun x => f p*(if p-T ≤ x then g x else 0) := by
        funext x
        have hh : p ≤ T+x ↔ p-T ≤ x := by constructor <;> intro h <;> linarith
        simp only [hh]
        split_ifs <;> simp [mul_comm]
      rw [he,integral_const_mul,lower_clip g ξ b (p-T) hξ (by linarith [hp.2])]
    calc
      _ = ∫ x in Icc ξ b,∫ p in Icc a (T+b),if p ≤ T+x then g x*f p else 0 := by
        rw [← closed_interval_integral _ ξ b hξ]
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact (hrow x hx).symm
      _ = ∫ p in Icc a (T+b),∫ x in Icc ξ b,if p ≤ T+x then g x*f p else 0 :=
        integral_integral_swap hV
      _ = _ := by
        rw [← closed_interval_integral _ a (T+b) hau]
        apply setIntegral_congr_fun measurableSet_Icc
        exact hcol

/-- The actual finite-cusp forcing kernel discrepancy. -/
def forcingKernelDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k x : ℝ) : ℂ :=
  kernelCut q br amp w (Real.exp k) x-
    physicalSelfSourceCoefficient q*forcingKernel q br amp (gradient q br) w x

/-- Both source-fixed forcing counterterm families, at the same finite cusp height. -/
def forcingCountertermDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k x : ℝ) : ℂ :=
  (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
      canonicalForcingCounterterm q br amp (gradient q br) w (horizonCoordinate x)+
    secondWeight q (Real.exp k)*
      canonicalForcingCounterterm q br amp (gradient q br+1) w (horizonCoordinate x)

def onsetDensity (q : XiZeroCopy) (br : Bool) (w : ℂ) (p : ℝ) : ℂ :=
  Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p

def staticForcingCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a ξ b T k : ℝ) : ℂ :=
  ∫ x in ξ..b,forcingKernelDifference q br amp w k x*
    (∫ p in a..max a (T+x),onsetDensity q br w p)

/-- The unchanged radial counterterm transported along the literal causal boundary. -/
def staticForcingCounterterm (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a ξ b T k : ℝ) : ℂ :=
  ∫ p in a..max a (T+b),onsetDensity q br w p*
    forcingCountertermDifference q br amp w k (max ξ (p-T))

private theorem onset_continuous (q : XiZeroCopy) (br : Bool) (w : ℂ) :
    Continuous (onsetDensity q br w) := by
  have ht : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  unfold onsetDensity
  fun_prop

theorem forcing_kernel_difference_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k : ℝ) :
    ContinuousOn (forcingKernelDifference q br amp w k) (Iio (0:ℝ)) := by
  have h0 := forcing_kernel_continuous q br amp (gradient q br) w
  have h1 := forcing_kernel_continuous q br amp (gradient q br+1) w
  have h := ((h0.const_mul (firstWeight q (Real.exp k))).add
    (h1.const_mul (secondWeight q (Real.exp k)))).sub (h0.const_mul (physicalSelfSourceCoefficient q))
  exact h.congr (fun x _ => by rw [forcingKernelDifference,kernel_two_kernels];rfl)

/-- The actual causal forcing triangle is exactly the time integral of its
original radial cuts with moving lower endpoint; finite product admission
justifies this exchange before any cutoff limit. -/
theorem static_forcing_triangle_identity (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a ξ b T k : ℝ) (hξ : ξ ≤ b) (hb : b < 0) :
    staticForcingCut q br amp w a ξ b T k=
      ∫ p in a..max a (T+b),onsetDensity q br w p*
        (∫ x in max ξ (p-T)..b,forcingKernelDifference q br amp w k x) :=
  causal_triangle_swap _ _ a ξ b T hξ (onset_continuous q br w)
    ((forcing_kernel_difference_continuous q br amp w k).mono (fun _ hx => hx.2.trans_lt hb))

/-- The actual canonical primitive at the original radial coordinate. -/
def primitiveDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (b k x : ℝ) : ℂ :=
  canonicalForcingDifferenceCut q br amp w (horizonCoordinate b) (horizonCoordinate x,k)

theorem forcing_counterterm_difference_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (k : ℝ) : ContinuousOn (forcingCountertermDifference q br amp w k) (Iio (0:ℝ)) := by
  intro x hx
  have he := (horizonCoordinate_interior x hx).1
  have h0 := (forcing_counterterm_continuousAt q br amp (gradient q br) w he).comp
    (horizonCoordinate_hasDerivAt x).continuousAt
  have h1 := (forcing_counterterm_continuousAt q br amp (gradient q br+1) w he).comp
    (horizonCoordinate_hasDerivAt x).continuousAt
  exact ((h0.const_mul _).add (h1.const_mul _)).continuousWithinAt

/-- The retained primitive and transported counterterm recover the original
radial integral exactly, without a limit or an assumed restoration identity. -/
theorem radial_difference_eq_primitive (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (b k x : ℝ) (hb : b < 0) (hx : x < 0) :
    (∫ y in x..b,forcingKernelDifference q br amp w k y)=
      primitiveDifference q br amp w b k x+forcingCountertermDifference q br amp w k x := by
  have hi (K : ℂ) : IntervalIntegrable (forcingKernel q br amp K w) volume x b :=
    ((forcing_kernel_continuous q br amp K w).mono
      (fun _ hy => hy.2.trans_lt (max_lt hx hb))).intervalIntegrable
  have hcut : IntervalIntegrable (kernelCut q br amp w (Real.exp k)) volume x b := by
    apply (((hi (gradient q br)).const_mul (firstWeight q (Real.exp k))).add
      ((hi (gradient q br+1)).const_mul (secondWeight q (Real.exp k)))).congr
    intro y _
    exact (kernel_two_kernels q br amp w _ y).symm
  unfold forcingKernelDifference primitiveDifference canonicalForcingDifferenceCut
  rw [tortoiseOf_horizonCoordinate hx,tortoiseOf_horizonCoordinate hb,
    intervalIntegral.integral_sub hcut ((hi (gradient q br)).const_mul _),intervalIntegral.integral_const_mul]
  unfold forcingCountertermDifference
  dsimp only [D4BMOriginalForcingJointHorizon.gradient]
  ring

theorem forcing_primitive_difference_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (b k : ℝ) (hb : b < 0) : ContinuousOn (primitiveDifference q br amp w b k) (Iio (0:ℝ)) := by
  have hg := forcing_kernel_difference_continuous q br amp w k
  have hc := forcing_counterterm_difference_continuous q br amp w k
  have h : ContinuousOn (fun x => (∫ y in x..b,forcingKernelDifference q br amp w k y)-
      forcingCountertermDifference q br amp w k x) (Iio (0:ℝ)) := by
    intro x hx
    have hi : IntervalIntegrable (forcingKernelDifference q br amp w k) volume x b :=
      (hg.mono (fun _ hy => hy.2.trans_lt (max_lt hx hb))).intervalIntegrable
    have hder := intervalIntegral.integral_hasDerivAt_left hi
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Iio hg x hx)
      ((hg x hx).continuousAt (Iio_mem_nhds hx))
    exact (hder.continuousAt.sub ((hc x hx).continuousAt (Iio_mem_nhds hx))).continuousWithinAt
  apply h.congr
  intro x hx
  dsimp only
  rw [radial_difference_eq_primitive q br amp w b k x hb hx,add_sub_cancel_right]

/-- The original moving forcing cut minus the unchanged counterterm transported
along its causal boundary equals the admitted integral of the canonical
primitive discrepancy. All finite horizon and temporal corners are retained. -/
theorem static_forcing_counterterm_identity (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a ξ b T k : ℝ) (hξ : ξ ≤ b) (hb : b < 0) :
    staticForcingCut q br amp w a ξ b T k-staticForcingCounterterm q br amp w a ξ b T k=
      ∫ p in a..max a (T+b),onsetDensity q br w p*primitiveDifference q br amp w b k (max ξ (p-T)) := by
  rw [static_forcing_triangle_identity q br amp w a ξ b T k hξ hb,staticForcingCounterterm]
  by_cases hT : T+b ≤ a
  · simp only [max_eq_left hT,intervalIntegral.integral_same,sub_self]
  · have hau : a ≤ T+b := (lt_of_not_ge hT).le
    rw [max_eq_right hau]
    have hmap : MapsTo (fun p : ℝ => max ξ (p-T)) (Icc a (T+b)) (Iio (0:ℝ)) := by
      intro p hp
      exact (max_le hξ (by linarith [hp.2])).trans_lt hb
    have hm : Continuous (fun p : ℝ => max ξ (p-T)) := by fun_prop
    have hJ := (onset_continuous q br w).continuousOn.mul
      ((forcing_primitive_difference_continuous q br amp w b k hb).comp hm.continuousOn hmap)
    have hC := (onset_continuous q br w).continuousOn.mul
      ((forcing_counterterm_difference_continuous q br amp w k).comp hm.continuousOn hmap)
    have he : (∫ p in a..T+b,onsetDensity q br w p*
        (∫ x in max ξ (p-T)..b,forcingKernelDifference q br amp w k x))=
        ∫ p in a..T+b,onsetDensity q br w p*primitiveDifference q br amp w b k (max ξ (p-T))+
          onsetDensity q br w p*forcingCountertermDifference q br amp w k (max ξ (p-T)) := by
      apply intervalIntegral.integral_congr
      intro p hp
      have hp' : p ∈ Icc a (T+b) := by simpa only [uIcc_of_le hau] using hp
      dsimp only
      rw [radial_difference_eq_primitive q br amp w b k _ hb (hmap hp'),mul_add]
    have hJI : IntervalIntegrable (fun p => onsetDensity q br w p*primitiveDifference q br amp w b k (max ξ (p-T)))
        volume a (T+b) := hJ.intervalIntegrable_of_Icc hau
    have hCI : IntervalIntegrable (fun p => onsetDensity q br w p*forcingCountertermDifference q br amp w k (max ξ (p-T)))
        volume a (T+b) := hC.intervalIntegrable_of_Icc hau
    rw [he,intervalIntegral.integral_add hJI hCI]
    abel

end
end RHTower.D4BMOriginalStaticForcingTriangle
