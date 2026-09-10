import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeRadialEndpoint
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointRadialFamilyAdmission
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Radial smoothing of the actual native angular energy family with the original
Dirichlet support and the literal projected radial derivative. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution
namespace RHTower.D4BMNativeResponse
open D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : SecondCountableTopologyEither ℝ D4BMModularCore.energyDomain := ⟨Or.inl inferInstance⟩
local instance : SecondCountableTopologyEither ℝ D4BMModularCore.Space := ⟨Or.inl inferInstance⟩

/-- The actual angular energy family with its shrinking Dirichlet neighborhood removed. -/
def nativeInteriorAngularEnergy (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ)
    (x : ℝ) : D4BMModularCore.energyDomain :=
  nativeDirichletCutoff m x • nativeTimePrimitiveAngularEnergy q s amplitude t n x

private theorem interior_continuous (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) :
    Continuous (nativeInteriorAngularEnergy q s amplitude t n m) :=
  (nativeDirichletCutoff_profile m).1.continuous.smul
    (nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n)

private theorem interior_compact (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) :
    HasCompactSupport (nativeInteriorAngularEnergy q s amplitude t n m) := by
  have he : nativeDirichletCutoff m • nativeTimePrimitiveAngularEnergy q s amplitude t n =
      nativeInteriorAngularEnergy q s amplitude t n m := by
    funext x
    rfl
  rw [← he]
  exact (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n).smul_left

private theorem interior_value (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) :
    (fun x => D4BMModularCore.embedding (nativeInteriorAngularEnergy q s amplitude t n m x)) =
    (fun x => nativeDirichletCutoff m x •
      D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)) := by
  funext x
  exact (D4BMModularCore.embedding.restrictScalars ℝ).map_smul _ _

private theorem interior_value_contDiff (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) :
    ContDiff ℝ 1 (fun x => D4BMModularCore.embedding
      (nativeInteriorAngularEnergy q s amplitude t n m x)) := by
  rw [interior_value]
  exact ((nativeDirichletCutoff_profile m).1.of_le (by simp)).smul
    (nativeTimePrimitiveAngularEnergy_value_contDiff q s amplitude t n)

private def smoothingWidth (m k : ℕ) : ℝ := (1/((m:ℝ)+1))/((k:ℝ)+2)
private theorem smoothingWidth_pos (m k : ℕ) : 0 < smoothingWidth m k := by
  unfold smoothingWidth
  positivity
private theorem smoothingWidth_lt (m k : ℕ) : smoothingWidth m k < 1/((m:ℝ)+1) := by
  unfold smoothingWidth
  apply div_lt_self (by positivity)
  have hk : (0:ℝ) ≤ k := by positivity
  linarith

/-- Convolution in the original angular energy space, using the existing normalized bump. -/
def nativeRadialMollification (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    ℝ → D4BMModularCore.energyDomain :=
  convolution (bumpMollifier (smoothingWidth_pos m k))
    (nativeInteriorAngularEnergy q s amplitude t n m) (ContinuousLinearMap.lsmul ℝ ℝ) volume

private theorem mollification_smooth (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    ContDiff ℝ ∞ (nativeRadialMollification q s amplitude t n m k) :=
  (hasCompactSupport_bumpMollifier (smoothingWidth_pos m k)).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (widthBump (smoothingWidth_pos m k)).contDiff_normed
    (interior_continuous q s amplitude t n m).locallyIntegrable

private theorem mollification_compact (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    HasCompactSupport (nativeRadialMollification q s amplitude t n m k) :=
  (hasCompactSupport_bumpMollifier (smoothingWidth_pos m k)).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (interior_compact q s amplitude t n m)

private theorem mollification_support (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    tsupport (nativeRadialMollification q s amplitude t n m k) ⊆ Iio 0 := by
  have hs : Function.support (nativeRadialMollification q s amplitude t n m k) ⊆
      Iic (-(1/((m:ℝ)+1))) := by
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)) hx
    have hy' : |y| < smoothingWidth m k := by
      change y ∈ Function.support ((widthBump (smoothingWidth_pos m k)).normed volume) at hy
      rw [(widthBump (smoothingWidth_pos m k)).support_normed_eq,
        Metric.mem_ball,Real.dist_eq,sub_zero] at hy
      exact hy
    have hz' : z < -2*(1/((m:ℝ)+1)) := by
      by_contra hh
      apply hz
      change nativeDirichletCutoff m z • nativeTimePrimitiveAngularEnergy q s amplitude t n z = 0
      rw [(nativeDirichletCutoff_profile m).2.2.1 z (le_of_not_gt hh),zero_smul]
    have hwidth := smoothingWidth_lt m k
    have hy'' := le_abs_self y
    change y+z ≤ -(1/((m:ℝ)+1))
    linarith
  have ht : tsupport (nativeRadialMollification q s amplitude t n m k) ⊆
      Iic (-(1/((m:ℝ)+1))) := closure_minimal hs isClosed_Iic
  intro x hx
  have h := ht hx
  have hp : (0:ℝ) < 1/((m:ℝ)+1) := by positivity
  exact lt_of_le_of_lt h (neg_neg_of_pos hp)

/-- A constructed smooth compact radial energy family inside the physical Dirichlet half-line. -/
def nativeRadialMollificationFamily (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    RadialEnergyFamily where
  field := nativeRadialMollification q s amplitude t n m k
  smooth := mollification_smooth q s amplitude t n m k
  compact := mollification_compact q s amplitude t n m k
  support := mollification_support q s amplitude t n m k

/-- Every constructed native smoothing is already in the original joint differential domain. -/
theorem nativeRadialMollification_graph_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    familyPacketLift (nativeRadialMollificationFamily q s amplitude t n m k).packet ∈ jointDomain :=
  (nativeRadialMollificationFamily q s amplitude t n m k).graph_mem

private theorem mollification_map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F)
    (g : ℝ → E) (hg : Continuous g) (m k : ℕ) (x : ℝ) :
    L (convolution (bumpMollifier (smoothingWidth_pos m k)) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
      convolution (bumpMollifier (smoothingWidth_pos m k)) (fun y => L (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hi : Integrable (fun y => bumpMollifier (smoothingWidth_pos m k) y • g (x-y)) (volume : Measure ℝ) :=
    (hasCompactSupport_bumpMollifier (smoothingWidth_pos m k)).convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (continuous_bumpMollifier (smoothingWidth_pos m k)).locallyIntegrable hg x
  change L (∫ y, bumpMollifier (smoothingWidth_pos m k) y • g (x-y)) =
    ∫ y, bumpMollifier (smoothingWidth_pos m k) y • L (g (x-y))
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => L.map_smul _ _)

/-- The original value embedding commutes with the actual native radial smoothing. -/
theorem nativeRadialMollification_value (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m k : ℕ) :
    (fun x => D4BMModularCore.embedding (nativeRadialMollification q s amplitude t n m k x)) =
    convolution (bumpMollifier (smoothingWidth_pos m k))
      (fun x => D4BMModularCore.embedding (nativeInteriorAngularEnergy q s amplitude t n m x))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  exact mollification_map (D4BMModularCore.embedding.restrictScalars ℝ) _
    (interior_continuous q s amplitude t n m) m k x

/-- After the original value embedding, the smoothed radial derivative is exactly
the convolution of the actual derivative, with the endpoint product rule retained. -/
theorem nativeRadialMollification_value_hasDerivAt (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n m k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => D4BMModularCore.embedding (nativeRadialMollification q s amplitude t n m k y))
      (convolution (bumpMollifier (smoothingWidth_pos m k))
        (deriv (fun y => D4BMModularCore.embedding (nativeInteriorAngularEnergy q s amplitude t n m y)))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x) x := by
  rw [nativeRadialMollification_value]
  apply HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (continuous_bumpMollifier (smoothingWidth_pos m k)).locallyIntegrable
    ((interior_compact q s amplitude t n m).comp_left (map_zero D4BMModularCore.embedding))
    (interior_value_contDiff q s amplitude t n m)


private theorem smoothingWidth_tendsto (m : ℕ) :
    Tendsto (smoothingWidth m) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (1/((m:ℝ)+1))/((k:ℝ)+2)) atTop (𝓝 0)
  simpa only [smoothingWidth,Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat (1/((m:ℝ)+1)))

private theorem smoothingWidth_le_one (m k : ℕ) : smoothingWidth m k ≤ 1 := by
  have h : (1:ℝ)/((m:ℝ)+1) ≤ 1 := by
    rw [div_le_one (by positivity : (0:ℝ) < (m:ℝ)+1)]
    have hm : (0:ℝ) ≤ m := by positivity
    linarith
  exact (smoothingWidth_lt m k).le.trans h

private theorem mollification_L2_convergence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E) (hg : Continuous g)
    (hc : HasCompactSupport g) (m : ℕ) :
    (∀ k : ℕ, Integrable (fun x => ‖convolution (bumpMollifier (smoothingWidth_pos m k)) g
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x-g x‖^2) radialMeasure) ∧
    Tendsto (fun k : ℕ => ∫ x, ‖convolution (bumpMollifier (smoothingWidth_pos m k)) g
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x-g x‖^2 ∂radialMeasure) atTop (𝓝 0) := by
  let f (k : ℕ) : ℝ → E := convolution (bumpMollifier (smoothingWidth_pos m k)) g
    (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hfc (k : ℕ) : Continuous (f k) :=
    ((hasCompactSupport_bumpMollifier (smoothingWidth_pos m k)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (widthBump (smoothingWidth_pos m k)).contDiff_normed
      hg.locallyIntegrable (n := 0)).continuous
  obtain ⟨R,hR⟩ := hc.isCompact.exists_bound_of_continuousOn continuous_id.continuousOn
  let K : Set ℝ := Icc (-max R 0-1) (max R 0+1)
  have hK : IsCompact K := isCompact_Icc
  have hgK : Function.support g ⊆ K := by
    intro x hx
    have h := (hR x (subset_closure hx)).trans (le_max_left R 0)
    change -max R 0-1 ≤ x ∧ x ≤ max R 0+1
    have hx' : |x| ≤ max R 0 := h
    exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
  have hfK (k : ℕ) : Function.support (f k) ⊆ K := by
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)) hx
    have hy' : |y| < smoothingWidth m k := by
      change y ∈ Function.support ((widthBump (smoothingWidth_pos m k)).normed volume) at hy
      rw [(widthBump (smoothingWidth_pos m k)).support_normed_eq,
        Metric.mem_ball,Real.dist_eq,sub_zero] at hy
      exact hy
    have hz' : |z| ≤ max R 0 := (hR z (subset_closure hz)).trans (le_max_left R 0)
    have hwidth := smoothingWidth_le_one m k
    change -max R 0-1 ≤ y+z ∧ y+z ≤ max R 0+1
    constructor <;> linarith [neg_abs_le y,neg_abs_le z,le_abs_self y,le_abs_self z]
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hg
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hfC (k : ℕ) (x : ℝ) : ‖f k x‖ ≤ C := by
    have hs : Function.support (bumpMollifier (smoothingWidth_pos m k)) ⊆
        Metric.ball (0:ℝ) (smoothingWidth m k) :=
      ((widthBump (smoothingWidth_pos m k)).support_normed_eq (μ := volume)).subset
    have h := dist_convolution_le (g := g) (μ := volume) (x₀ := x) (z₀ := (0:E)) hC₀
      hs (nonneg_bumpMollifier (smoothingWidth_pos m k)) (integral_bumpMollifier (smoothingWidth_pos m k))
      hg.aestronglyMeasurable (fun y _ => by simpa only [dist_zero_right] using hC y)
    simpa only [dist_zero_right] using h
  let M : ℝ → ℝ := K.indicator (fun _ => 4*C^2)
  have hM : Integrable M radialMeasure :=
    (integrableOn_const (μ := radialMeasure) (s := K) (C := 4*C^2) hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hec (k : ℕ) : Continuous (fun x => ‖f k x-g x‖^2) := ((hfc k).sub hg).norm.pow 2
  have hb (k : ℕ) (x : ℝ) : ‖‖f k x-g x‖^2‖ ≤ M x := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    dsimp only [M]
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      have hn := norm_sub_le (f k x) (g x)
      nlinarith [hfC k x,hC x,norm_nonneg (f k x-g x)]
    · have h0 : f k x = 0 := by
        by_contra hh
        exact hx (hfK k hh)
      have h1 : g x = 0 := by
        by_contra hh
        exact hx (hgK hh)
      rw [indicator_of_notMem hx,h0,h1,sub_zero,norm_zero]
      simp
  refine ⟨fun k => hM.mono' (hec k).aestronglyMeasurable (Eventually.of_forall (hb k)),?_⟩
  have hlim (x : ℝ) : Tendsto (fun k => f k x) atTop (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      (φ := fun k => widthBump (smoothingWidth_pos m k)) (smoothingWidth_tendsto m) hg x
  have h := tendsto_integral_of_dominated_convergence M (fun k => (hec k).aestronglyMeasurable)
    hM (fun k => Eventually.of_forall (hb k)) (f := fun _ : ℝ => (0:ℝ))
    (Eventually.of_forall fun x => by
      simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
        ((hlim x).sub (tendsto_const_nhds (x := g x))).norm.pow 2)
  simpa only [integral_zero] using h

/-- The actual native smoothings converge in angular energy L² at each interior cutoff. -/
theorem nativeRadialMollification_energy_convergence (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n m : ℕ) :
    (∀ k : ℕ, Integrable (fun x => ‖nativeRadialMollification q s amplitude t n m k x-
      nativeInteriorAngularEnergy q s amplitude t n m x‖^2) radialMeasure) ∧
    Tendsto (fun k : ℕ => ∫ x, ‖nativeRadialMollification q s amplitude t n m k x-
      nativeInteriorAngularEnergy q s amplitude t n m x‖^2 ∂radialMeasure) atTop (𝓝 0) :=
  mollification_L2_convergence _ (interior_continuous q s amplitude t n m)
    (interior_compact q s amplitude t n m) m

/-- The actual projected radial derivatives converge in original angular L²;
the convergence statement keeps every endpoint product-rule term. -/
theorem nativeRadialMollification_radial_convergence (q : XiZeroCopy) (s amplitude : ℂ)
    (t : ℝ) (n m : ℕ) :
    let g : ℝ → D4BMModularCore.Space := fun x => D4BMModularCore.embedding
      (nativeInteriorAngularEnergy q s amplitude t n m x)
    (∀ k : ℕ, Integrable (fun x => ‖deriv (fun y => D4BMModularCore.embedding
      (nativeRadialMollification q s amplitude t n m k y)) x-deriv g x‖^2) radialMeasure) ∧
    Tendsto (fun k : ℕ => ∫ x, ‖deriv (fun y => D4BMModularCore.embedding
      (nativeRadialMollification q s amplitude t n m k y)) x-deriv g x‖^2 ∂radialMeasure) atTop (𝓝 0) := by
  intro g
  have hc : HasCompactSupport g := (interior_compact q s amplitude t n m).comp_left
    (map_zero D4BMModularCore.embedding)
  have h := mollification_L2_convergence (deriv g)
    (contDiff_one_iff_deriv.mp (interior_value_contDiff q s amplitude t n m)).2 hc.deriv m
  simpa only [(nativeRadialMollification_value_hasDerivAt q s amplitude t n m _ _).deriv] using h


private theorem toLp_tendsto_of_integral_sq {E : Type*} [NormedAddCommGroup E]
    (a : ℕ → ℝ → E) (b : ℝ → E) (ha : ∀ k, MemLp (a k) 2 radialMeasure)
    (hb : MemLp b 2 radialMeasure)
    (hl : Tendsto (fun k => ∫ x, ‖a k x-b x‖^2 ∂radialMeasure) atTop (𝓝 0)) :
    Tendsto (fun k => (ha k).toLp (a k)) atTop (𝓝 (hb.toLp b)) := by
  have hn (k : ℕ) : ‖(ha k).toLp (a k)-hb.toLp b‖^2 =
      ∫ x, ‖a k x-b x‖^2 ∂radialMeasure := by
    rw [← MemLp.toLp_sub,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [((ha k).sub hb).coeFn_toLp] with x hx
    rw [hx]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun k => ‖(ha k).toLp (a k)-hb.toLp b‖^2) atTop (𝓝 0) := by
    simpa only [hn] using hl
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using h

private structure NativeFormFamily where
  field : ℝ → D4BMModularCore.energyDomain
  continuous : Continuous field
  compact : HasCompactSupport field
  valueC1 : ContDiff ℝ 1 (fun x => D4BMModularCore.embedding (field x))

private theorem NativeFormFamily.valueMem (h : NativeFormFamily) : MemLp h.field 2 radialMeasure :=
  h.continuous.memLp_of_hasCompactSupport h.compact
private def NativeFormFamily.radialField (h : NativeFormFamily) : ℝ → D4BMModularCore.Space :=
  deriv (fun x => D4BMModularCore.embedding (h.field x))
private theorem NativeFormFamily.radialMem (h : NativeFormFamily) : MemLp h.radialField 2 radialMeasure :=
  ((contDiff_one_iff_deriv.mp h.valueC1).2).memLp_of_hasCompactSupport
    ((h.compact.comp_left (map_zero D4BMModularCore.embedding)).deriv)
private def NativeFormFamily.weightedField (h : NativeFormFamily) (x : ℝ) : D4BMModularCore.energyDomain :=
  angularWeight x • h.field x
private theorem NativeFormFamily.weightedCompact (h : NativeFormFamily) : HasCompactSupport h.weightedField := by
  apply h.compact.mono
  intro x hx hz
  apply hx
  change angularWeight x • h.field x = 0
  rw [hz,smul_zero]
private theorem NativeFormFamily.weightedMem (h : NativeFormFamily) : MemLp h.weightedField 2 radialMeasure :=
  (angularWeight_smooth.continuous.smul h.continuous).memLp_of_hasCompactSupport h.weightedCompact
private def NativeFormFamily.value (h : NativeFormFamily) : RadialAngularSpace := h.valueMem.toLp h.field
private def NativeFormFamily.radial (h : NativeFormFamily) : Lp D4BMModularCore.Space 2 radialMeasure :=
  h.radialMem.toLp h.radialField
private def NativeFormFamily.weighted (h : NativeFormFamily) : RadialAngularSpace :=
  h.weightedMem.toLp h.weightedField
private def NativeFormFamily.graph (h : NativeFormFamily) : JointEnergySpace :=
  WithLp.toLp 2 ![radialFamilySlot 0 h.value,bochnerL2ProductEquiv h.radial,
    radialFamilySlot 1 h.weighted,radialFamilySlot 2 h.weighted]

private theorem angularWeight_norm_le_one (x : ℝ) : ‖angularWeight x‖ ≤ 1 := by
  rw [angularWeight,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.cosh_pos x)]
  simpa only [one_div] using (div_le_one (Real.cosh_pos x)).mpr (Real.one_le_cosh x)

private theorem NativeFormFamily.graph_tendsto (a : ℕ → NativeFormFamily) (b : NativeFormFamily)
    (hv : Tendsto (fun k => ∫ x, ‖(a k).field x-b.field x‖^2 ∂radialMeasure) atTop (𝓝 0))
    (hr : Tendsto (fun k => ∫ x, ‖(a k).radialField x-b.radialField x‖^2 ∂radialMeasure) atTop (𝓝 0)) :
    Tendsto (fun k => (a k).graph) atTop (𝓝 b.graph) := by
  have hv' : Tendsto (fun k => (a k).value) atTop (𝓝 b.value) :=
    toLp_tendsto_of_integral_sq _ _ (fun k => (a k).valueMem) b.valueMem hv
  have hr' : Tendsto (fun k => (a k).radial) atTop (𝓝 b.radial) :=
    toLp_tendsto_of_integral_sq _ _ (fun k => (a k).radialMem) b.radialMem hr
  have hw : Tendsto (fun k => ∫ x, ‖(a k).weightedField x-b.weightedField x‖^2 ∂radialMeasure)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun x => sq_nonneg _)) ?_ hv
    intro k
    have hwi := ((a k).weightedMem.sub b.weightedMem)
    have hvi := ((a k).valueMem.sub b.valueMem)
    apply integral_mono ((memLp_two_iff_integrable_sq_norm hwi.aestronglyMeasurable).mp hwi)
      ((memLp_two_iff_integrable_sq_norm hvi.aestronglyMeasurable).mp hvi)
    intro x
    change ‖angularWeight x • (a k).field x-angularWeight x • b.field x‖^2 ≤ _
    rw [← smul_sub,norm_smul]
    change (‖angularWeight x‖*‖(a k).field x-b.field x‖)^2 ≤ ‖(a k).field x-b.field x‖^2
    have he : ‖angularWeight x‖*‖(a k).field x-b.field x‖ ≤ ‖(a k).field x-b.field x‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (angularWeight_norm_le_one x)
        (norm_nonneg ((a k).field x-b.field x))
    nlinarith [norm_nonneg ((a k).field x-b.field x),
      mul_nonneg (norm_nonneg (angularWeight x)) (norm_nonneg ((a k).field x-b.field x))]
  have hw' : Tendsto (fun k => (a k).weighted) atTop (𝓝 b.weighted) :=
    toLp_tendsto_of_integral_sq _ _ (fun k => (a k).weightedMem) b.weightedMem hw
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => SpatialSpace)).tendsto _ |>.comp
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact (radialFamilySlot 0).continuous.tendsto _ |>.comp hv'
  · exact bochnerL2ProductEquiv.continuous.tendsto _ |>.comp hr'
  · exact (radialFamilySlot 1).continuous.tendsto _ |>.comp hw'
  · exact (radialFamilySlot 2).continuous.tendsto _ |>.comp hw'

private def NativeFormFamily.ofSmooth (h : RadialEnergyFamily) : NativeFormFamily where
  field := h.field
  continuous := h.smooth.continuous
  compact := h.compact
  valueC1 := (D4BMModularCore.embedding.restrictScalars ℝ).contDiff.comp (h.smooth.of_le (by simp))

private theorem NativeFormFamily.ofSmooth_graph (h : RadialEnergyFamily) :
    (NativeFormFamily.ofSmooth h).graph = familyPacketLift h.packet := by
  have he : (angularEnergySlot 0).compLp h.radial = (NativeFormFamily.ofSmooth h).radial := by
    apply Lp.ext
    filter_upwards [(angularEnergySlot 0).coeFn_compLp h.radial,h.radial_ae,
      (NativeFormFamily.ofSmooth h).radialMem.coeFn_toLp] with x h0 h1 h2
    change ((NativeFormFamily.ofSmooth h).radial : ℝ → D4BMModularCore.Space) x =
      (NativeFormFamily.ofSmooth h).radialField x at h2
    rw [h0,h1,h2]
    change D4BMModularCore.embedding (deriv h.field x) =
      deriv (fun y => D4BMModularCore.embedding (h.field y)) x
    have hd := ((D4BMModularCore.embedding.restrictScalars ℝ).hasFDerivAt (x := h.field x)).comp_hasDerivAt x
      ((h.smooth.differentiable (by simp)).differentiableAt.hasDerivAt (x := x))
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using hd.deriv.symm
  rw [familyPacketLift_apply]
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · exact congrArg bochnerL2ProductEquiv he.symm
  · rfl
  · rfl

private def nativeInteriorFormFamily (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) : NativeFormFamily where
  field := nativeInteriorAngularEnergy q s amplitude t n m
  continuous := interior_continuous q s amplitude t n m
  compact := interior_compact q s amplitude t n m
  valueC1 := interior_value_contDiff q s amplitude t n m

/-- The original four differential components of the actual interior native primitive. -/
def nativeInteriorJointGraph (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) : JointEnergySpace :=
  (nativeInteriorFormFamily q s amplitude t n m).graph

/-- The actual cusp and endpoint cutoff primitive belongs to the ORIGINAL joint form domain. -/
theorem nativeInteriorJointGraph_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n m : ℕ) :
    nativeInteriorJointGraph q s amplitude t n m ∈ jointDomain := by
  have ht := NativeFormFamily.graph_tendsto
    (fun k => NativeFormFamily.ofSmooth (nativeRadialMollificationFamily q s amplitude t n m k))
    (nativeInteriorFormFamily q s amplitude t n m)
    (nativeRadialMollification_energy_convergence q s amplitude t n m).2
    (nativeRadialMollification_radial_convergence q s amplitude t n m).2
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  apply Eventually.of_forall
  intro k
  rw [NativeFormFamily.ofSmooth_graph]
  exact nativeRadialMollification_graph_mem q s amplitude t n m k

private def nativeCuspFormFamily (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) : NativeFormFamily where
  field := nativeTimePrimitiveAngularEnergy q s amplitude t n
  continuous := nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n
  compact := nativeTimePrimitiveAngularEnergy_compact q s amplitude t n
  valueC1 := nativeTimePrimitiveAngularEnergy_value_contDiff q s amplitude t n

/-- The original four differential components of the actual cusp-cutoff native primitive. -/
def nativeCuspJointGraph (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) : JointEnergySpace :=
  (nativeCuspFormFamily q s amplitude t n).graph

/-- Removing the endpoint cutoff admits the actual cusp-cutoff primitive to the original joint domain. -/
theorem nativeCuspJointGraph_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    nativeCuspJointGraph q s amplitude t n ∈ jointDomain := by
  have hv := (nativeTimePrimitiveAngularEnergy_endpoint_value_convergence q s amplitude t n).2
  have hr : Tendsto (fun m => ∫ x, ‖(nativeInteriorFormFamily q s amplitude t n m).radialField x-
      (nativeCuspFormFamily q s amplitude t n).radialField x‖^2 ∂radialMeasure) atTop (𝓝 0) := by
    have hd : deriv (fun x => D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n x)) =
        nativeTimePrimitiveAngularRadial q s amplitude t n :=
      funext (fun x => (nativeTimePrimitiveAngularEnergy_value_hasDerivAt q s amplitude t n x).deriv)
    change Tendsto (fun m => ∫ x, ‖deriv (fun y => D4BMModularCore.embedding
      (nativeInteriorAngularEnergy q s amplitude t n m y)) x-
      deriv (fun y => D4BMModularCore.embedding (nativeTimePrimitiveAngularEnergy q s amplitude t n y)) x‖^2
      ∂radialMeasure) atTop (𝓝 0)
    simp only [interior_value,hd]
    exact (nativeTimePrimitiveAngularEnergy_endpoint_radial_convergence q s amplitude t n).2
  have ht := NativeFormFamily.graph_tendsto (nativeInteriorFormFamily q s amplitude t n)
    (nativeCuspFormFamily q s amplitude t n) hv hr
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  exact Eventually.of_forall (nativeInteriorJointGraph_mem q s amplitude t n)

end
end RHTower.D4BMNativeResponse
