import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIngoingFullCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonRegularity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCorrectionTemporalRestoration

/-!
# Actual causal metric current and finite-time horizon support

The original retarded potential agrees on exterior coordinate neighborhoods with its smooth
horizon extension. Its coexact stream has the exact ordered two-jet under the original
static-to-ingoing coordinate change. Reconstructing the metric before differentiation gives
precisely the complete Einstein action current, retaining both angular fluxes and source
contacts. Only metric values and first derivatives are identified with the stream table;
actual second metric derivatives are not replaced.

On each static-time slab bounded above by T, the original onset makes the stream, every jet
used by the current, and the current itself exactly zero for 1 < R < 1 + exp(-2*(T+1)). This
neighborhood depends on T. It supplies no growing-time limit, positive-ingoing-time horizon
cancellation, complete finite-part pairing, fixed-clock extinction, or proof of RH.
-/

open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMActualIngoingCurrent
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMIngoingCoordinates

/-- Original ingoing coordinates of a static point. -/
def ingoingPoint (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0+tortoise (x 1),x 1,x 2,x 3]

def ingoingDifferential (r : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi ![
    ContinuousLinearMap.proj 0+(r^2-1)⁻¹ • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1,ContinuousLinearMap.proj 2,ContinuousLinearMap.proj 3]

private theorem ingoing_hasFDerivAt (x : Fin 4 → ℝ) (hr : 1<x 1) :
    HasFDerivAt ingoingPoint (ingoingDifferential (x 1)) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · have ht := HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
      (f := fun z : Fin 4 → ℝ => z 1) x
      (tortoise_hasDerivAt (x 1) hr) (hasFDerivAt_apply 1 x)
    simpa [ingoingPoint,ingoingDifferential,Function.comp_def,Pi.add_apply]
      using! (hasFDerivAt_apply 0 x).add ht
  · exact hasFDerivAt_apply 1 x
  · exact hasFDerivAt_apply 2 x
  · exact hasFDerivAt_apply 3 x

private theorem differential_basis (r : ℝ) (i : Fin 4) :
    ingoingDifferential r (Pi.single i 1)=Pi.single i 1+
      (if i=1 then (r^2-1)⁻¹ else 0) • Pi.single 0 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [ingoingDifferential]

private theorem first_shift {F : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hr : 1<x 1) (hF : DifferentiableAt ℝ F (ingoingPoint x)) (i : Fin 4) :
    coordDeriv i (fun z => F (ingoingPoint z)) x =
      coordDeriv i F (ingoingPoint x)+
        (if i=1 then coordDeriv 0 F (ingoingPoint x)/((x 1:ℂ)^2-1) else 0) := by
  have h := hF.hasFDerivAt.comp x (ingoing_hasFDerivAt x hr)
  change (fderiv ℝ (F ∘ ingoingPoint) x) (Pi.single i 1) = _
  rw [h.fderiv,ContinuousLinearMap.comp_apply,differential_basis]
  simp only [map_add,map_smul,coordDeriv]
  split_ifs <;> simp [Complex.real_smul,div_eq_mul_inv,mul_comm]

private theorem partial_hasFDerivAt {F : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hF : ContDiffAt ℝ 2 F x) (j : Fin 4) :
    HasFDerivAt (coordDeriv j F)
      ((fderiv ℝ (fderiv ℝ F) x).flip (Pi.single j 1)) x := by
  have h := ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa [coordDeriv] using h.clm_apply (hasFDerivAt_const (Pi.single j 1) x)

private theorem first_shift_germ {F : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hr : 1<x 1) (hF : ContDiffAt ℝ 2 F (ingoingPoint x)) (j : Fin 4) :
    coordDeriv j (fun z => F (ingoingPoint z)) =ᶠ[𝓝 x]
      (fun z => coordDeriv j F (ingoingPoint z)+
        (if j=1 then coordDeriv 0 F (ingoingPoint z)/((z 1:ℂ)^2-1) else 0)) := by
  have hloc := (ingoing_hasFDerivAt x hr).continuousAt.tendsto.eventually
    (hF.eventually (by norm_num))
  filter_upwards [hloc,(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr] with z hz hzr
  exact first_shift hzr (hz.differentiableAt (by norm_num)) j

private theorem partial_add {F G : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : Fin 4) :
    coordDeriv i (fun y => F y+G y) x=coordDeriv i F x+coordDeriv i G x := by
  simp only [coordDeriv,fderiv_fun_add hF hG,add_apply]

private theorem partial_mul {F G : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : Fin 4) :
    coordDeriv i (fun y => F y*G y) x=coordDeriv i F x*G x+F x*coordDeriv i G x := by
  simp only [coordDeriv,fderiv_fun_mul hF hG,add_apply,
    smul_apply,smul_eq_mul]
  ring

private theorem inverse_horizon_derivative (x : Fin 4 → ℝ) (hr : 1<x 1) :
    HasFDerivAt (fun z : Fin 4 → ℝ => 1/((z 1:ℂ)^2-1))
      ((-2*(x 1:ℂ)/((x 1:ℂ)^2-1)^2) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1))) x := by
  have hf : (x 1:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show (x 1)^2-1 ≠ 0 by nlinarith)
  have hR := (hasDerivAt_id (x 1)).ofReal_comp
  have h := (hasDerivAt_const (x 1) (1:ℂ)).div ((hR.pow 2).sub_const 1) hf
  have h' : HasDerivAt (fun r : ℝ => 1/((r:ℂ)^2-1))
      (-2*(x 1:ℂ)/((x 1:ℂ)^2-1)^2) (x 1) := by
    convert! h using 1
    simp only [id_eq,Complex.ofReal_one,Pi.pow_apply]
    ring
  have houter : HasFDerivAt (fun r : ℝ => 1/((r:ℂ)^2-1))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-2*(x 1:ℂ)/((x 1:ℂ)^2-1)^2)) (x 1) :=
    h'.hasFDerivAt
  have hcoord : HasFDerivAt (fun z : Fin 4 → ℝ => z 1)
      (ContinuousLinearMap.proj 1 : (Fin 4 → ℝ) →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have hd := houter.comp x hcoord
  convert! hd using 1
  ext v
  simp [Complex.real_smul,mul_comm]

private theorem inverse_horizon_partial (x : Fin 4 → ℝ) (hr : 1<x 1) (i : Fin 4) :
    coordDeriv i (fun z : Fin 4 → ℝ => 1/((z 1:ℂ)^2-1)) x=
      if i=1 then -2*(x 1:ℂ)/((x 1:ℂ)^2-1)^2 else 0 := by
  rw [coordDeriv,(inverse_horizon_derivative x hr).fderiv]
  by_cases hi : i=1
  · subst i
    simp
  · simp [hi,Ne.symm hi]

/-- Every ordered derivative of the original coordinate substitution is retained. -/
theorem ofField_ingoing_comp {F : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hr : 1<x 1) (hF : ContDiffAt ℝ 2 F (ingoingPoint x)) :
    ofField (fun z => F (ingoingPoint z)) x=
      D4BMIngoingFullCurrent.toStatic (x 1) (ofField F (ingoingPoint x)) := by
  ext i j
  · rfl
  · exact first_shift hr (hF.differentiableAt (by norm_num)) i
  · change coordDeriv i (coordDeriv j (fun z => F (ingoingPoint z))) x = _
    have hg := first_shift_germ hr hF j
    have hA (k : Fin 4) : DifferentiableAt ℝ
        (fun z => coordDeriv k F (ingoingPoint z)) x :=
      ((partial_hasFDerivAt hF k).comp x (ingoing_hasFDerivAt x hr)).differentiableAt
    have hD (k : Fin 4) := first_shift hr (partial_hasFDerivAt hF k).differentiableAt i
    by_cases hj : j=1
    · subst j
      have he : coordDeriv 1 (fun z => F (ingoingPoint z)) =ᶠ[𝓝 x]
          (fun z => coordDeriv 1 F (ingoingPoint z)+coordDeriv 0 F (ingoingPoint z)*
            (1/((z 1:ℂ)^2-1))) := by simpa only [ite_true,mul_one_div] using hg
      rw [coordDeriv,he.fderiv_eq]
      change coordDeriv i (fun z => coordDeriv 1 F (ingoingPoint z)+
        coordDeriv 0 F (ingoingPoint z)*(1/((z 1:ℂ)^2-1))) x = _
      have hprod : DifferentiableAt ℝ (fun z : Fin 4 → ℝ =>
          coordDeriv 0 F (ingoingPoint z)*(1/((z 1:ℂ)^2-1))) x :=
        (hA 0).mul (inverse_horizon_derivative x hr).differentiableAt
      rw [partial_add (hA 1) hprod,
        partial_mul (hA 0) (inverse_horizon_derivative x hr).differentiableAt,
        hD 1,hD 0,inverse_horizon_partial x hr i]
      by_cases hi : i=1
      · simp only [D4BMIngoingFullCurrent.toStatic,ofField,hi,ite_true,and_self]
        have hf : (x 1:ℂ)^2-1 ≠ 0 := by exact_mod_cast (show (x 1)^2-1 ≠ 0 by nlinarith)
        field_simp [hf]
        ring
      · simp only [D4BMIngoingFullCurrent.toStatic,ofField,hi,ite_false,ite_true,false_and,add_zero]
        ring
    · have he : coordDeriv j (fun z => F (ingoingPoint z)) =ᶠ[𝓝 x]
          (fun z => coordDeriv j F (ingoingPoint z)) := by simpa only [hj,ite_false,add_zero] using hg
      rw [coordDeriv,he.fderiv_eq]
      change coordDeriv i (fun z => coordDeriv j F (ingoingPoint z)) x = _
      rw [hD j]
      simp only [D4BMIngoingFullCurrent.toStatic,ofField,hj,ite_false,and_false,add_zero]

open D4BMModularCore D4BMOriginalHorizonRegularity D4BMOriginalCausalPotential

/-- A fixed physical coordinate neighborhood crossing the future horizon. -/
def HorizonPoint := {x : Fin 4 → ℝ // 0<x 0 ∧ 1/3<x 1 ∧ x 1<3 ∧ 0<x 3}

/-- The original causal potential in physical ingoing radius and angular height. -/
def potential (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  horizonPotential q branch amp (x 0) ((x 1-1)/(x 1+1)) (x 2) (Real.log (x 3))

private theorem compact_radius_bounds (x : HorizonPoint) :
    -(1/2:ℝ)<(x.val 1-1)/(x.val 1+1) ∧ (x.val 1-1)/(x.val 1+1)<1/2 := by
  have hd : 0<x.val 1+1 := by linarith [x.property.2.1]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith [x.property.2.1]
  · apply (div_lt_iff₀ hd).mpr
    linarith [x.property.2.2.1]

/-- Joint regularity is inherited from the constructed original retarded source integral. -/
theorem potential_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : HorizonPoint) :
    ContDiffAt ℝ ∞ (potential q branch amp) x.val := by
  have hb := compact_radius_bounds x
  have hp := horizonPotential_smooth q branch amp
    ![x.val 0,(x.val 1-1)/(x.val 1+1),x.val 2,Real.log (x.val 3)] x.property.1 hb.1 hb.2
  have hd : x.val 1+1 ≠ 0 := by linarith [x.property.2.1]
  have hc : ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ =>
      ![z 0,(z 1-1)/(z 1+1),z 2,Real.log (z 3)]) x.val := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 0).contDiffAt
    · exact ((contDiff_apply ℝ ℝ 1).contDiffAt.sub contDiffAt_const).div
        ((contDiff_apply ℝ ℝ 1).contDiffAt.add contDiffAt_const) hd
    · exact (contDiff_apply ℝ ℝ 2).contDiffAt
    · exact (contDiff_apply ℝ ℝ 3).contDiffAt.log x.property.2.2.2.ne'
  have hcomp := hp.comp x.val hc
  exact hcomp

private theorem partial_smooth {F : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (hF : ContDiffAt ℝ ∞ F x) (i : Fin 4) : ContDiffAt ℝ ∞ (coordDeriv i F) x := by
  have h : ContDiffAt ℝ ((∞:ℕ∞ω)+1) F x := by simpa using hF
  exact (h.fderiv_right le_rfl).clm_apply contDiffAt_const

/-- Both original angular coexact components of the reconstructed causal stream. -/
def stream (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (j : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  (x 1:ℂ)*(if j=0 then coordDeriv 3 (potential q branch amp) x
    else -coordDeriv 2 (potential q branch amp) x)

/-- All actual causal stream derivatives exist across the horizon. -/
theorem stream_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (j : Fin 2) (x : HorizonPoint) :
    ContDiffAt ℝ ∞ (stream q branch amp j) x.val := by
  have h := potential_smooth q branch amp x
  have hr : ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ => (z 1:ℂ)) x.val :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x.val (contDiff_apply ℝ ℝ 1).contDiffAt
  fin_cases j
  · exact hr.mul (partial_smooth h 3)
  · exact hr.mul (partial_smooth h 2).neg

private theorem exp_tortoise (r : ℝ) (hr : 1<r) :
    Real.exp (2*tortoise r)=(r-1)/(r+1) := by
  rw [tortoise,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0),Real.exp_sub,
    Real.exp_log (by linarith : 0<r-1),Real.exp_log (by linarith : 0<r+1)]

/-- The smooth physical field equals the original full causal potential before differentiation. -/
theorem potential_eq_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : HorizonPoint) (hr : 1<x.val 1) :
    potential q branch amp x.val=originalPotential q branch amp
      (x.val 0) (x.val 0-2*tortoise (x.val 1)) (x.val 2) (Real.log (x.val 3)) := by
  have ht : tortoise (x.val 1)<0 := by
    have hl := Real.log_lt_log (by linarith : 0<x.val 1-1)
      (by linarith : x.val 1-1<x.val 1+1)
    dsimp only [tortoise]
    linarith
  let p : NNReal := ⟨x.val 0,x.property.1.le⟩
  let width : NNReal := ⟨-2*tortoise (x.val 1),by linarith⟩
  have he : Real.exp (-(width:ℝ))=(x.val 1-1)/(x.val 1+1) := by
    change Real.exp (-(-2*tortoise (x.val 1))) = _
    rw [neg_mul,neg_neg,exp_tortoise _ hr]
  have h := originalPotential_eq_horizonPotential q branch amp p width x.property.1
    (by rw [he]; exact (compact_radius_bounds x).2) (x.val 2) (Real.log (x.val 3))
  rw [he] at h
  have hpcoe : (p : ℝ) = x.val 0 := rfl
  have hwcoe : (width : ℝ) = -2*tortoise (x.val 1) := rfl
  change horizonPotential q branch amp (x.val 0) ((x.val 1-1)/(x.val 1+1))
    (x.val 2) (Real.log (x.val 3)) = _
  simpa only [hpcoe,hwcoe,sub_eq_add_neg,neg_mul] using h.symm


/-- Original full retarded potential expressed in physical ingoing coordinates. -/
def originalIngoingPotential (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : Fin 4 → ℝ) : ℂ :=
  originalPotential q branch amp (x 0) (x 0-2*tortoise (x 1)) (x 2) (Real.log (x 3))

/-- Equality holds on a coordinate neighborhood, so every actual derivative is identified. -/
theorem potential_eq_original_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : HorizonPoint) (hr : 1<x.val 1) :
    potential q branch amp =ᶠ[𝓝 x.val] originalIngoingPotential q branch amp := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds x.property.1,
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt (continuous_apply 1) continuous_const).mem_nhds x.property.2.2.1,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds x.property.2.2.2]
      with z hp hR hR3 hy
  exact potential_eq_original q branch amp ⟨z,hp,by linarith,hR3,hy⟩ hR

/-- Coexact reconstruction from the original full retarded integral. -/
def originalStream (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (j : Fin 2)
    (x : Fin 4 → ℝ) : ℂ :=
  (x 1:ℂ)*(if j=0 then coordDeriv 3 (originalIngoingPotential q branch amp) x
    else -coordDeriv 2 (originalIngoingPotential q branch amp) x)

theorem stream_eq_original_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : HorizonPoint) (hr : 1<x.val 1) (j : Fin 2) :
    stream q branch amp j =ᶠ[𝓝 x.val] originalStream q branch amp j := by
  have hd := (potential_eq_original_germ q branch amp x hr).fderiv (𝕜 := ℝ)
  filter_upwards [hd] with z hz
  simp only [stream,originalStream,coordDeriv,hz]

theorem originalStream_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : HorizonPoint) (hr : 1<x.val 1) (j : Fin 2) :
    ContDiffAt ℝ ∞ (originalStream q branch amp j) x.val :=
  (stream_smooth q branch amp j x).congr_of_eventuallyEq
    (stream_eq_original_germ q branch amp x hr j).symm

/-- Original stream in static coordinates, with the unchanged ingoing onset. -/
def originalStaticStream (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (j : Fin 2)
    (x : Fin 4 → ℝ) : ℂ := originalStream q branch amp j (ingoingPoint x)

/-- The complete current formula acts on actual coordinate derivatives of the original
causal stream. The test remains an arbitrary smooth ingoing field. -/
theorem original_causal_current (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : 0 < ingoingPoint x.val 0)
    (hR : x.val 1<3) (Q : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (hQ : ∀ j, ContDiffAt ℝ 2 (Q j) (ingoingPoint x.val)) :
    D4BMPhysicalLiftCurrent.ingoingAction x
      (fun j => ofField (originalStaticStream q branch amp j) x.val)
      (fun j => ofField (fun z => Q j (ingoingPoint z)) x.val) =
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun j => ofField (originalStream q branch amp j) (ingoingPoint x.val))
      (fun j => ofField (Q j) (ingoingPoint x.val)) := by
  let y : HorizonPoint := ⟨ingoingPoint x.val,hp,by
    simpa [ingoingPoint] using (show (1/3:ℝ)<x.val 1 by linarith [x.property.1]),
    hR,x.property.2⟩
  have hP (j : Fin 2) : ContDiffAt ℝ 2 (originalStream q branch amp j) (ingoingPoint x.val) :=
    (originalStream_smooth q branch amp y x.property.1 j).of_le (WithTop.coe_le_coe.mpr le_top)
  change D4BMPhysicalLiftCurrent.ingoingAction x
    (fun j => ofField (fun z => originalStream q branch amp j (ingoingPoint z)) x.val) _ = _
  simp_rw [ofField_ingoing_comp x.property.1 (hP _),
    ofField_ingoing_comp x.property.1 (hQ _)]
  exact D4BMIngoingFullCurrent.original_ingoing_current x _ _

private theorem partial_germ {F G : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : F =ᶠ[𝓝 x] G) (i : Fin 4) : coordDeriv i F =ᶠ[𝓝 x] coordDeriv i G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L => L (Pi.single i 1)) hy

private theorem ofField_germ {F G : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : F =ᶠ[𝓝 x] G) : ofField F x=ofField G x := by
  ext i j
  · exact h.self_of_nhds
  · exact (partial_germ h i).self_of_nhds
  · exact (partial_germ (partial_germ h j) i).self_of_nhds

/-- Every reconstructed stream derivative vanishes on the open pre-onset region. -/
theorem originalStream_zero_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : Fin 4 → ℝ) (hp : x 0<0) (j : Fin 2) :
    originalStream q branch amp j =ᶠ[𝓝 x] (fun _ => 0) := by
  have hZ : originalIngoingPotential q branch amp =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hp] with z hz
    exact originalPotential_before_onset q branch amp hz.le _ _
  filter_upwards [partial_germ hZ 3,partial_germ hZ 2] with z h3 h2
  simp only [originalStream,h3,h2]
  have hz (i : Fin 4) : coordDeriv i (fun _ : Fin 4 → ℝ => (0:ℂ)) z=0 := by
    exact congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first i) (ofField_constant 0 z)
  simp only [hz,neg_zero,ite_self,mul_zero]

/-- Actual static stream jets are exactly zero before the original ingoing onset. -/
theorem originalStaticStream_jet_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : ingoingPoint x.val 0<0) (j : Fin 2) :
    ofField (originalStaticStream q branch amp j) x.val=constant 0 := by
  have he := (ingoing_hasFDerivAt x.val x.property.1).continuousAt.tendsto.eventually
    (originalStream_zero_germ q branch amp (ingoingPoint x.val) hp j)
  have h := ofField_germ he
  change ofField (fun z => originalStream q branch amp j (ingoingPoint z)) x.val=constant 0
  simpa only [ofField_constant] using h

/-- The entire original current, including temporal and angular components, is zero
before onset against every test two-jet. No bound on the test at the horizon is required. -/
theorem original_current_before_onset (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : ingoingPoint x.val 0<0)
    (Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    D4BMPhysicalLiftCurrent.ingoingAction x
      (fun j => ofField (originalStaticStream q branch amp j) x.val) Q=0 := by
  simp_rw [originalStaticStream_jet_zero q branch amp x hp]
  unfold D4BMPhysicalLiftCurrent.ingoingAction
  simp only [D4BMMixedActionCurrent.stream_complete_action_current]
  ext i
  fin_cases i <;> simp [D4BMMixedActionCurrent.streamCurrentDensity,
    D4BMMixedActionCurrent.streamMasterValue,D4BMMixedActionCurrent.streamAngularAction,
    constant]
  all_goals right
  · change -((1-(x.val 1:ℂ)^2)*((Q 1).first 1*(0-0)))+
      -((Q 1).first 0*(0-0))/((x.val 1:ℂ)^2-1)=0
    simp
  · change -(((x.val 1:ℂ)^2-1)*((Q 0).first 1*(0-0)))-
      -((Q 0).first 0*(0-0))/((x.val 1:ℂ)^2-1)=0
    simp

/-- Explicit horizon neighborhood excluded by the actual causal support, uniformly over
every static-time slab bounded above by `T`. -/
theorem finite_static_slab_pre_onset (T : ℝ) (x : D4BMBackground.ExteriorPoint)
    (hT : x.val 0≤T) (hR : x.val 1<1+Real.exp (-2*(T+1))) :
    ingoingPoint x.val 0<0 := by
  have hlog := Real.log_lt_log (by linarith [x.property.1] : 0<x.val 1-1)
    (by linarith : x.val 1-1<Real.exp (-2*(T+1)))
  rw [Real.log_exp] at hlog
  have hplus := Real.log_pos (show 1<x.val 1+1 by linarith [x.property.1])
  change x.val 0+tortoise (x.val 1)<0
  dsimp only [tortoise]
  linarith

/-- Uniform exact horizon-current exclusion on every finite static-time slab,
including the actual singular physical left QNM as a test. -/
theorem original_current_finite_static_slab (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T : ℝ) (x : D4BMBackground.ExteriorPoint) (hT : x.val 0≤T)
    (hR : x.val 1<1+Real.exp (-2*(T+1)))
    (Q : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    D4BMPhysicalLiftCurrent.ingoingAction x
      (fun j => ofField (originalStaticStream q branch amp j) x.val) Q=0 :=
  original_current_before_onset q branch amp x (finite_static_slab_pre_onset T x hT hR) Q


open D4BMMixedActionCurrent D4BMMetricReconstruction

/-- Actual nonseparated metric reconstructed before any coordinate differentiation. -/
def reconstructedMetric (P : Fin 2 → (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  mixedMatrix (fun a => ((x 1:ℂ)^2-1)*coordDeriv 1 (P a) x)
    (fun a => coordDeriv 0 (P a) x/((x 1:ℂ)^2-1))

private theorem factor_partial (x : Fin 4 → ℝ) (i : Fin 4) :
    coordDeriv i (fun z : Fin 4 → ℝ => (z 1:ℂ)^2-1) x=
      if i=1 then 2*(x 1:ℂ) else 0 := by
  have hR : HasFDerivAt (fun z : Fin 4 → ℝ => (z 1:ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply 1 x)
  have hd := (hR.pow 2).sub_const 1
  rw [coordDeriv,hd.fderiv]
  by_cases hi : i=1
  · subst i
    simp
  · simp [hi,Ne.symm hi]

/-- Metric values and every first coordinate derivative agree with the original stream
jet table. No claim equates the actual metric's second derivatives to zero. -/
theorem reconstructedMetric_first (P : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (x : D4BMBackground.ExteriorPoint) (hP : ∀ a, ContDiffAt ℝ 2 (P a) x.val) :
    (ofMetricField (reconstructedMetric P) x.val).metric=
        (streamMetricJet (x.val 1) (fun a => ofField (P a) x.val)).metric ∧
    (ofMetricField (reconstructedMetric P) x.val).first=
        (streamMetricJet (x.val 1) (fun a => ofField (P a) x.val)).first := by
  have hR : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => (z 1:ℂ)) x.val :=
    Complex.ofRealCLM.differentiableAt.comp x.val (differentiableAt_apply 1 x.val)
  have hF : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => (z 1:ℂ)^2-1) x.val :=
    (hR.pow 2).sub_const 1
  have hD (a : Fin 2) (k : Fin 4) := (partial_hasFDerivAt (hP a) k).differentiableAt
  have hT (a : Fin 2) (k : Fin 4) :
      coordDeriv k (fun z : Fin 4 → ℝ => ((z 1:ℂ)^2-1)*coordDeriv 1 (P a) z) x.val=
      (if k=1 then 2*(x.val 1:ℂ)*coordDeriv 1 (P a) x.val else 0)+
        ((x.val 1:ℂ)^2-1)*coordDeriv k (coordDeriv 1 (P a)) x.val := by
    rw [partial_mul hF (hD a 1),factor_partial]
    split_ifs <;> simp
  have hU (a : Fin 2) (k : Fin 4) :
      coordDeriv k (fun z : Fin 4 → ℝ => coordDeriv 0 (P a) z/((z 1:ℂ)^2-1)) x.val=
      coordDeriv k (coordDeriv 0 (P a)) x.val/((x.val 1:ℂ)^2-1)-
        (if k=1 then 2*(x.val 1:ℂ)*coordDeriv 0 (P a) x.val/((x.val 1:ℂ)^2-1)^2 else 0) := by
    have he : (fun z : Fin 4 → ℝ => coordDeriv 0 (P a) z/((z 1:ℂ)^2-1))=
        (fun z => coordDeriv 0 (P a) z*(1/((z 1:ℂ)^2-1))) := by
      funext z
      rw [mul_one_div]
    rw [he,partial_mul (hD a 0) (inverse_horizon_derivative x.val x.property.1).differentiableAt,
      inverse_horizon_partial x.val x.property.1]
    split_ifs <;> ring
  have hzero (k : Fin 4) : coordDeriv k (fun _ : Fin 4 → ℝ => (0:ℂ)) x.val=0 :=
    congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first k) (ofField_constant 0 x.val)
  constructor
  · rfl
  · funext k i j
    fin_cases i <;> fin_cases j
    all_goals first | exact hzero k | exact hT 0 k | exact hT 1 k | exact hU 0 k | exact hU 1 k

/-- Original Einstein current of the actual metric fields, prior to coordinate change. -/
theorem reconstructedMetric_action (P Q : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (x : D4BMBackground.ExteriorPoint) (hP : ∀ a, ContDiffAt ℝ 2 (P a) x.val)
    (hQ : ∀ a, ContDiffAt ℝ 2 (Q a) x.val) (i : Fin 4) :
    (x.val 1:ℂ)^2/(x.val 3:ℂ)^2*actionSymplectic (D4BMBackground.jet (x.val 1) (x.val 3))
      (ofMetricField (reconstructedMetric P) x.val) (ofMetricField (reconstructedMetric Q) x.val) i=
      streamCurrentDensity (x.val 1) (x.val 3)
        (fun a => ofField (P a) x.val) (fun a => ofField (Q a) x.val) i := by
  have hp := reconstructedMetric_first P x hP
  have hq := reconstructedMetric_first Q x hQ
  rw [D4BMCorrectionAction.actionSymplectic_congr_first _ _ _ _ hp.1 hp.2]
  have hright := D4BMCorrectionAction.actionSymplectic_congr_first
    (D4BMBackground.jet (x.val 1) (x.val 3)) _ _
    (streamMetricJet (x.val 1) (fun a => ofField (P a) x.val)) hq.1 hq.2 i
  have he : actionSymplectic (D4BMBackground.jet (x.val 1) (x.val 3))
      (streamMetricJet (x.val 1) (fun a => ofField (P a) x.val))
      (ofMetricField (reconstructedMetric Q) x.val) i=
      actionSymplectic (D4BMBackground.jet (x.val 1) (x.val 3))
      (streamMetricJet (x.val 1) (fun a => ofField (P a) x.val))
      (streamMetricJet (x.val 1) (fun a => ofField (Q a) x.val)) i := by
    unfold actionSymplectic at hright ⊢
    linear_combination -hright
  rw [he,stream_complete_action_current]


private theorem ingoing_smooth (x : Fin 4 → ℝ) (hr : 1<x 1) :
    ContDiffAt ℝ 2 ingoingPoint x := by
  have hR : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => z 1) x :=
    (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have hm := (hR.sub contDiffAt_const).log (by linarith : x 1-1 ≠ 0)
  have hp := (hR.add contDiffAt_const).log (by linarith : x 1+1 ≠ 0)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt.add ((hm.sub hp).div_const 2)
  · exact hR
  · exact (contDiff_apply ℝ ℝ (2:Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (3:Fin 4)).contDiffAt

/-- Actual metric current in the ingoing chart, including the coordinate-volume factor. -/
def metricIngoingCurrent (x : D4BMBackground.ExteriorPoint)
    (P Q : Fin 2 → (Fin 4 → ℝ) → ℂ) : Fin 4 → ℂ :=
  let w := fun j => (x.val 1:ℂ)^2/(x.val 3:ℂ)^2*actionSymplectic
    (D4BMBackground.jet (x.val 1) (x.val 3))
    (ofMetricField (reconstructedMetric P) x.val) (ofMetricField (reconstructedMetric Q) x.val) j
  ![w 0+w 1/((x.val 1:ℂ)^2-1),w 1,w 2,w 3]

theorem metricIngoingCurrent_eq (P Q : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (x : D4BMBackground.ExteriorPoint) (hP : ∀ a, ContDiffAt ℝ 2 (P a) x.val)
    (hQ : ∀ a, ContDiffAt ℝ 2 (Q a) x.val) :
    metricIngoingCurrent x P Q=D4BMPhysicalLiftCurrent.ingoingAction x
      (fun a => ofField (P a) x.val) (fun a => ofField (Q a) x.val) := by
  unfold metricIngoingCurrent D4BMPhysicalLiftCurrent.ingoingAction
  simp only [reconstructedMetric_action P Q x hP hQ,stream_complete_action_current]

/-- The source's original integral and the actual reconstructed metric, with all derivatives
taken before the action, give exactly the complete ingoing current formula. -/
theorem original_causal_metric_current (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMBackground.ExteriorPoint) (hp : 0 < ingoingPoint x.val 0)
    (hR : x.val 1<3) (Q : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (hQ : ∀ j, ContDiffAt ℝ 2 (Q j) (ingoingPoint x.val)) :
    metricIngoingCurrent x (originalStaticStream q branch amp)
      (fun j z => Q j (ingoingPoint z)) =
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun j => ofField (originalStream q branch amp j) (ingoingPoint x.val))
      (fun j => ofField (Q j) (ingoingPoint x.val)) := by
  let y : HorizonPoint := ⟨ingoingPoint x.val,hp,by
    simpa [ingoingPoint] using (show (1/3:ℝ)<x.val 1 by linarith [x.property.1]),
    hR,x.property.2⟩
  have hP (j : Fin 2) : ContDiffAt ℝ 2 (originalStream q branch amp j) (ingoingPoint x.val) :=
    (originalStream_smooth q branch amp y x.property.1 j).of_le (WithTop.coe_le_coe.mpr le_top)
  have hs (j : Fin 2) : ContDiffAt ℝ 2 (originalStaticStream q branch amp j) x.val :=
    (hP j).comp x.val (ingoing_smooth x.val x.property.1)
  have hqs (j : Fin 2) : ContDiffAt ℝ 2 (fun z => Q j (ingoingPoint z)) x.val :=
    (hQ j).comp x.val (ingoing_smooth x.val x.property.1)
  rw [metricIngoingCurrent_eq _ _ x hs hqs]
  exact original_causal_current q branch amp x hp hR Q hQ

/-- The exact finite-static-time support exclusion holds for actual metric-field currents. -/
theorem original_metric_current_finite_static_slab (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T : ℝ) (x : D4BMBackground.ExteriorPoint) (hT : x.val 0≤T)
    (hR : x.val 1<1+Real.exp (-2*(T+1))) (Q : Fin 2 → (Fin 4 → ℝ) → ℂ)
    (hQ : ∀ j, ContDiffAt ℝ 2 (Q j) x.val) :
    metricIngoingCurrent x (originalStaticStream q branch amp) Q=0 := by
  have hp := finite_static_slab_pre_onset T x hT hR
  have hP (j : Fin 2) : ContDiffAt ℝ 2 (originalStaticStream q branch amp j) x.val := by
    have he := (ingoing_hasFDerivAt x.val x.property.1).continuousAt.tendsto.eventually
      (originalStream_zero_germ q branch amp (ingoingPoint x.val) hp j)
    exact contDiffAt_const.congr_of_eventuallyEq he
  rw [metricIngoingCurrent_eq _ _ x hP hQ]
  exact original_current_finite_static_slab q branch amp T x hT hR _

end RHTower.D4BMActualIngoingCurrent
