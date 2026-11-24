import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.CubeErosion
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.ChordSeparation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOperatorWindow

/-! # Enlarging an operator ball by independent phase displacements -/
open Matrix Set MeasureTheory Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Add all phase shifts in a centered coordinate cube of side r turns. -/
def phaseCube (A : Set (UnitAddTorus I)) (r : ℝ) : Set (UnitAddTorus I) :=
  (fun p : UnitAddTorus I × (I→ℝ) => p.1+(fun i => (p.2 i:UnitAddCircle))) ''
    (A ×ˢ univ.pi (fun _ => Icc (-r/2) (r/2)))

omit [Fintype I] [DecidableEq I] in
theorem closed_phaseCube {A : Set (UnitAddTorus I)} (hA : IsClosed A) (r : ℝ) :
    IsClosed (phaseCube A r) := by
  have hc : Continuous (fun p : UnitAddTorus I × (I→ℝ) => p.1+(fun i => (p.2 i:UnitAddCircle))) :=
    continuous_fst.add (continuous_pi fun i =>
      (AddCircle.continuous_mk' 1).comp ((continuous_apply i).comp continuous_snd))
  exact ((hA.isCompact.prod (isCompact_univ_pi fun _ => isCompact_Icc)).image hc).isClosed

omit [Fintype I] in
theorem packet_continuous : Continuous (packet (I:=I)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i=j
  · subst j
    simp only [packet,diagonal_apply_eq]
    exact (continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).comp
      ((AddCircle.continuous_toCircle (T:=1)).comp (continuous_apply i))
  · simpa only [packet,diagonal_apply_ne _ h] using
      (continuous_const : Continuous (fun _ : UnitAddTorus I => (0:ℂ)))

omit [Fintype I] [DecidableEq I] in
theorem phaseCube_zero (A : Set (UnitAddTorus I)) : phaseCube A 0=A := by
  ext z
  constructor
  · rintro ⟨⟨x,w⟩,⟨hx,hw⟩,rfl⟩
    have hz (i : I) : w i=(0:ℝ) := le_antisymm
      (by simpa only [zero_div] using (hw i (mem_univ i)).2)
      (by simpa only [neg_zero,zero_div] using (hw i (mem_univ i)).1)
    have he : w=0 := funext hz
    subst w
    simpa only [Pi.zero_apply,AddCircle.coe_zero,show (fun _ : I => (0:UnitAddCircle))=0 from rfl,add_zero] using hx
  · intro hz
    refine ⟨(z,0),⟨hz,fun _ _ => by simp⟩,?_⟩
    change z+(fun _ : I => ((0:ℝ):UnitAddCircle))=z
    simp only [AddCircle.coe_zero,show (fun _ : I => (0:UnitAddCircle))=0 from rfl,add_zero]

/-- The radius already spent on phase uncertainty subtracts directly
from the angular clearance to an antipodal eigenvector. -/
theorem volume_phaseCube_chord {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    {ε r g : ℝ} (hr : 0≤r) (hg : 0≤g) (hrg : r+g<1)
    (he : ε<2*Real.cos (Real.pi*(r+g)/2)) :
    volume (phaseCube {z : UnitAddTorus I | ‖C-packet z‖≤ε} r) ≤
      ENNReal.ofReal (1-g)^Fintype.card I := by
  let A := {z : UnitAddTorus I | ‖C-packet z‖≤ε}
  let F := phaseCube A (r+g)
  have hF : IsClosed F := closed_phaseCube (isClosed_le (continuous_const.sub packet_continuous).norm continuous_const) _
  have hcut (i : I) (z : UnitAddTorus I) : ∃ t : UnitAddCircle, z+Pi.single i t∉F := by
    obtain ⟨t,v,hv,hker⟩ := antipodal_fiber hC i z
    refine ⟨t,?_⟩
    rintro ⟨⟨x,u⟩,⟨hx,hu⟩,hz⟩
    rw [←hz] at hker
    have habs (j : I) : |u j|≤(r+g)/2 := abs_le.mpr
      ⟨by simpa only [neg_div] using (hu j (mem_univ _)).1,(hu j (mem_univ _)).2⟩
    exact he.not_ge ((antipodal_separation x u hrg.le habs hv hker).trans hx)
  let c : UnitAddTorus I := fun _ => ((-g/2:ℝ):UnitAddCircle)
  let E := cubeOrigins F g Finset.univ
  have hsub : phaseCube A r ⊆ (fun x : UnitAddTorus I => x+c) ⁻¹' E := by
    rintro _ ⟨⟨x,w⟩,⟨hx,hw⟩,rfl⟩ u hu _
    let v (j : I) := w j+(-g/2)+u j
    refine ⟨(x,v),⟨hx,?_⟩,?_⟩
    · intro i _
      have hwi := hw i (mem_univ i)
      change -(r+g)/2≤v i ∧ v i≤(r+g)/2
      dsimp only [v]
      constructor <;> linarith only [hwi.1,hwi.2,(hu i).1,(hu i).2]
    · funext i
      change x i+((w i+(-g/2)+u i:ℝ):UnitAddCircle)=((x i+(w i:UnitAddCircle))+((-g/2:ℝ):UnitAddCircle))+(u i:UnitAddCircle)
      rw [AddCircle.coe_add,AddCircle.coe_add]
      abel
  have hE := (closed_cubeOrigins hF g Finset.univ).measurableSet
  have hμ : volume F≤1 := (measure_mono (subset_univ F)).trans_eq (by simp)
  calc
    _ ≤ volume E := (measure_mono hsub).trans_eq
      ((measurePreserving_add_right volume c).measure_preimage hE.nullMeasurableSet)
    _ ≤ ENNReal.ofReal (1-g)^Fintype.card I*volume F := by
      simpa only [Finset.card_univ] using cube_volume_bound hF hcut hg (by linarith only [hr,hrg]) Finset.univ
    _ ≤ _ := (mul_le_mul_right hμ _).trans_eq (mul_one _)

/-- An independent phase uncertainty of r turns enlarges the sharp
fixed-target volume exponent from x to x+r. -/
theorem volume_phaseCube_ball {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ))
    {x r : ℝ} (hx : 0≤x) (hr : 0≤r) (hxr : x+r<1) :
    volume (phaseCube {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x} r) ≤
      ENNReal.ofReal (x+r)^Fintype.card I := by
  let a := x+r
  have ha : 0≤a := add_nonneg hx hr
  have ht : Tendsto (fun y : ℝ => ENNReal.ofReal y^Fintype.card I) (𝓝[>] a)
      (𝓝 (ENNReal.ofReal a^Fintype.card I)) := by
    have hpow := ENNReal.continuous_ofReal.comp (continuous_id.pow (Fintype.card I) : Continuous (fun y : ℝ => y^Fintype.card I))
    rw [←ENNReal.ofReal_pow ha]
    apply Filter.Tendsto.congr' _ (hpow.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ENNReal.ofReal_pow (ha.trans (le_of_lt (show a<y from hy))) _
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxr)] with y hy hy'
  have hxy : x+r<y := hy
  have hy₁ : y<1 := hy'
  have hprice := strictMonoOn_zeroGateArcTolerance_full
    (show x∈Icc (0:ℝ) 1 from ⟨hx,by linarith only [hr,hxr]⟩)
    (show y-r∈Icc (0:ℝ) 1 from ⟨by linarith only [hxy,hx],by linarith only [hy₁,hr]⟩)
    (show x<y-r by linarith only [hxy])
  have he : 2*Real.cos (Real.pi*(r+(1-y))/2)=zeroGateArcTolerance (y-r) := by
    rw [show Real.pi*(r+(1-y))/2=Real.pi/2-Real.pi*(y-r)/2 by ring,Real.cos_pi_div_two_sub]
    rfl
  have h := volume_phaseCube_chord hC hr (sub_nonneg.mpr hy₁.le)
    (by linarith only [hx,hxy] : r+(1-y)<1) (hprice.trans_eq he.symm)
  simpa only [sub_sub_cancel] using h

#print axioms volume_phaseCube_ball
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
