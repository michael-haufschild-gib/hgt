import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.IntegerOrbit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.StableFace

/-! # Recurrence on every lattice through a regular scalar face -/

open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
open EmptyVisitFlux
noncomputable section
variable {I : Type} [Fintype I]

/-- At a simple face one sign of each small phase displacement keeps
the packet inside its closed arc. Only the closing gap can decide the sign. -/
theorem opposite_at_face {w : I → ℝ} {r v : ℝ} {i j : I} (hr : 0<r)
    (hf : inwardFace w r v i j) :
    ∀ᶠ z in 𝓝 (0:UnitAddTorus I), flow w v+z∈anchoredUnitArc i r ∨
      flow w v+(-z)∈anchoredUnitArc i r := by
  let p := flow w v
  let O := ((↑) : ℝ → UnitAddCircle) '' Ioo 0 r
  have ho : IsOpen O := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  let interiorOK (z : UnitAddTorus I) := ∀ k, k≠i → k≠j → (p+z) k-(p+z) i∈O
  have hint : ∀ᶠ z in 𝓝 (0:UnitAddTorus I), interiorOK z := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hki : k=i
    · exact Eventually.of_forall fun _ h => (h hki).elim
    by_cases hkj : k=j
    · exact Eventually.of_forall fun _ _ h => (h hkj).elim
    have hc : Continuous (fun z : UnitAddTorus I => (p+z) k-(p+z) i) :=
      (continuous_const.add (continuous_apply k)).sub (continuous_const.add (continuous_apply i))
    have hpoint : (p+0) k-(p+0) i∈O := by simpa only [add_zero] using hf.2.2 k hki hkj
    have hh : ∀ᶠ z in 𝓝 (0:UnitAddTorus I), (p+z) k-(p+z) i∈O :=
      hc.continuousAt.tendsto (ho.mem_nhds hpoint)
    exact hh.mono fun _ hz _ _ => hz
  have hneg : Tendsto (fun z : UnitAddTorus I => -z) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.continuousAt (x:=(0:UnitAddTorus I))).tendsto
  let V := ((↑) : ℝ → UnitAddCircle) '' Ioo (-r) r
  have hv : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hz : (0:UnitAddCircle)∈V := ⟨0,⟨neg_lt_zero.mpr hr,hr⟩,AddCircle.coe_zero _⟩
  have hd : ∀ᶠ z in 𝓝 (0:UnitAddTorus I), z j-z i∈V :=
    ((continuous_apply j).sub (continuous_apply i)).continuousAt.tendsto
      (hv.mem_nhds (by simpa using hz))
  have anchor (z : UnitAddTorus I) (hi : interiorOK z) (hj : (p+z) j-(p+z) i∈forwardUnitArc r) :
      p+z∈anchoredUnitArc i r := by
    intro k hki
    by_cases hkj : k=j
    · simpa only [hkj] using hj
    · exact image_mono Ioo_subset_Icc_self (hi k hki hkj)
  filter_upwards [hint,hneg.eventually hint,hd] with z hp hn hgap
  obtain ⟨x,hx,hxe⟩ := hgap
  have he : p j-p i=(r:UnitAddCircle) := hf.2.1
  rcases le_total x 0 with h|h
  · apply Or.inl (anchor z hp ?_)
    refine ⟨r+x,⟨by linarith only [hx.1],by linarith only [h]⟩,?_⟩
    rw [AddCircle.coe_add,←he,hxe]
    change p j-p i+(z j-z i)=p j+z j-(p i+z i)
    abel
  · apply Or.inr (anchor (-z) hn ?_)
    refine ⟨r-x,⟨by linarith only [hx.2],by linarith only [h]⟩,?_⟩
    rw [AddCircle.coe_sub,←he,hxe]
    change p j-p i-(z j-z i)=p j+ -z j-(p i+ -z i)
    abel

/-- The tick gap is finite for every step, even when the orbit closure
is tangent to the face and all its affordable ticks lie on the boundary. -/
theorem face_tick_gaps {w : I → ℝ} {r v : ℝ} {i j : I} (hr : 0<r)
    (hf : inwardFace w r v i j) (τ : ℝ) :
    ∃ B : ℕ, ∀ n : ℤ, ∃ j ∈ Icc n (n+B), flow w (v+(j:ℝ)*τ)∈enclosingUnitArc r := by
  let f : ℤ →+ UnitAddTorus I :=
    { toFun := fun n => flow w ((n:ℝ)*τ)
      map_zero' := by funext k; simp [flow]
      map_add' := by intro a b; funext k; simp [flow,add_mul] }
  let A := {z : UnitAddTorus I | flow w v+z∈anchoredUnitArc i r}
  have hc : IsClosed A := (isClosed_anchoredUnitArc i r).preimage (continuous_const.add continuous_id)
  obtain ⟨B,hB⟩ := opposite_contact f hc (opposite_at_face hr hf)
  refine ⟨B,fun n => ?_⟩
  obtain ⟨l,hl,he⟩ := hB n
  refine ⟨l,hl,mem_iUnion.mpr ⟨i,?_⟩⟩
  have hsplit : flow w (v+(l:ℝ)*τ)=flow w v+f l := by
    funext k
    simp [f,flow,add_mul]
  rwa [hsplit]

#print axioms face_tick_gaps
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
