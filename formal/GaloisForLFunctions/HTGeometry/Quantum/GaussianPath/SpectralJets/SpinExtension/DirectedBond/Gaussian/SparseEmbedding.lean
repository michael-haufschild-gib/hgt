import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Coordinates

/-! # Spectral derivatives on affine slices of physical parameter space -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Form a linear combination of physical generators. -/
def synthesis (P : Fin n→E) : Controls n →L[ℂ] E :=
  ∑ i, (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : Fin n => ℂ) i).smulRight (P i)

theorem synthesis_apply (P : Fin n→E) (x : Controls n) : synthesis P x=∑ i, x i • P i := by
  simp [synthesis]

@[simp] theorem synthesis_axis (P : Fin n→E) (i : Fin n) : synthesis P (axis i)=P i := by
  rw [synthesis_apply]
  rw [Finset.sum_eq_single i]
  · simp [axis]
  · intro j _ hj
    simp [axis,hj]
  · simp

/-- Insert every sparse parameter in its physical Pauli coordinate. -/
def embed (x : Controls m) (ι : Fin n→Fin m) (y : Controls n) : Controls m :=
  x+synthesis (fun i => axis (ι i)) y

@[simp] theorem embed_zero (x : Controls m) (ι : Fin n→Fin m) : embed x ι 0=x := by simp [embed]

theorem embed_analytic (x : Controls m) (ι : Fin n→Fin m) : AnalyticAt ℂ (embed x ι) 0 :=
  analyticAt_const.add ((synthesis (fun i => axis (ι i))).analyticAt _)

theorem synthesis_embed (P : Fin m→E) (x : Controls m) (ι : Fin n→Fin m) (y : Controls n) :
    synthesis P (embed x ι y)=synthesis P x+synthesis (P ∘ ι) y := by
  rw [embed,map_add,synthesis_apply (fun i => axis (ι i)),map_sum]
  simp only [map_smul,synthesis_axis,synthesis_apply (P ∘ ι),Function.comp_apply]

theorem mixed_embed (w : List (Fin n)) (F : Controls m→ℂ) (x : Controls m) (ι : Fin n→Fin m) :
    mixed w (F ∘ embed x ι) 0=mixed (w.map ι) F x := by
  let L := synthesis (fun i => axis (ι i))
  have h (y v : Controls n) (t : ℂ) : embed x ι (y+t • v)=embed x ι y+t • L v := by
    simp only [embed,L,map_add,map_smul,add_assoc]
  have hr := response_affine (embed x ι) L h (w.map axis) F 0
  have hw : (w.map axis).map L=(w.map ι).map axis := by
    simp only [L,List.map_map,Function.comp_def,synthesis_axis]
  rw [hw,embed_zero] at hr
  exact (response_coordinate w (F ∘ embed x ι) 0).symm.trans (hr.trans (response_coordinate (w.map ι) F x))

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
