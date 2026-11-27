import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.BoxFrequency

/-! # Gaussian coefficient blocks missed by an adaptively chosen set of wires -/
open Finset Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section

private def rowCoord (w : ℕ) (p : ℕ × Fin w × PathPauliDirections) :=
  (w*p.1+p.2.1.val,p.2.2)

private theorem row_index {w : ℕ} (hw : 0<w) (k : ℕ) (i : Fin w) :
    (w*k+i.val)/w=k := by rw [Nat.mul_add_div hw,Nat.div_eq_of_lt i.isLt,add_zero]

private theorem row_injective {w : ℕ} (hw : 0<w) : Function.Injective (rowCoord w) := by
  rintro ⟨k,i,d⟩ ⟨l,j,f⟩ h
  obtain ⟨hrow,hdir⟩ := Prod.mk.inj h
  change w*k+i.val=w*l+j.val at hrow
  have he := congrArg (·/w) hrow
  rw [row_index hw,row_index hw] at he
  subst l
  exact Prod.ext rfl (Prod.ext (Fin.ext (Nat.add_left_cancel hrow)) hdir)

/-- Every prescribed positive-width coefficient box of fixed length
occurs in a block disjoint from any set of fewer than a positive
fraction of the prefix wires, even when that set uses the entire draw. -/
theorem gaussian_untouched_boxes {w : ℕ} (hw : 0<w) (ref : Fin w × PathPauliDirections → ℝ)
    (η : ℝ) (hη : 0<η) :
    ∃ p > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop,
      ∀ F : Finset ℕ, (F.card:ℝ)<p*m → ∃ k<m,
        (∀ i : Fin w, w*k+i.val∉F) ∧ ∀ a : Fin w × PathPauliDirections,
          |ω (w*k+a.1.val,a.2)-ref a|≤η := by
  classical
  let lo a := ref a-η
  let hi a := ref a+η
  obtain ⟨p,hp,h⟩ := gaussian_disjoint_box_frequency (rowCoord w) (row_injective hw) lo hi
    (fun a => by dsimp [lo,hi]; linarith only [hη])
  refine ⟨p,hp,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with m hm
  intro F hF
  let G := (Finset.range m).filter fun k => ∀ a, ω (rowCoord w (k,a)) ∈ Icc (lo a) (hi a)
  let J := F.image (·/w)
  have hc : J.card<G.card := (card_image_le (s:=F)).trans_lt (by exact_mod_cast hF.trans_le hm)
  have hex : ∃ k∈G, k∉J := by
    by_contra! hbad
    exact hc.not_ge (card_le_card hbad)
  obtain ⟨k,hk,hout⟩ := hex
  obtain ⟨hk',hr⟩ := mem_filter.mp hk
  refine ⟨k,mem_range.mp hk',fun i htouch => hout ?_,fun a => ?_⟩
  · exact mem_image.mpr ⟨w*k+i.val,htouch,row_index hw k i⟩
  · obtain ⟨hl,hu⟩ := hr a
    change ref a-η ≤ ω (w*k+a.1.val,a.2) at hl
    change ω (w*k+a.1.val,a.2) ≤ ref a+η at hu
    exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

#print axioms gaussian_untouched_boxes
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
