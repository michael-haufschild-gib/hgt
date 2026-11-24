import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ProductRank

/-! # The effect of changing the sign of a single terminal perturbation -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Multiply the final control by a scalar, preserving all earlier bonds. -/
def scaleLast (n : ℕ) (s : ℂ) : Controls (n+1) →L[ℂ] Controls (n+1) :=
  ContinuousLinearMap.pi fun i => (if i=Fin.last n then s else 1) •
    ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : Fin (n+1) => ℂ) i

theorem scaleLast_axis {n : ℕ} (s : ℂ) (i : Fin (n+1)) :
    scaleLast n s (axis i)=(if i=Fin.last n then s else 1) • axis i := by
  funext j
  change (if j=Fin.last n then s else 1)*axis i j=(if i=Fin.last n then s else 1)*axis i j
  by_cases h : j=i
  · rw [h]
  · simp [axis,h]

private theorem response_smul_head {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : ℂ) (v : E) (w : List E) (f : E→ℂ) (x : E) :
    response (s • v::w) f x=s*response (v::w) f x := by
  let g (t : ℂ) := response w f (x+t • v)
  have he : (fun t : ℂ => response w f (x+t • (s • v)))=fun t => g (s*t) := by
    funext t; simp only [g,smul_smul,mul_comm t s]
  change deriv _ 0=s*deriv g 0
  rw [he,deriv_comp_mul_left,mul_zero]

/-- Every ending-one word takes exactly one copy of the sector sign. -/
theorem mixed_scaleLast (n : ℕ) (s : ℂ) (v : List (Fin n)) (f : Controls (n+1)→ℂ) :
    mixed (letters false v) (f ∘ scaleLast n s) 0=s*mixed (letters false v) f 0 := by
  let L := scaleLast n s
  have h (p u : Controls (n+1)) (t : ℂ) : L (p+t • u)=L p+t • L u := by simp
  have hm : (((v.map Fin.castSucc).map axis).map L)=(v.map Fin.castSucc).map axis := by
    simp only [L,List.map_map,Function.comp_def,scaleLast_axis,Fin.castSucc_ne_last,if_false,one_smul]
  rw [←response_coordinate,←response_coordinate]
  change response _ (f ∘ L) 0=_
  rw [response_affine L L h]
  change response (L (axis (Fin.last n))::((v.map Fin.castSucc).map axis).map L) f (L 0)=_
  rw [hm,map_zero,show L (axis (Fin.last n))=s • axis (Fin.last n) by simp [L,scaleLast_axis],response_smul_head]
  rfl

#print axioms mixed_scaleLast
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
