import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Coordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Reading

/-! # Transport of the response minors to physical coordinate lists -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem readings_reindex (d : I≃J) (k : I) (w : I→List E) (m : Bool) (f : I→E × ℂ → ℂ) :
    (readings (d k) (fun i => w (d.symm i)) m (fun i => f (d.symm i))).det=(readings k w m f).det := by
  rw [←Matrix.det_reindex_self d (readings k w m f)]
  congr 1
  ext i l
  by_cases h : i=d k
  · subst i
    simp [readings,Matrix.reindex_apply,Matrix.submatrix_apply]
  · have h' : d.symm i≠k := fun he => h ((d.apply_symm_apply i).symm.trans (congrArg d he))
    simp [readings,Matrix.reindex_apply,Matrix.submatrix_apply,h,h']

def nextLabels {n : ℕ} (k : I) (w : I→List (Fin n)) : I⊕I → List (Fin (n+1)) :=
  Sum.elim (fun i => if i=k then [] else letters true (w i))
    (fun i => if i=k then [] else letters false (w i))

omit [Fintype I] in
theorem nextLabels_length {n : ℕ} (k : I) (w : I→List (Fin n)) (hw : ∀ i, (w i).length≤2*n) :
    ∀ i, (nextLabels k w i).length≤2*(n+1) := by
  rintro (i|i) <;> have hi := hw i <;> by_cases he : i=k <;>
    simp [nextLabels,he,letters_length,order] <;> omega

omit [Fintype I] in
theorem split_nextLabels {n : ℕ} (k : I) (w : I→List (Fin n)) (i : I⊕I) :
    ((nextLabels k w i).map axis).map (splitControls n) = nextWords k (fun l => (w l).map axis) i := by
  rcases i with i|i <;> by_cases he : i=k <;> simp [nextLabels,nextWords,he,split_letters,-List.map_map]

/-- Split the last bond in the earlier coordinates while carrying the new
terminal field along as an independent scalar. -/
def splitEarlier (n : ℕ) : (Controls (n+1) × ℂ) →L[ℂ] ((Controls n × ℂ) × ℂ) :=
  ((splitControls n).comp (ContinuousLinearMap.fst ℂ _ _)).prod (ContinuousLinearMap.snd ℂ _ _)

omit [Fintype I] in
theorem readings_coordinates {n : ℕ} (k : I) (v : I→List (Fin (n+1))) (m : Bool)
    (F : I→(Controls n × ℂ) × ℂ → ℂ) :
    readings k (fun i => (v i).map axis) m (fun l => F l ∘ splitEarlier n) =
    readings k (fun i => ((v i).map axis).map (splitControls n)) m F := by
  ext i l
  by_cases he : i=k
  · simp [readings,he]
  · simp only [readings,of_apply,if_neg he]
    change response _ _ ((0:Controls (n+1)),(0:ℂ))=response _ _ ((0:Controls n × ℂ),(0:ℂ))
    rw [read_extendWord,read_extendWord]
    apply congrArg (fun h : ℂ→ℂ => jet m h 0)
    funext t
    exact response_split (v i) (fun p => F l (p,t))

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
