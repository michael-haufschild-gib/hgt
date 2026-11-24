import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Words

/-! # Physical coordinate words for the directed spin chain -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

abbrev Controls (n : ℕ) := Fin n → ℂ

/-- Split off the last physical field from the preceding bond coordinates. -/
def splitControls (n : ℕ) : Controls (n+1) →L[ℂ] (Controls n × ℂ) :=
  (ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : Fin (n+1) => ℂ) i.castSucc).prod
    (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _ : Fin (n+1) => ℂ) (Fin.last n))

def axis {n : ℕ} (i : Fin n) : Controls n := Pi.single i 1

@[simp] theorem split_cast {n : ℕ} (i : Fin n) : splitControls n (axis i.castSucc)=(axis i,0) := by
  apply Prod.ext
  · funext j
    change axis i.castSucc j.castSucc=axis i j
    simp [axis,Pi.single_apply]
  · change axis i.castSucc (Fin.last n)=0
    simp [axis]

@[simp] theorem split_last (n : ℕ) : splitControls n (axis (Fin.last n))=(0,1) := by
  apply Prod.ext
  · funext j
    change axis (Fin.last n) j.castSucc=0
    simp [axis]
  · change axis (Fin.last n) (Fin.last n)=1
    simp [axis]

/-- Write the terminal multiplicity outside all preceding physical coordinates. -/
def letters {n : ℕ} (j : Bool) (w : List (Fin n)) : List (Fin (n+1)) :=
  match j with
  | false => Fin.last n :: w.map Fin.castSucc
  | true => Fin.last n :: Fin.last n :: w.map Fin.castSucc

theorem letters_length {n : ℕ} (j : Bool) (w : List (Fin n)) : (letters j w).length=order j+w.length := by
  cases j <;> simp [letters,order] <;> omega

theorem split_letters {n : ℕ} (j : Bool) (w : List (Fin n)) :
    ((letters j w).map axis).map (splitControls n) = extendWord j (w.map axis) := by
  have he : ((w.map Fin.castSucc).map axis).map (splitControls n)=liftWord (w.map axis) := by
    simp only [liftWord,List.map_map,Function.comp_def,split_cast]
  cases j <;> simp only [letters,List.map_cons,split_last,he] <;> rfl

theorem response_split {n : ℕ} (w : List (Fin (n+1))) (f : Controls n × ℂ → ℂ) :
    response (w.map axis) (fun p => f (splitControls n p)) 0 =
      response ((w.map axis).map (splitControls n)) f 0 := by
  have h (p v : Controls (n+1)) (t : ℂ) :
      splitControls n (p+t • v)=splitControls n p+t • splitControls n v := by simp
  simpa only [map_zero,Function.comp_def] using response_affine (splitControls n) (splitControls n) h (w.map axis) f 0

/-- The directional construction uses ordinary repeated partial derivatives in
the individual physical coefficients. -/
theorem mixed_letters {n : ℕ} (j : Bool) (w : List (Fin n)) (f : Controls n × ℂ → ℂ) :
    mixed (letters j w) (fun p => f (splitControls n p)) 0 =
      response (extendWord j (w.map axis)) f 0 := by
  rw [← response_coordinate]
  exact (response_split (letters j w) f).trans (by rw [split_letters])

#print axioms mixed_letters
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
